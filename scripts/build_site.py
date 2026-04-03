import json
import os
import re
from html.parser import HTMLParser


def clean_latex_title(title):
    title = re.sub(r'\\label\{.*?\}', '', title)
    title = re.sub(r'\\emph\{(.+?)\}', r'\1', title)
    title = re.sub(r'\\textbf\{(.+?)\}', r'\1', title)
    title = re.sub(r'\\cite\[.*?\]\{.*?\}', '', title)
    title = re.sub(r'\\cite\{.*?\}', '', title)
    title = title.replace(r'\"{a}', 'ä').replace(r'\"{o}', 'ö').replace(r'\"{u}', 'ü')
    title = title.replace(r'\"{A}', 'Ä').replace(r'\"{O}', 'Ö').replace(r'\"{U}', 'Ü')
    # Handle non-standard \{x} umlaut encoding (e.g. Lindstr\{o}m)
    _UMLAUT = {'a': 'ä', 'o': 'ö', 'u': 'ü', 'A': 'Ä', 'O': 'Ö', 'U': 'Ü'}
    title = re.sub(r'\\{([aouAOU])}', lambda m: _UMLAUT[m.group(1)], title)
    title = title.replace('--', '–') # en-dash
    title = title.replace('(part 1) (part 2)', '(part 1)').replace('(part 2) (part 2)', '(part 2)')
    return re.sub(r' {2,}', ' ', title.replace('\n', ' ')).strip()

def extract_tex_title(tex_path):
    if not os.path.exists(tex_path): return None
    with open(tex_path, 'r', encoding='utf-8') as f: content = f.read()
    cmd_match = re.search(r'\\(?:chapter|section|subsection|subsubsection)(?:\[.*?\])?\{', content)
    if cmd_match:
        start_pos = cmd_match.end()
        depth = 1
        current_pos = start_pos
        while depth > 0 and current_pos < len(content):
            if content[current_pos] == '{': depth += 1
            elif content[current_pos] == '}': depth -= 1
            current_pos += 1
        title_raw = content[start_pos:current_pos-1]
        return clean_latex_title(title_raw)
    return None

def extract_tex_headings(tex_path):
    mapping = {}
    if not os.path.exists(tex_path): return mapping
    with open(tex_path, 'r', encoding='utf-8') as f: content = f.read()
    
    current_heading = None
    pattern = re.compile(r'\\(?:chapter|section|subsection|subsubsection)(?:\[.*?\])?\{|\\label\{')
    
    pos = 0
    while True:
        match = pattern.search(content, pos)
        if not match: break
        start = match.start()
        end = match.end()
        if match.group(0) == r'\label{':
            close_idx = content.find('}', end)
            if close_idx != -1:
                label = content[end:close_idx]
                if current_heading: mapping[label] = current_heading
                pos = close_idx + 1
            else:
                pos = end
        else:
            depth = 1
            curr = end
            while depth > 0 and curr < len(content):
                if content[curr] == '{': depth += 1
                elif content[curr] == '}': depth -= 1
                curr += 1
            raw_title = content[end:curr-1]
            current_heading = clean_latex_title(raw_title)
            pos = curr
    return mapping

def get_clean_chapter_title(chapter):
    tex_path = chapter.get('source_path')
    if tex_path:
        tex_title = extract_tex_title(tex_path)
        if tex_title: return tex_title
    title = chapter['title']
    if ": (" in title: title = title.split(": (")[0]
    if title.startswith("ac-"): title = title[3:].replace("-", " ").title()
    return clean_latex_title(title)

class BlueprintContentParser(HTMLParser):
    def __init__(self):
        super().__init__()
        self.theorems = {}
        self.lean_entries = {}
        self.latex_links = {}
        self.current_id = None
        self.capture_type = None
        self.capture_html = []
        self.capture_depth = 0
        self.skip_depth = 0

    def handle_starttag(self, tag, attrs):
        attrs_dict = dict(attrs)

        if tag == "div" and "id" in attrs_dict:
            tid = attrs_dict["id"]
            if "_thmwrapper" in attrs_dict.get("class", ""):
                self.latex_links[tid] = tid
            if any(tid.startswith(p) for p in ["prop.", "thm.", "lem.", "cor.", "def.", "exa."]):
                self.current_id = tid
                
        if self.current_id and tag == "div" and "class" in attrs_dict:
            classes = attrs_dict["class"].split()
            if any(c.endswith("_thmmain") for c in classes):
                self.capture_type = 'math'
                self.capture_depth = 1
                self.capture_html = []
                self.skip_depth = 0
                return 

        if self.current_id and tag == "div" and "class" in attrs_dict:
            classes = attrs_dict["class"].split()
            if "lean-entry" in classes:
                if self.capture_type == 'math':
                    self.theorems[self.current_id] = "".join(self.capture_html)
                self.capture_type = 'lean'
                self.capture_depth = 0 
                self.capture_html = []
                self.skip_depth = 0

        if self.capture_type:
            if tag == "div" and "class" in attrs_dict:
                classes = attrs_dict["class"].split()
                if any(c in ["thm_header_extras", "thm_header_hidden_extras"] for c in classes):
                    self.skip_depth = 1
                    return
            
            if tag == "span" and "class" in attrs_dict:
                if "equation_label" in attrs_dict["class"].split():
                    self.skip_depth = 1
                    return

            if self.skip_depth > 0:
                self.skip_depth += 1
                return

            if tag == "div":
                self.capture_depth += 1
            
            new_attrs = []
            for k, v in attrs:
                if k == "href" and v:
                    if v.startswith("sect") and not v.startswith("http"):
                        v = "blueprint/" + v
                new_attrs.append((k, v))
            
            attr_str = " ".join([f'{k}="{v}"' if v is not None else k for k, v in new_attrs])
            self.capture_html.append(f"<{tag} {attr_str}>" if attr_str else f"<{tag}>")

    def handle_endtag(self, tag):
        if self.capture_type:
            if self.skip_depth > 0:
                self.skip_depth -= 1
                return

            if tag == "div":
                self.capture_depth -= 1
                if self.capture_depth == 0:
                    if self.capture_type == 'math':
                        self.theorems[self.current_id] = "".join(self.capture_html)
                    elif self.capture_type == 'lean':
                        self.capture_html.append(f"</{tag}>")
                        if self.current_id not in self.lean_entries:
                            self.lean_entries[self.current_id] = []
                        self.lean_entries[self.current_id].append("".join(self.capture_html))
                    self.capture_type = None
                    return

            self.capture_html.append(f"</{tag}>")

    def handle_data(self, data):
        if self.capture_type and self.skip_depth == 0:
            self.capture_html.append(data)
    def handle_entityref(self, name):
        if self.capture_type and self.skip_depth == 0: self.capture_html.append(f"&{name};")
    def handle_charref(self, name):
        if self.capture_type and self.skip_depth == 0: self.capture_html.append(f"&#{name};")

def build_site():
    missing_targets = []
    os.makedirs('site', exist_ok=True)
    if not os.path.exists('manifest.json'):
        print("Error: manifest.json not found — site not built.")
        return
        
    with open('manifest.json', 'r') as f: manifest = json.load(f)
    targets = []
    skipped_ids = {'thm.sf.pieri', 'thm.sf.jt-e', 'thm.det.cauchy', 'cor.lgv.catalan-hankel-det-0'}
    for chapter in manifest['chapters']:
        main_chapter_title = get_clean_chapter_title(chapter)
        tex_path = chapter.get('source_path')
        headings_map = extract_tex_headings(tex_path) if tex_path else {}
        for target in chapter['target_theorems']:
            if target in skipped_ids:
                continue
            sub_heading = headings_map.get(target, main_chapter_title)
            targets.append({
                'id': target, 
                'main_chapter': main_chapter_title,
                'sub_chapter': sub_heading
            })
            
    all_math = {}
    all_lean = {}
    target_latex_links = {}

    if os.path.exists('blueprint/web'):
        for filename in sorted(os.listdir('blueprint/web')):
            if filename.startswith('sect') and filename.endswith('.html'):
                with open(os.path.join('blueprint/web', filename), 'r', encoding='utf-8') as f:
                    content = f.read()
                    parser = BlueprintContentParser()
                    parser.feed(content)
                    for tid in parser.latex_links:
                        target_latex_links[tid] = f"blueprint/{filename}#{tid}"
                    all_math.update(parser.theorems)
                    for tid, entries in parser.lean_entries.items():
                        if tid not in all_lean: all_lean[tid] = []
                        for entry in entries:
                            if entry not in all_lean[tid]:
                                all_lean[tid].append(entry)

    targets_html = f"""<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Formalization - Algebraic Combinatorics</title>
    <link rel="stylesheet" href="blueprint/styles/theme-white.css" />
    <link rel="stylesheet" href="blueprint/styles/amsthm.css" />
    <link rel="stylesheet" href="blueprint/styles/blueprint.css" />
    <script>
      MathJax = {{
        tex: {{ inlineMath: [['$', '$'], ['\\\\(', '\\\\)']], displayMath: [['$$', '$$'], ['\\\\[', '\\\\]']], tags: 'ams' }}
      }};
    </script>
    <script type="text/javascript" src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-chtml.js"></script>
    <style>
        body {{ 
            font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, Helvetica, Arial, sans-serif; 
            line-height: 1.6; color: #24292e; background-color: #ffffff; margin: 0; padding: 0;
            display: flex !important; flex-direction: row !important; height: 100vh !important; overflow: hidden !important; width: 100vw !important;
        }}
        .sidebar {{
            width: 320px; min-width: 320px; overflow-y: auto; background-color: #f6f8fa; border-right: 1px solid #eaecef;
            padding: 1.5rem 1rem; box-sizing: border-box; height: 100vh !important;
            transition: width 0.2s ease, min-width 0.2s ease, padding 0.2s ease;
        }}
        .sidebar.collapsed {{ width: 40px; min-width: 40px; padding: 0.75rem 0; overflow: hidden; }}
        .sidebar.collapsed .sidebar-content {{ display: none; }}
        .sidebar-toggle {{
            display: flex; align-items: center; justify-content: flex-end; gap: 0.35rem; width: 100%;
            background: none; border: none; cursor: pointer; color: #666;
            font-size: 0.78rem; font-weight: 500; padding: 0.3rem 0.5rem; border-radius: 4px; margin-bottom: 0.75rem;
        }}
        .sidebar-toggle:hover {{ color: #222; background: #eaecef; }}
        .sidebar.collapsed .sidebar-toggle {{ justify-content: center; margin-bottom: 0; }}
        .sidebar-header {{ font-weight: 800; font-size: 1.2rem; margin-bottom: 1rem; color: #24292e; padding-left: 0.5rem; }}
        .toc-list {{ list-style: none; padding: 0; margin: 0; font-size: 0.85rem; line-height: 1.4; }}
        .toc-list ul {{ list-style: none; padding-left: 1rem; margin-top: 0.25rem; }}
        .toc-list li {{ margin-bottom: 0.4rem; }}
        .toc-list a {{ color: #0366d6; text-decoration: none; display: block; }}
        .toc-list a:hover {{ text-decoration: underline; }}
        .toc-main > a {{ font-weight: 700; color: #24292e; margin-top: 1rem; font-size: 0.95rem; padding-left: 0.5rem; }}
        .toc-sub > a {{ font-weight: 600; color: #444; margin-top: 0.5rem; display: block; }}
        
        .content-wrapper {{ flex: 1; overflow-y: auto; position: relative; scroll-behavior: smooth; height: 100vh !important; }}
        .container {{ max-width: 1400px; margin: 0 auto; padding: 2rem 3rem 5rem; display: block; }}
        header {{
            position: sticky; top: 0; z-index: 50; background: #f6f8fa;
            border-bottom: 1px solid #d1d5da;
        }}
        .header-inner {{
            max-width: 1400px; margin: 0 auto; padding: 1.25rem 3rem;
            display: flex; justify-content: space-between; align-items: center;
        }}
        .header-left h1 {{ margin: 0; font-size: 2rem; font-weight: 800; letter-spacing: -0.03em; color: #1b1f23; }}
        .header-right {{ display: flex; gap: 1rem; font-weight: 600; font-size: 0.88rem; flex-wrap: wrap; justify-content: flex-end; }}
        .header-right a {{ text-decoration: none; color: #333; }}
        .header-right a:hover {{ color: #0366d6; text-decoration: none; }}
        h1.chapter-heading {{ border-bottom: 1px solid #eaecef; padding-bottom: 0.5rem; margin-top: 4rem; margin-bottom: 2rem; font-size: 1.8rem; font-weight: 700; letter-spacing: -0.02em; color: #1b1f23; font-family: Georgia, Cambria, "Times New Roman", Times, serif; }}
        h2.section-heading {{ margin-top: 2rem; margin-bottom: 1.25rem; font-size: 1.25rem; font-weight: 600; letter-spacing: -0.01em; color: #444; font-family: Georgia, Cambria, "Times New Roman", Times, serif; }}
        
        .theorem-container {{
            margin-bottom: 3rem; padding-top: 0.75rem; border-top: 1px solid #f0f0f0; clear: both; background-color: #ffffff;
        }}
        h1.chapter-heading + .theorem-container,
        h2.section-heading + .theorem-container {{
            border-top: none; padding-top: 0;
        }}
        .theorem-body {{ 
            display: flex; width: 100%; align-items: stretch; gap: 2rem;
        }}
        .pane {{ padding: 0 !important; overflow-x: auto; flex: 1; min-width: 0; }}
        .pane-math {{ background-color: #ffffff; position: relative; font-family: Georgia, Cambria, "Times New Roman", Times, serif !important; }}
        .pane-lean {{ background-color: transparent !important; position: static !important; max-height: none !important; }}
        
        /* Math pane specific cleanup */
        .pane-math {{ font-family: Georgia, Cambria, "Times New Roman", Times, serif !important; }}
        
        .pane-math div[class*="_thmheading"] {{
            display: block !important; margin-bottom: 0 !important; border-bottom: none !important;
            padding-bottom: 0 !important; font-family: Georgia, Cambria, "Times New Roman", Times, serif !important; font-size: 1.05rem !important; font-weight: 600 !important;
            padding-right: 5rem !important;
        }}
        .pane-math div[class*="_thmheading"] span:not([class*="mjx"]) {{
            font-family: Georgia, Cambria, "Times New Roman", Times, serif !important;
        }}
        .pane-math span[class$="_thmlabel"] {{
            margin-left: 0 !important;
        }}
        .pane-math p, .pane-math div[class*="_thmcontent"] {{
            margin-left: 0 !important; margin-top: 0 !important; padding-left: 0 !important; text-indent: 0 !important;
        }}
        .blueprint-entry-link {{
            position: absolute; top: 0; right: 0; color: #6a9ccf !important; text-decoration: none !important;
            font-size: 0.8rem !important; font-weight: 500 !important; font-family: sans-serif !important; z-index: 10;
        }}
        .site-intro {{ margin-bottom: 2.5rem; }}
        .site-intro p {{ margin: 0 0 0.75rem; }}
        .site-intro .intro-main {{ font-size: 1.05rem; line-height: 1.75; color: #24292e; }}
        .site-intro .intro-note {{ font-size: 0.88rem; line-height: 1.6; color: #666; }}
        .site-intro a {{ color: #0366d6; text-decoration: none; }}
        .site-intro a:hover {{ text-decoration: underline; }}
        .cite-block {{ margin-top: 0.75rem; }}
        .cite-label {{ font-size: 0.82rem; font-weight: 600; color: #444; display: block; margin-bottom: 0.4rem; }}
        .cite-block pre {{
            margin: 0.5rem 0 0; padding: 0.85rem 1rem; background: #f6f8fa;
            border: 1px solid #d1d5da; border-radius: 6px;
            font-size: 0.78rem; line-height: 1.55; overflow-x: auto;
            font-family: "SFMono-Regular", Consolas, "Liberation Mono", Menlo, monospace;
            color: #24292e; white-space: pre;
        }}
        .cite-copy {{
            float: right; margin-left: 1rem; font-size: 0.75rem; font-weight: 500;
            color: #0366d6; cursor: pointer; background: none; border: none; padding: 0;
        }}
        .cite-copy:hover {{ text-decoration: underline; }}
    </style>
</head>
<body>
"""

    toc_html = '<nav class="sidebar" id="sidebar">\n<button class="sidebar-toggle" id="sidebar-toggle" onclick="toggleSidebar()" title="Collapse sidebar"><span id="sidebar-toggle-label">Hide</span> &#9664;</button>\n<div class="sidebar-content">\n<div class="sidebar-header">Contents</div>\n<ul class="toc-list">\n'
    main_html = """
    <div class="content-wrapper">
        <header>
            <div class="header-inner">
                <div class="header-left"><h1>Algebraic Combinatorics</h1></div>
                <div class="header-right">
                    <a href="blueprint/index.html">Blueprint</a>
                    <a href="https://github.com/faabian/algebraic-combinatorics/raw/main/blueprint/print/print.pdf" target="_blank">Blueprint PDF</a>
                    <a href="https://github.com/facebookresearch/repoprover/raw/main/auto_textbook_formalization.pdf" target="_blank">Paper</a>
                    <a href="https://github.com/faabian/algebraic-combinatorics">GitHub</a>
                    <a href="docs/index.html">API Docs</a>
                </div>
            </div>
        </header>
        <div class="container">
        <div class="site-intro">
            <p class="intro-main">A Lean 4 formalization of <a href="https://arxiv.org/abs/2506.00738" target="_blank"><em>An Introduction to Algebraic Combinatorics</em></a> by Darij Grinberg, built on Mathlib. Early chapters establish prerequisites (power series, generating functions, permutations); later chapters formalize important results including the Lindström–Gessel–Viennot lemma, q-binomial identities, and symmetric function theory.</p>
            <p class="intro-note">This page shows all 344 formalization targets for quick side-by-side comparison of mathematical statements and their Lean proofs. For full details, see the <a href="blueprint/index.html">Blueprint</a> or the <a href="https://github.com/faabian/algebraic-combinatorics">source on GitHub</a>.</p>
            <div class="cite-block">
                <span class="cite-label">Citation:</span>
                <pre id="bibtex-text"><button class="cite-copy" onclick="copyBibtex()">Copy</button>@misc{{gloecke2025textbook,
  title         = {{Automatic Textbook Formalization}},
  author        = {{Fabian Gloecke and Ahmad Rammal and Charles Arnal and
                   Remi Munos and Vivien Cabannes and Gabriel Synnaeve and
                   Amaury Hayat}},
  year          = {{2025}},
  howpublished  = {{\\url{{https://github.com/facebookresearch/repoprover}}}},
}}</pre>
            </div>
        </div>
"""

    current_main = None
    current_sub = None
    main_id = ""

    for t in targets:
        main_chap = t['main_chapter']
        sub_chap = t['sub_chapter']
        tid = t['id']
        
        if main_chap != current_main:
            if current_main is not None:
                if current_sub is not None:
                    toc_html += '</li>\n'
                toc_html += '</ul></li>\n'
            
            current_main = main_chap
            main_id = re.sub(r'[^a-zA-Z0-9]+', '-', current_main).strip('-').lower()
            toc_html += f'<li class="toc-main"><a href="#{main_id}">{current_main}</a>\n<ul class="toc-sublist">\n'
            main_html += f'<h1 id="{main_id}" class="chapter-heading">{current_main}</h1>\n'
            current_sub = None

        if sub_chap != current_main:
            if sub_chap != current_sub:
                if current_sub is not None:
                    toc_html += '</li>\n'
                current_sub = sub_chap
                sub_id = re.sub(r'[^a-zA-Z0-9]+', '-', current_sub).strip('-').lower()
                if sub_id == main_id: sub_id += "-sec"
                toc_html += f'<li class="toc-sub"><a href="#{sub_id}">{current_sub}</a>\n'
                main_html += f'<h2 id="{sub_id}" class="section-heading">{current_sub}</h2>\n'
        else:
            if current_sub is not None:
                toc_html += '</li>\n'
                current_sub = None

        if tid not in all_math:
            missing_targets.append((tid, 'no statement in blueprint'))
        if tid not in all_lean:
            missing_targets.append((tid, 'no lean entry in blueprint'))

        math_content = all_math.get(tid, f"<p><em>Statement not found in blueprint: {tid}</em></p>")
        math_content = math_content.replace('\\begin{bgroup}', '').replace('\\end{bgroup}', '')
        latex_link = target_latex_links.get(tid, "")
        entries = all_lean.get(tid, [])

        clean_entries = []
        for entry in entries:
            clean_entry = re.sub(r'\blean-side-panel\b', '', entry)
            clean_entry = re.sub(r'\blean-target\b', '', clean_entry)
            clean_entries.append(clean_entry)

        lean_content = "".join(clean_entries) if clean_entries else '<p style="color: #6a737d; font-style: italic;">Not yet linked in blueprint.</p>'

        main_html += f"""
        <div class="theorem-container" id="{tid}">
            <div class="theorem-body">
                <div class="pane pane-math">
                    {f'<a href="{latex_link}" class="blueprint-entry-link" target="_blank">blueprint</a>' if latex_link else ""}
                    {math_content}
                </div>
                <div class="pane pane-lean lean-side-panel">
                    {lean_content}
                </div>
            </div>
        </div>"""
        
    if current_main is not None:
        if current_sub is not None:
            toc_html += '</li>\n'
        toc_html += '</ul></li>\n'
        
    toc_html += '</ul>\n</div>\n</nav>\n'
    main_html += '        </div> <!-- end container -->\n    </div> <!-- end content-wrapper -->\n'
    
    sidebar_js = """<script>
function toggleSidebar() {
    var sidebar = document.getElementById('sidebar');
    var btn = document.getElementById('sidebar-toggle');
    var label = document.getElementById('sidebar-toggle-label');
    sidebar.classList.toggle('collapsed');
    var collapsed = sidebar.classList.contains('collapsed');
    btn.innerHTML = collapsed ? '&#9654;' : '<span id="sidebar-toggle-label">Hide</span> &#9664;';
    btn.title = collapsed ? 'Show contents' : 'Hide contents';
}
if (window.innerWidth < 900) {
    var sidebar = document.getElementById('sidebar');
    var btn = document.getElementById('sidebar-toggle');
    sidebar.classList.add('collapsed');
    btn.innerHTML = '&#9654;';
    btn.title = 'Show contents';
}
function copyBibtex() {
    var pre = document.getElementById('bibtex-text');
    var text = pre.innerText.replace(/^Copy\\n/, '').replace(/^Copy/, '');
    navigator.clipboard.writeText(text.trim());
    var btn = pre.querySelector('.cite-copy');
    btn.textContent = 'Copied!';
    setTimeout(function() {{ btn.textContent = 'Copy'; }}, 1500);
}
</script>"""
    targets_html += toc_html + main_html + sidebar_js + '\n</body>\n</html>'
    
    with open('site/targets.html', 'w', encoding='utf-8') as f: f.write(targets_html)
    with open('site/index.html', 'w', encoding='utf-8') as f:
        f.write('<!DOCTYPE html>\n<html lang="en"><head><meta charset="UTF-8"><meta http-equiv="refresh" content="0; url=targets.html" /><title>Algebraic Combinatorics</title></head><body></body></html>')
    print("Site built successfully.")
    return missing_targets

if __name__ == "__main__": build_site()