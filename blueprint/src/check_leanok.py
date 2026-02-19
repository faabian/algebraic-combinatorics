# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#!/usr/bin/env python3
"""
Check which proof blocks in blueprint tex files should get leanok added.
"""

import re
import os
import glob

TEX_DIR = "/home/fgloeckle/alg-comb-exps/blueprint/src"
LEAN_DIR = "/home/fgloeckle/alg-comb-exps/AlgebraicCombinatorics"

THEOREM_ENVS = ['theorem', 'lemma', 'proposition', 'corollary']
ALL_ENVS = THEOREM_ENVS + ['definition', 'convention']

# Files with sorries (filename stem -> sorry count)
# Key is the FULL relative path under AlgebraicCombinatorics/ without .lean
FILES_WITH_SORRIES = {
    'FPS/WeightedSets': 35,
    'SymmetricFunctions/LittlewoodRichardson': 22,
    'SymmetricFunctions/PieriJacobiTrudi': 11,
    'DesnanotJacobi': 9,
    'SignedCounting/AlternatingSums': 5,
    'Details/DominoTilings': 4,
    'PentagonalJacobi': 3,
    'SymmetricFunctions/Definitions': 3,
    'Determinants/LGV2': 2,
    'FPS/InfiniteProducts2': 2,
    'Details/InfiniteProducts2': 2,  # Both InfiniteProducts2 files
    'SymmetricFunctions/SchurBasics': 2,
    'Determinants/LGV1': 1,
    'FPS/InfiniteProducts': 1,
}

def build_lean_file_map():
    """Build a list of (relative_key, full_path) for all lean files."""
    lean_files = []
    for root, dirs, files in os.walk(LEAN_DIR):
        for f in files:
            if f.endswith('.lean'):
                path = os.path.join(root, f)
                # Relative path from LEAN_DIR without .lean extension
                rel = os.path.relpath(path, LEAN_DIR)[:-5]
                lean_files.append((rel, path))
    return lean_files

LEAN_FILES = build_lean_file_map()

def find_decl_in_file(content, short_name):
    """Check if a declaration with short_name exists in the file content."""
    # Handle names with apostrophes by escaping properly
    escaped = re.escape(short_name)
    # Match: theorem/lemma/def/etc. [qualifiers.] short_name
    # The name might be qualified like Perm.lehmerCode_bijective
    pat = re.compile(
        r'(?:noncomputable\s+)?(?:private\s+)?(?:protected\s+)?'
        r'(?:theorem|lemma|def|abbrev|instance)\s+'
        r'(?:\w+\.)*' + escaped + r'(?:\s|$|\.|\{|\(|\[|:)',
        re.MULTILINE
    )
    return pat.search(content)

def find_decl_file(decl_name, lean_contents):
    """Find which lean file contains a declaration."""
    short_name = decl_name.split('.')[-1]
    
    results = []
    for rel, path in LEAN_FILES:
        content = lean_contents.get(rel, '')
        if find_decl_in_file(content, short_name):
            results.append((rel, path))
    
    if len(results) == 1:
        return results[0]
    elif len(results) > 1:
        # Try to disambiguate using the full decl name
        for rel, path in results:
            content = lean_contents.get(rel, '')
            if decl_name in content:
                return (rel, path)
        # Return first match
        return results[0]
    return (None, None)

def check_sorry_in_decl(content, decl_name):
    """Check if a specific declaration in file content contains sorry."""
    short_name = decl_name.split('.')[-1]
    escaped = re.escape(short_name)
    
    pat = re.compile(
        r'(?:noncomputable\s+)?(?:private\s+)?(?:protected\s+)?'
        r'(?:theorem|lemma|def|abbrev|instance)\s+'
        r'(?:\w+\.)*' + escaped + r'(?:\s|$|\.|\{|\(|\[|:)',
        re.MULTILINE
    )
    match = pat.search(content)
    if not match:
        return None
    
    start_pos = match.end()
    
    # Find the next top-level declaration (starts at column 0)
    next_pat = re.compile(
        r'^(?:(?:@\[.*\]\s*\n)?(?:noncomputable\s+)?(?:private\s+)?(?:protected\s+)?'
        r'(?:theorem|lemma|def|abbrev|instance)\s+'
        r'|namespace\s+|section\s|end\s|open\s|variable\s|set_option\s|@\[|#check|#eval|/-)',
        re.MULTILINE
    )
    
    rest = content[start_pos:]
    next_match = next_pat.search(rest)
    
    if next_match:
        body = rest[:next_match.start()]
    else:
        body = rest
    
    return bool(re.search(r'\bsorry\b', body))

def parse_tex_file(filepath):
    """Parse a tex file and find envs where statement has leanok but proof doesn't."""
    with open(filepath, 'r') as f:
        lines = [l.rstrip('\n') for l in f.readlines()]
    
    results = []
    i = 0
    while i < len(lines):
        line = lines[i].strip()
        
        env_match = None
        for env in ALL_ENVS:
            if line.startswith(f'\\begin{{{env}}}'):
                env_match = env
                break
        
        if env_match is None:
            i += 1
            continue
        
        label = None
        lean_decls = None
        stmt_leanok = False
        end_env_line = None
        
        j = i
        while j < len(lines):
            l = lines[j].strip()
            
            label_m = re.search(r'\\label\{([^}]+)\}', l)
            if label_m and label is None:
                lbl = label_m.group(1)
                if not lbl.startswith('eq.'):
                    label = lbl
            
            lean_m = re.search(r'\\lean\{([^}]+)\}', l)
            if lean_m and lean_decls is None:
                lean_decls = lean_m.group(1).strip()
            
            if l.strip() == '\\leanok':
                stmt_leanok = True
            
            if l.startswith(f'\\end{{{env_match}}}'):
                end_env_line = j
                break
            
            j += 1
        
        if end_env_line is None:
            i += 1
            continue
        
        if env_match not in THEOREM_ENVS:
            i = end_env_line + 1
            continue
        
        if not stmt_leanok or not lean_decls:
            i = end_env_line + 1
            continue
        
        # Look for proof block
        k = end_env_line + 1
        found_proof = False
        proof_start = None
        while k < len(lines):
            pl = lines[k].strip()
            if pl == '' or pl.startswith('%'):
                k += 1
                continue
            if pl.startswith('\\begin{proof}'):
                found_proof = True
                proof_start = k
                break
            else:
                break
        
        if not found_proof:
            i = end_env_line + 1
            continue
        
        # Check if proof has leanok
        proof_leanok = False
        m = proof_start + 1
        while m < len(lines):
            pl2 = lines[m].strip()
            if pl2 == '\\leanok':
                proof_leanok = True
                break
            if pl2.startswith('\\end{proof}'):
                break
            if pl2.startswith('\\uses{') or pl2 == '':
                m += 1
                continue
            break
        
        if not proof_leanok:
            results.append({
                'label': label or '(no label)',
                'lean_decls': lean_decls,
                'tex_file': os.path.basename(filepath),
                'line': i + 1,
            })
        
        i = end_env_line + 1
    
    return results

def main():
    all_missing = []
    tex_files = sorted(glob.glob(os.path.join(TEX_DIR, "chapter_*.tex")))
    
    for tf in tex_files:
        missing = parse_tex_file(tf)
        all_missing.extend(missing)
    
    print(f"Found {len(all_missing)} proof blocks with leanok on statement but NOT on proof.\n")
    
    # Build lean file content cache
    lean_contents = {}
    for rel, path in LEAN_FILES:
        try:
            with open(path, 'r') as f:
                lean_contents[rel] = f.read()
        except:
            pass
    
    # Process results
    table = []
    for item in all_missing:
        decl_list = [d.strip() for d in item['lean_decls'].split(',')]
        
        all_clean = True
        any_unknown = False
        decl_details = []
        
        for decl in decl_list:
            rel, path = find_decl_file(decl, lean_contents)
            if rel is None:
                decl_details.append((decl, '???', None))
                any_unknown = True
                continue
            
            if rel not in FILES_WITH_SORRIES:
                decl_details.append((decl, rel, False))
            else:
                has_sorry = check_sorry_in_decl(lean_contents.get(rel, ''), decl)
                decl_details.append((decl, rel, has_sorry))
                if has_sorry is True:
                    all_clean = False
                elif has_sorry is None:
                    any_unknown = True
        
        if any_unknown:
            add_leanok = None
        elif all_clean:
            add_leanok = True
        else:
            add_leanok = False
        
        table.append({
            'label': item['label'],
            'decl_details': decl_details,
            'tex_file': item['tex_file'],
            'add_leanok': add_leanok,
            'line': item['line'],
        })
    
    # Print table
    hdr = f"{'#':<4} {'Label':<55} {'Lean decl(s)':<70} {'File(s)':<35} {'Sorry status':<20} {'Add leanok?'}"
    print(hdr)
    print("=" * len(hdr))
    
    add_count = 0
    no_count = 0
    unknown_count = 0
    
    for idx, row in enumerate(table, 1):
        decl_strs = []
        file_strs = []
        sorry_strs = []
        for decl, rel, has_sorry in row['decl_details']:
            short = decl.split('.')[-1]
            decl_strs.append(short)
            file_strs.append(str(rel).split('/')[-1] if rel else '???')
            if has_sorry is None:
                sorry_strs.append('???')
            elif has_sorry:
                sorry_strs.append('SORRY')
            else:
                sorry_strs.append('clean')
        
        decl_str = ', '.join(decl_strs)
        if len(decl_str) > 68:
            decl_str = decl_str[:65] + '...'
        file_str = ', '.join(sorted(set(file_strs)))
        
        if row['add_leanok'] is True:
            verdict = 'YES'
            add_count += 1
        elif row['add_leanok'] is False:
            verdict = 'NO'
            no_count += 1
        else:
            verdict = '???'
            unknown_count += 1
        
        sorry_info = ', '.join(sorry_strs)
        
        print(f"{idx:<4} {row['label']:<55} {decl_str:<70} {file_str:<35} {sorry_info:<20} {verdict}")
    
    print(f"\n{'='*len(hdr)}")
    print(f"Total: {len(table)} proofs missing leanok on proof block")
    print(f"  Should add leanok:  {add_count}")
    print(f"  Should NOT add:     {no_count}")
    print(f"  Unknown / check:    {unknown_count}")
    
    # Print summary of YES items grouped by tex file
    print(f"\n--- Items to add leanok (by tex file) ---")
    by_file = {}
    for row in table:
        if row['add_leanok'] is True:
            f = row['tex_file']
            if f not in by_file:
                by_file[f] = []
            by_file[f].append(row['label'])
    for f in sorted(by_file):
        print(f"\n  {f}:")
        for lbl in by_file[f]:
            print(f"    - {lbl}")
    
    # Print unknowns for manual review
    if unknown_count > 0:
        print(f"\n--- Unknown items (need manual review) ---")
        for row in table:
            if row['add_leanok'] is None:
                for decl, rel, has_sorry in row['decl_details']:
                    if has_sorry is None:
                        print(f"  {row['label']}: {decl} -> file={rel}")

if __name__ == '__main__':
    main()
