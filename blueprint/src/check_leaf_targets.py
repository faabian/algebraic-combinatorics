# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#!/usr/bin/env python3
"""Find terminal (leaf) formalized targets in the blueprint.

A "terminal" target is one that has a \\lean{} declaration but does not
appear in any \\uses{} of any other target. These are endpoints of the
dependency graph.
"""

import re, glob, sys

files = sorted(glob.glob('*.tex'))

# Collect all \uses mentions across all files
all_content = ''
for f in files:
    with open(f) as fh:
        all_content += fh.read()

uses_mentions = set()
for m in re.finditer(r'\\uses\{([^}]+)\}', all_content):
    for label in m.group(1).split(','):
        uses_mentions.add(label.strip())

# Collect all labels with \lean{} and their proof \leanok status
labels = {}

for f in files:
    with open(f) as fh:
        lines = fh.readlines()

    current_label = None
    in_proof = False
    proof_line_count = 0

    for line in lines:
        if '\\begin{proof}' in line:
            in_proof = True
            proof_line_count = 0
            if current_label and current_label in labels:
                labels[current_label]['has_proof'] = True

        if in_proof:
            proof_line_count += 1
            if '\\leanok' in line and proof_line_count <= 4:
                if current_label and current_label in labels:
                    labels[current_label]['proof_leanok'] = True

        if '\\end{proof}' in line:
            in_proof = False

        m2 = re.search(r'\\label\{([a-zA-Z0-9._()-]+)\}', line)
        if m2 and not in_proof:
            current_label = m2.group(1)
            if current_label not in labels:
                labels[current_label] = {
                    'file': f, 'has_lean': False, 'stmt_leanok': False,
                    'has_proof': False, 'proof_leanok': False
                }

        if current_label and not in_proof and '\\lean{' in line:
            labels[current_label]['has_lean'] = True

        if current_label and not in_proof and '\\leanok' in line:
            labels[current_label]['stmt_leanok'] = True

# Filter to formalized targets
formalized = {k: v for k, v in labels.items() if v['has_lean']}
terminal = sorted(k for k in formalized if k not in uses_mentions)

# Classify
sorry_terminal = []  # has proof block but no proof \leanok
proved_terminal = []  # has proof \leanok (or no proof block but stmt \leanok)

for label in terminal:
    info = formalized[label]
    if info['has_proof'] and not info['proof_leanok']:
        sorry_terminal.append(label)
    else:
        proved_terminal.append(label)

print(f"Total formalized targets: {len(formalized)}")
print(f"Terminal (leaf) targets:  {len(terminal)}")
print(f"  - sorry'd leaves:      {len(sorry_terminal)}")
print(f"  - proved leaves:       {len(proved_terminal)}")
print()

if sorry_terminal:
    print("=== Sorry'd terminal targets (have proof block, no proof \\leanok) ===")
    for label in sorry_terminal:
        print(f"  {label}  ({formalized[label]['file']})")
    print()

if '--all' in sys.argv:
    print("=== All terminal targets ===")
    for label in terminal:
        info = formalized[label]
        status = 'SORRY' if (info['has_proof'] and not info['proof_leanok']) else 'ok'
        print(f"  [{status:5s}] {label}  ({info['file']})")
