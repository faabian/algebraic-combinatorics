# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#!/usr/bin/env python3
"""
Thorough check for proof blocks missing \leanok in chapter_*.tex files.

For every \begin{proof}...\end{proof} block, checks if it contains \leanok.
For each proof block WITHOUT \leanok, finds the parent theorem/lemma/etc label
and checks if the parent statement has \leanok.

Reports results grouped by:
  a) Parent has \leanok (important - potentially need fixing)
  b) Parent does NOT have \leanok (expected - whole thing isn't tagged)
"""

import glob
import re
import os

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
TEX_PATTERN = os.path.join(SCRIPT_DIR, "chapter_*.tex")

# Environment types that can have proofs
STATEMENT_ENVS = {
    "theorem", "lemma", "definition", "proposition", "corollary",
    "remark", "example", "claim", "conjecture", "fact", "observation",
}


def parse_file(filepath):
    """Parse a single .tex file and find all proof blocks missing \leanok."""
    with open(filepath, "r") as f:
        lines = f.readlines()

    filename = os.path.basename(filepath)

    # Collect all interesting events with line numbers
    events = []
    for i, line in enumerate(lines, 1):
        stripped = line.strip()

        # Check for \begin{env} / \end{env} where env is a statement type
        for env in STATEMENT_ENVS:
            if f"\\begin{{{env}}}" in stripped:
                events.append(("stmt_begin", i, env))
            if f"\\end{{{env}}}" in stripped:
                events.append(("stmt_end", i, env))

        if "\\begin{proof}" in stripped:
            events.append(("proof_begin", i, None))
        if "\\end{proof}" in stripped:
            events.append(("proof_end", i, None))

        # Check for \label{...}
        label_matches = re.findall(r"\\label\{([^}]+)\}", stripped)
        for lbl in label_matches:
            events.append(("label", i, lbl))

        # Check for \leanok
        if "\\leanok" in stripped:
            events.append(("leanok", i, None))

    # Process events to build structure
    class StatementInfo:
        def __init__(self, env, start_line):
            self.env = env
            self.start_line = start_line
            self.label = None
            self.has_leanok = False

    class ProofInfo:
        def __init__(self, start_line):
            self.start_line = start_line
            self.has_leanok = False
            self.parent_label = None
            self.parent_has_leanok = False

    stmt_stack = []
    proof_stack = []
    in_proof_depth = 0

    # Track most recent statement info for proofs that appear after \end{theorem}
    most_recent_label = None
    most_recent_stmt_leanok = False

    missing_proofs = []

    for event_type, line_no, data in events:
        if event_type == "stmt_begin":
            info = StatementInfo(data, line_no)
            stmt_stack.append(info)

        elif event_type == "stmt_end":
            if stmt_stack:
                finished = stmt_stack.pop()
                most_recent_label = finished.label
                most_recent_stmt_leanok = finished.has_leanok

        elif event_type == "label":
            if in_proof_depth > 0:
                # Labels inside proofs don't count as parent labels
                pass
            elif stmt_stack:
                # Inside a statement env, assign label to innermost
                stmt_stack[-1].label = data
                most_recent_label = data
            else:
                # Label outside any statement
                most_recent_label = data
                most_recent_stmt_leanok = False

        elif event_type == "leanok":
            if in_proof_depth > 0:
                # \leanok inside a proof block
                if proof_stack:
                    proof_stack[-1].has_leanok = True
            elif stmt_stack:
                # \leanok inside a statement environment (not in proof)
                stmt_stack[-1].has_leanok = True
                most_recent_stmt_leanok = True

        elif event_type == "proof_begin":
            in_proof_depth += 1
            info = ProofInfo(line_no)
            # Determine parent
            if stmt_stack:
                info.parent_label = stmt_stack[-1].label
                info.parent_has_leanok = stmt_stack[-1].has_leanok
            else:
                info.parent_label = most_recent_label
                info.parent_has_leanok = most_recent_stmt_leanok
            proof_stack.append(info)

        elif event_type == "proof_end":
            if proof_stack:
                finished_proof = proof_stack.pop()
                if not finished_proof.has_leanok:
                    missing_proofs.append({
                        "file": filename,
                        "proof_line": finished_proof.start_line,
                        "parent_label": finished_proof.parent_label or "(no label found)",
                        "parent_has_leanok": finished_proof.parent_has_leanok,
                    })
            in_proof_depth = max(0, in_proof_depth - 1)

    return missing_proofs


def main():
    files = sorted(glob.glob(TEX_PATTERN))
    if not files:
        print(f"No files matching {TEX_PATTERN}")
        return

    print(f"Scanning {len(files)} chapter_*.tex files...\n")

    all_missing = []
    files_with_issues = set()

    for f in files:
        missing = parse_file(f)
        all_missing.extend(missing)
        if missing:
            files_with_issues.add(os.path.basename(f))

    # Split into two groups
    parent_has_leanok = [m for m in all_missing if m["parent_has_leanok"]]
    parent_no_leanok = [m for m in all_missing if not m["parent_has_leanok"]]

    # Print results
    print("=" * 80)
    print("GROUP A: Proof blocks missing \\leanok WHERE PARENT HAS \\leanok")
    print("         (These are potentially important -- the statement is tagged but")
    print("          the proof is not)")
    print("=" * 80)
    if parent_has_leanok:
        for m in parent_has_leanok:
            print(f"  File: {m['file']}")
            print(f"    Proof at line: {m['proof_line']}")
            print(f"    Parent label:  {m['parent_label']}")
            print()
    else:
        print("  (none found)\n")

    print("=" * 80)
    print("GROUP B: Proof blocks missing \\leanok WHERE PARENT DOES NOT HAVE \\leanok")
    print("         (Expected -- the whole statement+proof isn't tagged)")
    print("=" * 80)
    if parent_no_leanok:
        for m in parent_no_leanok:
            print(f"  File: {m['file']}")
            print(f"    Proof at line: {m['proof_line']}")
            print(f"    Parent label:  {m['parent_label']}")
            print()
    else:
        print("  (none found)\n")

    # Summary
    print("=" * 80)
    print("SUMMARY")
    print("=" * 80)
    print(f"  Total chapter_*.tex files scanned: {len(files)}")
    print(f"  Files with missing \\leanok in proofs: {len(files_with_issues)}")
    print(f"  Total proof blocks missing \\leanok: {len(all_missing)}")
    print(f"    Group A (parent HAS \\leanok):       {len(parent_has_leanok)}")
    print(f"    Group B (parent does NOT have):     {len(parent_no_leanok)}")


if __name__ == "__main__":
    main()
