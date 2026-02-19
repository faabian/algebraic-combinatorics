# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#!/usr/bin/env python3
"""Generate LOC and declarations over time charts from git history.

Uses two strategies for speed:
  - LOC and churn: reconstructed from `git log --numstat` in a single call (all commits)
  - Declarations: sampled at ~80 commits (requires reading file contents + regex)

Generates two x-axis versions of each chart:
  - *_by_commit.png: x-axis is commit number
  - *_by_date.png:   x-axis is calendar date
"""

import os
import subprocess
import re
from datetime import datetime

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import matplotlib.dates as mdates

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BRANCH = "HEAD"  # change to e.g. "run20260219" to chart a different branch

_DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|partial|nonrec)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|class)\b",
    re.MULTILINE,
)


def get_loc_history():
    """Get per-commit LOC deltas from git log --numstat (fast, single git call)."""
    result = subprocess.run(
        ["git", "log", "--first-parent", "--reverse", "--numstat",
         "--format=%H %aI", BRANCH, "--", "AlgebraicCombinatorics/"],
        capture_output=True, text=True, cwd=REPO
    )

    commits = []  # [(datetime, hash, added, deleted)]
    current_hash = None
    current_dt = None
    current_added = 0
    current_deleted = 0

    for line in result.stdout.split('\n'):
        stripped = line.strip()

        parts = stripped.split()
        if len(parts) == 2 and len(parts[0]) == 40:
            # New commit header — flush previous
            if current_hash:
                commits.append((current_dt, current_hash, current_added, current_deleted))
            current_hash = parts[0]
            current_dt = datetime.fromisoformat(parts[1])
            current_added = 0
            current_deleted = 0
        elif len(parts) >= 3 and parts[2].endswith('.lean') and '/tex/' not in parts[2]:
            try:
                current_added += int(parts[0])
                current_deleted += int(parts[1])
            except ValueError:
                pass  # binary files

    if current_hash:
        commits.append((current_dt, current_hash, current_added, current_deleted))

    return commits


def count_decls_at_commit(commit_hash):
    """Count declarations at a commit (slow — reads all files)."""
    result = subprocess.run(
        ["git", "ls-tree", "-r", "--name-only", commit_hash, "--", "AlgebraicCombinatorics/"],
        capture_output=True, text=True, cwd=REPO
    )
    lean_files = [f for f in result.stdout.strip().split('\n')
                  if f.endswith('.lean') and f.strip()]

    total_decls = 0
    for f in lean_files:
        r = subprocess.run(
            ["git", "show", f"{commit_hash}:{f}"],
            capture_output=True, text=True, cwd=REPO
        )
        if r.returncode == 0:
            total_decls += len(_DECL_RE.findall(r.stdout))

    return total_decls


def plot_metric(x_vals, y_vals, xlabel, ylabel, title, filename,
                fill_color, line_color, ylim_bottom=0):
    fig, ax = plt.subplots(figsize=(10, 4))
    ax.fill_between(x_vals, y_vals, alpha=0.3, color=fill_color)
    ax.plot(x_vals, y_vals, color=line_color, linewidth=1.5)
    ax.set_xlabel(xlabel)
    ax.set_ylabel(ylabel)
    ax.set_title(title)
    if ylim_bottom is not None:
        ax.set_ylim(bottom=ylim_bottom)
    if isinstance(x_vals[0], datetime):
        ax.xaxis.set_major_formatter(mdates.DateFormatter('%b %d'))
        ax.xaxis.set_major_locator(mdates.AutoDateLocator())
        fig.autofmt_xdate(rotation=30)
    ax.set_xlim(left=x_vals[0])
    ax.grid(axis='y', alpha=0.3)
    fig.tight_layout()
    fig.savefig(filename, dpi=150, facecolor='white')
    print(f"Saved {os.path.basename(filename)}")
    plt.close()


def plot_churn(x_vals, cum_added, cum_deleted, xlabel, title, filename):
    fig, ax = plt.subplots(figsize=(10, 4))
    ax.fill_between(x_vals, cum_added, alpha=0.4, color='#4CAF50', label='Lines added')
    ax.plot(x_vals, cum_added, color='#2E7D32', linewidth=1.5)
    ax.fill_between(x_vals, [-x for x in cum_deleted], alpha=0.4, color='#F44336', label='Lines removed')
    ax.plot(x_vals, [-x for x in cum_deleted], color='#C62828', linewidth=1.5)
    ax.axhline(y=0, color='black', linewidth=0.5)
    ax.set_xlabel(xlabel)
    ax.set_ylabel('Cumulative lines')
    ax.set_title(title)
    if isinstance(x_vals[0], datetime):
        ax.xaxis.set_major_formatter(mdates.DateFormatter('%b %d'))
        ax.xaxis.set_major_locator(mdates.AutoDateLocator())
        fig.autofmt_xdate(rotation=30)
    ax.set_xlim(left=x_vals[0])
    ax.legend(loc='upper left')
    ax.grid(axis='y', alpha=0.3)
    fig.tight_layout()
    fig.savefig(filename, dpi=150, facecolor='white')
    print(f"Saved {os.path.basename(filename)}")
    plt.close()


def main():
    out = f"{REPO}/assets"
    os.makedirs(out, exist_ok=True)

    # ── Fast: LOC and churn from git log --numstat (all commits) ──────
    print("Getting LOC history from git log --numstat...")
    history = get_loc_history()
    print(f"  {len(history)} commits with Lean file changes")

    # Reconstruct cumulative LOC
    cum_loc = 0
    loc_data = []  # [(datetime, commit_num, cum_loc, cum_added, cum_deleted)]
    cum_added = 0
    cum_deleted = 0
    for i, (dt, h, added, deleted) in enumerate(history):
        cum_loc += added - deleted
        cum_added += added
        cum_deleted += deleted
        loc_data.append((dt, i + 1, cum_loc, cum_added, cum_deleted))

    # Skip leading zeros
    loc_data = [d for d in loc_data if d[2] > 0]

    dates = [d[0] for d in loc_data]
    commit_nums = [d[1] for d in loc_data]
    locs = [d[2] for d in loc_data]
    cum_adds = [d[3] for d in loc_data]
    cum_dels = [d[4] for d in loc_data]

    print(f"  Final: {locs[-1]} LOC (commit {commit_nums[-1]})")
    print(f"  Churn: {cum_adds[-1]:,} added, {cum_dels[-1]:,} removed")

    # LOC charts
    plot_metric(commit_nums, locs, 'Commit', 'Lines of Lean code',
                'Lean LOC over time', f"{out}/loc_over_time_by_commit.png",
                '#2196F3', '#1565C0')
    plot_metric(dates, locs, 'Date', 'Lines of Lean code',
                'Lean LOC over time', f"{out}/loc_over_time_by_date.png",
                '#2196F3', '#1565C0')

    # Churn charts
    plot_churn(commit_nums, cum_adds, cum_dels, 'Commit',
               'Code churn over time (Lean files)', f"{out}/churn_over_time_by_commit.png")
    plot_churn(dates, cum_adds, cum_dels, 'Date',
               'Code churn over time (Lean files)', f"{out}/churn_over_time_by_date.png")

    # ── Slow: declarations (sampled ~80 commits) ─────────────────────
    print("\nSampling declarations (slow — reads file contents)...")
    n = len(loc_data)
    if n > 100:
        step = n // 80
        sample_idx = list(range(0, n, step))
        if n - 1 not in sample_idx:
            sample_idx.append(n - 1)
    else:
        sample_idx = list(range(n))

    sampled_commits = [history[loc_data[i][1] - 1] for i in sample_idx]
    sampled_dates = [loc_data[i][0] for i in sample_idx]
    sampled_nums = [loc_data[i][1] for i in sample_idx]

    decls = []
    for si, (dt, h, _, _) in enumerate(sampled_commits):
        nd = count_decls_at_commit(h)
        decls.append(nd)
        if (si + 1) % 10 == 0:
            print(f"  {si+1}/{len(sampled_commits)}: commit {sampled_nums[si]} ({dt.strftime('%Y-%m-%d')}) — {nd} decls")

    print(f"  Final: {decls[-1]} declarations")

    # Declarations charts
    plot_metric(sampled_nums, decls, 'Commit', 'Number of declarations',
                'Lean declarations over time', f"{out}/declarations_over_time_by_commit.png",
                '#4CAF50', '#2E7D32')
    plot_metric(sampled_dates, decls, 'Date', 'Number of declarations',
                'Lean declarations over time', f"{out}/declarations_over_time_by_date.png",
                '#4CAF50', '#2E7D32')


if __name__ == "__main__":
    main()
