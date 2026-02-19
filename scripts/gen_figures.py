# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#!/usr/bin/env python3
"""
Generate publication-quality figures for PR analysis and growth charts.

Figures are sized for two-column A4 paper (~3.4 inch column width).
All plots are saved as both PNG (300 DPI) and PDF.

Usage:
    cd scripts
    python gen_figures.py
    python gen_figures.py --skip-decls  # Skip slow declarations charts

Output goes to ../assets/
"""

import argparse
import os
import re
import subprocess
from collections import Counter, defaultdict
from datetime import datetime
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.cm as cm
import matplotlib.dates as mdates
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.colors import LogNorm


# ============================================================
# Configuration
# ============================================================

SCRIPT_DIR = Path(__file__).parent.resolve()
REPO = SCRIPT_DIR.parent
BRANCH = "run20260219"
OUT_DIR = REPO / "assets"

# Figure sizing for two-column A4 paper (~3.3 inch column width)
COL_WIDTH = 3.4  # inches (1/2 column width)
THIRD_WIDTH = 2.2  # inches (1/3 column width for 3-up layouts)
FIG_HEIGHT = 2.4  # inches
THIRD_HEIGHT = 1.8  # inches (shorter for compact 3-up)

# Font sizes appropriate for publication
plt.rcParams.update(
    {
        "font.size": 8,
        "axes.titlesize": 9,
        "axes.labelsize": 8,
        "xtick.labelsize": 7,
        "ytick.labelsize": 7,
        "legend.fontsize": 7,
    }
)

# Regex for counting declarations in Lean files
_DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|partial|nonrec)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|class)\b",
    re.MULTILINE,
)


# ============================================================
# Utility functions
# ============================================================


def savefig_both(fig, filename_base):
    """Save figure as both PNG and PDF."""
    fig.savefig(f"{filename_base}.png", dpi=300, facecolor="white")
    fig.savefig(f"{filename_base}.pdf", facecolor="white")
    print(f"Saved {Path(filename_base).name}.png/.pdf")


def symlog(x):
    """Symmetric log transform with 0 included.
    Maps: -100→-3, -10→-2, -1→-1, 0→0, 1→1, 10→2, 100→3
    """
    x = np.asarray(x, dtype=float)
    result = np.zeros_like(x)
    pos = x > 0
    neg = x < 0
    result[pos] = np.log10(x[pos]) + 1
    result[neg] = -(np.log10(-x[neg]) + 1)
    return result


# ============================================================
# Data loading
# ============================================================


def get_pr_stats():
    """Get per-PR (first-parent commit) stats from git log --numstat.

    Returns list of dicts with: hash, datetime, lean_added, lean_deleted, lean_net,
    other_added, other_deleted, other_net, lean_files, other_files
    """
    result = subprocess.run(
        [
            "git",
            "log",
            "--first-parent",
            "--reverse",
            "--numstat",
            "--format=%H %aI",
            BRANCH,
        ],
        capture_output=True,
        text=True,
        cwd=REPO,
    )

    prs = []
    current_hash = None
    current_dt = None
    lean_added = lean_deleted = lean_files = 0
    other_added = other_deleted = other_files = 0

    def flush():
        if current_hash and (
            lean_added > 0 or lean_deleted > 0 or other_added > 0 or other_deleted > 0
        ):
            prs.append(
                {
                    "hash": current_hash,
                    "datetime": current_dt,
                    "lean_added": lean_added,
                    "lean_deleted": lean_deleted,
                    "lean_net": lean_added - lean_deleted,
                    "lean_files": lean_files,
                    "other_added": other_added,
                    "other_deleted": other_deleted,
                    "other_net": other_added - other_deleted,
                    "other_files": other_files,
                }
            )

    for line in result.stdout.split("\n"):
        stripped = line.strip()
        parts = stripped.split()

        if len(parts) == 2 and len(parts[0]) == 40:
            flush()
            current_hash = parts[0]
            current_dt = datetime.fromisoformat(parts[1])
            lean_added = lean_deleted = lean_files = 0
            other_added = other_deleted = other_files = 0
        elif len(parts) >= 3:
            filepath = parts[2]
            if "/tex/" in filepath:
                continue
            try:
                add = int(parts[0])
                delete = int(parts[1])
            except ValueError:
                continue

            if filepath.endswith(".lean"):
                lean_added += add
                lean_deleted += delete
                lean_files += 1
            else:
                other_added += add
                other_deleted += delete
                other_files += 1

    flush()
    return prs


def get_commit_messages():
    """Get all commit messages in one git call."""
    result = subprocess.run(
        ["git", "log", "--first-parent", "--reverse", "--format=%H %s", BRANCH],
        capture_output=True,
        text=True,
        cwd=REPO,
    )

    hash_to_msg = {}
    for line in result.stdout.strip().split("\n"):
        parts = line.split(" ", 1)
        if len(parts) == 2:
            hash_to_msg[parts[0]] = parts[1]
    return hash_to_msg


def get_loc_history():
    """Get per-commit LOC deltas from git log --numstat (fast, single git call)."""
    result = subprocess.run(
        [
            "git",
            "log",
            "--first-parent",
            "--reverse",
            "--numstat",
            "--format=%H %aI",
            BRANCH,
            "--",
            "AlgebraicCombinatorics/",
        ],
        capture_output=True,
        text=True,
        cwd=REPO,
    )

    commits = []
    current_hash = None
    current_dt = None
    current_added = 0
    current_deleted = 0

    for line in result.stdout.split("\n"):
        stripped = line.strip()
        parts = stripped.split()
        if len(parts) == 2 and len(parts[0]) == 40:
            if current_hash:
                commits.append(
                    (current_dt, current_hash, current_added, current_deleted)
                )
            current_hash = parts[0]
            current_dt = datetime.fromisoformat(parts[1])
            current_added = 0
            current_deleted = 0
        elif len(parts) >= 3 and parts[2].endswith(".lean") and "/tex/" not in parts[2]:
            try:
                current_added += int(parts[0])
                current_deleted += int(parts[1])
            except ValueError:
                pass

    if current_hash:
        commits.append((current_dt, current_hash, current_added, current_deleted))
    return commits


def count_decls_at_commit(commit_hash):
    """Count declarations at a commit (slow — reads all files)."""
    result = subprocess.run(
        [
            "git",
            "ls-tree",
            "-r",
            "--name-only",
            commit_hash,
            "--",
            "AlgebraicCombinatorics/",
        ],
        capture_output=True,
        text=True,
        cwd=REPO,
    )
    lean_files = [
        f
        for f in result.stdout.strip().split("\n")
        if f.endswith(".lean") and f.strip()
    ]

    total_decls = 0
    for f in lean_files:
        r = subprocess.run(
            ["git", "show", f"{commit_hash}:{f}"],
            capture_output=True,
            text=True,
            cwd=REPO,
        )
        if r.returncode == 0:
            total_decls += len(_DECL_RE.findall(r.stdout))
    return total_decls


# ============================================================
# Plotting functions
# ============================================================


def plot_histogram(data, filename_base, color, log_scale=True, compact=False):
    """Plot histogram with consistent styling.

    Args:
        compact: If True, use 1/3 width sizing with fewer bins (for 3-up layouts)
    """
    if compact:
        fig, ax = plt.subplots(figsize=(THIRD_WIDTH, THIRD_HEIGHT))
        n_bins = 15
    else:
        fig, ax = plt.subplots(figsize=(COL_WIDTH, FIG_HEIGHT))
        n_bins = 30

    if log_scale and data.max() > 100:
        bins = np.logspace(
            np.log10(max(1, data.min())), np.log10(data.max() + 1), n_bins
        )
        ax.set_xscale("log")
    else:
        bins = n_bins

    ax.hist(data, bins=bins, color=color, alpha=0.7, edgecolor="white", linewidth=0.3)
    ax.grid(axis="y", alpha=0.3, linewidth=0.5)
    fig.tight_layout()
    savefig_both(fig, filename_base)
    plt.close()


def plot_net_histogram(data, filename_base, color, compact=False):
    """Plot net change histogram with symlog scale (includes 0).

    Args:
        compact: If True, use 1/3 width sizing with fewer bins (for 3-up layouts)
    """
    data_sym = symlog(data)

    if compact:
        fig, ax = plt.subplots(figsize=(THIRD_WIDTH, THIRD_HEIGHT))
        n_bins = 15
    else:
        fig, ax = plt.subplots(figsize=(COL_WIDTH, FIG_HEIGHT))
        n_bins = 30

    ax.hist(
        data_sym, bins=n_bins, color=color, alpha=0.7, edgecolor="white", linewidth=0.3
    )
    ax.axvline(x=0, color="black", linewidth=0.8, linestyle="--", alpha=0.5)

    # All powers with consistent notation, smaller font
    tick_vals = [-1000, -100, -10, -1, 0, 1, 10, 100, 1000]
    tick_pos = [symlog(v) for v in tick_vals]
    tick_labels = [
        r"$\text{-}10^3$",
        r"$\text{-}10^2$",
        r"$\text{-}10^1$",
        r"$\text{-}10^0$",
        r"$0$",
        r"$10^0$",
        r"$10^1$",
        r"$10^2$",
        r"$10^3$",
    ]
    ax.set_xticks(tick_pos)
    ax.set_xticklabels(tick_labels, fontsize=5)

    ax.grid(axis="y", alpha=0.3, linewidth=0.5)
    fig.tight_layout()
    savefig_both(fig, filename_base)
    print(f"  (n={len(data)})")
    plt.close()


def plot_2d_hist(lean_sym, other_sym, filename_base, n_prs):
    """Plot 2D histogram with symlog axes."""
    fig, ax = plt.subplots(figsize=(COL_WIDTH, COL_WIDTH))

    try:
        h = ax.hist2d(lean_sym, other_sym, bins=9, cmap="Blues", cmin=1, norm=LogNorm())
    except ValueError:
        h = ax.hist2d(lean_sym, other_sym, bins=9, cmap="Blues", cmin=1)

    cbar = fig.colorbar(h[3], ax=ax)
    cbar.ax.tick_params(labelsize=6)

    ax.axhline(y=0, color="gray", linewidth=0.5, linestyle="-", alpha=0.4, zorder=0)
    ax.axvline(x=0, color="gray", linewidth=0.5, linestyle="-", alpha=0.4, zorder=0)

    tick_vals = [-1000, -100, -10, -1, 0, 1, 10, 100, 1000]
    tick_pos = [symlog(v) for v in tick_vals]
    tick_labels = [str(v) for v in tick_vals]
    ax.set_xticks(tick_pos)
    ax.set_xticklabels(tick_labels, rotation=45, ha="right")
    ax.set_yticks(tick_pos)
    ax.set_yticklabels(tick_labels)

    ax.set_xlabel("Lean")
    ax.set_ylabel("Other")
    fig.tight_layout()
    savefig_both(fig, filename_base)
    print(f"  (n={n_prs})")
    plt.close()


def plot_temporal_scatter(lean_sym, other_sym, sequence_pos, filename_base, n_prs):
    """Plot temporal scatter with jitter."""
    np.random.seed(42)
    jitter_std = 0.3
    lean_jittered = lean_sym + np.random.normal(0, jitter_std, len(lean_sym))
    other_jittered = other_sym + np.random.normal(0, jitter_std, len(other_sym))

    fig, ax = plt.subplots(figsize=(COL_WIDTH, COL_WIDTH))

    ax.scatter(
        lean_jittered,
        other_jittered,
        c=sequence_pos,
        cmap="viridis",
        s=8,
        alpha=0.35,
        edgecolors="none",
    )

    sm = plt.cm.ScalarMappable(cmap="viridis", norm=plt.Normalize(0, 1))
    sm.set_array([])
    cbar = fig.colorbar(sm, ax=ax, ticks=[0, 1], alpha=0.8)
    cbar.ax.set_yticklabels(["Start", "End"], fontsize=6)
    cbar.ax.tick_params(labelsize=6)

    ax.axhline(y=0, color="gray", linewidth=0.5, linestyle="-", alpha=0.4, zorder=0)
    ax.axvline(x=0, color="gray", linewidth=0.5, linestyle="-", alpha=0.4, zorder=0)

    tick_vals = [-1000, -100, -10, -1, 0, 1, 10, 100, 1000]
    tick_pos = [symlog(v) for v in tick_vals]
    tick_labels = [str(v) for v in tick_vals]
    ax.set_xticks(tick_pos)
    ax.set_xticklabels(tick_labels, rotation=45, ha="right")
    ax.set_yticks(tick_pos)
    ax.set_yticklabels(tick_labels)

    ax.set_xlabel("Lean")
    ax.set_ylabel("Other")
    fig.tight_layout()
    savefig_both(fig, filename_base)
    print(f"  (n={n_prs})")
    plt.close()


def plot_growth_metric(
    x_vals, y_vals, filename_base, fill_color, line_color, ylim_bottom=0
):
    """Plot growth metric with fill."""
    fig, ax = plt.subplots(figsize=(COL_WIDTH, FIG_HEIGHT))
    ax.fill_between(x_vals, y_vals, alpha=0.3, color=fill_color)
    ax.plot(x_vals, y_vals, color=line_color, linewidth=1)
    if ylim_bottom is not None:
        ax.set_ylim(bottom=ylim_bottom)
    if isinstance(x_vals[0], datetime):
        ax.xaxis.set_major_formatter(mdates.DateFormatter("%b %d"))
        ax.xaxis.set_major_locator(mdates.AutoDateLocator())
        fig.autofmt_xdate(rotation=30)
    else:
        ax.set_xlabel("Commit")
    ax.set_xlim(left=x_vals[0])
    ax.grid(axis="y", alpha=0.3, linewidth=0.5)
    fig.tight_layout()
    savefig_both(fig, filename_base)
    plt.close()


def plot_churn(x_vals, cum_added, cum_deleted, filename_base):
    """Plot cumulative churn (added vs deleted)."""
    fig, ax = plt.subplots(figsize=(COL_WIDTH, FIG_HEIGHT))
    ax.fill_between(x_vals, cum_added, alpha=0.4, color="#4CAF50", label="added")
    ax.plot(x_vals, cum_added, color="#2E7D32", linewidth=1)
    ax.fill_between(
        x_vals,
        [-x for x in cum_deleted],
        alpha=0.4,
        color="#F44336",
        label="removed",
    )
    ax.plot(x_vals, [-x for x in cum_deleted], color="#C62828", linewidth=1)
    ax.axhline(y=0, color="black", linewidth=0.5)
    if isinstance(x_vals[0], datetime):
        ax.xaxis.set_major_formatter(mdates.DateFormatter("%b %d"))
        ax.xaxis.set_major_locator(mdates.AutoDateLocator())
        fig.autofmt_xdate(rotation=30)
    else:
        ax.set_xlabel("Commit")
    ax.set_xlim(left=x_vals[0])
    ax.legend(loc="upper left", fontsize=6, framealpha=0.8)
    ax.grid(axis="y", alpha=0.3, linewidth=0.5)
    fig.tight_layout()
    savefig_both(fig, filename_base)
    plt.close()


# ============================================================
# Main
# ============================================================


def main(skip_decls=False):
    print(f"Repo: {REPO}")
    print(f"Branch: {BRANCH}")
    print(f"Output: {OUT_DIR}")
    if skip_decls:
        print("Skipping declarations charts (--skip-decls)")
    print()

    os.makedirs(OUT_DIR, exist_ok=True)
    out = str(OUT_DIR)

    # ========== PR STATS ==========
    print("Loading PR stats...")
    prs = get_pr_stats()
    print(f"Loaded {len(prs)} PRs")
    print(
        f"  - PRs with Lean changes: {sum(1 for p in prs if p['lean_added'] > 0 or p['lean_deleted'] > 0)}"
    )
    print(
        f"  - PRs with other changes: {sum(1 for p in prs if p['other_added'] > 0 or p['other_deleted'] > 0)}"
    )
    print()

    # Extract arrays
    lean_added = np.array([p["lean_added"] for p in prs])
    lean_deleted = np.array([p["lean_deleted"] for p in prs])
    lean_net = np.array([p["lean_net"] for p in prs])
    lean_files = np.array([p["lean_files"] for p in prs])

    other_added = np.array([p["other_added"] for p in prs])
    other_deleted = np.array([p["other_deleted"] for p in prs])
    other_net = np.array([p["other_net"] for p in prs])

    # ========== LEAN HISTOGRAMS ==========
    print("Generating Lean histograms...")
    lean_added_pos = lean_added[lean_added > 0]
    lean_deleted_pos = lean_deleted[lean_deleted > 0]

    # Standard 1/2 width versions
    plot_histogram(
        lean_added_pos,
        f"{out}/pr_lean_added_hist",
        "#4CAF50",
        log_scale=True,
    )
    plot_histogram(
        lean_deleted_pos,
        f"{out}/pr_lean_deleted_hist",
        "#F44336",
        log_scale=True,
    )
    plot_net_histogram(lean_net, f"{out}/pr_lean_net_hist", "#2196F3")

    # Compact 1/3 width versions (for 3-up layouts)
    plot_histogram(
        lean_added_pos,
        f"{out}/pr_lean_added_hist_compact",
        "#4CAF50",
        log_scale=True,
        compact=True,
    )
    plot_histogram(
        lean_deleted_pos,
        f"{out}/pr_lean_deleted_hist_compact",
        "#F44336",
        log_scale=True,
        compact=True,
    )
    plot_net_histogram(
        lean_net, f"{out}/pr_lean_net_hist_compact", "#2196F3", compact=True
    )

    # ========== OTHER HISTOGRAMS ==========
    print("Generating other-files histograms...")
    other_added_pos = other_added[other_added > 0]
    other_deleted_pos = other_deleted[other_deleted > 0]

    # Standard 1/2 width versions
    plot_histogram(
        other_added_pos,
        f"{out}/pr_other_added_hist",
        "#4CAF50",
        log_scale=True,
    )
    plot_histogram(
        other_deleted_pos,
        f"{out}/pr_other_deleted_hist",
        "#F44336",
        log_scale=True,
    )
    plot_net_histogram(other_net, f"{out}/pr_other_net_hist", "#2196F3")

    # Compact 1/3 width versions (for 3-up layouts)
    plot_histogram(
        other_added_pos,
        f"{out}/pr_other_added_hist_compact",
        "#4CAF50",
        log_scale=True,
        compact=True,
    )
    plot_histogram(
        other_deleted_pos,
        f"{out}/pr_other_deleted_hist_compact",
        "#F44336",
        log_scale=True,
        compact=True,
    )
    plot_net_histogram(
        other_net, f"{out}/pr_other_net_hist_compact", "#2196F3", compact=True
    )

    # ========== 2D PLOTS ==========
    print("Generating 2D plots...")
    lean_sym = symlog(lean_net)
    other_sym = symlog(other_net)

    plot_2d_hist(lean_sym, other_sym, f"{out}/pr_lean_vs_other_net", len(prs))

    sequence_pos = np.arange(len(prs)) / (len(prs) - 1)
    plot_temporal_scatter(
        lean_sym, other_sym, sequence_pos, f"{out}/pr_lean_vs_other_temporal", len(prs)
    )

    # ========== FILES HISTOGRAM ==========
    print("Generating files histogram...")
    lean_files_pos = lean_files[lean_files > 0]
    max_files = int(lean_files_pos.max())

    fig, ax = plt.subplots(figsize=(COL_WIDTH, FIG_HEIGHT))
    bins = np.arange(0.5, max_files + 1.5, 1)
    ax.hist(
        lean_files_pos,
        bins=bins,
        color="#9C27B0",
        alpha=0.7,
        edgecolor="white",
        linewidth=0.3,
    )
    ax.set_yscale("log")
    ax.set_xticks(range(1, max_files + 1))
    ax.grid(axis="y", alpha=0.3, linewidth=0.5)
    fig.tight_layout()
    savefig_both(fig, f"{out}/pr_lean_files_hist")
    plt.close()

    # ========== AGENT TYPES ==========
    print("Extracting agent types...")
    hash_to_msg = get_commit_messages()

    agent_types = []
    for p in prs:
        msg = hash_to_msg.get(p["hash"], "")
        match = re.match(r"Merge\s+(\w+)-", msg)
        if match:
            agent_types.append(match.group(1))
        else:
            agent_types.append("other")

    agent_counts = Counter(agent_types)
    print("Agent type counts:")
    for agent, count in agent_counts.most_common():
        print(f"  {count:5d} | {agent}")
    print()

    # Agent bar chart
    fig, ax = plt.subplots(figsize=(COL_WIDTH, FIG_HEIGHT))
    agents_sorted = agent_counts.most_common()
    labels = [a for a, c in agents_sorted]
    counts_sorted = [c for a, c in agents_sorted]

    ax.barh(range(len(labels)), counts_sorted, color="#2196F3", alpha=0.7)
    ax.set_yticks(range(len(labels)))
    ax.set_yticklabels(labels)
    ax.invert_yaxis()
    ax.set_xscale("log")
    ax.set_xlim(20, 2000)
    ax.set_xticks([20, 50, 100, 200, 500, 1000, 2000])
    ax.set_xticklabels(["20", "50", "100", "200", "500", "1k", "2k"])
    ax.grid(axis="x", alpha=0.3, linewidth=0.5)
    fig.tight_layout()
    savefig_both(fig, f"{out}/pr_agent_types")
    plt.close()

    # ========== PER-AGENT 2D PLOTS ==========
    print("Generating per-agent plots...")
    agent_type_arr = np.array(agent_types)

    for agent_name in ["maintain", "prove"]:
        mask = agent_type_arr == agent_name
        n = mask.sum()
        if n < 2:
            print(f"Skipping {agent_name} - only {n} PRs")
            continue

        lean_sym_filtered = symlog(lean_net[mask])
        other_sym_filtered = symlog(other_net[mask])
        indices = np.where(mask)[0]
        seq_pos_filtered = indices / (len(prs) - 1)

        plot_2d_hist(
            lean_sym_filtered,
            other_sym_filtered,
            f"{out}/pr_lean_vs_other_net_{agent_name}",
            n,
        )
        plot_temporal_scatter(
            lean_sym_filtered,
            other_sym_filtered,
            seq_pos_filtered,
            f"{out}/pr_lean_vs_other_temporal_{agent_name}",
            n,
        )

    # ========== COMBINED AGENT SCATTER ==========
    print("Generating combined agent scatter...")
    fig, ax = plt.subplots(figsize=(COL_WIDTH, COL_WIDTH))
    np.random.seed(42)
    jitter_std = 0.3

    for agent_name, color, label in [
        ("maintain", "#E53935", "maintain"),
        ("prove", "#1E88E5", "prove"),
    ]:
        mask = agent_type_arr == agent_name
        lean_sym_filtered = symlog(lean_net[mask])
        other_sym_filtered = symlog(other_net[mask])

        lean_jittered = lean_sym_filtered + np.random.normal(
            0, jitter_std, len(lean_sym_filtered)
        )
        other_jittered = other_sym_filtered + np.random.normal(
            0, jitter_std, len(other_sym_filtered)
        )

        ax.scatter(
            lean_jittered,
            other_jittered,
            c=color,
            s=6,
            alpha=0.3,
            edgecolors="none",
            label=f"{label} (n={mask.sum()})",
        )

    ax.axhline(y=0, color="gray", linewidth=0.5, linestyle="-", alpha=0.4, zorder=0)
    ax.axvline(x=0, color="gray", linewidth=0.5, linestyle="-", alpha=0.4, zorder=0)

    tick_vals = [-1000, -100, -10, -1, 0, 1, 10, 100, 1000]
    tick_pos = [symlog(v) for v in tick_vals]
    tick_labels = [str(v) for v in tick_vals]
    ax.set_xticks(tick_pos)
    ax.set_xticklabels(tick_labels, rotation=45, ha="right")
    ax.set_yticks(tick_pos)
    ax.set_yticklabels(tick_labels)

    ax.set_xlabel("Lean")
    ax.set_ylabel("Other")
    ax.legend(loc="upper left", fontsize=6, framealpha=0.8)
    fig.tight_layout()
    savefig_both(fig, f"{out}/pr_lean_vs_other_agents")
    plt.close()

    # ========== AGENT FILES HISTOGRAM ==========
    print("Generating agent files histogram...")
    maintain_mask = agent_type_arr == "maintain"
    prove_mask = agent_type_arr == "prove"

    maintain_files = lean_files[maintain_mask]
    prove_files = lean_files[prove_mask]

    maintain_files_pos = maintain_files[maintain_files > 0]
    prove_files_pos = prove_files[prove_files > 0]

    max_files = max(maintain_files_pos.max(), prove_files_pos.max())
    bins = np.arange(0.5, max_files + 1.5, 1)

    fig, ax = plt.subplots(figsize=(COL_WIDTH, FIG_HEIGHT))
    ax.hist(
        maintain_files_pos,
        bins=bins,
        color="#E53935",
        alpha=0.6,
        edgecolor="white",
        linewidth=0.3,
        label=f"maintain (n={len(maintain_files_pos)})",
    )
    ax.hist(
        prove_files_pos,
        bins=bins,
        color="#1E88E5",
        alpha=0.6,
        edgecolor="white",
        linewidth=0.3,
        label=f"prove (n={len(prove_files_pos)})",
    )

    ax.set_yscale("log")
    ax.set_xticks(range(1, int(max_files) + 1))
    ax.legend(loc="upper right", fontsize=6, framealpha=0.8)
    ax.grid(axis="y", alpha=0.3, linewidth=0.5)
    fig.tight_layout()
    savefig_both(fig, f"{out}/pr_lean_files_agents")
    plt.close()

    # ========== GROWTH CHARTS ==========
    print()
    print("=" * 60)
    print("GROWTH CHARTS")
    print("=" * 60)

    print("Getting LOC history...")
    loc_history = get_loc_history()
    print(f"  {len(loc_history)} commits with Lean file changes")

    # Reconstruct cumulative LOC
    cum_loc = 0
    loc_data = []
    cum_added = 0
    cum_deleted = 0
    for i, (dt, h, added, deleted) in enumerate(loc_history):
        cum_loc += added - deleted
        cum_added += added
        cum_deleted += deleted
        loc_data.append((dt, i + 1, cum_loc, cum_added, cum_deleted))

    loc_data = [d for d in loc_data if d[2] > 0]

    dates = [d[0] for d in loc_data]
    commit_nums = [d[1] for d in loc_data]
    locs = [d[2] for d in loc_data]
    cum_adds = [d[3] for d in loc_data]
    cum_dels = [d[4] for d in loc_data]

    print(f"Final: {locs[-1]} LOC (commit {commit_nums[-1]})")
    print(f"Churn: {cum_adds[-1]:,} added, {cum_dels[-1]:,} removed")

    # LOC charts
    print("Generating LOC charts...")
    plot_growth_metric(
        commit_nums,
        locs,
        f"{out}/loc_over_time_by_commit",
        "#2196F3",
        "#1565C0",
    )
    plot_growth_metric(
        dates,
        locs,
        f"{out}/loc_over_time_by_date",
        "#2196F3",
        "#1565C0",
    )

    # Churn charts
    print("Generating churn charts...")
    plot_churn(commit_nums, cum_adds, cum_dels, f"{out}/churn_over_time_by_commit")
    plot_churn(dates, cum_adds, cum_dels, f"{out}/churn_over_time_by_date")

    # Declarations (sampled) - slow, can be skipped with --skip-decls
    if not skip_decls:
        print("Sampling declarations (slow — reads file contents)...")
        n = len(loc_data)
        if n > 100:
            step = n // 80
            sample_idx = list(range(0, n, step))
            if n - 1 not in sample_idx:
                sample_idx.append(n - 1)
        else:
            sample_idx = list(range(n))

        sampled_commits = [loc_history[loc_data[i][1] - 1] for i in sample_idx]
        sampled_dates = [loc_data[i][0] for i in sample_idx]
        sampled_nums = [loc_data[i][1] for i in sample_idx]

        decls = []
        for si, (dt, h, _, _) in enumerate(sampled_commits):
            nd = count_decls_at_commit(h)
            decls.append(nd)
            if (si + 1) % 10 == 0:
                print(
                    f"  {si+1}/{len(sampled_commits)}: commit {sampled_nums[si]} — {nd} decls"
                )

        print(f"Final: {decls[-1]} declarations")

        print("Generating declaration charts...")
        plot_growth_metric(
            sampled_nums,
            decls,
            f"{out}/declarations_over_time_by_commit",
            "#4CAF50",
            "#2E7D32",
        )
        plot_growth_metric(
            sampled_dates,
            decls,
            f"{out}/declarations_over_time_by_date",
            "#4CAF50",
            "#2E7D32",
        )

    print()
    print("=" * 60)
    print("All plots saved as PNG and PDF!")
    print("=" * 60)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Generate publication figures")
    parser.add_argument(
        "--skip-decls",
        action="store_true",
        help="Skip the slow declarations charts",
    )
    args = parser.parse_args()
    main(skip_decls=args.skip_decls)
