# Building AlgebraicCombinatorics

## Prerequisites

- A working Lean 4 / elan installation
- A C compiler (Linux/macOS)

## Build

From the repo root:

```bash
lake build AlgebraicCombinatorics
```

## Regenerating charts

The `assets/` directory contains charts showing project growth and theorem status. To regenerate them:

```bash
python3 scripts/gen_growth_charts.py        # loc_over_time, declarations_over_time, churn_over_time
python3 scripts/gen_dep_graph_theorems.py   # dep_graph_theorems (colored theorem status boxes)
```
