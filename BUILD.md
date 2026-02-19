# Building AlgebraicCombinatorics

Instructions for building the project, documentation, and blueprint.

## Building the project

### Prerequisites

- A working Lean 4 / elan installation
- A C compiler (Linux/macOS)

### Build

From the repo root:

```bash
lake build AlgebraicCombinatorics
```

## Building the documentation

This project uses [doc-gen4](https://github.com/leanprover/doc-gen4) to generate documentation. A `docbuild` subdirectory is already set up for this purpose.

### One-time setup

From the repo root:

```bash
cd docbuild
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update doc-gen4
```

The `MATHLIB_NO_CACHE_ON_UPDATE=1` prefix is required because this project depends on Mathlib.

If you update the parent project's dependencies, also run:

```bash
cd docbuild
lake update AlgebraicCombinatorics
```

### Generating the docs

```bash
cd docbuild
lake build AlgebraicCombinatorics:docs
```

### Viewing the docs locally

The generated HTML files need to be served over HTTP (opening them directly in a browser won't work due to the Same Origin Policy). From the repo root:

```bash
cd docbuild/.lake/build/doc
python3 -m http.server
```

Then open `http://localhost:8000` in your browser.

## Building the blueprint

The blueprint is built using [leanblueprint](https://github.com/PatrickMassot/leanblueprint). Install it with:

```bash
pip install leanblueprint
```

To build and preview locally:

```bash
leanblueprint web
leanblueprint serve
```

Then open `http://0.0.0.0:8000/` in your browser.

## Publishing to GitHub Pages

The API docs and blueprint can be hosted on GitHub Pages. Install `ghp-import` if you haven't already:

```bash
pip install ghp-import
```

### API docs

Build and push to the `gh-pages` branch:

```bash
cd docbuild
lake build AlgebraicCombinatorics:docs
cd ..
ghp-import -n -p -f docbuild/.lake/build/doc
```

### Blueprint

Build and push to the `gh-pages` branch (use a separate repo or branch if hosting both):

```bash
leanblueprint web
ghp-import -n -p -f blueprint/web
```

Enable GitHub Pages in Settings > Pages with source set to the `gh-pages` branch at `/ (root)`.

## Regenerating charts

The `assets/` directory contains charts showing project growth and theorem status. To regenerate them:

```bash
python3 scripts/gen_growth_charts.py        # loc_over_time, declarations_over_time, churn_over_time
python3 scripts/gen_dep_graph_theorems.py   # dep_graph_theorems (colored theorem status boxes)
```
