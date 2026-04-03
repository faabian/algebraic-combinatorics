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

The blueprint is built using [leanblueprint](https://github.com/faabian/leanblueprint/tree/side-by-side-layout). Install it with:

```bash
pip install git+https://github.com/faabian/leanblueprint.git@side-by-side-layout
```

To build and preview locally:

```bash
leanblueprint web
leanblueprint serve
```

Then open `http://0.0.0.0:8000/` in your browser.

## Building the unified site

To prepare the unified site containing the landing page, blueprint, API docs, and target theorems, you can run the end-to-end build script:

```bash
python3 scripts/build_all.py
```

This script automates the following steps:
1. Builds the Lean API documentation using `lake build AlgebraicCombinatorics:docs`.
2. Builds the blueprint web version using `leanblueprint web`.
3. Runs `leanblueprint checkdecls` to verify that all theorems mentioned in the blueprint exist in the Lean code.
4. Collects the results and generates a unified site in the `site/` directory, including a "Project Targets" page that flags any missing formalizations.

Alternatively, you can run the steps manually:

```bash
# 1. Build the API docs
cd docbuild
lake build AlgebraicCombinatorics:docs
cd ..

# 2. Build the blueprint
leanblueprint web

# 3. Create the unified site structure
mkdir -p site/docs site/blueprint
cp -r docbuild/.lake/build/doc/* site/docs/
cp -r blueprint/web/* site/blueprint/

# 4. Generate the landing page and targets page
python3 scripts/build_site.py
```

## Publishing to GitHub Pages

The unified site is automatically deployed to GitHub Pages via a GitHub Actions workflow when changes to the `site/` directory are pushed to the `main` branch.

To deploy updates, simply run the build steps above to regenerate the `site/` contents, then commit and push them:

```bash
git add site/
git commit -m "Update unified site"
git push origin main
```

## Regenerating charts

The `assets/` directory contains charts showing project growth and theorem status. To regenerate them:

```bash
python3 scripts/gen_growth_charts.py        # loc_over_time, declarations_over_time, churn_over_time
python3 scripts/gen_dep_graph_theorems.py   # dep_graph_theorems (colored theorem status boxes)
```
