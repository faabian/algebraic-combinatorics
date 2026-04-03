import os
import subprocess
import sys
import shutil
from pathlib import Path

def run_command(command, cwd=None, shell=False):
    """Run a shell command and return its output."""
    print(f"Running: {' '.join(command) if isinstance(command, list) else command}")
    try:
        result = subprocess.run(
            command,
            cwd=cwd,
            check=True,
            capture_output=True,
            text=True,
            shell=shell
        )
        return result.stdout
    except subprocess.CalledProcessError as e:
        print(f"Error running command: {e}")
        print(f"Stdout: {e.stdout}")
        print(f"Stderr: {e.stderr}")
        return None

def build_docs():
    """Build the Lean documentation."""
    print("--- Building Lean Documentation ---")
    output = run_command(["lake", "build", "AlgebraicCombinatorics:docs"], cwd="docbuild")
    if output is None:
        print("Warning: Failed to build docs. Continuing anyway...")
        return False
    return True

def build_blueprint():
    """Build the blueprint."""
    print("--- Building Blueprint ---")
    output = run_command(["leanblueprint", "web"])
    if output is None:
        print("Warning: Failed to build blueprint. Continuing anyway...")
        return False
    return True


def build_unified_site():
    """Copy build artifacts to site/ and generate the landing page."""
    print("--- Building Unified Site ---")

    if os.path.exists("site"):
        shutil.rmtree("site")
    os.makedirs("site/docs", exist_ok=True)
    os.makedirs("site/blueprint", exist_ok=True)

    doc_src = Path("docbuild/.lake/build/doc")
    if doc_src.exists():
        print("Copying Lean documentation...")
        sources = list(doc_src.glob("*"))
        if sources:
            run_command(["cp", "-r"] + [str(p) for p in sources] + ["site/docs/"])
    else:
        print("Warning: docbuild/.lake/build/doc not found.")

    bp_src = Path("blueprint/web")
    if bp_src.exists():
        print("Copying Blueprint...")
        sources = list(bp_src.glob("*"))
        if sources:
            run_command(["cp", "-r"] + [str(p) for p in sources] + ["site/blueprint/"])
    else:
        print("Warning: blueprint/web not found.")

    print("Generating overview and redirect...")
    sys.path.insert(0, str(Path(__file__).parent))
    from build_site import build_site
    return build_site()

def main():
    # 1. Build docs
    build_docs()

    # 2. Build blueprint
    build_blueprint()

    # 3. Build unified site
    missing_targets = build_unified_site()

    print("--- All steps completed ---")

    if missing_targets:
        print(f"\nWARNING: {len(missing_targets)} target(s) incomplete in blueprint:")
        for tid, reason in missing_targets:
            print(f"  - {tid}: {reason}")

if __name__ == "__main__":
    main()
