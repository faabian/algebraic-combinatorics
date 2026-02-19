# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#!/usr/bin/env python3
"""Test doc-gen data loading."""
import json
from pathlib import Path

DOCGEN_DATA = Path("../docbuild/.lake/build/doc/declarations/declaration-data.bmp")
LEAN_DECLS = Path("lean_decls")

def test():
    data = json.loads(DOCGEN_DATA.read_text())
    decls = data["declarations"]
    print(f"✓ Loaded {len(decls)} declarations")
    
    lean_names = LEAN_DECLS.read_text().strip().split('\n')
    matched = sum(1 for n in lean_names if n.strip() in decls)
    print(f"✓ Matched {matched}/{len(lean_names)} from lean_decls")

if __name__ == "__main__":
    test()
