#!/usr/bin/env python3

import os
import re
from pathlib import Path

def main():
    # Get the current working directory
    script_dir = Path.cwd()
    physlib_alpha_dir = script_dir / "PhyslibAlpha"
    physlib_alpha_lean = script_dir / "PhyslibAlpha.lean"

    # Check if PhyslibAlpha directory exists
    if not physlib_alpha_dir.exists():
        print(f"Error: {physlib_alpha_dir} directory not found")
        return False

    # Check if PhyslibAlpha.lean file exists
    if not physlib_alpha_lean.exists():
        print(f"Error: {physlib_alpha_lean} file not found")
        return False

    # Get all .lean files in PhyslibAlpha directory (recursively, including nested subdirectories)
    # and convert each to its module name, e.g. PhyslibAlpha/Sub/File.lean -> PhyslibAlpha.Sub.File
    lean_modules = set()
    for f in physlib_alpha_dir.rglob("*.lean"):
        rel = f.relative_to(physlib_alpha_dir).with_suffix("")
        module_name = ".".join(("PhyslibAlpha",) + rel.parts)
        lean_modules.add(module_name)

    if not lean_modules:
        print(f"No .lean files found in {physlib_alpha_dir}")
        return True

    # Read PhyslibAlpha.lean and extract imports
    with open(physlib_alpha_lean, 'r') as f:
        content = f.read()

    # Extract import statements (looking for "import PhyslibAlpha.<module>" including nested modules)
    import_pattern = r'import\s+(PhyslibAlpha(?:\.\w+)+)'
    imported_modules = set(re.findall(import_pattern, content))

    # Check for missing imports
    missing = lean_modules - imported_modules

    if missing:
        print(f"Error: The following .lean files are not imported in {physlib_alpha_lean}:")
        for module_name in sorted(missing):
            print(f"  - public import {module_name}")
        return False
    else:
        print(f"✓ All {len(lean_modules)} .lean files in {physlib_alpha_dir} are imported in {physlib_alpha_lean}")
        return True

if __name__ == "__main__":
    success = main()
    exit(0 if success else 1)
