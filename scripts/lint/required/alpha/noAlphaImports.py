#!/usr/bin/env python3
"""
This module validates that no files in the Physlib and QuantumInfo directories
contain import statements that reference PhyslibAlpha. It walks through all .lean
files in these directories and reports any violations found, returning an exit code
indicating success or failure of the validation check.

It checks each line in these files.
"""
import os
import sys

def check_no_alpha_imports():
    """Check that no files in ./Physlib or ./QuantumInfo contain lines with both 'import' and 'PhyslibAlpha'."""
    directories = ['./Physlib', './QuantumInfo']
    violations = []

    for directory in directories:
        if not os.path.exists(directory):
            print(f"Warning: Directory {directory} does not exist")
            continue

        for root, dirs, files in os.walk(directory):
            for file in files:
                if file.endswith('.lean'):
                    filepath = os.path.join(root, file)
                    try:
                        with open(filepath, 'r', encoding='utf-8') as f:
                            for line_num, line in enumerate(f, 1):
                                if 'import' in line and 'PhyslibAlpha' in line:
                                    violations.append((filepath, line_num, line.strip()))
                    except Exception as e:
                        print(f"Error reading {filepath}: {e}")

    if violations:
        print("Found violations:")
        for filepath, line_num, line in violations:
            print(f"  {filepath}:{line_num}: {line}")
        return False
    else:
        print("No violations found. All files passed the check.")
        return True

if __name__ == '__main__':
    success = check_no_alpha_imports()
    sys.exit(0 if success else 1)
