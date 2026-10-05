#!/usr/bin/env bash

set -exo pipefail

# This is adapted from the linter for mathlib4.

################################################################################

# 1. Call the Lean file linter, implemented in Python

touch scripts/lint/exemptions/style-exceptions.txt

git ls-files 'PhyslibAlpha/*.lean' | xargs ./scripts/lint/required/lint-style.py "$@"

# 2. Global checks on the PhyslibAlpha repository

# 2.1 Check for executable bit on Lean files

executable_files="$(find . -name '*.lean' -type f \( -perm -u=x -o -perm -g=x -o -perm -o=x \))"

if [[ -n "$executable_files" ]]
then
	echo "ERROR: The following Lean files have the executable bit set."
	echo "$executable_files"
	exit 1
fi

# 2.2 Check that there are no filenames with the same lower-case reduction

# `uniq -D`: print all duplicate lines
ignore_case_clashes="$(git ls-files | sort --ignore-case | uniq -D --ignore-case)"

if [ -n "${ignore_case_clashes}" ]; then
	printf $'The following files have the same lower-case form:\n\n%s\n
Please, make sure to avoid such clashes!\n' "${ignore_case_clashes}"
	exit 1
fi
