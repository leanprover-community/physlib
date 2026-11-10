---
name: tidy
description: Pick a single PhyslibAlpha file, and clean it up to the standard of AGENTS.md without changing what it says. A task of physlibAlpha-worker.
---

Pick a single file in PhyslibAlpha, of at most 400 lines, that falls short of the standard of
AGENTS.md and docs/ReviewGuidelines.md, and tidy it to that standard, without changing the name or
statement of any declaration, removing one, or changing what a definition computes.

Change no other file, apart from scripts/lint/exemptions/Theorems.txt and
scripts/lint/exemptions/spellingWords.txt where needed. Do not add `sorry`, `admit`, `axiom` or
`native_decide`. Do not commit, push or open a pull request.

Your final message becomes the commit message: its first line is a title naming the file and the
declarations changed, then a blank line and a short list of what you changed.
