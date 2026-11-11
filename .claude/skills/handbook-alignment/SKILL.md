---
name: handbook-alignment
description: A check of a pull request or local changes based on how it aligns with the points mentioned in docs/ContributionHandbook/. For each file within the handbook, it scores the changes from 0 - 5 and provides constructive suggestions on how to get a better score.
argument-hint: "[PR number | local] [handbook files…]"
---

This skill is model-independent and lives in `.agents/skills/handbook-alignment/`.
Read `.agents/skills/handbook-alignment/SKILL.md` and follow it, with `SKILL_DIR` being
`.agents/skills/handbook-alignment`. The arguments, if any, are a PR number or `local`,
optionally followed by the names of the tip files to check: $ARGUMENTS
