---
name: ai-notes
description: Advisory AI assessment of a Physlib pull request. Scores the PR from 0 to 5 on each review rubric with constructive suggestions, and posts one comment on the PR after the user confirms. Makes no decisions. Use when asked to assess a PR, to run the ai-notes skill, or to work through PRs labelled `ai-notes`.
argument-hint: "[PR number]"
---

This skill is model-independent and lives in `.agents/skills/ai-notes/`.
Read `.agents/skills/ai-notes/SKILL.md` and follow it, with `SKILL_DIR` being
`.agents/skills/ai-notes`. The argument, if any, is the PR number: $ARGUMENTS
