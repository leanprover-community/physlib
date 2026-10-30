<!--
This file gives the instructions to AI-agents working on a single file within `docs/ContributionHandbook/`.
-->

# Shared protocol

## Overview

You have been assigned one file in Physlib's contribution handbook, `docs/ContributionHandbook/`. Physlib is a Lean 4 library for physics built on Mathlib and has two companion libraries `QuantumInfo` and `PhyslibAlpha` in the same repo. Your role is to see how closely the changes made either in a pull request or locally align with the principles and rules given in your specific file of the handbook. There are other agents working on other files.

## Inputs

As an input you have the following information:
- a checkout of the changes
- the PR description (if there is one)
- the diff
- the list of untracked files (for local changes)
- the path to Mathlib's source, to check whether a result already exists there
- a selected file in `docs/ContributionHandbook/`.

The handbook file is written by and for human authors to the project. You should read its content as rules which the changes should be compared against.

## Output

You should output a single JSON object of the form:

```json
{
  "tips": "<the name of your handbook file without `.md`, e.g. Basic>",
  "score": 0 | 1 | 2 | 3 | 4 | 5 | null,
  "summary": "<a 1-2 sentence summary explaining your score with evidence>",
  "improvements": [
    { "file": "<path, or empty if about the whole change>",
      "line": "<int; 0 if not line-specific>",
      "handbook-line": "<the number and title of the handbook section this relates to, e.g. 1. Don't rush>",
      "suggestion": "<a concrete suggested improvement to better align with the handbook>" }
  ]
}
```

The score has the following meanings:

| Score | Meaning |
| --- | --- |
| 5 | Nothing to suggest under this file |
| 4 | Small polish suggestions only |
| 3 | Several worthwhile improvements |
| 2 | Substantial improvements recommended |
| 1 | Most of the change would benefit from rework under this file |
| 0 | The core idea needs rethinking under this file |

Use `null` only when nothing in your handbook file applies to the change.

Keep everything clear and concise.

## Scope

Do not report what the linters or continuous-integration already checks.
