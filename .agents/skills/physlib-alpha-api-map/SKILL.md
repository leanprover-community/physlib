---
name: physlib-alpha-api-map
description: Help a newcomer contribute an API map for physics, supporting Physlib issue 1891. Take an issue, physics topic, or request to get started through an edited map, checked references, and a reviewable diff.
---

# Contribute an Alpha API map

Help the contributor make a useful documentation change to an 
API-map that they can understand.
They can supply a physics topic or issue, or ask you to choose a first contribution.
For an action request, carry the work through editing and checking; only stop at
options if that is what they requested. This workflow supports the API-map work in
[#1891](https://github.com/leanprover-community/physlib/issues/1891); a single map
improvement does not close the whole issue.

## Choose the change

Read `AGENTS.md`, `AI-POLICY.md`, `docs/ReviewGuidelines.md`, the files in
`docs/ContributionHandbook/`, and `docs/API_MAP_GUIDE.md` for current conventions.
Reuse the user's checkout or clone Physlib if needed; preserve existing edits.
Read the chosen issue's current comments, assignments, and linked PRs. Public web
access is sufficient if GitHub CLI is unavailable; no login is needed to edit locally.

Use the contributor's topic, or choose a small Alpha area if selection is delegated.
Search maps across Physlib, QuantumInfo, and PhyslibAlpha for the concept and its
declarations. Check matching open PRs before settling on a file. If remote checks
fail, report overlap as unknown. Improve the map already covering the topic; create
one only for a coherent API that lacks a map, in the location the guide specifies.
Alpha headings denote review status, so a map outside `PhyslibAlpha/` may document
Alpha code. Preserve a requested proof or Lean API task instead of redirecting it
into this documentation workflow. Your headings should be `Alpha`

Choose a concrete improvement: explain a convention, cover an existing result,
correct a claim, or supply a missing map. Read the relevant declarations and their
dependencies before writing. Ask only when a missing physics decision would change
what the contribution means; do not require the newcomer to select Lean declarations.

## Edit and verify

Explain the physics for a colleague who does not know the Lean names. Include the
domain, assumptions, and conventions. Inspect full declaration types before citing
them. Distinguish definitions, proved results, informal declarations, and planned
material. Mark unformalized claims `[TODO]`, including statements only recorded as
informal declarations; split sentences mixing proved and unproved claims. Look 
at other examples.

Follow the guide's Alpha sections, `[1]` Lean citations, `{1}` literature citations,
and exact file/declaration reference entries. Use actual sources for added physics
claims. Do not invent bibliographic details or place citations in the abstract.

Use the checkout's `lean-toolchain` and `lake-manifest.json`. Inspect installed
versions with `elan toolchain list`; install the pinned toolchain if needed, following
the official Lean installation link in the getting-started guide from `CONTRIBUTING.md`.
Honor offline or no-install constraints. Do not change dependency versions to bypass
an error. This Markdown task needs no Physlib or 
PhyslibAlpha build and no full cache download.

Run `lake exe api_map_lint --verbose` before and after the edit. Fix new diagnostics
and rerun the check. The linter checks format and reference presence, not the meaning
of a claim: compare the final prose with the Lean types yourself. Resolve ambiguous
notation or instances with `#check` or `#synth` in the pinned environment when needed.
Inspect the diff, run `git diff --check`, and apply relevant Markdown/spelling checks
from CI. Include new files when reviewing the diff. Report unavailable checks and
actual diagnostics; do not label an unrun check as passing.

## Hand back a reviewable contribution

Show the changed map and explain the improvement, supporting declarations and
sources, remaining `[TODO]` material, and actual check results. The human verifies
the physics and bibliography and writes the PR description under `AI-POLICY.md` and
`AGENTS.md`. Give them review evidence rather than generating that description.
