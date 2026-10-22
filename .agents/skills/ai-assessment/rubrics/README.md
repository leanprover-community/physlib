# Review rubrics

Each file here is the prompt for one review agent. A PR is reviewed by several independent
agents, each judging a single angle. An agent's full prompt is `_common.md` (the shared
protocol) followed by its angle file.

Agents run only after CI is green, so the mechanical layer (build, axiom audit, the Mathlib
linter set, the import boundary) is already satisfied and no agent re-checks it.

## The angles

The table is in review order: rubrics run one at a time and a `block` halts the round, so the
block-capable integrity angles run first (cheapest, most-likely-to-block earliest).

| Rubric | Question | Can block? |
| --- | --- | --- |
| [`correctness`](correctness.md) | Do the statements and definitions say what they should? | yes |
| [`reuse`](reuse.md) | Does it reuse Mathlib / TauCeti instead of reinventing? | yes (outright duplication) |
| [`scope`](scope.md) | Is this on the roadmap, and a single topic? | yes |
| [`attribution`](attribution.md) | Does it credit its formal and informal sources? | yes (clear missing credit) |
| [`api-design`](api-design.md) | Minimal public surface, complete characteristic API? | no |
| [`generality`](generality.md) | Weakest assumptions; natural level? | no |
| [`placement`](placement.md) | Canonical home; direct, minimal imports? | no |
| [`naming`](naming.md) | Conclusion-describing names; conventional notation? | no |
| [`documentation`](documentation.md) | Accurate module and declaration docstrings? | no |
| [`proof-quality`](proof-quality.md) | Automation-first, robust proofs? | no |

Blocking angles are integrity checks. The rest use `request_changes` for fixable issues.
