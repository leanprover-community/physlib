# Assessment rubrics

Each file here is the prompt for one assessment agent. A PR is assessed by several independent
agents, each scoring a single angle from 0 to 5. An agent's full prompt is `_common.md` (the
shared protocol, including the score anchors) followed by its angle file.

The assessment is **advisory**: it makes no decisions and is intended to improve the PR where
possible. Humans make every decision about a PR.

CI covers the mechanical layer (the build, `sorry` and axiom checks, the linters, the theorem
list, the module-doc headings), so no agent re-checks it.

## The angles

| Rubric | Question |
| --- | --- |
| [`correctness`](correctness.md) | Do the statements and definitions say what they should? |
| [`reuse`](reuse.md) | Does it reuse Mathlib and Physlib instead of reinventing? |
| [`scope`](scope.md) | Is it a single coherent concept? |
| [`attribution`](attribution.md) | Does it credit its formal and informal sources? |
| [`api-design`](api-design.md) | Minimal public surface, complete characteristic API? |
| [`generality`](generality.md) | Weakest assumptions; natural level? |
| [`placement`](placement.md) | Canonical home; direct, minimal imports? |
| [`naming`](naming.md) | Conclusion-describing names; conventional notation? |
| [`documentation`](documentation.md) | Accurate and helpful module and declaration docstrings? |
| [`proof-quality`](proof-quality.md) | Short, robust, readable proofs? |

The rubrics are adapted from those of Tau Ceti; see [NOTICE.md](NOTICE.md).
