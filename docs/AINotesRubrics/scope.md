# Scope: a single coherent concept

One question: is this PR a single coherent unit? `AGENTS.md` asks that a PR add a **single
coherent concept**: every definition and lemma should either *be* that concept or supply the
minimal API to state and prove it. `docs/ReviewGuidelines.md` adds that a PR should be concise,
and gives rule-of-thumb PR lengths.

Whether the concept is physically relevant is the physical-relevance angle; whether its
statements are faithful is the correctness angle. Judge only the shape of the PR.

## What to look for

- More than one topic: an opportunistic refactor of prerequisite material bundled with new
  work, or several unrelated results at once. Suggest how to split the PR, naming which
  declarations go in which part and in what order the parts could land.
- Periphery: declarations that neither are the concept nor are needed to state or prove it.
  Suggest dropping them or moving them to a follow-up PR.
- Size: a PR well beyond the guideline lengths in `docs/ReviewGuidelines.md` that could be
  landed in stages. Suggest the stages.
- A PR description that does not say what the concept is. Suggest a one-line statement of it.

A single refactor that is itself the topic is fine, as are the file moves the placement angle
calls for alongside new material. A refactor of already-merged code needs no fresh
justification of its content.

## Score guidance

- 0–1 when the PR is several unrelated topics.
- 2–3 when one concept is clear but a substantial part of the PR is periphery or a bundled
  refactor.
- 5 when the PR is one concept with its minimal API.
