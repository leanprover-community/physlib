# Fill in an API map requirement

Work in this repository (Physlib). Read [AGENTS.md](../../AGENTS.md) and
[docs/API_MAP_GUIDE.md](../API_MAP_GUIDE.md) before you start.

## Pick a requirement

Search the `API-map.yaml` files (`find Physlib -name API-map.yaml`) for a requirement
marked `done: false` with `location: N/A`. Choose one that is a single, self-contained
piece of physics you can formalize completely. Say which map and which requirement you
picked, and why it is tractable, before writing any Lean.

## Formalize it in PhyslibAlpha

Put the work in the file under `PhyslibAlpha/` that mirrors the map's place in `Physlib/`
(e.g. a requirement in `Physlib/ClassicalMechanics/Pendulum/API-map.yaml` is filled in
under `PhyslibAlpha/ClassicalMechanics/Pendulum/`). Add to an existing file where one
fits; only create a new file with good reason, and import it into `PhyslibAlpha.lean`
(keep the list sorted).

Do not edit the `API-map.yaml`: `done: true` records content that lives in `Physlib`.

Follow AGENTS.md throughout — no `sorry`, no `axiom`, `lemma` over `theorem`, a docstring
on every definition, numbered sections, proofs under 50 LOC with longer arguments split
into named lemmas.


## Report

State the requirement you filled in, the declarations you added and the file each lives
in, the result of every check above, and your verdict on each review criterion.
