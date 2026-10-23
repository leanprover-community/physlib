# Reuse and duplication

Pull requests should not duplicate existing material from Mathlib or Physlib, whether directly
or via thin wrappers. Where existing developments can be reused, the PR should reuse them and
make effective use of the Mathlib theory. `AGENTS.md` also asks not to add lemmas that are
trivial rewrites of existing Mathlib or Physlib results, unless they add genuine physics
context.

## Detecting potential duplication

Run each of these searches. Choose relevant search terms and grep (under
`.lake/packages/mathlib`, `Physlib/`, `QuantumInfo/` and `PhyslibAlpha/`) to verify.

- For each new declaration, search for an existing one with the same content.
  (Sometimes you'll find something with a different name than expected, or a variant that
  matches up to renaming, definitional unfolding, symmetry or duality, or an existing
  bridging lemma.)
- For each proof more than a few lines long, search for the goal, and for its key
  intermediate steps. Standard plumbing (image and preimage computations, `Finset` sums,
  `Fin` case bashes, inner-product and norm manipulations) almost always has a named lemma;
  keep searching until you find it or are confident it is absent.
- For each definition assembled from raw pieces, search for a library combinator that does
  the assembly.
- For each new block of code, grep Physlib for its distinctive identifiers or proof shape,
  to find near-clones that could be factored into a shared construction.
- Within the diff itself, look for private lemmas restating public ones up to defeq,
  composite lemmas that their component `@[simp]` lemmas already prove, and `∧`-bundles of
  existing lemmas.
- A restatement that adds genuine physics context (a physically named special case that
  readers will look for) is not duplication; say so if you consider it.

## Reporting it

Every finding names the located existing declaration and says exactly how to use it
(if necessary with the one-liner showing how). If there are overlapping public and private
APIs, explain the overlap. Back every claim of duplication with explicit references from your
grep searches; don't ask the author to search themselves. Not every hit is duplication:
Mathlib itself keeps per-type restatements of generic lemmas, and a specialization with
genuine consumers can earn its place.

## Score guidance

- 0–1 when a central new declaration is directly replaced by an existing one.
- 2–3 for reprovable results, special cases, or parallel APIs, and for proofs, definitions,
  or scaffolding that re-derive what a located lemma, combinator, or earlier line already
  provides.
- 5 when the PR adds genuinely new material and reuses existing API where it can.
