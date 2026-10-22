# Reuse and duplication

Pull requests must not duplicate existing material from Mathlib or TauCeti, whether directly or via unnecessary thin wrappers. Whenever it is possible to reuse existing developments from Mathlib, it is essential to do so, and to ensure that new contributions make effective use of the Mathlib theory.

A new declaration that a located existing declaration directly replaces should result in a
`block` review; every other form of duplication below is `request_changes`.

## Detecting potential duplication

Run each of these searches. Choose relevant search terms and grep (under
`.lake/packages/mathlib` and `TauCeti/`) to verify.

- For each new declaration, search for an existing one with the same content.
  (Sometimes you'll find something with a different name than expected, or a variant that
  matches up to renaming, definitional unfolding, symmetry or duality, or an existing
  bridging lemma.)
- For each proof more than a few lines long, search for the goal, and for its key
  intermediate steps. Standard plumbing (image and preimage computations, `Finsupp` support
  arithmetic, `Fin` case bashes) almost always has a named lemma;
  keep searching until you find it or are confident it is absent.
- For each definition assembled from raw pieces, search for a library combinator that does
  the assembly (for example `Finsupp.ofSupportFinite` rather than `Finsupp.onFinset`
  plumbing).
- For each new block of code, grep TauCeti for its distinctive identifiers or proof shape,
  to find near-clones that should be factored into a shared construction.
- Within the diff itself, look for private lemmas restating public ones up to defeq,
  composite lemmas that their component `@[simp]` lemmas already prove, and `∧`-bundles of
  existing lemmas.
- Treat compatibility-only aliases, wrapper declarations, forwarding import modules, deprecated
  shims, and duplicate theorem names as unnecessary duplication. The canonical replacement is
  the located existing API; require the compatibility artifact's deletion.

## Rejecting it

Every finding must name the located replacement and say exactly how to use it.
Name the existing lemmas you've found (and if necessary the one-liner showing how to use it).
If there are unnecessary duplications as public and private APIs, explain the overlaps.
Make sure that all assertions about duplication are backed up by explicit references based
on your grep searches; don't ask the author to search themselves.
Not every hit is a defect: Mathlib itself keeps per-type restatements of generic lemmas, and
a specialization with genuine consumers can earn its place.

## Verdict

- `block` on a declaration an existing one directly replaces.
- `request_changes` for reprovable results, special cases, or parallel APIs, and for proofs,
  definitions, or scaffolding that re-derive what a located lemma, combinator, or earlier
  line already provides.
- `approve` when the PR adds genuinely new material and reuses existing API where it can.
