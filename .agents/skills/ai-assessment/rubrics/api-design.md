# Public API

You assess the public interface the PR exposes.

- Assess the post-PR interface. An old name or module path should not survive solely for
  compatibility unless the project asks for a deprecation; suggest removing aliases and
  wrapper declarations that only preserve an obsolete surface.
- Under-exposure is a finding too. A declaration whose statement mentions only Mathlib types and
  whose proof does not depend on this file's subject is general infrastructure: it belongs in its
  canonical home (for example under `Physlib/Mathematics/` or the relevant `Space` file), public,
  not `private` here. Generality is a reason to relocate and export, never a reason to hide.
  `private` is for a step genuinely specific to the surrounding argument.
- Expose what later developments need and genuinely reusable general results. Keep an
  implementation helper `private` when it has no use outside the proof or file it serves. Do
  not expose definition bodies to compensate for missing lemmas: suggest the missing lemma
  instead.
- A definition needs the API that characterizes it: introduction and elimination, the
  `*_def` and `mem_*_iff` restatements, interaction with the operations in scope, and the
  universal property where there is one. For a physical quantity this includes how it behaves
  under the operations physicists apply to it (linearity, symmetries, Lorentz or rotation
  covariance, units). Try to use the new API without unfolding and suggest any missing
  characteristic lemmas.
- A bundled definition should be **extensional on the object it denotes**: it exposes no data
  its laws leave unconstrained. If a structure field or indexed family is left free on inputs
  no operation or law actually uses, two terms that agree everywhere meaningful can still
  differ, so no `@[ext]` holds and equality reasoning is blocked for every consumer. Suggest
  constraining or dropping the free data.
- Suggest symmetric, dual, or parallel forms only when the file already develops both sides.
- Annotate `@[simp]` the normal-form lemmas (and `@[grind]` where the surrounding files use
  `grind`). Point out a characteristic lemma that would benefit from one, and an annotation
  that would loop or fire wrongly.

## Score guidance

- 2–3 for an over-exposed surface, general infrastructure hidden as `private` instead of
  relocated, a body exposed for want of API, an incomplete characteristic API, free data that
  defeats extensionality, or missing or wrong automation annotations.
- 5 when the surface is minimal and the characteristic API is complete and annotated.
