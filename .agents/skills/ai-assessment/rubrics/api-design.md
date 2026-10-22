# Public API

You judge the public interface the PR exposes. Uses `request_changes`.

- Judge only the canonical post-PR interface. An old name or module path must not survive solely
  for compatibility: require deletion of compatibility aliases, wrapper declarations, forwarding
  import modules, deprecated shims (including `deprecated_module`), and duplicate theorem names.
  Never request such an artifact for external users of an older revision.
- Under-exposure is a finding too. A declaration whose statement mentions only Mathlib types and
  whose proof does not depend on this file's subject is general infrastructure: it belongs in its
  canonical home, public, not `private` here. Generality is a reason to relocate and export, never
  a reason to hide. `private` is for a step genuinely specific to the surrounding argument, not for
  a result that would stand on its own in an earlier file or in Mathlib.
- Expose what later stages of the roadmap need, the explicit products of the roadmap, and genuinely reusable general results. Keep an implementation helper `private` when it has no use outside the proof or file it serves. The roadmap's named targets are not the whole allowed surface, so do not ask for something to be `private` merely because it is not named there. Do not expose bodies to compensate for missing
  lemmas: keep bodies unexposed (no `@[expose]`) where possible unless a consumer must unfold or compute,
  and ask for the missing lemma instead. Recall that we can avoid making lemmas rely on defeq downstream by using `:= (rfl)` instead of `:= rfl`.
- A definition needs the API that characterizes it: introduction and elimination, the
  `*_def` and `mem_*_iff` restatements, interaction with the operations in scope, and the
  universal property where there is one. Try to use the new API without unfolding and demand any missing characteristic lemmas.
- A bundled definition must be **extensional on the object it denotes**: it exposes no data its
  laws leave unconstrained. If a structure field or indexed family is left free on inputs no
  operation or law actually uses, two terms that agree everywhere meaningful can still differ,
  so no `@[ext]` holds and equality and uniqueness reasoning are blocked for every consumer — a
  user-visible risk, not taste. Constrain or drop the free data: carry only what the laws use,
  and recover any wider view as a derived, canonically-determined accessor. Test: if `@[ext]`
  cannot be derived from agreement on the inputs the operations and laws actually use, the
  definition carries free data; require its removal.
- Require symmetric, dual, or parallel forms only when the file already develops both sides or
  the roadmap needs them.
- Annotate `@[simp]` the normal-form lemmas and `@[grind]` the lemmas that should drive
  `grind`. Flag a characteristic lemma that should carry one and does not, and an annotation
  that would loop or fire wrongly.

## Verdict

- `request_changes` for a compatibility-only surface, an over-exposed surface, general
  infrastructure hidden as `private` instead of relocated, a body exposed
  for want of API, an incomplete characteristic API, free data that defeats extensionality, or
  missing or wrong automation annotations.
- `approve` when the surface is minimal, bodies are hidden, and the characteristic API is
  complete and annotated, with no obsolete compatibility layer.
