# Naming and notation

You assess the names and notation introduced. Casing and mechanical style are linter-enforced;
do not re-report them. The Mathlib naming conventions document is included after this rubric
as part of your context; cite its rule when you say terminology is nonstandard. Physlib also
follows the Mathlib/Physlib conventions referred to in `docs/ReviewChecklist.md` (Level 4).

- A theorem name describes its conclusion, read from the conclusion outward, in standard
  Mathlib terminology. Check adjacent declarations first: consistency beats a theoretically
  better name. If you say terminology is nonstandard, cite the existing Mathlib or Physlib
  name or the source term.
- Physics names should use the standard term from the physics literature (`kineticEnergy`,
  `lorentzForce`), not an ad hoc abbreviation; where Mathlib and physics terminology differ,
  follow the convention of the surrounding Physlib files.
- Compare name strength to statement strength: a name should not advertise a missing converse,
  uniqueness, or equality (named `…_iff` with one direction, or `…_eq` proving only `≤`).
- Physlib organises material in topical namespaces (`ClassicalMechanics`, `Electromagnetism`,
  `Lorentz`, `Space`, …). A declaration whose first explicit argument has an existing Lean,
  Mathlib or Physlib type belongs in that type's namespace, so `x.foo` dot notation works.
  Point out material in a namespace that does not fit its subject.
- Introduce notation sparingly and `scoped`, following the precedent and precedence of
  existing Mathlib and Physlib notation for the same object.

## Score guidance

- 2–3 for names that describe the proof, use nonstandard terminology, overstate the
  statement, or sit in the wrong namespace, and for gratuitous or unscoped notation.
- 5 when names describe conclusions in standard terminology and notation is minimal and
  conventional.
