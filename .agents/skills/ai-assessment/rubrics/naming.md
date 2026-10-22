# Naming and notation

You judge the names and notation introduced. Casing and mechanical style are linter-enforced;
do not re-report them. Uses `request_changes`. The Mathlib naming conventions document is
included after this rubric as part of your context; cite its rule when you claim terminology
is nonstandard.

- A theorem name describes its conclusion, read from the conclusion outward, in standard
  Mathlib terminology. Check adjacent declarations first: consistency beats a theoretically
  better name. If you claim terminology is nonstandard, cite the existing Mathlib name or the
  source term.
- Compare name strength to statement strength: a name must not advertise a missing converse,
  uniqueness, or equality (named `…_iff` with one direction, or `…_eq` proving only `≤`).
- Material goes in the `TauCeti` namespace, except when it is dot notation on something already
  defined in Lean or Mathlib: a declaration whose first explicit argument has an existing Lean or
  Mathlib type belongs in that type's namespace, so `x.foo` elaborates for consumers and the
  declaration can be upstreamed without renaming. Flag a file that opens `namespace TauCeti` and
  then `namespace Foo` for a Lean or Mathlib type `Foo` whose declarations take a `Foo`. Do not
  flag Tau Ceti's own notions that share a name with a Mathlib namespace, nor material merely filed
  under an organisational namespace such as `AlgebraicGeometry` or `MeasureTheory`.
- Introduce notation sparingly and `scoped`, following the precedent and precedence of
  existing Mathlib notation for the same object.

## Verdict

- `request_changes` for a name that describes the proof, uses nonstandard terminology,
  overstates the statement, or is wrong for its namespace, and for gratuitous or unscoped
  notation.
- `approve` when names describe conclusions in standard terminology and notation is minimal
  and conventional.
