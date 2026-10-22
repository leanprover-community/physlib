# Generality

Is the material at the natural Mathlib level? Uses `request_changes`. This is API quality;
leave assumptions that change the claim to correctness.

- Flag assumptions that are visibly unused, stronger than standard Mathlib convention, or
  contradicted by a nearby more general theorem. Show the stronger or weaker signature you
  want.
- Prove the general result first and derive special cases; flag a proof duplicated for a
  special case the PR also proves, or could readily prove, in general.
- Generalize to the natural form, not speculatively: flag both under-generalization and
  abstraction with no use and no roadmap need, such as parameters that never specialize to
  the target.

## Verdict

- `request_changes` for unused or too-strong assumptions, special-case duplication, or the
  wrong level in either direction.
- `approve` when the statements sit at the natural level.
