# Generality

Is the material at its natural level? This is API quality; leave assumptions that change the
claim to the correctness angle, and whether assumptions are physically meaningful to the
physical-relevance angle.

- Point out assumptions that are visibly unused, stronger than standard Mathlib convention, or
  superseded by a nearby more general theorem. Show the weaker signature you suggest.
- Prove the general result first and derive special cases; point out a proof duplicated for a
  special case the PR also proves, or could readily prove, in general. `AGENTS.md` asks to
  extract the general statement and keep the specialization as a corollary.
- Part of a proof may use only a weaker form of a hypothesis (only continuity, not
  smoothness); suggest stating that part as a lemma under the weaker assumption.
- Generalize to the natural form, not speculatively: point out both under-generalization (a
  result stated for `ℝ³` that holds in any dimension, for a specific metric when any would do)
  and abstraction with no use, such as parameters that never specialize to anything in the
  library.

## Score guidance

- 2–3 for unused or too-strong assumptions, special-case duplication, or the wrong level in
  either direction.
- 5 when the statements sit at the natural level.
