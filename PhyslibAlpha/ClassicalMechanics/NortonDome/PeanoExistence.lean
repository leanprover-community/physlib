/-
Copyright (c) 2026 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Physlib.Meta.Linters.Sorry
/-!

# Peano's existence theorem (statements)

## i. Overview

Peano's existence theorem: the initial value problem `x' = f (t, x)`, `x t₀ = x₀` has a
solution on a closed time interval whenever `f` is continuous on the product of that interval
with a closed ball about `x₀` and the interval is short enough for the solution to stay in the
ball. No Lipschitz condition is asked, and only existence is guaranteed.

The theorem is not yet in Mathlib. This file records the hypotheses and the two forms of the
conclusion as stated in the Mathlib pull request
[#42148](https://github.com/leanprover-community/mathlib4/pull/42148), by Julian Rolfes,
Luke Schleef, Philipp Svinger, Paul Niessner and Florian Grube, with the proofs replaced by
`sorry` and the results marked `@[sorryful]`. Names and namespace are those of the pull
request, so that once it is merged this file can be deleted and its uses redirected to
Mathlib's `IsPeano` by a change of imports. `NortonDome.NewtonianSystem` uses the theorem to
show that a Newtonian system with a continuous force has local solutions.

## ii. Key results

- `IsPeano` collects the hypotheses: the initial time lies in the interval, the vector field is
  continuous on the cylinder, bounded by `L` there, and `L` times the length of the interval on
  either side of `t₀` is at most the radius `r` of the ball.
- `IsPeano.exists_eq_forall_mem_Icc_eq_integral` is the theorem in integral form.
- `IsPeano.exists_eq_forall_mem_Icc_hasDerivWithinAt₀` is the theorem in differential form.

## iii. Table of contents

- A. The hypotheses
- B. The theorem

## iv. References

- Mathlib pull request [#42148](https://github.com/leanprover-community/mathlib4/pull/42148),
  `Mathlib/Analysis/ODE/Peano.lean`.
- Hartman, P., *Ordinary Differential Equations*, 2nd ed., SIAM (2002), Theorem II.2.1.

-/

@[expose] public section

open Metric Set
open scoped NNReal

/-!

## A. The hypotheses

-/

/-- The hypotheses for Peano's existence theorem on a closed time interval and a closed ball. -/
structure IsPeano {E : Type*} [NormedAddCommGroup E]
    (f : ℝ × E → E) (tmin tmax t₀ : ℝ) (x₀ : E) (r L : ℝ≥0) : Prop where
  /-- The initial time belongs to the time interval. -/
  t₀_mem : t₀ ∈ Icc tmin tmax
  /-- The vector field is continuous on the set product of a time interval and a closed ball. -/
  continuousOn : ContinuousOn f (Icc tmin tmax ×ˢ closedBall x₀ r)
  /-- `L` is an upper bound of the norm of the vector field. -/
  norm_le : ∀ t ∈ Icc tmin tmax, ∀ x ∈ closedBall x₀ r, ‖f (t, x)‖ ≤ L
  /-- The time interval of validity. -/
  mul_max_le : L * max (tmax - t₀) (t₀ - tmin) ≤ r

namespace IsPeano

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : ℝ × E → E} {tmin tmax t₀ : ℝ} {x₀ : E} {r L : ℝ≥0}

/-!

## B. The theorem

-/

/-- Peano existence theorem, integral form. A solution exists on the full time interval and
  remains in `closedBall x₀ r`. Statement copied from Mathlib pull request #42148; the proof is
  pending upstream. -/
@[sorryful]
lemma exists_eq_forall_mem_Icc_eq_integral
    (hf : IsPeano f tmin tmax t₀ x₀ r L) :
    ∃ α : ℝ → E, ContinuousOn α (Icc tmin tmax) ∧ MapsTo α (Icc tmin tmax) (closedBall x₀ r) ∧
      ∀ t ∈ Icc tmin tmax, α t = x₀ + ∫ s in t₀..t, f (s, α s) := by
  sorry

/-- Peano existence theorem, differential form. A solution to the initial value problem exists
  on the full time interval. Statement copied from Mathlib pull request #42148; the proof is
  pending upstream. -/
@[sorryful]
lemma exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    (hf : IsPeano f tmin tmax t₀ x₀ r L) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧
      ∀ t ∈ Icc tmin tmax, HasDerivWithinAt α (f (t, α t)) (Icc tmin tmax) t := by
  sorry

end IsPeano

end
