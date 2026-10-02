/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.JordanOrderUnit.Observable
public import PhyslibAlpha.ProbabilisticTheory.JordanOrderUnit.Quadratic.Order

/-!

# Conditioning a state on a projection

## i. Overview

For a Jordan projection `p` with positive quadratic representation `U_p`, and a state `ω` with `ω(p)
≠ 0`, the functional `x ↦ ω(U_p x) / ω(p)` is a state: `ω` conditioned on the outcome `p`.

## ii. Key results

- `JordanAlgebra.IsJordanProjection.condition` : the conditioned state.
- `JordanAlgebra.IsJordanProjection.condition_self` : the conditioned state assigns probability `1`
  to `p`.

## iii. Table of contents

- A. Quadratic conditioning

-/

@[expose] public section

namespace ProbabilisticTheory

open JordanAlgebra
open scoped JordanAlgebra

variable {E : Type*} [IsJordanOrderUnit E]

/-! ## A. Quadratic conditioning -/

namespace JordanAlgebra

/-- Condition a state on a Jordan projection.  Positivity of the quadratic representation is
kept explicit, since it does not follow from the weak `IsJordanOrderUnit` interface. -/
noncomputable def IsJordanProjection.condition {p : E}
    (hp : IsJordanProjection p) (ω : 𝓢[ℝ, E]) (hmass : 0 < ω p)
    (hU : ∀ x, 0 ≤ x → 0 ≤ U p x) : 𝓢[ℝ, E] :=
  UnitalPositiveLinearMap.ofLinearMap
    ((ω p)⁻¹ • (ω.toLinearMap.comp (U p)))
    (fun x hx => by
      change 0 ≤ (ω p)⁻¹ * ω (U p x)
      exact mul_nonneg (inv_nonneg.mpr hmass.le) (ω.map_nonneg (hU x hx)))
    (by
      change (ω p)⁻¹ * ω (U p 1) = 1
      rw [hp.quadRep_one]
      exact inv_mul_cancel₀ hmass.ne')

@[simp]
lemma IsJordanProjection.condition_apply {p : E}
    (hp : IsJordanProjection p) (ω : 𝓢[ℝ, E]) (hmass : 0 < ω p)
    (hU : ∀ x, 0 ≤ x → 0 ≤ U p x) (x : E) :
    hp.condition ω hmass hU x = (ω p)⁻¹ * ω (U p x) :=
  rfl

lemma IsJordanProjection.condition_one {p : E}
    (hp : IsJordanProjection p) (ω : 𝓢[ℝ, E]) (hmass : 0 < ω p)
    (hU : ∀ x, 0 ≤ x → 0 ≤ U p x) :
    hp.condition ω hmass hU 1 = 1 := by
  rw [hp.condition_apply, hp.quadRep_one]
  exact inv_mul_cancel₀ hmass.ne'

lemma IsJordanProjection.condition_nonneg {p : E}
    (hp : IsJordanProjection p) (ω : 𝓢[ℝ, E]) (hmass : 0 < ω p)
    (hU : ∀ x, 0 ≤ x → 0 ≤ U p x) {x : E} (hx : 0 ≤ x) :
    0 ≤ hp.condition ω hmass hU x :=
  (hp.condition ω hmass hU).map_nonneg hx

/-- Conditioning on `p` makes `p` certain. -/
lemma IsJordanProjection.condition_self {p : E}
    (hp : IsJordanProjection p) (ω : 𝓢[ℝ, E]) (hmass : 0 < ω p)
    (hU : ∀ x, 0 ≤ x → 0 ≤ U p x) :
    hp.condition ω hmass hU p = 1 := by
  rw [hp.condition_apply, hp.quadRep_self]
  exact inv_mul_cancel₀ hmass.ne'

/-- Conditioning on `p` assigns probability zero to every projection Jordan-orthogonal to `p`. -/
lemma IsJordanProjection.condition_apply_of_jordanOrthogonal {p q : E}
    (hp : IsJordanProjection p) (ω : 𝓢[ℝ, E]) (hmass : 0 < ω p)
    (hU : ∀ x, 0 ≤ x → 0 ≤ U p x) (horth : p * q = 0) :
    hp.condition ω hmass hU q = 0 := by
  rw [hp.condition_apply, hp.quadRep_jordanOrthogonal horth, map_zero, mul_zero]

/-- Conditioning on a projection assigns probability zero to its algebraic complement. -/
lemma IsJordanProjection.condition_complement {p : E}
    (hp : IsJordanProjection p) (ω : 𝓢[ℝ, E]) (hmass : 0 < ω p)
    (hU : ∀ x, 0 ≤ x → 0 ≤ U p x) :
    hp.condition ω hmass hU (1 - p) = 0 :=
  hp.condition_apply_of_jordanOrthogonal ω hmass hU hp.jordanOrthogonal_complement

/-- Condition a state on a Jordan projection using the ambient quadratic-order capability.
This is the physics-facing form of `condition`: its only non-algebraic input is exactly the
positivity of quadratic representations, bundled by `IsQuadraticallyPositive`. -/
noncomputable def IsJordanProjection.conditionOfQuadraticPositive {p : E}
    (hp : IsJordanProjection p) (ω : 𝓢[ℝ, E]) (hmass : 0 < ω p)
    [IsQuadraticallyPositive E] : 𝓢[ℝ, E] :=
  hp.condition ω hmass fun _ hx => quadRep_nonneg p hx

@[simp]
lemma IsJordanProjection.conditionOfQuadraticPositive_apply {p : E}
    (hp : IsJordanProjection p) (ω : 𝓢[ℝ, E]) (hmass : 0 < ω p)
    [IsQuadraticallyPositive E] (x : E) :
    hp.conditionOfQuadraticPositive ω hmass x = (ω p)⁻¹ * ω (U p x) :=
  by rw [conditionOfQuadraticPositive, condition_apply]

end JordanAlgebra

end ProbabilisticTheory
