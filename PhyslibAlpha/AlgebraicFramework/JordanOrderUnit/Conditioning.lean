/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.JordanOrderUnit.Observable
public import PhyslibAlpha.AlgebraicFramework.JordanOrderUnit.Quadratic.Order

/-!

# Conditioning a state by a Jordan projection

For a projection `p`, quadratic compression is `U_p`.  Whenever `U_p` is positive and the state
assigns nonzero probability to `p`, the normalized functional

`x ↦ ω(U_p x) / ω(p)`

is again a state.  Positivity of `U_p` is an explicit hypothesis here: it is a theorem of JB
spectral theory, not part of the weak `IsJordanOrderUnit` interface.  This separation lets the
conditioning construction live at its true level without postulating the missing JB theorem.

-/

@[expose] public section

open JordanAlgebra
open scoped JordanAlgebra

variable {E : Type*} [NonAssocCommRing E] [PartialOrder E] [IsOrderedAddMonoid E]
  [Module ℝ E] [SMulCommClass ℝ E E] [IsOrderUnit E]

/-! ## Quadratic conditioning -/

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

omit [IsOrderUnit E] in
@[simp]
theorem IsJordanProjection.condition_apply {p : E}
    (hp : IsJordanProjection p) (ω : 𝓢[ℝ, E]) (hmass : 0 < ω p)
    (hU : ∀ x, 0 ≤ x → 0 ≤ U p x) (x : E) :
    hp.condition ω hmass hU x = (ω p)⁻¹ * ω (U p x) :=
  rfl

omit [IsOrderUnit E] in
theorem IsJordanProjection.condition_one {p : E}
    (hp : IsJordanProjection p) (ω : 𝓢[ℝ, E]) (hmass : 0 < ω p)
    (hU : ∀ x, 0 ≤ x → 0 ≤ U p x) :
    hp.condition ω hmass hU 1 = 1 := by
  rw [hp.condition_apply, hp.quadRep_one]
  exact inv_mul_cancel₀ hmass.ne'

omit [IsOrderUnit E] in
theorem IsJordanProjection.condition_nonneg {p : E}
    (hp : IsJordanProjection p) (ω : 𝓢[ℝ, E]) (hmass : 0 < ω p)
    (hU : ∀ x, 0 ≤ x → 0 ≤ U p x) {x : E} (hx : 0 ≤ x) :
    0 ≤ hp.condition ω hmass hU x :=
  (hp.condition ω hmass hU).map_nonneg hx

omit [IsOrderUnit E] in
/-- Conditioning on `p` makes `p` certain. -/
theorem IsJordanProjection.condition_self {p : E}
    (hp : IsJordanProjection p) (ω : 𝓢[ℝ, E]) (hmass : 0 < ω p)
    (hU : ∀ x, 0 ≤ x → 0 ≤ U p x) :
    hp.condition ω hmass hU p = 1 := by
  rw [hp.condition_apply, hp.quadRep_self]
  exact inv_mul_cancel₀ hmass.ne'

omit [IsOrderUnit E] in
/-- Conditioning on `p` assigns probability zero to every projection Jordan-orthogonal to `p`. -/
theorem IsJordanProjection.condition_apply_of_jordanOrthogonal {p q : E}
    (hp : IsJordanProjection p) (ω : 𝓢[ℝ, E]) (hmass : 0 < ω p)
    (hU : ∀ x, 0 ≤ x → 0 ≤ U p x) (horth : p * q = 0) :
    hp.condition ω hmass hU q = 0 := by
  rw [hp.condition_apply, hp.quadRep_jordanOrthogonal horth, map_zero, mul_zero]

omit [IsOrderUnit E] in
/-- Conditioning on a projection assigns probability zero to its algebraic complement. -/
theorem IsJordanProjection.condition_complement {p : E}
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

omit [IsOrderUnit E] in
@[simp]
theorem IsJordanProjection.conditionOfQuadraticPositive_apply {p : E}
    (hp : IsJordanProjection p) (ω : 𝓢[ℝ, E]) (hmass : 0 < ω p)
    [IsQuadraticallyPositive E] (x : E) :
    hp.conditionOfQuadraticPositive ω hmass x = (ω p)⁻¹ * ω (U p x) :=
  by rw [conditionOfQuadraticPositive, condition_apply]

end JordanAlgebra
