/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!

# One-parameter subgroups of real Banach algebras

## i. Overview

Let `E` be a real Banach algebra. This file proves that every continuous additive character
`U : AddChar ℝ E` has the form `U(t) = exp (t • A)`, where `A = deriv U 0`.

This is the Banach-algebra argument underlying the correspondence between norm-continuous unitary
one-parameter groups and bounded self-adjoint generators. See
`Physlib.Mathematics.ForMathlib.OneParameterSubgroups.Unitary` for that correspondence.

**Proof outline.** Continuity at zero implies that, for sufficiently small `d > 0`, the integral of
`U` over `[0, d]` is close to `d • 1` and therefore invertible. If `I` is the indefinite integral of
`U`, the homomorphism law gives `U(t) * I(d) = I(t + d) - I(t)`. This identity proves that `U` is
differentiable. Setting `A` to the derivative at zero then gives the differential equation
`U'(t) = U(t)A`. Consequently `U(t) * exp (-tA)` has zero derivative and is constant. Uniqueness
follows by differentiating two exponential representations at zero.

## ii. Key results

* `OneParameterSubgroup.apply_eq_exp_smul_deriv`: A continuous one-parameter subgroup is the
  exponential of its derivative at zero.
* `OneParameterSubgroup.generator_unique`: Any exponential generator equals the derivative at zero.

## iii. References

* None.
-/

@[expose] public section

open Filter Topology

noncomputable section

namespace OneParameterSubgroup

variable {E : Type*} [NormedRing E] [NormedAlgebra ℝ E] [CompleteSpace E]

/-- `NormedSpace.exp`'s API wants a `ℚ`-algebra structure (for the `1/n!` coefficients), which
isn't automatic from `NormedAlgebra ℝ E` alone; derive it once here rather than at each use site. -/
local instance : NormedAlgebra ℚ E := .restrictScalars ℚ ℝ E

lemma exists_isUnit_intervalIntegral [Nontrivial E] (U : AddChar ℝ E) (hU : Continuous U) :
    ∃ d : ℝ, 0 < d ∧ IsUnit (∫ x in (0 : ℝ)..d, U x) := by
  have hone : 0 < ‖(1 : E)‖ := norm_pos_iff.mpr one_ne_zero
  have hevent : ∀ᶠ x : ℝ in 𝓝 0, ‖U x - 1‖ < ‖(1 : E)‖⁻¹ / 2 := by
    have hmem : Set.Iio (‖(1 : E)‖⁻¹ / 2) ∈ 𝓝 ‖U 0 - 1‖ := by
      simpa using Iio_mem_nhds (by positivity : 0 < ‖(1 : E)‖⁻¹ / 2)
    exact (continuous_norm.comp (hU.sub continuous_const)).continuousAt hmem
  obtain ⟨r, hr, hrU⟩ := Metric.eventually_nhds_iff.mp hevent
  let d := r / 2
  have hd : 0 < d := by positivity
  let q : Eˣ := {
    val := d • 1
    inv := d⁻¹ • 1
    val_inv := by rw [smul_mul_smul_comm, mul_inv_cancel₀ hd.ne', one_smul, one_mul]
    inv_val := by rw [smul_mul_smul_comm, inv_mul_cancel₀ hd.ne', one_smul, one_mul] }
  refine ⟨d, hd, (Units.ofNearby q _ ?_).isUnit⟩
  calc
    _ = ‖(∫ x in (0 : ℝ)..d, U x) - d • (1 : E)‖ := rfl
    _ = ‖(∫ x in (0 : ℝ)..d, U x) - ∫ _x in (0 : ℝ)..d, (1 : E)‖ := by
      rw [intervalIntegral.integral_const, sub_zero]
    _ = ‖∫ x in (0 : ℝ)..d, (U x - 1)‖ := by
      rw [intervalIntegral.integral_sub (hU.intervalIntegrable 0 d)
        (continuous_const.intervalIntegrable 0 d)]
    _ ≤ (‖(1 : E)‖⁻¹ / 2) * |d - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => by
        apply le_of_lt
        apply hrU
        rw [Real.dist_0_eq_abs]
        rw [Set.uIoc_of_le hd.le] at hx
        rw [abs_of_nonneg hx.1.le]
        exact hx.2.trans_lt (by dsimp [d]; linarith))
    _ = (‖(1 : E)‖⁻¹ / 2) * d := by rw [sub_zero, abs_of_pos hd]
    _ < d * ‖(1 : E)‖⁻¹ := by nlinarith [inv_pos.mpr hone]
    _ = ‖q.inv‖⁻¹ := by simp [q, norm_smul, mul_comm, abs_of_pos hd]


/-- Translating a one-parameter subgroup translates its interval integral. -/
lemma mul_intervalIntegral_eq_sub (U : AddChar ℝ E) (hU : Continuous U) (s t : ℝ) :
    U s * ∫ x in (0 : ℝ)..t, U x =
      (∫ x in (0 : ℝ)..(s + t), U x) - ∫ x in (0 : ℝ)..s, U x := by
  let L : E →L[ℝ] E :=
    (LinearMap.mulLeft ℝ (U s)).mkContinuous ‖U s‖ (fun x => norm_mul_le _ _)
  calc
    _ = L (∫ x in (0 : ℝ)..t, U x) := rfl
    _ = ∫ x in (0 : ℝ)..t, L (U x) :=
      (L.intervalIntegral_comp_comm (hU.intervalIntegrable 0 t)).symm
    _ = ∫ x in (0 : ℝ)..t, U (s + x) := by
      apply intervalIntegral.integral_congr
      intro x _
      exact (U.map_add_eq_mul s x).symm
    _ = ∫ x in s..(s + t), U x := by
      rw [intervalIntegral.integral_comp_add_left, add_zero]
    _ = (∫ x in (0 : ℝ)..(s + t), U x) - ∫ x in (0 : ℝ)..s, U x := by
      rw [eq_sub_iff_add_eq, add_comm]
      exact intervalIntegral.integral_add_adjacent_intervals
        (hU.intervalIntegrable 0 s) (hU.intervalIntegrable s (s + t))

lemma differentiable [Nontrivial E] (U : AddChar ℝ E) (hU : Continuous U) :
    Differentiable ℝ U := by
  obtain ⟨d, _, hV⟩ := exists_isUnit_intervalIntegral U hU
  let V : E := ∫ x in (0 : ℝ)..d, U x
  let v : Eˣ := hV.unit
  have hv : (v : E) = V := hV.unit_spec
  let F : ℝ → E := fun t => ∫ x in (0 : ℝ)..t, U x
  have hF (t : ℝ) : HasDerivAt F (U t) t :=
    (hU.integral_hasStrictDerivAt 0 t).hasDerivAt
  have htranslate (t : ℝ) : U t * V = F (t + d) - F t :=
    mul_intervalIntegral_eq_sub U hU t d
  intro t
  have hR : HasDerivAt (fun s : ℝ => F (s + d) - F s)
      (U (t + d) - U t) t := by
    exact (HasDerivAt.comp_add_const t d (hF (t + d))).sub (hF t)
  have heq : U = fun s : ℝ => (F (s + d) - F s) * (↑v⁻¹ : E) := by
    funext s
    calc
      U s = (U s * (v : E)) * (↑v⁻¹ : E) := by simp
      _ = (F (s + d) - F s) * (↑v⁻¹ : E) := by rw [hv, htranslate]
  rw [heq]
  exact (hR.mul_const (↑v⁻¹ : E)).differentiableAt

lemma apply_eq_exp_smul_deriv (U : AddChar ℝ E) (hU : Continuous U) (t : ℝ) :
    U t = NormedSpace.exp (t • deriv U 0) := by
  cases subsingleton_or_nontrivial E with
  | inl _ => exact Subsingleton.elim _ _
  | inr _ =>
    have hdiff : Differentiable ℝ U := differentiable U hU
    let A : E := deriv U 0
    have hUderiv (t : ℝ) : HasDerivAt U (U t * A) t := by
      have ht : HasDerivAt U (deriv U t) t :=
        hdiff.differentiableAt.hasDerivAt
      have h0 : HasDerivAt U (deriv U 0) 0 :=
        hdiff.differentiableAt.hasDerivAt
      have hleft : HasDerivAt (fun s : ℝ => U (t + s)) (deriv U t) 0 :=
        HasDerivAt.comp_const_add t 0 (by simpa using ht)
      have hright : HasDerivAt (fun s : ℝ => U t * U s) (U t * A) 0 := by
        dsimp only [A]
        exact HasDerivAt.const_mul (U t) h0
      have heq : (fun s : ℝ => U (t + s)) = fun s : ℝ => U t * U s := by
        funext s
        exact U.map_add_eq_mul t s
      have hder : deriv U t = U t * A := hleft.unique (heq ▸ hright)
      rwa [← hder]
    let G : ℝ → E := fun t => U t * NormedSpace.exp (t • (-A))
    have hG : Differentiable ℝ G := fun t =>
      ((hUderiv t).mul (hasDerivAt_exp_smul_const (-A) t)).differentiableAt
    have hGder (t : ℝ) : deriv G t = 0 := by
      apply ((hUderiv t).mul (hasDerivAt_exp_smul_const (-A) t)).deriv.trans
      have hcomm : Commute A (NormedSpace.exp (t • (-A))) := by
        exact ((Commute.refl A).neg_right.smul_right t).exp_right
      rw [mul_assoc, hcomm.eq]
      noncomm_ring
    have hconst (t : ℝ) : G t = G 0 := is_const_of_deriv_eq_zero hG hGder t 0
    have hone : U t * Ring.inverse (NormedSpace.exp (t • A)) = 1 := by
      simpa [G, ← Ring.inverse_exp] using hconst t
    have hexp : IsUnit (NormedSpace.exp (t • A)) := NormedSpace.isUnit_exp (t • A)
    let e : Eˣ := hexp.unit
    have he : (e : E) = NormedSpace.exp (t • A) := hexp.unit_spec
    rw [← he, Ring.inverse_unit] at hone
    calc
      U t = (U t * (↑e⁻¹ : E)) * (e : E) := by simp
      _ = NormedSpace.exp (t • A) := by
        rw [hone, one_mul, he]

/-- Any exponential generator of a one-parameter subgroup is its derivative at zero. -/
lemma generator_unique (U : AddChar ℝ E) (A : E)
    (h : ∀ t : ℝ, U t = NormedSpace.exp (t • A)) : A = deriv U 0 := by
  simp [funext h, (hasDerivAt_exp_smul_const A (0 : ℝ)).deriv]

end OneParameterSubgroup
