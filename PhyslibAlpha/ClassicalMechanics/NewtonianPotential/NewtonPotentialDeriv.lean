/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.ClassicalMechanics.NewtonianPotential.NewtonPotential
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# The derivative of the Newtonian potential

## i. Overview

For a Schwartz mass density `ρ` on `Space 3` the Newtonian potential `Φ` is differentiable, and
its derivative in a direction `v` is the Newtonian potential of the derivative of `ρ` in the
direction `v`. The derivative is obtained by writing `Φ(x) = -G ∫ ρ(x - z) / ‖z‖ dz` and
differentiating under the integral. In particular `Φ` is continuous.

## ii. Key results

- `hasFDerivAt_newtonPotential` : the Newtonian potential is differentiable.
- `fderiv_newtonPotential_apply` : the derivative of the potential is the potential of the
  derivative.
- `continuous_newtonPotential` : the Newtonian potential is continuous.

## iii. Table of contents

- A. Differentiating under the integral
- B. Continuity

## iv. References

- None.
-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.NewtonianPotential

open MeasureTheory Space Physlib Distribution
open scoped SchwartzMap LineDeriv

/-!

## A. Differentiating under the integral

-/

/-- The Newtonian potential as an integral over the relative position. -/
lemma newtonPotential_eq_integral_sub (G : ℝ) (ρ : 𝓢(Space 3, ℝ)) (x : Space 3) :
    newtonPotential G ρ x = -G * ∫ z : Space 3, ρ (x - z) * ‖z‖⁻¹ := by
  rw [newtonPotential_apply,
    ← integral_sub_left_eq_self (fun y : Space 3 => ρ y * ‖x - y‖⁻¹) volume x]
  simp

/-- The derivative of a Schwartz map at `x - z` decays in `z`, locally uniformly in `x`. -/
lemma exists_norm_fderiv_sub_le (ρ : 𝓢(Space 3, ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x z : Space 3,
      ‖fderiv ℝ ρ (x - z)‖ ≤ C * (1 + ‖x‖) ^ 4 * ((1 + ‖z‖) ^ 4)⁻¹ := by
  set C : ℝ := 2 ^ 4 * (Finset.Iic ((4, 1) : ℕ × ℕ)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) ρ with hC
  have hdec : ∀ w : Space 3, (1 + ‖w‖) ^ 4 * ‖fderiv ℝ ρ w‖ ≤ C := by
    intro w
    have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (4, 1)) (k := 4) (n := 1)
      le_rfl le_rfl ρ w
    rwa [norm_iteratedFDeriv_one] at this
  have hC0 : 0 ≤ C := le_trans (by positivity) (hdec 0)
  refine ⟨C, hC0, fun x z => ?_⟩
  have hz : 1 + ‖z‖ ≤ (1 + ‖x - z‖) * (1 + ‖x‖) := by
    have h3 : ‖z‖ ≤ ‖x - z‖ + ‖x‖ := by
      simpa [add_comm] using norm_sub_le x (x - z)
    nlinarith [norm_nonneg (x - z), norm_nonneg x, norm_nonneg z]
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc ‖fderiv ℝ ρ (x - z)‖ * (1 + ‖z‖) ^ 4
      ≤ ‖fderiv ℝ ρ (x - z)‖ * ((1 + ‖x - z‖) * (1 + ‖x‖)) ^ 4 := by gcongr
    _ = (1 + ‖x - z‖) ^ 4 * ‖fderiv ℝ ρ (x - z)‖ * (1 + ‖x‖) ^ 4 := by ring
    _ ≤ C * (1 + ‖x‖) ^ 4 := by
        gcongr
        exact hdec (x - z)

/-- The function `(1 + ‖y‖)⁻⁴` is integrable on `Space 3`. -/
lemma integrable_one_add_norm_pow_four_inv :
    Integrable (fun y : Space 3 => ((1 + ‖y‖) ^ 4)⁻¹) := by
  have h := integrable_one_add_norm (E := Space 3) (μ := volume) (r := 4) (by simp; norm_num)
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rw [Real.rpow_neg (by positivity)]
  norm_cast

open PhyslibAlpha.Hydrogen in
/-- The integrand of the derivative of the Newtonian potential is integrable. -/
lemma integrable_inv_norm_smul_fderiv_sub (ρ : 𝓢(Space 3, ℝ)) (x : Space 3) :
    Integrable (fun z : Space 3 => ‖z‖⁻¹ • fderiv ℝ ρ (x - z)) := by
  obtain ⟨C, hC, hb⟩ := exists_norm_fderiv_sub_le ρ
  have hcont : Continuous (fun w : Space 3 => fderiv ℝ ρ w) :=
    (ρ.smooth 1).continuous_fderiv (by norm_num)
  refine Integrable.mono' ((integrable_inv_norm_mul_one_add_norm_pow (d := 3) (by norm_num)
    (M := 4) (by norm_num)).const_mul (C * (1 + ‖x‖) ^ 4))
    ((measurable_norm.inv.aestronglyMeasurable).smul
      (hcont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun z => ?_)
  rw [norm_smul, norm_inv, norm_norm]
  calc ‖z‖⁻¹ * ‖fderiv ℝ ρ (x - z)‖
      ≤ ‖z‖⁻¹ * (C * (1 + ‖x‖) ^ 4 * ((1 + ‖z‖) ^ 4)⁻¹) := by gcongr; exact hb x z
    _ = _ := by ring

open Metric in
/-- On the ball of radius one around `x₀`, `1 + ‖x‖ ≤ 2 + ‖x₀‖`. -/
lemma one_add_norm_le_of_mem_ball {x x₀ : Space 3} (hx : x ∈ ball x₀ 1) :
    1 + ‖x‖ ≤ 2 + ‖x₀‖ := by
  have h1 : ‖x - x₀‖ < 1 := by simpa [dist_eq_norm] using hx
  have h2 := norm_sub_norm_le x x₀
  linarith

open PhyslibAlpha.Hydrogen Metric in
/-- The Newtonian potential is differentiable, with derivative given by differentiating the
density under the integral. -/
lemma hasFDerivAt_newtonPotential (G : ℝ) (ρ : 𝓢(Space 3, ℝ)) (x₀ : Space 3) :
    HasFDerivAt (newtonPotential G ρ)
      (-G • ∫ z : Space 3, ‖z‖⁻¹ • fderiv ℝ ρ (x₀ - z)) x₀ := by
  have hfun : newtonPotential G ρ = fun x => -G * ∫ z : Space 3, ρ (x - z) * ‖z‖⁻¹ :=
    funext fun x => newtonPotential_eq_integral_sub G ρ x
  rw [hfun]
  obtain ⟨C, hC, hb⟩ := exists_norm_fderiv_sub_le ρ
  have hρd : ∀ w : Space 3, HasFDerivAt ρ (fderiv ℝ ρ w) w := fun w =>
    ((ρ.smooth 1).differentiable (by norm_num) w).hasFDerivAt
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun (x : Space 3) (z : Space 3) => ρ (x - z) * ‖z‖⁻¹)
    (F' := fun (x : Space 3) (z : Space 3) => ‖z‖⁻¹ • fderiv ℝ ρ (x - z))
    (bound := fun z : Space 3 => C * (2 + ‖x₀‖) ^ 4 * (‖z‖⁻¹ * ((1 + ‖z‖) ^ 4)⁻¹))
    (ball_mem_nhds x₀ one_pos)
    (Filter.Eventually.of_forall fun x => by fun_prop)
    (by
      simpa using (integrable_mul_inv_norm_sub ρ x₀).comp_sub_left x₀)
    (integrable_inv_norm_smul_fderiv_sub ρ x₀).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z x hx => by
      rw [norm_smul, norm_inv, norm_norm]
      have hx' := one_add_norm_le_of_mem_ball hx
      calc ‖z‖⁻¹ * ‖fderiv ℝ ρ (x - z)‖
          ≤ ‖z‖⁻¹ * (C * (2 + ‖x₀‖) ^ 4 * ((1 + ‖z‖) ^ 4)⁻¹) := by
            gcongr
            exact (hb x z).trans (by gcongr)
        _ = C * (2 + ‖x₀‖) ^ 4 * (‖z‖⁻¹ * ((1 + ‖z‖) ^ 4)⁻¹) := by ring)
    ((integrable_inv_norm_mul_one_add_norm_pow (d := 3) (by norm_num) (M := 4)
      (by norm_num)).const_mul _)
    (Filter.Eventually.of_forall fun z x _ => by
      have h1 : HasFDerivAt (fun x : Space 3 => x - z) (ContinuousLinearMap.id ℝ (Space 3)) x :=
        (hasFDerivAt_id x).sub_const z
      simpa using ((hρd (x - z)).comp x h1).mul_const ‖z‖⁻¹)
  exact key.const_mul (-G)

/-- The derivative of the Newtonian potential in a direction `v` is the Newtonian potential of
the derivative of the density in the direction `v`. -/
lemma fderiv_newtonPotential_apply (G : ℝ) (ρ : 𝓢(Space 3, ℝ)) (x v : Space 3) :
    fderiv ℝ (newtonPotential G ρ) x v = newtonPotential G (∂_{v} ρ) x := by
  rw [(hasFDerivAt_newtonPotential G ρ x).fderiv, newtonPotential_eq_integral_sub,
    _root_.smul_apply,
    ContinuousLinearMap.integral_apply (integrable_inv_norm_smul_fderiv_sub ρ x), smul_eq_mul]
  congr 1
  congr 1 with z
  simp [SchwartzMap.lineDerivOp_apply_eq_fderiv, mul_comm]

/-!

## B. Continuity

-/

/-- The Newtonian potential of a Schwartz density is continuous. -/
@[fun_prop]
lemma continuous_newtonPotential (G : ℝ) (ρ : 𝓢(Space 3, ℝ)) :
    Continuous (newtonPotential G ρ) :=
  continuous_iff_continuousAt.mpr fun x => (hasFDerivAt_newtonPotential G ρ x).continuousAt

end PhyslibAlpha.NewtonianPotential
