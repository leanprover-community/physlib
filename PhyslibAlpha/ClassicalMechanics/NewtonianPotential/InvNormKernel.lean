/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.ClassicalMechanics.NewtonianPotential.GaussianKernel
public import PhyslibAlpha.ClassicalMechanics.NewtonianPotential.NewtonPotential
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The inverse-norm kernel on `Space 3` is positive semi-definite

## i. Overview

For a Schwartz map `ρ` on `Space 3` the quadratic form of the kernel `1 / ‖x - y‖` is
nonnegative: `0 ≤ ∫∫ ρ(x) ρ(y) / ‖x - y‖ dx dy`. This is the statement that the electrostatic
self-energy of a charge density is nonnegative and that the gravitational self-energy of a mass
density is nonpositive.

The proof writes the inverse norm as a superposition of Gaussians,
`√π / ‖z‖ = ∫₀^∞ s^(-1/2) exp (-s ‖z‖²) ds`, and uses that each Gaussian kernel is positive
semi-definite.

## ii. Key results

- `integral_rpow_mul_exp_neg_mul_norm_sq` : the inverse norm as a superposition of Gaussians.
- `integral_mul_mul_inv_norm_sub_nonneg` : the inverse-norm kernel is positive semi-definite.

## iii. Table of contents

- A. The inverse norm as a superposition of Gaussians
- B. The inverse-norm kernel is positive semi-definite

## iv. References

- None.
-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.NewtonianPotential

open MeasureTheory Space Physlib Distribution Set
open scoped SchwartzMap

/-!

## A. The inverse norm as a superposition of Gaussians

-/

/-- The inverse norm as a superposition of Gaussians:
`∫₀^∞ s^(-1/2) exp (-s ‖z‖²) ds = √π / ‖z‖` for `z ≠ 0`. -/
lemma integral_rpow_mul_exp_neg_mul_norm_sq {E : Type*} [NormedAddCommGroup E] {z : E}
    (hz : z ≠ 0) :
    ∫ s in Ioi (0 : ℝ), s ^ (-(1 / 2 : ℝ)) * Real.exp (-(s * ‖z‖ ^ 2)) =
      Real.sqrt Real.pi * ‖z‖⁻¹ := by
  have hr : 0 < ‖z‖ ^ 2 := by positivity
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1 / 2) (r := ‖z‖ ^ 2) (by norm_num) hr
  rw [Real.Gamma_one_half_eq] at h
  have e1 : (1 / ‖z‖ ^ 2) ^ (1 / 2 : ℝ) = ‖z‖⁻¹ := by
    rw [one_div, ← Real.sqrt_eq_rpow, Real.sqrt_inv, Real.sqrt_sq (norm_nonneg z)]
  rw [e1] at h
  rw [mul_comm, ← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  congr 2
  · norm_num
  · ring

/-!

## B. The inverse-norm kernel is positive semi-definite

-/

/-- The diagonal of `Space 3 × Space 3` is a null set. -/
lemma ae_prod_fst_ne_snd :
    ∀ᵐ p : Space 3 × Space 3 ∂((volume : Measure (Space 3)).prod volume), p.1 ≠ p.2 := by
  have hm : MeasurableSet {p : Space 3 × Space 3 | p.1 ≠ p.2} :=
    (measurableSet_eq_fun measurable_fst measurable_snd).compl
  refine (Measure.ae_prod_iff_ae_ae hm).2 (Filter.Eventually.of_forall fun x => ae_iff.2 ?_)
  simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton']
  exact measure_singleton x

/-- The bilinear form of the inverse-norm kernel as a superposition of Gaussian bilinear
forms. -/
lemma sqrt_pi_mul_integral_mul_mul_inv_norm_sub (ρ₁ ρ₂ : 𝓢(Space 3, ℝ)) :
    Real.sqrt Real.pi * ∫ p : Space 3 × Space 3, ρ₁ p.1 * ρ₂ p.2 * ‖p.1 - p.2‖⁻¹ =
      ∫ s in Ioi (0 : ℝ), s ^ (-(1 / 2 : ℝ)) *
        ∫ p : Space 3 × Space 3, ρ₁ p.1 * ρ₂ p.2 * Real.exp (-(s * ‖p.1 - p.2‖ ^ 2)) := by
  let H : Space 3 × Space 3 → ℝ → ℝ := fun p s =>
    ρ₁ p.1 * ρ₂ p.2 * (s ^ (-(1 / 2 : ℝ)) * Real.exp (-(s * ‖p.1 - p.2‖ ^ 2)))
  have hHm : Measurable (Function.uncurry H) := by
    simp only [H]
    fun_prop
  have hinner : ∀ p : Space 3 × Space 3, p.1 ≠ p.2 →
      ∫ s in Ioi (0 : ℝ), s ^ (-(1 / 2 : ℝ)) * Real.exp (-(s * ‖p.1 - p.2‖ ^ 2)) =
        Real.sqrt Real.pi * ‖p.1 - p.2‖⁻¹ :=
    fun p hp => integral_rpow_mul_exp_neg_mul_norm_sq (sub_ne_zero.2 hp)
  have hinnerInt : ∀ p : Space 3 × Space 3, p.1 ≠ p.2 →
      IntegrableOn (fun s : ℝ => s ^ (-(1 / 2 : ℝ)) * Real.exp (-(s * ‖p.1 - p.2‖ ^ 2)))
        (Ioi 0) := by
    intro p hp
    have hz : 0 < ‖p.1 - p.2‖ ^ 2 := by
      have := sub_ne_zero.2 hp
      positivity
    refine (integrableOn_rpow_mul_exp_neg_mul_rpow (s := -(1 / 2)) (p := 1) (by norm_num)
      one_pos hz).congr_fun (fun s _ => ?_) measurableSet_Ioi
    simp only [Real.rpow_one, neg_mul, mul_comm (‖p.1 - p.2‖ ^ 2)]
  have hHint : Integrable (Function.uncurry H)
      (((volume : Measure (Space 3)).prod volume).prod (volume.restrict (Ioi 0))) := by
    rw [integrable_prod_iff hHm.aestronglyMeasurable]
    constructor
    · filter_upwards [ae_prod_fst_ne_snd] with p hp
      exact (hinnerInt p hp).const_mul (ρ₁ p.1 * ρ₂ p.2)
    · have hbase := ((integrable_prod_mul_mul_inv_norm_sub ρ₁ ρ₂).norm).const_mul
        (Real.sqrt Real.pi)
      refine hbase.congr ?_
      filter_upwards [ae_prod_fst_ne_snd] with p hp
      have hn : ∀ s ∈ Ioi (0 : ℝ), ‖H p s‖ =
          |ρ₁ p.1 * ρ₂ p.2| * (s ^ (-(1 / 2 : ℝ)) * Real.exp (-(s * ‖p.1 - p.2‖ ^ 2))) := by
        intro s hs
        simp [H, abs_mul, abs_of_nonneg (Real.rpow_nonneg (le_of_lt hs) _)]
      change _ = ∫ s in Ioi (0 : ℝ), ‖H p s‖
      rw [setIntegral_congr_fun measurableSet_Ioi hn, integral_const_mul, hinner p hp]
      simp only [Real.norm_eq_abs, abs_mul, abs_inv, abs_norm]
      ring
  have hsw : ∫ p, ∫ s in Ioi (0 : ℝ), H p s = ∫ s in Ioi (0 : ℝ), ∫ p, H p s :=
    integral_integral_swap hHint
  have hL : ∫ p, ∫ s in Ioi (0 : ℝ), H p s =
      Real.sqrt Real.pi * ∫ p : Space 3 × Space 3, ρ₁ p.1 * ρ₂ p.2 * ‖p.1 - p.2‖⁻¹ := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_prod_fst_ne_snd] with p hp
    simp only [H, integral_const_mul, hinner p hp]
    ring
  rw [← hL, hsw]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  simp only [H]
  rw [← integral_const_mul]
  congr 1 with p
  ring

/-- The inverse-norm kernel is positive semi-definite on Schwartz maps:
`0 ≤ ∫∫ ρ(x) ρ(y) / ‖x - y‖ dx dy`. -/
lemma integral_mul_mul_inv_norm_sub_nonneg (ρ : 𝓢(Space 3, ℝ)) :
    0 ≤ ∫ p : Space 3 × Space 3, ρ p.1 * ρ p.2 * ‖p.1 - p.2‖⁻¹ := by
  have h := sqrt_pi_mul_integral_mul_mul_inv_norm_sub ρ ρ
  have hR : 0 ≤ ∫ s in Ioi (0 : ℝ), s ^ (-(1 / 2 : ℝ)) *
      ∫ p : Space 3 × Space 3, ρ p.1 * ρ p.2 * Real.exp (-(s * ‖p.1 - p.2‖ ^ 2)) :=
    setIntegral_nonneg measurableSet_Ioi fun s hs =>
      mul_nonneg (Real.rpow_nonneg (le_of_lt hs) _) (integral_mul_mul_exp_nonneg ρ hs)
  rw [← h] at hR
  exact nonneg_of_mul_nonneg_right hR (Real.sqrt_pos.2 Real.pi_pos)

end PhyslibAlpha.NewtonianPotential
