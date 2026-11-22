/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.ClassicalMechanics.NewtonianPotential.GaussianKernel
public import Physlib.Mathematics.InnerProductSpace.Gaussian

/-!
# The Gaussian mass density

## i. Overview

The Gaussian mass density of total mass `m` and width `σ` centred at `a` is
`ρ(x) = m (2πσ²)^(-3/2) exp (-‖x - a‖² / (2σ²))`. This module defines it as a Schwartz map on
`Space 3` and computes the bilinear form of the Gaussian kernel `exp (-s ‖x - y‖²)` on two such
densities, which is again a Gaussian in the distance of the two centres.

## ii. Key results

- `gaussianDensity` : the Gaussian mass density as a Schwartz map.
- `integral_gaussianDensity` : the Gaussian mass density has total mass `m`.
- `integral_prod_exp_mul_exp_mul_exp` : the Gaussian bilinear form of two Gaussians.
- `integral_gaussianDensity_mul_gaussianDensity_mul_exp` : the Gaussian bilinear form of two
  Gaussian densities.

## iii. Table of contents

- A. The Gaussian mass density
- B. The Gaussian bilinear form of two Gaussians
- C. The Gaussian bilinear form of two Gaussian densities

## iv. References

- None.
-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.NewtonianPotential

open MeasureTheory Space Physlib Distribution Set
open scoped SchwartzMap

/-!

## A. The Gaussian mass density

-/

/-- The Gaussian mass density of total mass `m` and width `σ` centred at `a`. -/
def gaussianDensity (m : ℝ) {σ : ℝ} (hσ : 0 < σ) (a : Space 3) : 𝓢(Space 3, ℝ) :=
  (m * (1 / (2 * Real.pi * σ ^ 2)) ^ (3 / 2 : ℝ)) •
    InnerProductSpace.gaussian ℝ
      (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := Space 3) (Units.mk0 σ hσ.ne')) a

/-- The Gaussian mass density evaluated at a point. -/
lemma gaussianDensity_apply (m : ℝ) {σ : ℝ} (hσ : 0 < σ) (a x : Space 3) :
    gaussianDensity m hσ a x = m * (1 / (2 * Real.pi * σ ^ 2)) ^ (3 / 2 : ℝ) *
      Real.exp (-(1 / (2 * σ ^ 2) * ‖x - a‖ ^ 2)) := by
  have h : (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := Space 3) (Units.mk0 σ hσ.ne')).symm
      (x - a) = σ⁻¹ • (x - a) := by
    rfl
  simp only [gaussianDensity, _root_.smul_apply, InnerProductSpace.gaussian_apply, smul_eq_mul,
    RCLike.ofReal_real_eq_id, id]
  rw [h, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hσ)]
  congr 2
  field_simp

/-- The Gaussian mass density has total mass `m`. -/
lemma integral_gaussianDensity (m : ℝ) {σ : ℝ} (hσ : 0 < σ) (a : Space 3) :
    ∫ x, gaussianDensity m hσ a x = m := by
  have hpi := Real.pi_pos
  have h3 : 1 / (2 * Real.pi * σ ^ 2) * (2 * Real.pi * σ ^ 2) = 1 := by
    field_simp
  simp only [gaussianDensity, _root_.smul_apply, smul_eq_mul]
  rw [integral_const_mul, InnerProductSpace.integral_gaussian_smulLeft, Space.finrank_eq_dim]
  simp only [Nat.cast_ofNat]
  rw [mul_assoc, ← Real.mul_rpow (by positivity) (by positivity), h3, Real.one_rpow, mul_one]

/-!

## B. The Gaussian bilinear form of two Gaussians

-/

/-- A shifted Gaussian is integrable on `Space 3`. -/
lemma integrable_exp_neg_mul_norm_sub_sq {b : ℝ} (hb : 0 < b) (a : Space 3) :
    Integrable (fun w : Space 3 => Real.exp (-(b * ‖w - a‖ ^ 2))) := by
  simpa [neg_mul] using (integrable_exp_neg_mul_norm_sq hb).comp_sub_right a

/-- The Gaussian bilinear form of two Gaussians centred at `a` and `b` is again a Gaussian in
`a - b`. -/
lemma integral_prod_exp_mul_exp_mul_exp {β₁ β₂ s : ℝ} (h₁ : 0 < β₁) (h₂ : 0 < β₂) (hs : 0 < s)
    (a b : Space 3) :
    ∫ p : Space 3 × Space 3, Real.exp (-(β₁ * ‖p.1 - a‖ ^ 2)) *
        Real.exp (-(β₂ * ‖p.2 - b‖ ^ 2)) * Real.exp (-(s * ‖p.1 - p.2‖ ^ 2)) =
      (Real.pi / (s + β₂)) ^ (3 / 2 : ℝ) * (Real.pi / (β₁ + s * β₂ / (s + β₂))) ^ (3 / 2 : ℝ) *
        Real.exp (-(β₁ * (s * β₂ / (s + β₂)) / (β₁ + s * β₂ / (s + β₂)) * ‖a - b‖ ^ 2)) := by
  have hγ : 0 < s * β₂ / (s + β₂) := by positivity
  have hint : Integrable (fun p : Space 3 × Space 3 => Real.exp (-(β₁ * ‖p.1 - a‖ ^ 2)) *
      Real.exp (-(β₂ * ‖p.2 - b‖ ^ 2)) * Real.exp (-(s * ‖p.1 - p.2‖ ^ 2)))
      ((volume : Measure (Space 3)).prod volume) := by
    refine Integrable.mono' (Integrable.mul_prod (integrable_exp_neg_mul_norm_sub_sq h₁ a)
      (integrable_exp_neg_mul_norm_sub_sq h₂ b)) (by fun_prop)
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_of_le_one_right (by positivity)
      (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖p.1 - p.2‖]))
  refine (integral_prod _ hint).trans ?_
  have hinner : ∀ x : Space 3, ∫ y : Space 3, Real.exp (-(β₁ * ‖x - a‖ ^ 2)) *
      Real.exp (-(β₂ * ‖y - b‖ ^ 2)) * Real.exp (-(s * ‖x - y‖ ^ 2)) =
      (Real.pi / (s + β₂)) ^ (3 / 2 : ℝ) * (Real.exp (-(β₁ * ‖a - x‖ ^ 2)) *
        Real.exp (-(s * β₂ / (s + β₂) * ‖x - b‖ ^ 2))) := by
    intro x
    have e := integral_exp_mul_exp_eq_of_pos (d := 3) hs h₂ x b
    simp only [Nat.cast_ofNat] at e
    have e1 : ∫ y : Space 3, Real.exp (-(β₁ * ‖x - a‖ ^ 2)) *
        Real.exp (-(β₂ * ‖y - b‖ ^ 2)) * Real.exp (-(s * ‖x - y‖ ^ 2)) =
        Real.exp (-(β₁ * ‖x - a‖ ^ 2)) *
          ∫ y : Space 3, Real.exp (-(s * ‖x - y‖ ^ 2)) * Real.exp (-(β₂ * ‖y - b‖ ^ 2)) := by
      rw [← integral_const_mul]
      congr 1 with y
      ring
    rw [e1, e, norm_sub_rev a x]
    ring
  have e2 := integral_exp_mul_exp_eq_of_pos (d := 3) h₁ hγ a b
  simp only [Nat.cast_ofNat] at e2
  simp_rw [hinner]
  rw [integral_const_mul, e2]
  ring

/-!

## C. The Gaussian bilinear form of two Gaussian densities

-/

/-- The Gaussian bilinear form of two Gaussian densities. -/
lemma integral_gaussianDensity_mul_gaussianDensity_mul_exp (m₁ m₂ : ℝ) {σ₁ σ₂ : ℝ}
    (h₁ : 0 < σ₁) (h₂ : 0 < σ₂) (a b : Space 3) {s : ℝ} (hs : 0 < s) :
    ∫ p : Space 3 × Space 3, gaussianDensity m₁ h₁ a p.1 * gaussianDensity m₂ h₂ b p.2 *
        Real.exp (-(s * ‖p.1 - p.2‖ ^ 2)) =
      m₁ * m₂ * (1 / (1 + 2 * (σ₁ ^ 2 + σ₂ ^ 2) * s)) ^ (3 / 2 : ℝ) *
        Real.exp (-(s / (1 + 2 * (σ₁ ^ 2 + σ₂ ^ 2) * s) * ‖a - b‖ ^ 2)) := by
  set β₁ := 1 / (2 * σ₁ ^ 2) with hβ₁
  set β₂ := 1 / (2 * σ₂ ^ 2) with hβ₂
  have hb₁ : 0 < β₁ := by positivity
  have hb₂ : 0 < β₂ := by positivity
  have hpi := Real.pi_pos
  have hL := integral_prod_exp_mul_exp_mul_exp hb₁ hb₂ hs a b
  have e : ∀ p : Space 3 × Space 3, gaussianDensity m₁ h₁ a p.1 * gaussianDensity m₂ h₂ b p.2 *
      Real.exp (-(s * ‖p.1 - p.2‖ ^ 2)) =
      (m₁ * (1 / (2 * Real.pi * σ₁ ^ 2)) ^ (3 / 2 : ℝ) *
        (m₂ * (1 / (2 * Real.pi * σ₂ ^ 2)) ^ (3 / 2 : ℝ))) *
        (Real.exp (-(β₁ * ‖p.1 - a‖ ^ 2)) * Real.exp (-(β₂ * ‖p.2 - b‖ ^ 2)) *
          Real.exp (-(s * ‖p.1 - p.2‖ ^ 2))) := by
    intro p
    rw [gaussianDensity_apply, gaussianDensity_apply]
    ring
  simp_rw [e]
  rw [integral_const_mul, hL]
  have c1 : (1 / (2 * Real.pi * σ₁ ^ 2)) ^ (3 / 2 : ℝ) *
      (1 / (2 * Real.pi * σ₂ ^ 2)) ^ (3 / 2 : ℝ) *
      ((Real.pi / (s + β₂)) ^ (3 / 2 : ℝ) * (Real.pi / (β₁ + s * β₂ / (s + β₂))) ^ (3 / 2 : ℝ)) =
      (1 / (1 + 2 * (σ₁ ^ 2 + σ₂ ^ 2) * s)) ^ (3 / 2 : ℝ) := by
    rw [← Real.mul_rpow (by positivity) (by positivity),
      ← Real.mul_rpow (by positivity) (by positivity),
      ← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    rw [hβ₁, hβ₂]
    field_simp
    ring
  have c2 : β₁ * (s * β₂ / (s + β₂)) / (β₁ + s * β₂ / (s + β₂)) =
      s / (1 + 2 * (σ₁ ^ 2 + σ₂ ^ 2) * s) := by
    rw [hβ₁, hβ₂]
    field_simp
    ring
  rw [c2, ← c1]
  ring

end PhyslibAlpha.NewtonianPotential
