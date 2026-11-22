/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import Physlib.SpaceAndTime.Space.Norm.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# The Gaussian kernel on `Space 3` is positive semi-definite

## i. Overview

For a Schwartz map `ρ` on `Space 3` and `s > 0` the quadratic form of the Gaussian kernel is
nonnegative: `0 ≤ ∫∫ ρ(x) ρ(y) exp (-s ‖x - y‖²) dx dy`. The proof writes the Gaussian kernel
as a convolution square, which turns the quadratic form into the integral of a square.

## ii. Key results

- `integral_exp_mul_exp_eq_of_pos` : the convolution of two Gaussians is a Gaussian.
- `integral_exp_mul_exp_eq` : the Gaussian kernel is a convolution square.
- `integral_mul_mul_exp_nonneg` : the Gaussian kernel is positive semi-definite.

## iii. Table of contents

- A. The Gaussian kernel as a convolution square
- B. Positivity of the Gaussian quadratic form

## iv. References

- None.
-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.NewtonianPotential

open MeasureTheory Space Physlib Distribution Set
open scoped SchwartzMap

/-!

## A. The Gaussian kernel as a convolution square

-/

/-- The convolution of two Gaussians is a Gaussian:
`∫ exp (-α ‖x - w‖²) exp (-β ‖w - y‖²) dw = (π / (α + β))^(3/2) exp (-αβ/(α + β) ‖x - y‖²)`. -/
lemma integral_exp_mul_exp_eq_of_pos {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (x y : Space 3) :
    ∫ w : Space 3, Real.exp (-(α * ‖x - w‖ ^ 2)) * Real.exp (-(β * ‖w - y‖ ^ 2)) =
      (Real.pi / (α + β)) ^ (3 / 2 : ℝ) * Real.exp (-(α * β / (α + β) * ‖x - y‖ ^ 2)) := by
  have hαβ : 0 < α + β := by positivity
  set m : Space 3 := (α / (α + β)) • x + (β / (α + β)) • y with hm
  have key : ∀ w : Space 3, Real.exp (-(α * ‖x - w‖ ^ 2)) * Real.exp (-(β * ‖w - y‖ ^ 2)) =
      Real.exp (-(α + β) * ‖w - m‖ ^ 2) * Real.exp (-(α * β / (α + β) * ‖x - y‖ ^ 2)) := by
    intro w
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    have h1 : x - w = (β / (α + β)) • (x - y) - (w - m) := by
      rw [hm]
      match_scalars <;> field_simp <;> ring
    have h2 : w - y = (α / (α + β)) • (x - y) + (w - m) := by
      rw [hm]
      match_scalars <;> field_simp <;> ring
    rw [h1, h2, norm_sub_sq_real, norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left,
      real_inner_smul_left]
    simp only [Real.norm_eq_abs, abs_of_pos (div_pos hβ hαβ), abs_of_pos (div_pos hα hαβ)]
    field_simp
    ring
  simp_rw [key]
  rw [integral_mul_const]
  congr 1
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := Space 3) (b := α + β) hαβ
  rw [Space.finrank_eq_dim] at h
  rw [← integral_sub_right_eq_self (fun w : Space 3 => Real.exp (-(α + β) * ‖w‖ ^ 2)) m] at h
  rw [h]
  norm_num

/-- The Gaussian kernel is a convolution square:
`∫ exp (-2s ‖x - w‖²) exp (-2s ‖w - y‖²) dw = (π / (4s))^(3/2) exp (-s ‖x - y‖²)`. -/
lemma integral_exp_mul_exp_eq (s : ℝ) (hs : 0 < s) (x y : Space 3) :
    ∫ w : Space 3, Real.exp (-(2 * s * ‖x - w‖ ^ 2)) * Real.exp (-(2 * s * ‖w - y‖ ^ 2)) =
      (Real.pi / (4 * s)) ^ (3 / 2 : ℝ) * Real.exp (-(s * ‖x - y‖ ^ 2)) := by
  have h := integral_exp_mul_exp_eq_of_pos (α := 2 * s) (β := 2 * s) (by positivity)
    (by positivity) x y
  rw [h]
  congr 3
  · ring
  · field_simp
    ring

/-!

## B. Positivity of the Gaussian quadratic form

-/

/-- A Gaussian is integrable on `Space 3`. -/
lemma integrable_exp_neg_mul_norm_sq {b : ℝ} (hb : 0 < b) :
    Integrable (fun w : Space 3 => Real.exp (-b * ‖w‖ ^ 2)) := by
  by_contra h
  have h1 := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := Space 3) hb
  rw [integral_undef h] at h1
  have : (0 : ℝ) < (Real.pi / b) ^ (Module.finrank ℝ (Space 3) / 2 : ℝ) := by positivity
  linarith

/-- The Gaussian kernel is positive semi-definite on Schwartz maps:
`0 ≤ ∫∫ ρ(x) ρ(y) exp (-s ‖x - y‖²) dx dy` for `s > 0`. -/
lemma integral_mul_mul_exp_nonneg (ρ : 𝓢(Space 3, ℝ)) {s : ℝ} (hs : 0 < s) :
    0 ≤ ∫ p : Space 3 × Space 3, ρ p.1 * ρ p.2 * Real.exp (-(s * ‖p.1 - p.2‖ ^ 2)) := by
  set c : ℝ := (Real.pi / (4 * s)) ^ (3 / 2 : ℝ) with hc
  have hcpos : 0 < c := by positivity
  let E : Space 3 → Space 3 → ℝ := fun x w => Real.exp (-(2 * s * ‖x - w‖ ^ 2))
  have hE : ∀ x y : Space 3, Real.exp (-(s * ‖x - y‖ ^ 2)) = c⁻¹ * ∫ w, E x w * E w y := by
    intro x y
    have := integral_exp_mul_exp_eq s hs x y
    simp only [E]
    rw [this, ← hc, inv_mul_cancel_left₀ hcpos.ne']
  let G : Space 3 × Space 3 → Space 3 → ℝ := fun p w => (ρ p.1 * E p.1 w) * (ρ p.2 * E w p.2)
  have hρm : Measurable ρ := ρ.continuous.measurable
  have hGint : Integrable (Function.uncurry G) ((volume.prod volume).prod volume) := by
    have hk : Integrable (fun w : Space 3 => Real.exp (-(2 * s) * ‖w‖ ^ 2)) :=
      integrable_exp_neg_mul_norm_sq (by positivity)
    have hf : Integrable (fun p : Space 3 × Space 3 => |ρ p.1| * |ρ p.2|) (volume.prod volume) :=
      Integrable.mul_prod ρ.integrable.norm ρ.integrable.norm
    have hmeasG : Measurable (Function.uncurry G) := by
      simp only [G, E]
      fun_prop
    refine Integrable.mono' (g := fun q : (Space 3 × Space 3) × Space 3 =>
      |ρ q.1.1| * |ρ q.1.2| * Real.exp (-(2 * s) * ‖q.2 - q.1.1‖ ^ 2)) ?_
      hmeasG.aestronglyMeasurable (Filter.Eventually.of_forall fun q => ?_)
    · rw [integrable_prod_iff (by fun_prop)]
      refine ⟨Filter.Eventually.of_forall fun p => by
        simpa using (hk.comp_sub_right p.1).const_mul (|ρ p.1| * |ρ p.2|), ?_⟩
      have : (fun p : Space 3 × Space 3 =>
          ∫ w, ‖|ρ p.1| * |ρ p.2| * Real.exp (-(2 * s) * ‖w - p.1‖ ^ 2)‖) =
          fun p => (|ρ p.1| * |ρ p.2|) * ∫ w : Space 3, Real.exp (-(2 * s) * ‖w‖ ^ 2) := by
        funext p
        simp only [norm_mul, Real.norm_eq_abs, abs_abs, Real.abs_exp]
        rw [integral_const_mul,
          integral_sub_right_eq_self (fun w : Space 3 => Real.exp (-(2 * s) * ‖w‖ ^ 2)) p.1]
      rw [this]
      exact hf.mul_const _
    · simp only [Function.uncurry, G, E, Real.norm_eq_abs, abs_mul, Real.abs_exp]
      have hB : Real.exp (-(2 * s * ‖q.2 - q.1.2‖ ^ 2)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖q.2 - q.1.2‖])
      rw [norm_sub_rev q.1.1 q.2,
        show -(2 * s * ‖q.2 - q.1.1‖ ^ 2) = -(2 * s) * ‖q.2 - q.1.1‖ ^ 2 by ring]
      calc |ρ q.1.1| * Real.exp (-(2 * s) * ‖q.2 - q.1.1‖ ^ 2) *
            (|ρ q.1.2| * Real.exp (-(2 * s * ‖q.2 - q.1.2‖ ^ 2)))
          = |ρ q.1.1| * |ρ q.1.2| * Real.exp (-(2 * s) * ‖q.2 - q.1.1‖ ^ 2) *
            Real.exp (-(2 * s * ‖q.2 - q.1.2‖ ^ 2)) := by ring
        _ ≤ |ρ q.1.1| * |ρ q.1.2| * Real.exp (-(2 * s) * ‖q.2 - q.1.1‖ ^ 2) * 1 := by gcongr
        _ = _ := by ring
  have h1 : ∫ p : Space 3 × Space 3, ρ p.1 * ρ p.2 * Real.exp (-(s * ‖p.1 - p.2‖ ^ 2)) =
      c⁻¹ * ∫ w, ∫ p, G p w := by
    have hsw : ∫ p, ∫ w, G p w = ∫ w, ∫ p, G p w := integral_integral_swap hGint
    rw [← hsw, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    have hp : ∫ w, G p w = ρ p.1 * ρ p.2 * ∫ w, E p.1 w * E w p.2 := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
      simp only [G]
      ring
    simp only
    rw [hp, hE]
    ring
  have h2 : ∀ w : Space 3, ∫ p, G p w = (∫ x, ρ x * E x w) ^ 2 := by
    intro w
    have h := integral_prod_mul (μ := (volume : Measure (Space 3)))
      (ν := (volume : Measure (Space 3))) (fun x => ρ x * E x w) (fun y => ρ y * E w y)
    rw [sq]
    rw [show (∫ y, ρ y * E y w) = ∫ y, ρ y * E w y from by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [E]
      rw [norm_sub_rev]] at *
    exact h
  rw [h1]
  simp_rw [h2]
  exact mul_nonneg (inv_nonneg.2 hcpos.le) (integral_nonneg fun w => sq_nonneg _)

end PhyslibAlpha.NewtonianPotential
