/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.WaveEquation.Kirchhoff.Phase
public import PhyslibAlpha.Mathematics.Geometry.Sphere.Fourier
/-!
# Fourier transform and integrability of spherical means

The spherical mean of a Schwartz function has the transform of the sphere measure times that of
the function.

## i. Overview

The Fourier integral of a spherical mean is the transform of the sphere measure times that of
the function. Spherical means are integrable and square integrable.

## ii. Key results

* `sphericalIntegral_fourier`: the Fourier integral of a spherical mean.
* `integrable_sphericalIntegral`, `memLp_two_sphericalIntegral`: integrability of spherical means.

## iii. Table of contents

- A. The Fourier transform of a spherical mean
- B. Integrability of the spherical mean

## iv. References

* None.
-/

@[expose] public section

namespace WaveEquation.Kirchhoff

open MeasureTheory Sphere3
open scoped Pointwise FourierTransform SchwartzMap

/-! ## A. The Fourier transform of a spherical mean -/

lemma translate_complex (f : Space 3 → ℂ) (v ξ : Space 3) :
    ∫ x : Space 3, phase (inner ℝ x ξ) * f (x + v) =
      (phase (inner ℝ v ξ))⁻¹ * ∫ x : Space 3, phase (inner ℝ x ξ) * f x := by
  have h := integral_add_right_eq_self (μ := (volume : Measure (Space 3)))
    (fun x : Space 3 => phase (inner ℝ (x - v) ξ) * f x) v
  simp only [add_sub_cancel_right] at h
  rw [h, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [inner_sub_left]
  have hp : phase (inner ℝ x ξ - inner ℝ v ξ) = (phase (inner ℝ v ξ))⁻¹ * phase (inner ℝ x ξ) := by
    unfold phase
    rw [← Complex.exp_neg, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hp, mul_assoc]

lemma sphericalIntegral_fourier_integral (f : 𝓢(Space 3, ℂ)) (r : ℝ) (ξ : Space 3) :
    ∫ x : Space 3, phase (inner ℝ x ξ) * sphericalIntegral r f x =
      (∫ n : Sph, (phase (inner ℝ (r • n.1) ξ))⁻¹ ∂sphereMeasure) *
        ∫ x : Space 3, phase (inner ℝ x ξ) * f x := by
  have hint : Integrable (Function.uncurry fun (x : Space 3) (n : Sph) =>
      phase (inner ℝ x ξ) * f (x + r • n.1)) (volume.prod sphereMeasure) := by
    have hcont : Continuous (Function.uncurry fun (x : Space 3) (n : Sph) =>
        phase (inner ℝ x ξ) * f (x + r • n.1)) := by
      have h1 : Continuous fun p : Space 3 × Sph => inner ℝ p.1 ξ :=
        continuous_fst.inner continuous_const
      exact (continuous_phase.comp h1).mul
        (f.continuous.comp (continuous_fst.add
          ((continuous_const : Continuous fun _ : Space 3 × Sph => r).smul
            (continuous_subtype_val.comp continuous_snd))))
    have hnorm : ∀ (x : Space 3) (n : Sph),
        ‖phase (inner ℝ x ξ) * f (x + r • n.1)‖ = ‖f (x + r • n.1)‖ := fun x n => by
      rw [norm_mul, norm_phase, one_mul]
    rw [integrable_prod_iff' hcont.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun n => ?_, ?_⟩
    · refine Integrable.mono' ((f.integrable.comp_add_right (r • n.1)).norm)
        (hcont.comp (Continuous.prodMk_left n)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => ?_)
      show ‖phase (inner ℝ x ξ) * f (x + r • n.1)‖ ≤ ‖f (x + r • n.1)‖
      rw [hnorm]
    · have : (fun n : Sph => ∫ x : Space 3, ‖phase (inner ℝ x ξ) * f (x + r • n.1)‖) =
          fun _ => ∫ x : Space 3, ‖f x‖ := by
        funext n
        simp_rw [hnorm]
        exact integral_add_right_eq_self (fun x : Space 3 => ‖f x‖) (r • n.1)
      simp only [Function.uncurry_apply_pair]
      rw [this]
      exact integrable_const _
  have step1 : ∫ x : Space 3, phase (inner ℝ x ξ) * sphericalIntegral r f x =
      ∫ x : Space 3, ∫ n : Sph, phase (inner ℝ x ξ) * f (x + r • n.1) ∂sphereMeasure := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show phase (inner ℝ x ξ) * (∫ n : Sph, f (x + r • n.1) ∂sphereMeasure) =
      ∫ n : Sph, phase (inner ℝ x ξ) * f (x + r • n.1) ∂sphereMeasure
    exact (integral_const_mul _ _).symm
  rw [step1, integral_integral_swap hint]
  simp_rw [translate_complex]
  rw [integral_mul_const]

/-- **Fourier multiplier of the spherical mean.** For `ξ ≠ 0` and `r > 0`, the Fourier integral of
the unnormalized spherical mean is `4π sin(2π r |ξ|) / (2π r |ξ|)` times that of `f`. -/
lemma sphericalIntegral_fourier (f : 𝓢(Space 3, ℂ)) {r : ℝ} (hr : 0 < r)
    {ξ : Space 3} (hξ : ξ ≠ 0) :
    ∫ x : Space 3, phase (inner ℝ x ξ) * sphericalIntegral r f x =
      ((4 * Real.pi * Real.sin (2 * Real.pi * r * ‖ξ‖) / (2 * Real.pi * r * ‖ξ‖) : ℝ) : ℂ) *
        ∫ x : Space 3, phase (inner ℝ x ξ) * f x := by
  rw [sphericalIntegral_fourier_integral]
  congr 1
  have hR : 0 < 2 * Real.pi * r := by positivity
  have h := sphere_fourier ξ hξ hR
  have hinv : ∀ n : Sph, (phase (inner ℝ (r • n.1) ξ))⁻¹ =
      Complex.exp (Complex.I * ((2 * Real.pi * r * inner ℝ ξ n.1 : ℝ) : ℂ)) := by
    intro n
    unfold phase
    rw [← Complex.exp_neg, neg_neg]
    congr 1
    rw [real_inner_smul_left, real_inner_comm]
    push_cast
    ring
  simp_rw [hinv]
  rw [h]

/-! ## B. Integrability of the spherical mean -/

lemma integrable_translate_prod (f : 𝓢(Space 3, ℂ)) (r : ℝ) :
    Integrable (Function.uncurry fun (x : Space 3) (n : Sph) => f (x + r • n.1))
      (volume.prod sphereMeasure) := by
  have hcont : Continuous (Function.uncurry fun (x : Space 3) (n : Sph) => f (x + r • n.1)) :=
    f.continuous.comp (continuous_fst.add
      ((continuous_const : Continuous fun _ : Space 3 × Sph => r).smul
        (continuous_subtype_val.comp continuous_snd)))
  rw [integrable_prod_iff' hcont.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun n => ?_, ?_⟩
  · exact f.integrable.comp_add_right (r • n.1)
  · have : (fun n : Sph => ∫ x : Space 3, ‖f (x + r • n.1)‖) = fun _ => ∫ x : Space 3, ‖f x‖ := by
      funext n
      exact integral_add_right_eq_self (fun x : Space 3 => ‖f x‖) (r • n.1)
    simp only [Function.uncurry_apply_pair]
    rw [this]
    exact integrable_const _

/-- The spherical mean of a Schwartz function is integrable. -/
lemma integrable_sphericalIntegral (f : 𝓢(Space 3, ℂ)) (r : ℝ) :
    Integrable (sphericalIntegral r f) volume :=
  (integrable_translate_prod f r).integral_prod_left

lemma sphericalIntegral_bound (f : 𝓢(Space 3, ℂ)) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖sphericalIntegral r f x‖ ≤ C := by
  set B := ‖f.toBoundedContinuousFunction‖ with hB
  refine ⟨B * sphereMeasure.real Set.univ,
    mul_nonneg (norm_nonneg _) measureReal_nonneg, fun x => ?_⟩
  unfold sphericalIntegral
  refine (norm_integral_le_of_norm_le_const (C := B)
    (Filter.Eventually.of_forall fun n => ?_)).trans
    le_rfl
  exact (f.toBoundedContinuousFunction.norm_coe_le_norm _)

/-- The spherical mean of a Schwartz function is square integrable. -/
lemma memLp_two_sphericalIntegral (f : 𝓢(Space 3, ℂ)) (r : ℝ) :
    MemLp (sphericalIntegral r f) 2 volume := by
  obtain ⟨C, hC0, hC⟩ := sphericalIntegral_bound f r
  have hint := integrable_sphericalIntegral f r
  refine (memLp_two_iff_integrable_sq_norm hint.aestronglyMeasurable).mpr ?_
  refine Integrable.mono' (g := fun x => C * ‖sphericalIntegral r f x‖) (hint.norm.const_mul C)
    (hint.aestronglyMeasurable.norm.pow 2) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _), sq]
  exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

end WaveEquation.Kirchhoff
