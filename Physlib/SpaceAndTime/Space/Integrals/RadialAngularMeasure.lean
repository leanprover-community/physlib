/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Mathematics.ForMathlib.Integration.Basic
public import Physlib.SpaceAndTime.Space.Integrals.Basic
/-!

# The radial angular measure on Space

## i. Overview

The normal measure on `Space d` is `r^(d-1) dr dΩ` in spherical coordinates,
where `dΩ` is the angular measure on the unit sphere. The radial angular measure
is the measure `dr dΩ`, cancelling the radius contribution from the measure in spherical
coordinates.

This file is equivalent to `invPowMeasure`, which will slowly be deprecated.

## ii. Key results

- `radialAngularMeasure`: The radial angular measure on `Space d`.

## iii. Table of contents

- A. The definition of the radial angular measure
  - A.1. Basic equalities
- B. Integrals with respect to radialAngularMeasure
- C. The radialAngularMeasure on balls
- D. Integrability conditions
- E. HasTemperateGrowth of measures
  - E.1. Integrability of powers
  - E.2. radialAngularMeasure has temperate growth

## iv. References

* None.
-/

@[expose] public section

open NNReal Real
noncomputable section

variable (𝕜 : Type) {E F F' : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup F']

variable [NormedSpace ℝ E] [NormedSpace ℝ F]

namespace Space

open MeasureTheory

/-!

## A. The definition of the radial angular measure

-/

/-- The measure on `Space d` weighted by `1 / ‖x‖ ^ (d - 1)`. -/
def radialAngularMeasure {d : ℕ} : Measure (Space d) :=
  volume.withDensity (fun x : Space d => ENNReal.ofReal (1 / ‖x‖ ^ (d - 1)))

/-!

### A.1. Basic equalities

-/

lemma radialAngularMeasure_eq_volume_withDensity {d : ℕ} : radialAngularMeasure =
    volume.withDensity (fun x : Space d => ENNReal.ofReal (1 / ‖x‖ ^ (d - 1))) := by
  rfl

@[simp]
lemma radialAngularMeasure_zero_eq_volume :
    radialAngularMeasure (d := 0) = volume := by
  simp [radialAngularMeasure]

/-!

### A.2. SFinite property

-/

instance (d : ℕ) : SFinite (radialAngularMeasure (d := d)) := by
  dsimp [radialAngularMeasure]
  infer_instance

/-!

## B. Integrals with respect to radialAngularMeasure

-/

lemma integral_radialAngularMeasure {d : ℕ} (f : Space d → F) :
    ∫ x, f x ∂radialAngularMeasure = ∫ x, (1 / ‖x‖ ^ (d - 1)) • f x := by
  dsimp [radialAngularMeasure]
  rw [Integration.integral_withDensity_ofReal_eq_integral_smul (by fun_prop)]
  intro r
  positivity

lemma lintegral_radialMeasure {d : ℕ} (f : Space d → ENNReal) (hf : Measurable f) :
    ∫⁻ x, f x ∂radialAngularMeasure = ∫⁻ x, ENNReal.ofReal (1 / ‖x‖ ^ (d - 1)) * f x := by
  dsimp [radialAngularMeasure]
  rw [lintegral_withDensity_eq_lintegral_mul]
  simp only [one_div, Pi.mul_apply]
  all_goals fun_prop

lemma lintegral_radialMeasure_eq_spherical_mul (d : ℕ) [NeZero d]
    (f : Space d → ENNReal) (hf : Measurable f) :
    ∫⁻ x, f x ∂radialAngularMeasure = ∫⁻ x, f (x.2.1 • x.1.1)
      ∂(volume (α := Space d).toSphere.prod (Measure.volumeIoiPow 0)) := by
  rw [lintegral_radialMeasure, lintegral_volume_eq_spherical_mul]
  apply lintegral_congr_ae
  filter_upwards with x
  have hpos : (0 : ℝ) < x.2 := x.2.2
  have hnorm : ‖(x.2 : ℝ) • (x.1 : Space d)‖ = x.2 := by
    rw [norm_smul, mem_sphere_zero_iff_norm.mp x.1.2, mul_one, Real.norm_eq_abs,
      abs_of_nonneg hpos.le]
  rw [hnorm, mul_right_comm, ← ENNReal.ofReal_mul (by positivity), one_div,
    inv_mul_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul]
  all_goals fun_prop

/-!

## C. The radialAngularMeasure on balls

-/

@[simp]
lemma radialAngularMeasure_closedBall (r : ℝ) :
    radialAngularMeasure (Metric.closedBall (0 : Space 3) r) = ENNReal.ofReal (4 * π * r) := by
  rw [← setLIntegral_one, ← MeasureTheory.lintegral_indicator measurableSet_closedBall,
    lintegral_radialMeasure_eq_spherical_mul _ _
    ((measurable_indicator_const_iff 1).mpr measurableSet_closedBall)]
  have h1 (x : (Metric.sphere (0 : Space) 1) × ↑(Set.Ioi (0 : ℝ))) :
      (Metric.closedBall (0 : Space) r).indicator (fun x => (1 : ENNReal)) (x.2.1 • x.1.1) =
      (Set.univ ×ˢ {a | a.1 ≤ r}).indicator (fun x => 1) x :=
      Set.indicator_const_eq_indicator_const <| by
    simp [norm_smul]
    rw [abs_of_nonneg (le_of_lt x.2.2)]
  simp [h1]
  rw [MeasureTheory.lintegral_indicator <|
    MeasurableSet.prod MeasurableSet.univ (measurableSet_setOfPred.mpr (by fun_prop))]
  simp [MeasureTheory.Measure.prod_prod, Measure.volumeIoiPow]
  rw [MeasureTheory.Measure.comap_apply _ Subtype.val_injective
    (fun s hs => MeasurableSet.subtype_image measurableSet_Ioi hs)
    _ (measurableSet_setOfPred.mpr (by fun_prop))]
  trans 3 * ENNReal.ofReal (4 / 3 * π) * volume (α := ℝ) (Set.Ioc 0 r)
  · congr
    ext x
    simp only [Set.mem_image, Set.mem_ofPred_eq, Subtype.exists, Set.mem_Ioi, exists_and_left,
      exists_prop, exists_eq_right_right, Set.mem_Ioc]
    grind
  simp only [volume_Ioc, sub_zero]
  trans ENNReal.ofReal (3 * ((4 / 3 * π))) * ENNReal.ofReal r
  · simp [ENNReal.ofReal_mul]
  field_simp
  rw [← ENNReal.ofReal_mul (by positivity)]

lemma radialAngularMeasure_real_closedBall (r : ℝ) (hr : 0 < r) :
    radialAngularMeasure.real (Metric.closedBall (0 : Space 3) r) = 4 * π * r := by
  change (radialAngularMeasure (Metric.closedBall (0 : Space 3) r)).toReal = _
  simp only [radialAngularMeasure_closedBall, ENNReal.toReal_ofReal_eq_iff]
  positivity

/-!

## D. Integrability conditions

-/

lemma integrable_radialAngularMeasure_iff {d : ℕ} {f : Space d → F} :
    Integrable f (radialAngularMeasure (d := d)) ↔
      Integrable (fun x => (1 / ‖x‖ ^ (d - 1)) • f x) volume := by
  refine (integrable_withDensity_iff_integrable_smul₀
    (f := fun x : Space d => Real.toNNReal (1 / ‖x‖ ^ (d - 1))) (by fun_prop)).trans ?_
  refine integrable_congr ?_
  filter_upwards with x
  rw [Real.toNNReal_of_nonneg (by positivity), NNReal.smul_def, coe_mk]

omit [NormedSpace ℝ F] in
lemma integrable_radialAngularMeasure_of_spherical {d : ℕ} [NeZero d] (f : Space d → F)
    (hae : StronglyMeasurable f)
    (hf : Integrable (fun x => f (x.2.1 • x.1.1))
    (volume (α := Space d).toSphere.prod (Measure.volumeIoiPow 0))) :
    Integrable f radialAngularMeasure := by
  refine ⟨StronglyMeasurable.aestronglyMeasurable hae, ?_⟩
  rw [hasFiniteIntegral_iff_norm, lintegral_radialMeasure_eq_spherical_mul _ _
    (by simpa using StronglyMeasurable.enorm hae), ← hasFiniteIntegral_iff_norm]
  exact hf.2

/-!

## E. HasTemperateGrowth of measures

-/

/-!

### E.1. Integrability of powers

-/
private lemma integrable_neg_pow_on_ioi (n : ℕ) :
    IntegrableOn (fun x : ℝ => (|((1 : ℝ) + x) ^ (- (n + 2) : ℝ)|)) (Set.Ioi 0) := by
  have hpre : (fun x : ℝ => (1 : ℝ) + x) ⁻¹' Set.Ioi 1 = Set.Ioi 0 := by
    ext x
    simp
  have integrableOn_rpow_neg :
      IntegrableOn (fun x : ℝ => ((1 : ℝ) + x) ^ (- (n + 2) : ℝ)) (Set.Ioi 0) := by
    rw [← hpre]
    exact ((measurePreserving_add_left volume (1 : ℝ)).integrableOn_comp_preimage
      (measurableEmbedding_addLeft 1)
      (f := fun y : ℝ => y ^ (- (n + 2) : ℝ)) (s := Set.Ioi 1)).mpr
      (integrableOn_Ioi_rpow_of_lt (by linarith [Nat.cast_nonneg (α := ℝ) n]) one_pos)
  refine integrableOn_rpow_neg.congr_fun (fun x hx => ?_) measurableSet_Ioi
  rw [Set.mem_Ioi] at hx
  rw [abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]

lemma radialAngularMeasure_integrable_pow_neg_two {d : ℕ} :
    Integrable (fun x : Space d => (1 + ‖x‖) ^ (- (d + 1) : ℝ))
      radialAngularMeasure := by
  match d with
  | 0 => simp
  | dm1 + 1 =>
  apply integrable_radialAngularMeasure_of_spherical _ (by fun_prop)
  simp [norm_smul]
  rw [MeasureTheory.integrable_prod_iff (AEMeasurable.aestronglyMeasurable (by fun_prop))]
  refine ⟨?_, by simp⟩
  filter_upwards with x
  simp [Measure.volumeIoiPow]
  refine ((MeasureTheory.integrableOn_iff_comap_subtypeVal measurableSet_Ioi).mp
    (integrable_neg_pow_on_ioi dm1)).congr ?_
  filter_upwards with y
  have hy : (0 : ℝ) < y.1 := y.2
  simp only [Function.comp_apply]
  rw [abs_of_pos hy, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  congr 1
  ring

/-!

### E.2. radialAngularMeasure has temperate growth

-/

instance (d : ℕ) : Measure.HasTemperateGrowth (radialAngularMeasure (d := d)) where
  exists_integrable := by
    use d + 1
    simpa using radialAngularMeasure_integrable_pow_neg_two (d := d)

end Space
