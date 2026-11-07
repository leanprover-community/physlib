/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Mathematics.Geometry.Sphere.Polar
/-!
# Spherical profiles and invariant sphere integrals

The invariant sphere measure has mass `4 π` and admits directional integration formulas.

## i. Overview

Differentiating the ball integral in the radius gives Archimedes' projection of the sphere onto an
axis. This is the sphere transform for axis directions. Rotation invariance of the sphere measure
extends it to every direction.

## ii. Key results

* `sphereProfile_eq`: Archimedes' projection of the sphere onto an axis.
* `sphereEquiv_measurePreserving`: the sphere measure is invariant under linear isometries.
* `sphereMeasure_univ`: the total mass is `4 π`.
* `sphereIntegral_dir`: Archimedes' formula for a function of one direction.
* `integral_sphere_neg`: invariance of the sphere measure under the antipodal map.

## iii. Table of contents

- A. The radial profile of the sphere average
- B. Archimedes' projection
- C. Rotation invariance and general directions
- D. Functions of one direction

## iv. References

* None.
-/

@[expose] public section

namespace Sphere3

open MeasureTheory
open scoped Pointwise FourierTransform SchwartzMap

/-! ## A. The radial profile of the sphere average -/

/-- The average of `h (r n_i)` over the unit sphere, as a function of the radius. -/
noncomputable def sphereProfile {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (i : Fin 3) (h : ℝ → F) (r : ℝ) : F :=
  ∫ n : Sph, h (r * (n.1 i)) ∂sphereMeasure

lemma ball_integral_profile {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (i : Fin 3) {h : ℝ → F} (hh : Continuous h) {R : ℝ} (hR : 0 < R) :
    ∫ x in Metric.ball (0 : Space 3) R, h (x i) =
      ∫ r in Set.Ioo 0 R, r ^ 2 • sphereProfile i h r := by
  rw [ball_integral_polar i hh]
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn hh.continuousOn
  have hint : Integrable (fun p : Sph × ℝ => p.2 ^ 2 • h (p.2 * (p.1.1 i)))
      (sphereMeasure.prod (volume.restrict (Set.Ioo 0 R))) := by
    refine Integrable.of_bound (C := R ^ 2 * M) ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      have hc : Continuous fun p : Sph × ℝ => p.1.1 i :=
        (Space.eval_continuous i).comp (continuous_subtype_val.comp continuous_fst)
      exact (continuous_snd.pow 2).smul (hh.comp (continuous_snd.mul hc))
    · have hae : ∀ᵐ p : Sph × ℝ ∂(sphereMeasure.prod (volume.restrict (Set.Ioo 0 R))),
          p.2 ∈ Set.Ioo 0 R :=
        (Measure.quasiMeasurePreserving_snd (μ := sphereMeasure)
          (ν := volume.restrict (Set.Ioo 0 R))).ae (ae_restrict_mem measurableSet_Ioo)
      filter_upwards [hae] with p hp
      have hcoord : |p.1.1 i| ≤ 1 := by
        have hn : ‖p.1.1‖ = 1 := by simp
        calc |p.1.1 i| = |inner ℝ p.1.1 (Space.basis i)| := by simp
          _ ≤ ‖p.1.1‖ * ‖(Space.basis i : Space 3)‖ := abs_real_inner_le_norm _ _
          _ = 1 := by rw [hn, Space.basis.norm_eq_one]; simp
      have hz : |p.2 * p.1.1 i| ≤ R := by
        rw [abs_mul, abs_of_pos hp.1]
        nlinarith [hp.1, hp.2, hcoord, abs_nonneg (p.1.1 i)]
      have hb := hM (p.2 * p.1.1 i) ⟨by linarith [abs_le.mp hz], (abs_le.mp hz).2⟩
      rw [norm_smul, Real.norm_eq_abs, abs_pow, abs_of_pos hp.1]
      have hM0 : 0 ≤ M := (norm_nonneg _).trans hb
      have hsq : p.2 ^ 2 ≤ R ^ 2 := by nlinarith [hp.1, hp.2]
      exact mul_le_mul hsq hb (norm_nonneg _) (sq_nonneg R)
  rw [integral_integral_swap hint]
  refine setIntegral_congr_fun measurableSet_Ioo fun r _ => ?_
  simp only [sphereProfile]
  rw [integral_smul]

lemma continuous_sphereProfile {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (i : Fin 3) {h : ℝ → F} (hh : Continuous h) :
    Continuous (sphereProfile i h) := by
  have hc : Continuous (Function.uncurry fun (r : ℝ) (n : Sph) => h (r * (n.1 i))) := by
    have hcoord : Continuous fun p : ℝ × Sph => p.2.1 i :=
      (Space.eval_continuous i).comp (continuous_subtype_val.comp continuous_snd)
    exact hh.comp (continuous_fst.mul hcoord)
  have hcpt : IsCompact (Set.univ : Set Sph) := isCompact_univ_iff.mpr
    (isCompact_iff_compactSpace.mp (isCompact_sphere (0 : Space 3) 1))
  have := continuous_parametric_integral_of_continuous (μ := sphereMeasure) hc hcpt
  have h2 : sphereProfile i h = fun r => ∫ n : Sph, h (r * (n.1 i)) ∂sphereMeasure := rfl
  rw [h2]
  simpa using this

/-! ## B. Archimedes' projection -/

/-- The closed-form side: the integral of `π (R² - z²) h(z)`, as a function of `R`. -/
noncomputable def discProfile {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (h : ℝ → F) (R : ℝ) : F :=
  (Real.pi * R ^ 2) • (∫ z in (-R)..R, h z) - Real.pi • ∫ z in (-R)..R, z ^ 2 • h z

lemma hasDerivAt_discProfile {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {h : ℝ → F} (hh : Continuous h) (R : ℝ) :
    HasDerivAt (discProfile h) ((2 * Real.pi * R) • ∫ z in (-R)..R, h z) R := by
  have hz2 : Continuous fun z : ℝ => z ^ 2 • h z := (continuous_id.pow 2).smul hh
  have hH : ∀ t : ℝ, HasDerivAt (fun t => ∫ z in (0 : ℝ)..t, h z) (h t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hh.intervalIntegrable _ _)
      hh.aestronglyMeasurable.stronglyMeasurableAtFilter hh.continuousAt
  have hK : ∀ t : ℝ, HasDerivAt (fun t => ∫ z in (0 : ℝ)..t, z ^ 2 • h z) (t ^ 2 • h t) t :=
    fun t => intervalIntegral.integral_hasDerivAt_right (hz2.intervalIntegrable _ _)
      hz2.aestronglyMeasurable.stronglyMeasurableAtFilter hz2.continuousAt
  have hI : HasDerivAt (fun R => ∫ z in (-R)..R, h z) (h R + h (-R)) R := by
    have e : ∀ R : ℝ, ∫ z in (-R)..R, h z =
        (∫ z in (0 : ℝ)..R, h z) - ∫ z in (0 : ℝ)..(-R), h z := fun R => by
      rw [intervalIntegral.integral_interval_sub_left (hh.intervalIntegrable _ _)
        (hh.intervalIntegrable _ _)]
    simp_rw [e]
    have := (hH R).sub ((hH (-R)).scomp R (hasDerivAt_neg R))
    simp only [neg_smul, one_smul, sub_neg_eq_add] at this
    exact this
  have hJ : HasDerivAt (fun R => ∫ z in (-R)..R, z ^ 2 • h z)
      (R ^ 2 • h R + R ^ 2 • h (-R)) R := by
    have e : ∀ R : ℝ, ∫ z in (-R)..R, z ^ 2 • h z =
        (∫ z in (0 : ℝ)..R, z ^ 2 • h z) - ∫ z in (0 : ℝ)..(-R), z ^ 2 • h z := fun R => by
      rw [intervalIntegral.integral_interval_sub_left (hz2.intervalIntegrable _ _)
        (hz2.intervalIntegrable _ _)]
    simp_rw [e]
    have := (hK R).sub ((hK (-R)).scomp R (hasDerivAt_neg R))
    simp only [neg_smul, one_smul, sub_neg_eq_add, neg_sq] at this
    exact this
  have hmain := ((hasDerivAt_pow 2 R).const_mul Real.pi |>.smul hI).sub (hJ.const_smul Real.pi)
  unfold discProfile
  convert hmain using 1
  norm_num
  module

lemma sphereProfile_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (i : Fin 3) {h : ℝ → F} (hh : Continuous h) {R : ℝ} (hR : 0 < R) :
    sphereProfile i h R = (2 * Real.pi / R) • ∫ z in (-R)..R, h z := by
  have hcont : Continuous fun r : ℝ => r ^ 2 • sphereProfile i h r :=
    (continuous_id.pow 2).smul (continuous_sphereProfile i hh)
  -- the radial integral equals the closed form on `(0, ∞)`
  have heq : ∀ r : ℝ, 0 < r →
      (∫ s in (0 : ℝ)..r, s ^ 2 • sphereProfile i h s) = discProfile h r := by
    intro r hr
    have h1 := ball_integral_profile i hh hr
    have h2 := integral_ball_coord i hh hr
    have h3 : ∫ s in (0 : ℝ)..r, s ^ 2 • sphereProfile i h s =
        ∫ s in Set.Ioo 0 r, s ^ 2 • sphereProfile i h s := by
      rw [intervalIntegral.integral_of_le hr.le, integral_Ioc_eq_integral_Ioo]
    have h4 : discProfile h r = ∫ z in Set.Ioo (-r) r, (Real.pi * (r ^ 2 - z ^ 2)) • h z := by
      have hle : -r ≤ r := by linarith
      have hi1 : IntegrableOn h (Set.Ioo (-r) r) :=
        (hh.continuousOn.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
      have hi2 : IntegrableOn (fun z : ℝ => z ^ 2 • h z) (Set.Ioo (-r) r) :=
        ((continuous_id.pow 2).smul hh).continuousOn.integrableOn_Icc.mono_set
          Set.Ioo_subset_Icc_self
      unfold discProfile
      rw [intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le hle,
        integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo,
        ← integral_smul, ← integral_smul]
      have hs1 : Integrable (fun a : ℝ => (Real.pi * r ^ 2) • h a)
          (volume.restrict (Set.Ioo (-r) r)) := hi1.smul _
      have hs2 : Integrable (fun a : ℝ => Real.pi • a ^ 2 • h a)
          (volume.restrict (Set.Ioo (-r) r)) := hi2.smul _
      rw [← integral_sub hs1 hs2]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [smul_smul]
      module
    rw [h3, ← h1, h2, h4]
  have hA : HasDerivAt (fun r => ∫ s in (0 : ℝ)..r, s ^ 2 • sphereProfile i h s)
      (R ^ 2 • sphereProfile i h R) R :=
    intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable _ _)
      hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt
  have hB := hasDerivAt_discProfile hh R
  have hev : (fun r => ∫ s in (0 : ℝ)..r, s ^ 2 • sphereProfile i h s) =ᶠ[nhds R] discProfile h :=
    Filter.eventually_of_mem (Ioi_mem_nhds hR) fun r hr => heq r hr
  have hu := hA.unique (hB.congr_of_eventuallyEq hev)
  have hR2 : R ^ 2 ≠ 0 := by positivity
  have : sphereProfile i h R = (R ^ 2)⁻¹ • ((2 * Real.pi * R) • ∫ z in (-R)..R, h z) := by
    rw [← hu, smul_smul, inv_mul_cancel₀ hR2, one_smul]
  rw [this, smul_smul]
  congr 1
  field_simp

/-! ## C. Rotation invariance and general directions -/

/-- The restriction of a linear isometry of `Space 3` to the unit sphere. -/
noncomputable def sphereEquiv (U : Space 3 ≃ₗᵢ[ℝ] Space 3) : Sph ≃ₜ Sph where
  toFun n := ⟨U n.1, by simp⟩
  invFun n := ⟨U.symm n.1, by simp⟩
  left_inv n := by ext; simp
  right_inv n := by ext; simp
  continuous_toFun := by
    exact Continuous.subtype_mk (U.continuous.comp continuous_subtype_val) _
  continuous_invFun := by
    exact Continuous.subtype_mk (U.symm.continuous.comp continuous_subtype_val) _

lemma sphereEquiv_coe (U : Space 3 ≃ₗᵢ[ℝ] Space 3) (n : Sph) :
    ((sphereEquiv U n : Sph) : Space 3) = U n.1 := rfl

lemma sphereEquiv_measurePreserving (U : Space 3 ≃ₗᵢ[ℝ] Space 3) :
    MeasurePreserving (sphereEquiv U) sphereMeasure sphereMeasure := by
  refine ⟨(sphereEquiv U).continuous.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply (sphereEquiv U).continuous.measurable hs]
  have hs' : MeasurableSet ((sphereEquiv U) ⁻¹' s) := (sphereEquiv U).continuous.measurable hs
  rw [Measure.toSphere_apply' _ hs', Measure.toSphere_apply' _ hs]
  congr 1
  let e : Space 3 ≃ᵐ Space 3 := U.toHomeomorph.toMeasurableEquiv
  have hmp : MeasurePreserving e (volume : Measure (Space 3)) volume := U.measurePreserving
  have himg : (Subtype.val '' ((sphereEquiv U) ⁻¹' s) : Set (Space 3)) =
      U ⁻¹' (Subtype.val '' s) := by
    ext x
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨sphereEquiv U n, hn, rfl⟩
    · rintro ⟨m, hm, hmx⟩
      have hx : ‖x‖ = 1 := by
        have := m.2
        rw [mem_sphere_zero_iff_norm] at this
        rw [← U.norm_map, ← hmx]; exact this
      refine ⟨⟨x, by simpa using hx⟩, ?_, rfl⟩
      show sphereEquiv U ⟨x, _⟩ ∈ s
      have : sphereEquiv U ⟨x, by simpa using hx⟩ = m := Subtype.ext hmx.symm
      rw [this]; exact hm
  have hsm : (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' ((sphereEquiv U) ⁻¹' s) : Set (Space 3))) =
      U ⁻¹' (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s : Set (Space 3))) := by
    rw [himg]
    ext x
    simp only [Set.mem_preimage]
    constructor
    · rintro ⟨r, hr, y, hy, rfl⟩
      exact ⟨r, hr, U y, hy, by simp⟩
    · rintro ⟨r, hr, y, hy, hyx⟩
      refine ⟨r, hr, U.symm y, by simpa using hy, ?_⟩
      apply U.injective
      simp [hyx]
  rw [hsm]
  exact hmp.measure_preimage_equiv _

/-- The total mass of the sphere measure is the area `4 π`. -/
lemma sphereMeasure_univ : sphereMeasure Set.univ = ENNReal.ofReal (4 * Real.pi) := by
  rw [Measure.toSphere_apply_univ, Space.volume_metricBall_three, Space.finrank_eq_dim]
  rw [show ((3 : ℕ) : ENNReal) = ENNReal.ofReal 3 by simp, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

/-! ## D. Functions of one direction -/

/-- **Archimedes in an arbitrary direction.** The sphere integral of a function of the inner product
with a fixed vector `z ≠ 0` is a one-dimensional integral over `[-‖z‖, ‖z‖]`. -/
lemma sphereIntegral_dir {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {h : ℝ → F} (hh : Continuous h) {z : Space 3} (hz : z ≠ 0) :
    ∫ n : Sph, h (inner ℝ z n.1) ∂sphereMeasure =
      (2 * Real.pi / ‖z‖) • ∫ s in (-‖z‖)..‖z‖, h s := by
  have ha : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  set a := ‖z‖ with ha_def
  let w : Space 3 := a • Space.basis (0 : Fin 3)
  have hw : ‖z‖ = ‖w‖ := by
    simp [w, norm_smul, ha_def]
  let U : Space 3 ≃ₗᵢ[ℝ] Space 3 := Submodule.reflection (ℝ ∙ (z - w))ᗮ
  have hUz : U z = w := Submodule.reflection_sub hw
  have hinner : ∀ n : Sph, inner ℝ z n.1 = a * (U n.1) 0 := by
    intro n
    have h1 := U.inner_map_map z n.1
    rw [hUz] at h1
    rw [← h1]
    simp [w, inner_smul_left, Space.basis_inner]
  have hcongr : ∀ n : Sph, h (inner ℝ z n.1) =
      (fun m : Sph => h (a * m.1 0)) (sphereEquiv U n) := by
    intro n
    simp only [hinner, sphereEquiv_coe]
  simp_rw [hcongr]
  have key := (sphereEquiv_measurePreserving U).integral_comp' (f := (sphereEquiv
    U).toMeasurableEquiv)
    (fun m : Sph => h (a * m.1 0))
  refine Eq.trans key ?_
  have := sphereProfile_eq (0 : Fin 3) hh (R := a) (by positivity)
  simpa [sphereProfile] using this

/-- The sphere measure is invariant under the antipodal map. -/
lemma integral_sphere_neg {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Space 3 → F) : ∫ n : Sph, f (-n.1) ∂sphereMeasure = ∫ n : Sph, f n.1 ∂sphereMeasure := by
  let U : Space 3 ≃ₗᵢ[ℝ] Space 3 := LinearIsometryEquiv.neg ℝ
  have h := (sphereEquiv_measurePreserving U).integral_comp (sphereEquiv U).measurableEmbedding
    (fun n : Sph => f n.1)
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
  simp [sphereEquiv_coe, U]

end Sphere3
