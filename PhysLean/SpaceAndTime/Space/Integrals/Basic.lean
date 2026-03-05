/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.SpaceAndTime.Space.Module
/-!

# Integrals in Space

## i. Overview

In this module we give general properties of integrals over `Space d`.
We focus here on the volume measure, which is the usual measure on `Space d`, i.e.
`dx dy dz`.

## ii. Key results

- `volume_eq_addHaar` : The volume measure on `Space d` is the same as the Haar measure
  associated with the basis of `Space d`.
- `integral_volume_eq_spherical` : The integral of a function over `Space d.succ` with
  respect to the volume measure can be expressed as an integral over the unit sphere and
  the positive reals.
- `lintegral_volume_eq_spherical` : The lower Lebesgue integral of a function over `Space d.succ`
  with respect to the volume measure can be expressed as a lower Lebesgue integral over the unit
  sphere and the positive reals.

-/

namespace Space

open InnerProductSpace MeasureTheory

/-!

## A. Properties of the volume measure

-/

lemma volume_eq_addHaar {d} : (volume (α := Space d)) = Space.basis.toBasis.addHaar := by
  exact (OrthonormalBasis.addHaar_eq_volume _).symm

lemma volume_closedBall_ne_zero {d : ℕ} (x : Space d.succ) {r : ℝ} (hr : 0 < r) :
    volume (Metric.closedBall x r) ≠ 0 := by
  obtain ⟨k,hk⟩ := Nat.even_or_odd' d.succ
  rcases hk with hk | hk
  · rw [InnerProductSpace.volume_closedBall_of_dim_even (k := k)]
    simp only [Nat.succ_eq_add_one, finrank_eq_dim, ne_eq, mul_eq_zero, Nat.add_eq_zero_iff,
      one_ne_zero, and_false, not_false_eq_true, pow_eq_zero_iff, ENNReal.ofReal_eq_zero, not_or,
      not_le]
    apply And.intro
    · simp_all
    · positivity
    · simpa using hk
  · rw [InnerProductSpace.volume_closedBall_of_dim_odd (k := k)]
    simp only [Nat.succ_eq_add_one, finrank_eq_dim, ne_eq, mul_eq_zero, Nat.add_eq_zero_iff,
      one_ne_zero, and_false, not_false_eq_true, pow_eq_zero_iff, ENNReal.ofReal_eq_zero, not_or,
      not_le]
    apply And.intro
    · simp_all
    · positivity
    · simpa using hk

lemma volume_closedBall_ne_top {d : ℕ} (x : Space d.succ) (r : ℝ) :
    volume (Metric.closedBall x r) ≠ ⊤ := by
  obtain ⟨k,hk⟩ := Nat.even_or_odd' d.succ
  rcases hk with hk | hk
  · rw [InnerProductSpace.volume_closedBall_of_dim_even (by simpa using hk)]
    simp only [Nat.succ_eq_add_one, finrank_eq_dim, ne_eq]
    apply not_eq_of_beq_eq_false
    rfl
  · rw [InnerProductSpace.volume_closedBall_of_dim_odd (by simpa using hk)]
    simp only [Nat.succ_eq_add_one, finrank_eq_dim, ne_eq]
    apply not_eq_of_beq_eq_false
    rfl

@[simp]
lemma volume_metricBall_three :
    volume (Metric.ball (0 : Space 3) 1) = ENNReal.ofReal (4 / 3 * Real.pi) := by
  rw [InnerProductSpace.volume_ball_of_dim_odd (k := 1)]
  simp only [ENNReal.ofReal_one, finrank_eq_dim, one_pow, pow_one, Nat.reduceAdd,
    Nat.doubleFactorial.eq_3, Nat.doubleFactorial, mul_one, Nat.cast_ofNat, one_mul]
  ring_nf
  simp

@[simp]
lemma volume_metricBall_two :
    volume (Metric.ball (0 : Space 2) 1) = ENNReal.ofReal Real.pi := by
  rw [InnerProductSpace.volume_ball_of_dim_even (k := 1)]
  simp [finrank_eq_dim]
  simp [finrank_eq_dim]

@[simp]
lemma volume_metricBall_two_real :
    (volume.real (Metric.ball (0 : Space 2) 1)) = Real.pi := by
  trans (volume (Metric.ball (0 : Space 2) 1)).toReal
  · rfl
  rw [volume_metricBall_two]
  simp only [ENNReal.toReal_ofReal_eq_iff]
  exact Real.pi_nonneg

@[simp]
lemma volume_metricBall_three_real :
    (volume.real (Metric.ball (0 : Space 3) 1)) = 4 / 3 * Real.pi := by
  trans (volume (Metric.ball (0 : Space 3) 1)).toReal
  · rfl
  rw [volume_metricBall_three]
  simp only [ENNReal.toReal_ofReal_eq_iff]
  positivity

/-!

## B. Integrals over one-dimensional space

-/

lemma integral_one_dim_eq_integral_real {f : Space 1 → ℝ} :
    ∫ x, f x ∂volume = ∫ x, f (oneEquiv.symm x) ∂volume := by rw [integral_comp]

/-!

## C. Integrals over volume to spherical

-/

lemma integral_volume_eq_spherical (d : ℕ) (f : Space d.succ → F)
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    ∫ x, f x ∂volume = ∫ x, f (x.2.1 • x.1.1) ∂(volume (α := Space d.succ).toSphere.prod
        (Measure.volumeIoiPow (Module.finrank ℝ (Space d.succ) - 1))) := by
  rw [← MeasureTheory.MeasurePreserving.integral_comp (f := homeomorphUnitSphereProd _)
    (MeasureTheory.Measure.measurePreserving_homeomorphUnitSphereProd
    (volume (α := Space d.succ)))
    (Homeomorph.measurableEmbedding (homeomorphUnitSphereProd (Space d.succ)))]
  simp only [Nat.succ_eq_add_one, homeomorphUnitSphereProd_apply_snd_coe,
    homeomorphUnitSphereProd_apply_fst_coe]
  let f' : (x : (Space d.succ)) → F := fun x => f (‖↑x‖ • ‖↑x‖⁻¹ • ↑x)
  conv_rhs =>
    enter [2, x]
    change f' x.1
  rw [MeasureTheory.integral_subtype_comap (by simp), ← setIntegral_univ]
  simp [f']
  refine integral_congr_ae ?_
  have h1 : ∀ᵐ x ∂(volume (α := Space d.succ)), x ≠ 0 := by
    exact Measure.ae_ne volume 0
  filter_upwards [Measure.ae_ne volume 0] with x hx
  congr
  simp [smul_smul]
  have hx : ‖x‖ ≠ 0 := by
    simpa using hx
  field_simp
  simp

/- An instance of `sfinite` on the spherical integral measure on `Space d`.
  This is needed in many of the calculations related to spherical integrals,
  but cannot be inferred by Lean without this. -/
instance : SFinite (@Measure.comap ↑(Set.Ioi 0) ℝ Subtype.instMeasurableSpace
        Real.measureSpace.toMeasurableSpace Subtype.val volume) := by
      refine { out' := ?_ }
      have h1 := SFinite.out' (μ := volume (α := ℝ))
      obtain ⟨m, h⟩ := h1
      use fun n => Measure.comap Subtype.val (m n)
      apply And.intro
      · intro n
        refine (isFiniteMeasure_iff (Measure.comap Subtype.val (m n))).mpr ?_
        rw [MeasurableEmbedding.comap_apply (MeasurableEmbedding.subtype_coe measurableSet_Ioi)]
        simp only [Set.image_univ, Subtype.range_coe_subtype, Set.mem_Ioi]
        have hm := h.1 n
        exact measure_lt_top (m n) {x | 0 < x}
      · ext s hs
        rw [MeasurableEmbedding.comap_apply, Measure.sum_apply]
        conv_rhs =>
          enter [1, i]
          rw [MeasurableEmbedding.comap_apply (MeasurableEmbedding.subtype_coe measurableSet_Ioi)]
        have h2 := h.2
        rw [Measure.ext_iff'] at h2
        rw [← Measure.sum_apply]
        exact h2 (Subtype.val '' s)
        refine MeasurableSet.subtype_image measurableSet_Ioi hs
        exact hs
        apply MeasurableEmbedding.subtype_coe
        simp

/-!

## D. Lower Lebesgue integral over volume to spherical

-/

lemma lintegral_volume_eq_spherical (d : ℕ) (f : Space d.succ → ENNReal) (hf : Measurable f) :
    ∫⁻ x, f x ∂volume = ∫⁻ x, f (x.2.1 • x.1.1) ∂(volume (α := Space d.succ).toSphere.prod
        (Measure.volumeIoiPow (Module.finrank ℝ (Space d.succ) - 1))) := by
  have h0 := MeasureTheory.MeasurePreserving.lintegral_comp
    (f := fun x => f (x.2.1 • x.1.1)) (g := homeomorphUnitSphereProd _)
    (MeasureTheory.Measure.measurePreserving_homeomorphUnitSphereProd
    (volume (α := Space d.succ)))
    (by fun_prop)
  rw [← h0]
  simp only [Nat.succ_eq_add_one, homeomorphUnitSphereProd_apply_snd_coe,
    homeomorphUnitSphereProd_apply_fst_coe]
  let f' : (x : (Space d.succ)) → ENNReal := fun x => f (‖↑x‖ • ‖↑x‖⁻¹ • ↑x)
  conv_rhs =>
    enter [2, x]
    change f' x.1
  rw [MeasureTheory.lintegral_subtype_comap (by simp)]
  simp [f']
  refine lintegral_congr_ae ?_
  filter_upwards [Measure.ae_ne volume 0] with x hx
  congr
  simp [smul_smul]
  have hx : ‖x‖ ≠ 0 := by
    simpa using hx
  field_simp
  rw [one_smul]

lemma lintegral_volume_eq_spherical_mul (d : ℕ) (f : Space d.succ → ENNReal) (hf : Measurable f) :
    ∫⁻ x, f x ∂volume = ∫⁻ x, f (x.2.1 • x.1.1) * .ofReal (x.2.1 ^ d)
      ∂(volume (α := Space d.succ).toSphere.prod (Measure.volumeIoiPow 0)) := by
  rw [lintegral_volume_eq_spherical, Measure.volumeIoiPow,
    MeasureTheory.prod_withDensity_right,
    MeasureTheory.lintegral_withDensity_eq_lintegral_mul,
    Measure.volumeIoiPow, MeasureTheory.prod_withDensity_right,
    MeasureTheory.lintegral_withDensity_eq_lintegral_mul]
  · refine lintegral_congr_ae ?_
    simp only [Nat.succ_eq_add_one, finrank_eq_dim, add_tsub_cancel_right, pow_zero,
      ENNReal.ofReal_one]
    filter_upwards with x
    simp only [Pi.mul_apply, one_mul]
    ring
  all_goals fun_prop

end Space
