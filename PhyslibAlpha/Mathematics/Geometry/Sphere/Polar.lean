/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Physlib.SpaceAndTime.Space.Norm.Basic
public import Physlib.SpaceAndTime.Space.Slice
/-!
# Polar coordinates on balls of space

Integrals over balls of `Space 3` reduce to integrals over the unit sphere and the radius.

## i. Overview

The coordinate slice `Space 3 ≃ ℝ × Space 2` preserves volume. This gives integrals over a ball of
functions of one coordinate as one-dimensional integrals against the disc area `π (R² - z²)`.
Polar coordinates write the ball integral as an integral over the unit sphere and over the radius.
The unit sphere carries the surface measure of total mass `4 π`. The same holds for general
integrands. Integrability of `1 / |x|` times a continuous function and of radial exponentials is
included.

## ii. Key results

* `slice_measurePreserving`: the slice map preserves volume.
* `integral_ball_coord`: a ball integral of a function of one coordinate.
* `ball_integral_polar`, `ball_integral_polar_general`: polar coordinates on a ball.
* `integrable_inv_norm_mul`: integrability of the singular Green density.

## iii. Table of contents

- A. Volume preservation of coordinate maps
- B. Integrals over a ball of a function of one coordinate
- C. Polar coordinates on the ball
- D. Polar coordinates for general integrands

## iv. References

* None.
-/

@[expose] public section

namespace Sphere3

open MeasureTheory
open scoped Pointwise FourierTransform SchwartzMap

/-! ## A. Volume preservation of coordinate maps -/

lemma equivPi_measurePreserving (d : ℕ) :
    MeasurePreserving (Space.equivPi d) (volume : Measure (Space d))
      (volume : Measure (Fin d → ℝ)) := by
  have h1 : MeasurePreserving (Space.basis (d := d)).repr (volume : Measure (Space d))
      (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
    (Space.basis (d := d)).measurePreserving_repr
  have h2 : MeasurePreserving (@WithLp.ofLp 2 (Fin d → ℝ)) :=
    PiLp.volume_preserving_ofLp (Fin d)
  exact h2.comp h1

lemma slice_measurePreserving {d : ℕ} (i : Fin d.succ) :
    MeasurePreserving (Space.slice i) (volume : Measure (Space d.succ))
      (volume : Measure (ℝ × Space d)) := by
  have h1 := equivPi_measurePreserving d.succ
  have h2 := volume_preserving_piFinSuccAbove (fun _ : Fin d.succ => ℝ) i
  have h3 : MeasurePreserving (Space.equivPi d).symm (volume : Measure (Fin d → ℝ))
      (volume : Measure (Space d)) :=
    (equivPi_measurePreserving d).symm (Space.equivPi d).toHomeomorph.toMeasurableEquiv
  have h4 : MeasurePreserving (Prod.map (id : ℝ → ℝ) (Space.equivPi d).symm)
      (volume : Measure (ℝ × (Fin d → ℝ))) (volume : Measure (ℝ × Space d)) :=
    (MeasurePreserving.id volume).prod h3
  have := h4.comp (h2.comp h1)
  convert this using 1
  funext x
  rfl

/-! ## B. Integrals over a ball of a function of one coordinate -/

lemma volume_ball_two (ρ : ℝ) (hρ : 0 ≤ ρ) :
    volume (Metric.ball (0 : Space 2) ρ) = ENNReal.ofReal (Real.pi * ρ ^ 2) := by
  rw [Measure.addHaar_ball _ _ hρ, Space.volume_metricBall_two]
  have hf : Module.finrank ℝ (Space 2) = 2 := Space.finrank_eq_dim
  rw [hf, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

lemma integral_ball_coord_aux {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (i : Fin 3) (h : ℝ → F) {R : ℝ} :
    ∫ x in Metric.ball (0 : Space 3) R, h (x i) =
      ∫ p : ℝ × Space 2, (Metric.ball (0 : Space 3) R).indicator (fun x => h (x i))
        ((Space.slice i).symm p) := by
  let e : Space 3 ≃ᵐ ℝ × Space 2 := (Space.slice i).toHomeomorph.toMeasurableEquiv
  have hmp : MeasurePreserving e (volume : Measure (Space 3)) (volume : Measure (ℝ × Space 2)) :=
    slice_measurePreserving i
  have h2 := (hmp.symm e).integral_comp'
    ((Metric.ball (0 : Space 3) R).indicator (fun x => h (x i)))
  rw [integral_indicator measurableSet_ball] at h2
  exact h2.symm

lemma indicator_slice_apply {F : Type*} [NormedAddCommGroup F]
    (i : Fin 3) (h : ℝ → F) {R : ℝ} (hR : 0 < R) (z : ℝ) (y : Space 2) :
    (Metric.ball (0 : Space 3) R).indicator (fun x => h (x i)) ((Space.slice i).symm (z, y)) =
      {y' : Space 2 | z ^ 2 + ‖y'‖ ^ 2 < R ^ 2}.indicator (fun _ => h z) y := by
  by_cases hy : z ^ 2 + ‖y‖ ^ 2 < R ^ 2
  · have hm : (Space.slice i).symm (z, y) ∈ Metric.ball (0 : Space 3) R := by
      rw [mem_ball_zero_iff, Space.norm_slice_symm_eq, Real.sqrt_lt' hR]
      simpa using hy
    rw [Set.indicator_of_mem hm, Set.indicator_of_mem (show y ∈ _ from hy)]
    simp
  · have hm : (Space.slice i).symm (z, y) ∉ Metric.ball (0 : Space 3) R := by
      rw [mem_ball_zero_iff, Space.norm_slice_symm_eq, Real.sqrt_lt' hR]
      simpa using hy
    rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (show y ∉ _ from hy)]

lemma slab_section_volume (R z : ℝ) :
    volume {y : Space 2 | z ^ 2 + ‖y‖ ^ 2 < R ^ 2} =
      ENNReal.ofReal (Real.pi * (R ^ 2 - z ^ 2)) := by
  by_cases hz : z ^ 2 < R ^ 2
  · have hρ : 0 ≤ Real.sqrt (R ^ 2 - z ^ 2) := Real.sqrt_nonneg _
    have hset : {y : Space 2 | z ^ 2 + ‖y‖ ^ 2 < R ^ 2} =
        Metric.ball (0 : Space 2) (Real.sqrt (R ^ 2 - z ^ 2)) := by
      ext y
      simp only [Set.mem_ofPred_eq, mem_ball_zero_iff]
      rw [Real.lt_sqrt (norm_nonneg _)]
      constructor <;> intro h <;> linarith
    rw [hset, volume_ball_two _ hρ, Real.sq_sqrt (by linarith)]
  · have hset : {y : Space 2 | z ^ 2 + ‖y‖ ^ 2 < R ^ 2} = ∅ := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      nlinarith [sq_nonneg ‖y‖]
    rw [hset, measure_empty]
    symm
    rw [ENNReal.ofReal_eq_zero]
    have := Real.pi_pos
    nlinarith

/-- A ball integral of a function of one coordinate reduces to a one-dimensional integral against
the disc area. -/
lemma integral_ball_coord {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (i : Fin 3) {h : ℝ → F} (hh : Continuous h) {R : ℝ} (hR : 0 < R) :
    ∫ x in Metric.ball (0 : Space 3) R, h (x i) =
      ∫ z in Set.Ioo (-R) R, (Real.pi * (R ^ 2 - z ^ 2)) • h z := by
  rw [integral_ball_coord_aux]
  simp_rw [indicator_slice_apply i h hR]
  have hint : Integrable (fun p : ℝ × Space 2 =>
      {y' : Space 2 | p.1 ^ 2 + ‖y'‖ ^ 2 < R ^ 2}.indicator (fun _ => h p.1) p.2)
      (volume.prod volume) := by
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
      hh.continuousOn
    set K : Set (ℝ × Space 2) := Set.Icc (-R) R ×ˢ Metric.closedBall (0 : Space 2) R with hK
    have hKc : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
    have hT : MeasurableSet {p : ℝ × Space 2 | p.1 ^ 2 + ‖p.2‖ ^ 2 < R ^ 2} :=
      measurableSet_lt (by fun_prop) measurable_const
    have hform : (fun p : ℝ × Space 2 =>
        {y' : Space 2 | p.1 ^ 2 + ‖y'‖ ^ 2 < R ^ 2}.indicator (fun _ => h p.1) p.2) =
        {p : ℝ × Space 2 | p.1 ^ 2 + ‖p.2‖ ^ 2 < R ^ 2}.indicator (fun p => h p.1) := by
      funext p
      rfl
    rw [hform, ← Measure.volume_eq_prod]
    refine Integrable.mono' (g := K.indicator (fun _ => M)) ?_ ?_ ?_
    · exact (integrable_indicator_iff hKc.measurableSet).mpr
        (integrableOn_const hKc.measure_lt_top.ne)
    · exact ((hh.comp continuous_fst).aestronglyMeasurable).indicator hT
    · have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨neg_nonpos.mpr hR.le, hR.le⟩)
      refine Filter.Eventually.of_forall fun p => ?_
      by_cases hp : p ∈ {p : ℝ × Space 2 | p.1 ^ 2 + ‖p.2‖ ^ 2 < R ^ 2}
      · have hp' : p.1 ^ 2 + ‖p.2‖ ^ 2 < R ^ 2 := hp
        have h1 : p.1 ^ 2 < R ^ 2 := by nlinarith [sq_nonneg ‖p.2‖]
        have h2 : ‖p.2‖ ^ 2 < R ^ 2 := by nlinarith [sq_nonneg p.1]
        obtain ⟨hl, hr⟩ := abs_lt_of_sq_lt_sq' h1 hR.le
        have h3 : ‖p.2‖ < R := lt_of_pow_lt_pow_left₀ 2 hR.le h2
        have hpK : p ∈ K := ⟨⟨hl.le, hr.le⟩, by rw [mem_closedBall_zero_iff]; exact h3.le⟩
        rw [Set.indicator_of_mem hp, Set.indicator_of_mem hpK]
        exact hM p.1 ⟨hl.le, hr.le⟩
      · rw [Set.indicator_of_notMem hp, norm_zero]
        exact Set.indicator_nonneg (fun _ _ => hM0) p
  rw [Measure.volume_eq_prod, integral_prod _ hint]
  have hinner : ∀ z : ℝ, ∫ y : Space 2,
      {y' : Space 2 | z ^ 2 + ‖y'‖ ^ 2 < R ^ 2}.indicator (fun _ => h z) y =
      ((Set.Ioo (-R) R).indicator
        (fun z => (Real.pi * (R ^ 2 - z ^ 2)) • h z)) z := by
    intro z
    have hms : MeasurableSet {y' : Space 2 | z ^ 2 + ‖y'‖ ^ 2 < R ^ 2} :=
      measurableSet_lt (by fun_prop) measurable_const
    rw [integral_indicator_const _ hms]
    have hvol : (volume {y' : Space 2 | z ^ 2 + ‖y'‖ ^ 2 < R ^ 2}).toReal =
        max (Real.pi * (R ^ 2 - z ^ 2)) 0 := by
      rw [slab_section_volume, ENNReal.toReal_ofReal']
    change (volume {y' : Space 2 | z ^ 2 + ‖y'‖ ^ 2 < R ^ 2}).toReal • h z = _
    rw [hvol]
    by_cases hz : z ∈ Set.Ioo (-R) R
    · have hpos : 0 ≤ Real.pi * (R ^ 2 - z ^ 2) := by
        have := Real.pi_pos
        have : z ^ 2 < R ^ 2 := by nlinarith [hz.1, hz.2]
        nlinarith
      rw [Set.indicator_of_mem hz, max_eq_left hpos]
    · have hneg : Real.pi * (R ^ 2 - z ^ 2) ≤ 0 := by
        have := Real.pi_pos
        have : R ^ 2 ≤ z ^ 2 := by
          by_contra hc
          push Not at hc
          exact hz ⟨by nlinarith [abs_lt.mp (abs_lt_of_sq_lt_sq hc hR.le)], by
            nlinarith [abs_lt.mp (abs_lt_of_sq_lt_sq hc hR.le)]⟩
        nlinarith
      rw [Set.indicator_of_notMem hz, max_eq_right hneg, zero_smul]
  simp_rw [hinner]
  rw [integral_indicator measurableSet_Ioo]

/-! ## C. Polar coordinates on the ball -/

/-- The unit sphere of `Space 3` with its surface measure. -/
abbrev Sph := ↑(Metric.sphere (0 : Space 3) 1)

/-- The surface measure on the unit sphere, normalized so that the total mass is `4 π`. -/
noncomputable abbrev sphereMeasure : Measure Sph := (volume : Measure (Space 3)).toSphere

lemma integrable_ball_indicator_coord {F : Type*} [NormedAddCommGroup F]
    (i : Fin 3) {h : ℝ → F} (hh : Continuous h) (R : ℝ) :
    Integrable ((Metric.ball (0 : Space 3) R).indicator (fun x => h (x i))) volume := by
  rw [integrable_indicator_iff measurableSet_ball]
  have hc : Continuous fun x : Space 3 => h (x i) := hh.comp (Space.eval_continuous i)
  exact (hc.continuousOn.integrableOn_compact (isCompact_closedBall 0 R)).mono_set
    Metric.ball_subset_closedBall

lemma ball_integral_polar {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (i : Fin 3) {h : ℝ → F} (hh : Continuous h) {R : ℝ} :
    ∫ x in Metric.ball (0 : Space 3) R, h (x i) =
      ∫ n : Sph, ∫ r in Set.Ioo 0 R, r ^ 2 • h (r * (n.1 i)) ∂volume ∂sphereMeasure := by
  rw [← integral_indicator measurableSet_ball,
    Space.integral_volume_eq_spherical_integral _ (integrable_ball_indicator_coord i hh R)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
  have hfr : Module.finrank ℝ (Space 3) - 1 = 2 := by
    rw [Space.finrank_eq_dim]
  simp only []
  have h1 := integral_subtype_comap (μ := (volume : Measure ℝ)) (measurableSet_Ioi (a := (0 : ℝ)))
    (fun r : ℝ => r ^ 2 • (Metric.ball (0 : Space 3) R).indicator (fun x => h (x i)) (r • n.1))
  refine h1.trans ?_
  have h2 : ∀ r ∈ Set.Ioi (0 : ℝ), r ^ 2 • (Metric.ball (0 : Space 3) R).indicator
      (fun x => h (x i)) (r • n.1) =
      (Set.Iio R).indicator (fun r : ℝ => r ^ 2 • h (r * (n.1 i))) r := by
    intro r hr
    have hr0 : (0 : ℝ) < r := hr
    have hn : ‖n.1‖ = 1 := by simp
    have hmem : r • n.1 ∈ Metric.ball (0 : Space 3) R ↔ r < R := by
      rw [mem_ball_zero_iff, norm_smul, hn, Real.norm_eq_abs, abs_of_pos hr0, mul_one]
    by_cases hrR : r < R
    · rw [Set.indicator_of_mem ((hmem.mpr hrR)), Set.indicator_of_mem (show r ∈ Set.Iio R from hrR)]
      simp
    · rw [Set.indicator_of_notMem (fun hx => hrR (hmem.mp hx)),
        Set.indicator_of_notMem (show r ∉ Set.Iio R from hrR)]
      simp
  rw [setIntegral_congr_fun measurableSet_Ioi h2, setIntegral_indicator measurableSet_Iio,
    Set.Ioi_inter_Iio]

/-! ## D. Polar coordinates for general integrands -/

/-- A continuous function has an integrable restriction to a ball. -/
lemma integrable_ball_indicator {F : Type*} [NormedAddCommGroup F]
    {g : Space 3 → F} (hg : Continuous g) (R : ℝ) :
    Integrable ((Metric.ball (0 : Space 3) R).indicator g) volume := by
  rw [integrable_indicator_iff measurableSet_ball]
  exact (hg.continuousOn.integrableOn_compact (isCompact_closedBall 0 R)).mono_set
    Metric.ball_subset_closedBall

/-- `‖z‖⁻¹` times a continuous function is integrable on a ball of `Space 3`. -/
lemma integrable_inv_norm_mul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : Space 3 → F} (hk : Continuous k) (R : ℝ) :
    Integrable ((Metric.ball (0 : Space 3) R).indicator (fun z => (‖z‖⁻¹ : ℝ) • k z)) volume := by
  rw [integrable_indicator_iff measurableSet_ball]
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Space 3) R).exists_bound_of_continuousOn
    hk.continuousOn
  refine integrableOn_ball_of_norm_le_rpow (E := Space 3) (F := F) (f := fun z : Space 3 => (‖z‖⁻¹ :
    ℝ) • k z) (μ := (volume : Measure (Space 3))) (C := C) (α := 1) (r := R) ?_ ?_ ?_ ?_
  · rw [Space.finrank_eq_dim]; norm_num
  · rw [Space.finrank_eq_dim]; norm_num
  · rw [ae_restrict_iff' measurableSet_ball]
    refine Filter.Eventually.of_forall fun z hz => ?_
    have hz' : z ∈ Metric.closedBall (0 : Space 3) R := Metric.ball_subset_closedBall hz
    rw [norm_smul, norm_inv, norm_norm, Real.rpow_neg_one, mul_comm]
    exact mul_le_mul_of_nonneg_right (hC z hz') (inv_nonneg.mpr (norm_nonneg _))
  · exact (continuous_norm.measurable.inv).aestronglyMeasurable.smul hk.aestronglyMeasurable

/-- Polar coordinates on a ball for a general continuous integrand. -/
lemma ball_integral_polar_general {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : Space 3 → F} {R : ℝ}
    (hg : Integrable ((Metric.ball (0 : Space 3) R).indicator g) volume) :
    ∫ y in Metric.ball (0 : Space 3) R, g y =
      ∫ n : Sph, ∫ r in Set.Ioo 0 R, r ^ 2 • g (r • n.1) ∂volume ∂sphereMeasure := by
  rw [← integral_indicator measurableSet_ball,
    Space.integral_volume_eq_spherical_integral _ hg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
  have hfr : Module.finrank ℝ (Space 3) - 1 = 2 := by
    rw [Space.finrank_eq_dim]
  simp only []
  have h1 := integral_subtype_comap (μ := (volume : Measure ℝ)) (measurableSet_Ioi (a := (0 : ℝ)))
    (fun r : ℝ => r ^ 2 • (Metric.ball (0 : Space 3) R).indicator g (r • n.1))
  refine h1.trans ?_
  have h2 : ∀ r ∈ Set.Ioi (0 : ℝ), r ^ 2 • (Metric.ball (0 : Space 3) R).indicator g (r • n.1) =
      (Set.Iio R).indicator (fun r : ℝ => r ^ 2 • g (r • n.1)) r := by
    intro r hr
    have hr0 : (0 : ℝ) < r := hr
    have hn : ‖n.1‖ = 1 := by simp
    have hmem : r • n.1 ∈ Metric.ball (0 : Space 3) R ↔ r < R := by
      rw [mem_ball_zero_iff, norm_smul, hn, Real.norm_eq_abs, abs_of_pos hr0, mul_one]
    by_cases hrR : r < R
    · rw [Set.indicator_of_mem ((hmem.mpr hrR)), Set.indicator_of_mem (show r ∈ Set.Iio R from hrR)]
    · rw [Set.indicator_of_notMem (fun hx => hrR (hmem.mp hx)),
        Set.indicator_of_notMem (show r ∉ Set.Iio R from hrR)]
      simp
  rw [setIntegral_congr_fun measurableSet_Ioi h2, setIntegral_indicator measurableSet_Iio,
    Set.Ioi_inter_Iio]

/-- Translation of a ball integral to the origin. -/
lemma setIntegral_ball_translate {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : Space 3 → F) (x : Space 3) (R : ℝ) :
    ∫ y in Metric.ball x R, G y = ∫ z in Metric.ball (0 : Space 3) R, G (x + z) := by
  rw [← integral_indicator measurableSet_ball, ← integral_indicator measurableSet_ball]
  rw [← integral_add_left_eq_self (μ := (volume : Measure (Space 3)))
    (fun y => (Metric.ball x R).indicator G y) x]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  show _ = (Metric.ball (0 : Space 3) R).indicator (fun z => G (x + z)) z
  by_cases hz : z ∈ Metric.ball (0 : Space 3) R
  · have : x + z ∈ Metric.ball x R := by simpa using hz
    rw [Set.indicator_of_mem hz]
    exact Set.indicator_of_mem this G
  · have : x + z ∉ Metric.ball x R := by simpa using hz
    rw [Set.indicator_of_notMem hz]
    exact Set.indicator_of_notMem this G

end Sphere3
