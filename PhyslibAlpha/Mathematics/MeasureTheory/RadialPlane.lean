/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!

# The integral of a radial function over the plane

Integrating a radial function over two extra variables gives the tail integral of its profile.

## i. Overview

For a radial function with profile `Φ` the integral over the plane at distance `ρ` is
`∫ Φ (√(ρ² + |y|²)) dy`. In polar coordinates this is `2π ∫ s Φ (√(ρ² + s²)) ds`. The substitution
`u = √(ρ² + s²)` turns it into `2π ∫_{u > ρ} u Φ (u) du`. The tail integral has the derivative
`-ρ Φ (ρ)`.

## ii. Key results

- `RadialPlane.integral_plane_radial` : the integral of a radial function over the plane.
- `RadialPlane.hasDerivAt_tail` : the derivative of the tail integral.

## iii. Table of contents

- A. The plane integral
- B. The tail integral

## iv. References

None.

## A. The plane integral

- `RadialPlane.integral_plane_radial` : the integral of a radial function over the plane.

## B. The tail integral

- `RadialPlane.hasDerivAt_tail` : the derivative of the tail integral.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology

namespace RadialPlane

/-- The decay of the profile used in the radial estimates. -/
def RadialDecay (Φ : ℝ → ℂ) : Prop :=
  Continuous Φ ∧ ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u → ‖Φ u‖ ≤ C * (1 + u) ^ (-(3 : ℝ))

/-- A bound for the profile times the radius. -/
lemma radial_bound {Φ : ℝ → ℂ} {C : ℝ} (hC : ∀ u : ℝ, 0 ≤ u → ‖Φ u‖ ≤ C * (1 + u) ^ (-(3 : ℝ)))
    {x u : ℝ} (hx : 0 ≤ x) (hxu : x ≤ u) : ‖x • Φ u‖ ≤ |C| * (1 + ‖x‖) ^ (-(2 : ℝ)) := by
  have hu : 0 ≤ u := hx.trans hxu
  have h1 := hC u hu
  have hx1 : (0 : ℝ) < 1 + x := by linarith
  have hCa : C ≤ |C| := le_abs_self C
  have hpow : (1 + u) ^ (-(3 : ℝ)) ≤ (1 + x) ^ (-(3 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hx1 (by linarith) (by norm_num)
  rw [Real.norm_of_nonneg hx, norm_smul, Real.norm_of_nonneg hx]
  have hC0 : 0 ≤ C := by
    have := norm_nonneg (Φ u)
    have hp : 0 < (1 + u) ^ (-(3 : ℝ)) := by positivity
    by_contra hneg
    nlinarith
  calc x * ‖Φ u‖ ≤ x * (C * (1 + u) ^ (-(3 : ℝ))) := by gcongr
    _ ≤ x * (|C| * (1 + x) ^ (-(3 : ℝ))) := by gcongr
    _ ≤ (1 + x) * (|C| * (1 + x) ^ (-(3 : ℝ))) := by gcongr; linarith
    _ = |C| * (1 + x) ^ (-(2 : ℝ)) := by
      have : (1 + x) ^ (-(2 : ℝ)) = (1 + x) * (1 + x) ^ (-(3 : ℝ)) := by
        rw [← Real.rpow_one_add' hx1.le (by norm_num)]
        norm_num
      rw [this]; ring

/-- **The integral of a radial function over the plane.** -/
lemma integral_plane_radial {Φ : ℝ → ℂ} (hΦ : RadialDecay Φ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∫ y : EuclideanSpace ℝ (Fin 2), Φ (Real.sqrt (ρ ^ 2 + ‖y‖ ^ 2)) =
      (2 * Real.pi : ℝ) • ∫ u in Ioi ρ, u • Φ u := by
  obtain ⟨hc, C, hC⟩ := hΦ
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := by simp
  have hvol : (volume : Measure (EuclideanSpace ℝ (Fin 2))).real (Metric.ball 0 1) = Real.pi := by
    rw [Measure.real, EuclideanSpace.volume_ball_fin_two]
    simp [Real.pi_nonneg]
  have h1 := integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin 2)))
    (fun s : ℝ => Φ (Real.sqrt (ρ ^ 2 + s ^ 2)))
  rw [hdim, hvol] at h1
  simp only [nsmul_eq_mul, Nat.cast_ofNat] at h1
  set R : ℝ → ℝ := fun s => Real.sqrt (ρ ^ 2 + s ^ 2) with hR
  have hRpos : ∀ s, ρ ≤ R s := fun s => by
    rw [hR]
    exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg s])
  have hRs : ∀ s, 0 ≤ s → s ≤ R s := fun s hs => by
    rw [hR]
    exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ρ])
  have hRne : ∀ s, R s ≠ 0 := fun s => (lt_of_lt_of_le hρ (hRpos s)).ne'
  have hRd : ∀ x, HasDerivAt R (x / R x) x := fun x => by
    have hq : HasDerivAt (fun x : ℝ => ρ ^ 2 + x ^ 2) (2 * x) x := by
      have := (hasDerivAt_pow 2 x).const_add (ρ ^ 2)
      simpa using this
    have h := HasDerivAt.sqrt hq (by positivity)
    have hRx := hRne x
    convert h using 1
    rw [hR]
    simp only
    have : Real.sqrt (ρ ^ 2 + x ^ 2) ≠ 0 := hRx
    field_simp
  have hint2 : Integrable (fun u : ℝ => (1 + ‖u‖) ^ (-(2 : ℝ))) := by
    refine integrable_one_add_norm (E := ℝ) ?_
    simp
  have hbound : ∀ x u : ℝ, 0 ≤ x → x ≤ u → ‖x • Φ u‖ ≤ |C| * (1 + ‖x‖) ^ (-(2 : ℝ)) :=
    fun x u hx hxu => radial_bound hC hx hxu
  have hsub : ∫ s in Ioi (0 : ℝ), s • Φ (R s) = ∫ u in Ioi ρ, u • Φ u := by
    have h := integral_deriv_smul_comp_Ioi (f := R) (f' := fun x => x / R x)
      (g := fun u : ℝ => u • Φ u) (a := 0) ?_ ?_ ?_ ?_ ?_ ?_
    · have e : R 0 = ρ := by rw [hR]; simp [Real.sqrt_sq hρ.le]
      rw [e] at h
      rw [← h]
      refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
      simp only [Function.comp_apply, Complex.real_smul]
      have := hRne x
      have hc' : (R x : ℂ) ≠ 0 := by exact_mod_cast this
      push_cast
      field_simp
    · exact (continuous_iff_continuousAt.2 fun x => (hRd x).continuousAt).continuousOn
    · exact tendsto_atTop_mono' atTop
        (eventually_of_mem (Ici_mem_atTop 0) fun s hs => hRs s hs) tendsto_id
    · exact fun x _ => (hRd x).hasDerivWithinAt
    · exact (continuous_id.smul hc).continuousOn
    · have hsub' : R '' Ici 0 ⊆ Ici ρ := by
        rintro _ ⟨s, -, rfl⟩
        exact hRpos s
      refine IntegrableOn.mono_set ?_ hsub'
      refine Integrable.mono' (hint2.integrableOn.const_mul |C|)
        (continuous_id.smul hc).aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
      exact hbound u u (hρ.le.trans hu) le_rfl
    · have hfun : (fun x : ℝ => (x / R x) • ((fun u : ℝ => u • Φ u) ∘ R) x) =
          fun x => x • Φ (R x) := by
        funext x
        have := hRne x
        have hc' : (R x : ℂ) ≠ 0 := by exact_mod_cast this
        simp only [Function.comp_apply, Complex.real_smul]
        push_cast
        field_simp
      rw [hfun]
      refine Integrable.mono' (hint2.integrableOn.const_mul |C|)
        ((continuous_id.smul (hc.comp (continuous_iff_continuousAt.2
          fun x => (hRd x).continuousAt))).aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
      exact hbound x (R x) hx (hRs x hx)
  have e : ∫ y in Ioi (0 : ℝ), y ^ (2 - 1) • Φ (Real.sqrt (ρ ^ 2 + y ^ 2)) =
      ∫ s in Ioi (0 : ℝ), s • Φ (R s) := by
    simp [hR]
  rw [h1, e, hsub]
  simp only [Complex.real_smul]
  push_cast
  ring

/-- The profile times the radius is integrable on a half line. -/
lemma integrableOn_radial {Φ : ℝ → ℂ} (hΦ : RadialDecay Φ) {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun u : ℝ => u • Φ u) (Ioi a) := by
  obtain ⟨hc, C, hC⟩ := hΦ
  have hint2 : Integrable (fun u : ℝ => (1 + ‖u‖) ^ (-(2 : ℝ))) := by
    refine integrable_one_add_norm (E := ℝ) ?_
    simp
  refine Integrable.mono' (hint2.integrableOn.const_mul |C|)
    (continuous_id.smul hc).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact radial_bound hC (ha.trans (le_of_lt hu)) le_rfl

/-- **The derivative of the tail integral.** -/
lemma hasDerivAt_tail {Φ : ℝ → ℂ} (hΦ : RadialDecay Φ) {ρ : ℝ} (hρ : 0 < ρ) :
    HasDerivAt (fun r : ℝ => ∫ u in Ioi r, u • Φ u) (-(ρ • Φ ρ)) ρ := by
  have hint := integrableOn_radial hΦ (half_pos hρ).le
  have hcont : Continuous fun u : ℝ => u • Φ u := continuous_id.smul hΦ.1
  have h1 : HasDerivAt (fun r : ℝ => ∫ u in (ρ / 2)..r, u • Φ u) (ρ • Φ ρ) ρ :=
    intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable _ _)
      (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt
  have h2 := h1.const_sub (∫ u in Ioi (ρ / 2), u • Φ u)
  refine h2.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds (half_lt_self hρ)] with r hr
  rw [← intervalIntegral.integral_Ioi_sub_Ioi hint (le_of_lt hr)]
  ring

/-- A continuous profile that vanishes beyond some radius has the radial decay. -/
lemma radialDecay_of_vanishing {Φ : ℝ → ℂ} (hc : Continuous Φ) {S : ℝ}
    (h : ∀ u, S < u → Φ u = 0) : RadialDecay Φ := by
  refine ⟨hc, ?_⟩
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -|S|) (b := |S|)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max M 0 * (1 + |S|) ^ 3, fun u hu => ?_⟩
  by_cases huS : u ≤ S
  · have hu1 : u ∈ Icc (-|S|) |S| := ⟨by linarith [abs_nonneg S, neg_abs_le S], by
      linarith [le_abs_self S]⟩
    have h1 := hM u hu1
    have hpos : 0 < (1 + u) := by linarith
    have hS0 : 0 ≤ |S| := abs_nonneg S
    rw [Real.rpow_neg hpos.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    have : (1 + u) ^ 3 ≤ (1 + |S|) ^ 3 := by
      gcongr
      exact huS.trans (le_abs_self S)
    calc ‖Φ u‖ * (1 + u) ^ 3 ≤ max M 0 * (1 + |S|) ^ 3 := by
          gcongr
          exact h1.trans (le_max_left _ _)
      _ = _ := by ring
  · rw [h u (not_le.1 huS), norm_zero]
    positivity

/-- **The integral of a radial function over the plane at the origin.** -/
lemma integral_plane_radial_zero (Φ : ℝ → ℂ) :
    ∫ y : EuclideanSpace ℝ (Fin 2), Φ ‖y‖ = (2 * Real.pi : ℝ) • ∫ u in Ioi (0 : ℝ), u • Φ u := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := by simp
  have hvol : (volume : Measure (EuclideanSpace ℝ (Fin 2))).real (Metric.ball 0 1) = Real.pi := by
    rw [Measure.real, EuclideanSpace.volume_ball_fin_two]
    simp [Real.pi_nonneg]
  have h1 := integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin 2))) Φ
  rw [hdim, hvol] at h1
  simp only [nsmul_eq_mul, Nat.cast_ofNat] at h1
  rw [h1]
  simp only [Complex.real_smul]
  push_cast
  simp only [pow_one]
  ring

end RadialPlane
