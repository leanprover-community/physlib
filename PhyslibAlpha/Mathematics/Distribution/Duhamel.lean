/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Mathematics.Distribution.TimeSlice

/-!

# The Duhamel integral of Fourier multiplied slices

The slice of a source at each time is propagated by a Fourier multiplier.

## i. Overview

The slice of a source at each time is propagated by a Fourier multiplier. The Duhamel integral adds
the contributions of all earlier times.

## ii. Key results

- `propagatedSlice` : The spatial Fourier propagation of the slice `f(s, ·)` by a multiplier family
  `m` over the time `r`, evaluated at the position `x`.
- `duhamel` : The retarded Duhamel integral of the sources `f` for a multiplier family `m`: the
  source at the time `s` is propagated over the time `t - s` and summed over `s ≤ t`.
- `continuous_propagatedSlice` : The propagated slices are jointly continuous in the propagation
  time, the source time and the position, for every multiplier family that is jointly continuous and
  locally bounded in time.
- `duhamel_eq_integral_fourier` : The Duhamel integral is the inverse Fourier integral of the
  per-frequency Duhamel integral of the Fourier transformed slices.

## iii. Table of contents

- A. The Duhamel integral of Fourier multiplied slices

## iv. References

None.

## A. The Duhamel integral of Fourier multiplied slices

- `propagatedSlice` : The spatial Fourier propagation of the slice `f(s, ·)` by a multiplier family
  `m` over the time `r`, evaluated at the position `x`.
- `duhamel` : The retarded Duhamel integral of the sources `f` for a multiplier family `m`: the
  source at the time `s` is propagated over the time `t - s` and summed over `s ≤ t`.

Lemmas: `continuous_propagatedSlice`, `propagatedSlice_eq_zero_of_notMem`, `integrable_duhamel`,
`exists_timeBound`, `duhamel_eq_intervalIntegral`, `duhamel_eq_integral_fourier`.

-/

@[expose] public section

noncomputable section

open scoped FourierTransform Distributions
open TimeSlice TopologicalSpace Topology

namespace Duhamel

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F]
variable (f : 𝓓((⊤ : Opens (ℝ × E)), F))

/-- The spatial Fourier propagation of the slice `f(s, ·)` by a multiplier family `m` over the
time `r`, evaluated at the position `x`. It is independent of the equation: the equation only
enters through the multiplier family. -/
def propagatedSlice (m : ℝ → E → ℂ) (r s : ℝ) (x : E) : F :=
  ∫ ξ : E, 𝐞 (inner ℝ ξ x) • (m r ξ • 𝓕 (slice F f s) ξ)

omit [CompleteSpace F] in
/-- The propagated slices are jointly continuous in the propagation time, the source time and the
position, for every multiplier family that is jointly continuous and locally bounded in time. -/
lemma continuous_propagatedSlice (m : ℝ → E → ℂ)
    (hm : Continuous fun p : ℝ × E => m p.1 p.2)
    (hb : ∀ R : ℝ, ∃ B : ℝ, ∀ r ξ, |r| ≤ R → ‖m r ξ‖ ≤ B) :
    Continuous fun q : ℝ × ℝ × E => propagatedSlice F f m q.1 q.2.1 q.2.2 := by
  unfold propagatedSlice
  refine continuous_iff_continuousAt.2 fun q₀ => ?_
  set N := Module.finrank ℝ E + 1
  obtain ⟨K, hK⟩ := exists_fourier_decay F f
  obtain ⟨B, hB⟩ := hb (|q₀.1| + 1)
  refine MeasureTheory.continuousAt_of_dominated
    (bound := fun ξ => |B| * (|K| * (1 + ‖ξ‖) ^ (-(N : ℝ)))) ?_ ?_ ?_ ?_
  · refine Filter.Eventually.of_forall fun q => Continuous.aestronglyMeasurable ?_
    have h1 : Continuous fun ξ : E => m q.1 ξ :=
      hm.comp (continuous_const.prodMk continuous_id)
    have h2 : Continuous fun ξ : E => 𝓕 (slice F f q.2.1) ξ := (𝓕 (slice F f q.2.1)).continuous
    exact (Real.continuous_fourierChar.comp
      (continuous_id.inner continuous_const)).smul (h1.smul h2)
  · have : ∀ᶠ q in nhds q₀, |q.1| ≤ |q₀.1| + 1 := by
      have hc : Continuous fun q : ℝ × ℝ × E => |q.1| := continuous_fst.abs
      exact (hc.continuousAt.eventually (gt_mem_nhds (by linarith : |q₀.1| < |q₀.1| + 1))).mono
        fun q hq => hq.le
    filter_upwards [this] with q hq
    refine Filter.Eventually.of_forall fun ξ => ?_
    rw [Circle.norm_smul, norm_smul]
    have hpos : 0 ≤ (1 + ‖ξ‖) ^ (-(N : ℝ)) := by positivity
    exact mul_le_mul ((hB _ _ hq).trans (le_abs_self _))
      ((hK _ _).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hpos)) (norm_nonneg _)
      (abs_nonneg _)
  · exact ((integrable_one_add_norm (E := E) (r := (N : ℝ)) (by simp [N])).const_mul _).const_mul _
  · refine Filter.Eventually.of_forall fun ξ => ?_
    have h1 : Continuous fun q : ℝ × ℝ × E => m q.1 ξ :=
      (hm.comp (continuous_id.prodMk continuous_const) :
        Continuous fun r : ℝ => m r ξ).comp continuous_fst
    have h2 : Continuous fun q : ℝ × ℝ × E => 𝓕 (slice F f q.2.1) ξ :=
      (continuous_fourier_slice F f).comp
        ((continuous_fst.comp continuous_snd).prodMk (continuous_const (y := ξ)))
    exact ((Real.continuous_fourierChar.comp
      (continuous_const.inner (continuous_snd.comp continuous_snd))).smul (h1.smul h2)).continuousAt

omit [CompleteSpace F] in
lemma propagatedSlice_eq_zero_of_notMem (m : ℝ → E → ℂ) (r : ℝ) {s : ℝ}
    (hs : s ∉ Prod.fst '' tsupport f) (x : E) : propagatedSlice F f m r s x = 0 := by
  simp [propagatedSlice, slice_eq_zero_of_notMem F f hs]

/-- The retarded Duhamel integral of the sources `f` for a multiplier family `m`:
the source at the time `s` is propagated over the time `t - s` and summed over `s ≤ t`. -/
def duhamel (m : ℝ → E → ℂ) (t : ℝ) (x : E) : F :=
  ∫ s in Set.Iic t, propagatedSlice F f m (t - s) s x

omit [CompleteSpace F] in
/-- The integrand of the Duhamel integral is integrable. -/
lemma integrable_duhamel (m : ℝ → E → ℂ)
    (hm : Continuous fun p : ℝ × E => m p.1 p.2)
    (hb : ∀ R : ℝ, ∃ B : ℝ, ∀ r ξ, |r| ≤ R → ‖m r ξ‖ ≤ B) (t : ℝ) (x : E) :
    MeasureTheory.Integrable fun s : ℝ => propagatedSlice F f m (t - s) s x := by
  have hc : Continuous fun s : ℝ => propagatedSlice F f m (t - s) s x :=
    (continuous_propagatedSlice F f m hm hb).comp
      ((continuous_const.sub continuous_id).prodMk (continuous_id.prodMk continuous_const))
  refine hc.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_timeSupport F f) fun s hs => ?_
  exact propagatedSlice_eq_zero_of_notMem F f m _ hs x

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] in
/-- A time strictly before the support of the source. -/
lemma exists_timeBound : ∃ a : ℝ, ∀ s ≤ a, s ∉ Prod.fst '' tsupport f := by
  obtain ⟨a, ha⟩ := (isCompact_timeSupport F f).bddBelow
  exact ⟨a - 1, fun s hs hmem => by linarith [ha hmem]⟩

omit [CompleteSpace F] in
/-- The Duhamel integral starts at any time before the support of the source. -/
lemma duhamel_eq_intervalIntegral (m : ℝ → E → ℂ) {a : ℝ}
    (ha : ∀ s ≤ a, s ∉ Prod.fst '' tsupport f) {t : ℝ} (hat : a ≤ t) (x : E) :
    duhamel F f m t x = ∫ s in a..t, propagatedSlice F f m (t - s) s x := by
  rw [duhamel, intervalIntegral.integral_of_le hat]
  refine MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Iic
    Set.Ioc_subset_Iic_self fun s hs => ?_
  have : s ≤ a := by
    by_contra h
    exact hs.2 (Set.mem_Ioc.2 ⟨not_le.1 h, hs.1⟩)
  exact propagatedSlice_eq_zero_of_notMem F f m _ (ha s this) x

omit [CompleteSpace F] in
/-- The Duhamel integral is the inverse Fourier integral of the per-frequency Duhamel integral
of the Fourier transformed slices. -/
lemma duhamel_eq_integral_fourier (m : ℝ → E → ℂ)
    (hm : Continuous fun p : ℝ × E => m p.1 p.2)
    (hb : ∀ R : ℝ, ∃ B : ℝ, ∀ r ξ, |r| ≤ R → ‖m r ξ‖ ≤ B) {a : ℝ}
    (ha : ∀ s ≤ a, s ∉ Prod.fst '' tsupport f) {t : ℝ} (hat : a ≤ t) (x : E) :
    duhamel F f m t x =
      ∫ ξ : E, 𝐞 (inner ℝ ξ x) • ∫ s in a..t, m (t - s) ξ • 𝓕 (slice F f s) ξ := by
  rw [duhamel_eq_intervalIntegral F f m ha hat x]
  unfold propagatedSlice
  set N := Module.finrank ℝ E + 1
  obtain ⟨K, hK⟩ := exists_fourier_decay F f
  obtain ⟨B, hB⟩ := hb |t - a|
  have hint : MeasureTheory.Integrable
      (Function.uncurry fun (s : ℝ) (ξ : E) => 𝐞 (inner ℝ ξ x) • (m (t - s) ξ • 𝓕 (slice F f s) ξ))
      ((MeasureTheory.volume.restrict (Set.uIoc a t)).prod MeasureTheory.volume) := by
    rw [Set.uIoc_of_le hat]
    have hg : MeasureTheory.Integrable (fun ξ : E => |B| * (|K| * (1 + ‖ξ‖) ^ (-(N : ℝ))))
        MeasureTheory.volume :=
      ((integrable_one_add_norm (E := E) (r := (N : ℝ)) (by simp [N])).const_mul _).const_mul _
    refine (hg.comp_snd (MeasureTheory.volume.restrict (Set.Ioc a t))).mono' ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      have h1 : Continuous fun p : ℝ × E => m (t - p.1) p.2 :=
        hm.comp ((continuous_const.sub continuous_fst).prodMk continuous_snd)
      have h2 : Continuous fun p : ℝ × E => 𝓕 (slice F f p.1) p.2 :=
        continuous_fourier_slice F f
      have h3 : Continuous fun p : ℝ × E => (inner ℝ p.2 x : ℝ) :=
        continuous_snd.inner continuous_const
      exact (Real.continuous_fourierChar.comp h3).smul (h1.smul h2)
    · have hS : ∀ᵐ s ∂MeasureTheory.volume.restrict (Set.Ioc a t), s ∈ Set.Ioc a t :=
        MeasureTheory.ae_restrict_mem measurableSet_Ioc
      have h1 : Continuous fun p : ℝ × E => m (t - p.1) p.2 :=
        hm.comp ((continuous_const.sub continuous_fst).prodMk continuous_snd)
      have h2 : Continuous fun p : ℝ × E => 𝓕 (slice F f p.1) p.2 :=
        continuous_fourier_slice F f
      have h3 : Continuous fun p : ℝ × E => (inner ℝ p.2 x : ℝ) :=
        continuous_snd.inner continuous_const
      have hcont : Continuous fun p : ℝ × E =>
          ‖𝐞 (inner ℝ p.2 x) • (m (t - p.1) p.2 • 𝓕 (slice F f p.1) p.2)‖ :=
        ((Real.continuous_fourierChar.comp h3).smul (h1.smul h2)).norm
      have hcont2 : Continuous fun p : ℝ × E =>
          |B| * (|K| * (1 + ‖p.2‖) ^ (-(N : ℝ))) :=
        continuous_const.mul (continuous_const.mul
          ((continuous_const.add continuous_snd.norm).rpow_const fun p =>
            Or.inl (add_pos_of_pos_of_nonneg one_pos (norm_nonneg p.2)).ne'))
      have hms : MeasurableSet {p : ℝ × E |
          ‖𝐞 (inner ℝ p.2 x) • (m (t - p.1) p.2 • 𝓕 (slice F f p.1) p.2)‖ ≤
            |B| * (|K| * (1 + ‖p.2‖) ^ (-(N : ℝ)))} :=
        measurableSet_le hcont.measurable hcont2.measurable
      refine (MeasureTheory.Measure.ae_prod_iff_ae_ae hms).2 ?_
      filter_upwards [hS] with s hs
      refine Filter.Eventually.of_forall fun ξ => ?_
      show ‖𝐞 (inner ℝ ξ x) • (m (t - s) ξ • 𝓕 (slice F f s) ξ)‖ ≤ _
      rw [Circle.norm_smul, norm_smul]
      have hts : |t - s| ≤ |t - a| := by
        rw [abs_of_nonneg (by linarith [hs.2]), abs_of_nonneg (by linarith)]
        linarith [hs.1]
      have hpos : 0 ≤ (1 + ‖ξ‖) ^ (-(N : ℝ)) := by positivity
      exact mul_le_mul ((hB _ _ hts).trans (le_abs_self _))
        ((hK _ _).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hpos)) (norm_nonneg _)
        (abs_nonneg _)
  rw [MeasureTheory.intervalIntegral_integral_swap hint]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [Circle.smul_def]
  exact intervalIntegral.integral_smul _ _
end

end Duhamel
