/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.FreeEvolution
public import PhyslibAlpha.Mathematics.Distribution.Duhamel
public import PhyslibAlpha.Mathematics.Distribution.TimeSliceSmooth
public import PhyslibAlpha.Mathematics.SpecialFunctions.SincPropagator.Oscillator

/-!

# The retarded and advanced solution

The retarded solution of a test function source is the Duhamel integral of the sine evolution.

## i. Overview

The retarded solution of a test function source is the Duhamel integral of the sine evolution. It
solves the equation and is linear in the source.

## ii. Key results

- `sourceHat` : The Fourier transform of the source at the frequency `ξ`, as a function of the time.
- `freqSolution` : The retarded solution at the spatial frequency `ξ`, with zero data at the time
  `a`.
- `freqSolution1` : The time derivative of the per-frequency solution.
- `solution` : The retarded solution of the Klein–Gordon equation with the source `f`.
- `advancedSolution` : The advanced solution: the retarded solution of the time-reflected source,
  reflected back.
- `testOperator` : The Klein–Gordon operator `∂ₜ² - Δ + μ` on compact spacetime test fields.

## iii. Table of contents

- A. The retarded Klein–Gordon solution of a test-function source
- B. Causal support of the retarded solution
- C. The two-sided Klein–Gordon inverse on compact test fields

## iv. References

None.

## A. The retarded Klein–Gordon solution of a test-function source

- `sourceHat` : The Fourier transform of the source at the frequency `ξ`, as a function of the time.
- `freqSolution` : The retarded solution at the spatial frequency `ξ`, with zero data at the time
  `a`.
- `freqSolution1` : The time derivative of the per-frequency solution.
- `solution` : The retarded solution of the Klein–Gordon equation with the source `f`.

Lemmas: `continuous_sourceHat`, `freqSolution_eq`, `hasDerivAt_freqSolution`,
`hasDerivAt_freqSolution1`, `norm_freqSolution1_le`, `norm_freqSolution_le`,
`continuous_freqSolution_xi`, `continuous_freqSolution1_xi`, `hasDerivAt_solution_time`,
`hasDerivAt_solution_time1` and more.

## B. Causal support of the retarded solution

- `advancedSolution` : The advanced solution: the retarded solution of the time-reflected source,
  reflected back.

Lemmas: `propagatedSlice_eq_sineEvolution`, `advancedSolution_equation`,
`integrableOn_sineEvolution_slice`, `solution_eq_integral`, `solution_add`, `solution_smul`.

## C. The two-sided Klein–Gordon inverse on compact test fields

- `testOperator` : The Klein–Gordon operator `∂ₜ² - Δ + μ` on compact spacetime test fields.

Lemmas: `slice_testOperator`, `testOperator_apply`, `fourier_frequencySqOperator`,
`sourceHat_testOperator`, `freqSolution_testOperator`, `solution_testOperator`,
`solution_equation_at`, `testOperator_reflect`, `advancedSolution_testOperator`.

-/

@[expose] public section

noncomputable section

open scoped SchwartzMap FourierTransform Distributions Laplacian
open Duhamel FourierIntegral TimeSlice TopologicalSpace Real Topology LineDeriv

namespace KleinGordon

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] (f : 𝓓((⊤ : Opens (ℝ × E)), F))

/-- The Fourier transform of the source at the frequency `ξ`, as a function of the time. -/
def sourceHat (ξ : E) (s : ℝ) : F := 𝓕 (slice F f s) ξ

omit [CompleteSpace F] in
lemma continuous_sourceHat (ξ : E) : Continuous (sourceHat F f ξ) :=
  (continuous_fourier_slice F f).comp (continuous_id.prodMk continuous_const)

/-- The retarded solution at the spatial frequency `ξ`, with zero data at the time `a`. -/
def freqSolution (μ a : ℝ) (ξ : E) (t : ℝ) : F :=
  ∫ s in a..t, multiplier (t - s) μ ξ • sourceHat F f ξ s

omit [CompleteSpace F] in
lemma freqSolution_eq (μ a : ℝ) (ξ : E) (t : ℝ) :
    freqSolution F f μ a ξ t = duhamelOsc (dispersion μ ξ) a (sourceHat F f ξ) t := by
  unfold freqSolution duhamelOsc multiplier
  refine intervalIntegral.integral_congr fun s _ => ?_
  exact Complex.coe_smul _ _

/-- The time derivative of the per-frequency solution. -/
def freqSolution1 (μ a : ℝ) (ξ : E) (t : ℝ) : F :=
  duhamelOscCos (dispersion μ ξ) a (sourceHat F f ξ) t

lemma hasDerivAt_freqSolution (μ a : ℝ) (ξ : E) (t : ℝ) :
    HasDerivAt (freqSolution F f μ a ξ) (freqSolution1 F f μ a ξ t) t := by
  have : freqSolution F f μ a ξ = duhamelOsc (dispersion μ ξ) a (sourceHat F f ξ) :=
    funext (freqSolution_eq F f μ a ξ)
  rw [this]
  exact hasDerivAt_duhamelOsc (continuous_sourceHat F f ξ) _ a t

lemma hasDerivAt_freqSolution1 (μ a : ℝ) (ξ : E) (t : ℝ) :
    HasDerivAt (freqSolution1 F f μ a ξ)
      (sourceHat F f ξ t - (dispersion μ ξ ^ 2) • freqSolution F f μ a ξ t) t := by
  rw [freqSolution_eq]
  exact hasDerivAt_duhamelOscCos (continuous_sourceHat F f ξ) _ a t
end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] (f : 𝓓((⊤ : Opens (ℝ × E)), F))
variable {F f}

omit [CompleteSpace F] in
lemma norm_freqSolution1_le {K N : ℝ} (hK : ∀ (ξ : E) s, ‖sourceHat F f ξ s‖ ≤ K * (1 + ‖ξ‖) ^ (-N))
    (μ a : ℝ) (ξ : E) (t : ℝ) :
    ‖freqSolution1 F f μ a ξ t‖ ≤ K * (1 + ‖ξ‖) ^ (-N) * |t - a| := by
  unfold freqSolution1 duhamelOscCos
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := t)
    (f := fun s => cos (dispersion μ ξ * (t - s)) • sourceHat F f ξ s)
    (C := K * (1 + ‖ξ‖) ^ (-N)) fun s _ => by
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul (abs_cos_le_one _) (hK ξ s) (norm_nonneg _) zero_le_one).trans_eq
        (one_mul _)
  simpa [abs_sub_comm] using this

omit [CompleteSpace F] in
lemma norm_freqSolution_le {K N : ℝ} (hK : ∀ (ξ : E) s, ‖sourceHat F f ξ s‖ ≤ K * (1 + ‖ξ‖) ^ (-N))
    (μ a : ℝ) (ξ : E) (t : ℝ) :
    ‖freqSolution F f μ a ξ t‖ ≤ K * (1 + ‖ξ‖) ^ (-N) * |t - a| * |t - a| := by
  rw [freqSolution_eq]
  unfold duhamelOsc
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := t)
    (f := fun s => sincPropagator (t - s) (dispersion μ ξ) • sourceHat F f ξ s)
    (C := K * (1 + ‖ξ‖) ^ (-N) * |t - a|) fun s hs => by
      rw [norm_smul]
      have hs' : |t - s| ≤ |t - a| := by
        rcases Set.mem_uIoc.1 hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
        · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
      have h1 : ‖sincPropagator (t - s) (dispersion μ ξ)‖ ≤ |t - a| :=
        (abs_sincPropagator_le _ _).trans hs'
      exact mul_le_mul h1 (hK ξ s) (norm_nonneg _) (abs_nonneg _) |>.trans_eq (mul_comm _ _)
  simpa [abs_sub_comm] using this
end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] (f : 𝓓((⊤ : Opens (ℝ × E)), F))
variable {F f}
variable (F f)

omit [CompleteSpace F] in
lemma continuous_freqSolution_xi (μ a t : ℝ) : Continuous fun ξ : E => freqSolution F f μ a ξ
    t := by
  unfold freqSolution sourceHat
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ a t
  have h1 : Continuous fun p : E × ℝ => multiplier (t - p.2) μ p.1 :=
    (continuous_multiplier_uncurry (E := E) μ).comp
      ((continuous_const.sub continuous_snd).prodMk continuous_fst)
  have h2 : Continuous fun p : E × ℝ => 𝓕 (slice F f p.2) p.1 :=
    (continuous_fourier_slice F f).comp (continuous_snd.prodMk continuous_fst)
  exact h1.smul h2

omit [CompleteSpace F] in
lemma continuous_freqSolution1_xi (μ a t : ℝ) : Continuous fun ξ : E => freqSolution1 F f μ a ξ
    t := by
  unfold freqSolution1 duhamelOscCos sourceHat
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ a t
  have h1 : Continuous fun p : E × ℝ => cos (dispersion μ p.1 * (t - p.2)) :=
    Real.continuous_cos.comp
      (((continuous_dispersion μ).comp continuous_fst).mul (continuous_const.sub continuous_snd))
  have h2 : Continuous fun p : E × ℝ => 𝓕 (slice F f p.2) p.1 :=
    (continuous_fourier_slice F f).comp (continuous_snd.prodMk continuous_fst)
  exact h1.smul h2

/-- The first time derivative of the Fourier integral of the retarded solution. -/
lemma hasDerivAt_solution_time {μ : ℝ} (a t : ℝ) (x : E) :
    HasDerivAt (fun t' => ∫ ξ : E, (𝐞 (inner ℝ ξ x) : ℂ) • freqSolution F f μ a ξ t')
      (∫ ξ : E, (𝐞 (inner ℝ ξ x) : ℂ) • freqSolution1 F f μ a ξ t) t := by
  set N := Module.finrank ℝ E + 1
  obtain ⟨K, hK⟩ := exists_fourier_decay F f
  have hbd : MeasureTheory.Integrable (fun ξ : E => |K| * (1 + ‖ξ‖) ^ (-(N : ℝ)) * (|t - a| + 1))
      MeasureTheory.volume :=
    ((integrable_one_add_norm (E := E) (r := (N : ℝ)) (by simp [N])).const_mul _).mul_const _
  have hK' : ∀ (ξ : E) s, ‖sourceHat F f ξ s‖ ≤ |K| * (1 + ‖ξ‖) ^ (-(N : ℝ)) :=
    fun ξ s => (hK s ξ).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  have hchar : Continuous fun ξ : E => (𝐞 (inner ℝ ξ x) : ℂ) :=
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp
      (continuous_id.inner continuous_const))
  have hnorm : ∀ (ξ : E) (v : F), ‖(𝐞 (inner ℝ ξ x) : ℂ) • v‖ = ‖v‖ := fun ξ v => by
    rw [norm_smul, Circle.norm_coe, one_mul]
  have hmeas : ∀ t', MeasureTheory.AEStronglyMeasurable
      (fun ξ : E => (𝐞 (inner ℝ ξ x) : ℂ) • freqSolution F f μ a ξ t') MeasureTheory.volume :=
    fun t' => (hchar.smul (continuous_freqSolution_xi F f μ a t')).aestronglyMeasurable
  have hmeas1 : MeasureTheory.AEStronglyMeasurable
      (fun ξ : E => (𝐞 (inner ℝ ξ x) : ℂ) • freqSolution1 F f μ a ξ t) MeasureTheory.volume :=
    (hchar.smul (continuous_freqSolution1_xi F f μ a t)).aestronglyMeasurable
  have hint : MeasureTheory.Integrable
      (fun ξ : E => (𝐞 (inner ℝ ξ x) : ℂ) • freqSolution F f μ a ξ t) MeasureTheory.volume := by
    refine (hbd.mul_const (|t - a| + 1)).mono' (hmeas t) (Filter.Eventually.of_forall fun ξ => ?_)
    rw [hnorm]
    refine (norm_freqSolution_le hK' μ a ξ t).trans ?_
    have : |t - a| * |t - a| ≤ (|t - a| + 1) * (|t - a| + 1) := by
      have := abs_nonneg (t - a); nlinarith
    have hpos : 0 ≤ |K| * (1 + ‖ξ‖) ^ (-(N : ℝ)) := by positivity
    calc _ = |K| * (1 + ‖ξ‖) ^ (-(N : ℝ)) * (|t - a| * |t - a|) := by ring
      _ ≤ |K| * (1 + ‖ξ‖) ^ (-(N : ℝ)) * ((|t - a| + 1) * (|t - a| + 1)) :=
          mul_le_mul_of_nonneg_left this hpos
      _ = _ := by ring
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t' ξ => (𝐞 (inner ℝ ξ x) : ℂ) • freqSolution F f μ a ξ t')
    (F' := fun t' ξ => (𝐞 (inner ℝ ξ x) : ℂ) • freqSolution1 F f μ a ξ t')
    (bound := fun ξ => |K| * (1 + ‖ξ‖) ^ (-(N : ℝ)) * (|t - a| + 1))
    (Metric.ball_mem_nhds t one_pos) (Filter.Eventually.of_forall hmeas) hint
    (by simpa using hmeas1) ?_ hbd ?_).2
  · refine Filter.Eventually.of_forall fun ξ t' ht' => ?_
    rw [hnorm]
    refine (norm_freqSolution1_le hK' μ a ξ t').trans ?_
    have h1 : |t' - a| ≤ |t - a| + 1 := by
      have := Metric.mem_ball.1 ht'
      rw [Real.dist_eq] at this
      calc |t' - a| = |(t' - t) + (t - a)| := by ring_nf
        _ ≤ |t' - t| + |t - a| := abs_add_le _ _
        _ ≤ _ := by linarith
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  · exact Filter.Eventually.of_forall fun ξ t' _ =>
      (hasDerivAt_freqSolution F f μ a ξ t').const_smul _

/-- The second time derivative of the Fourier integral: the source minus `ω²` times the solution. -/
lemma hasDerivAt_solution_time1 {μ : ℝ} (hμ : 0 ≤ μ) (a t : ℝ) (x : E) :
    HasDerivAt (fun t' => ∫ ξ : E, (𝐞 (inner ℝ ξ x) : ℂ) • freqSolution1 F f μ a ξ t')
      (∫ ξ : E, (𝐞 (inner ℝ ξ x) : ℂ) •
        (sourceHat F f ξ t - (dispersion μ ξ ^ 2) • freqSolution F f μ a ξ t)) t := by
  set d := Module.finrank ℝ E
  obtain ⟨K, hK⟩ := exists_fourier_decay_pow F f (d + 3)
  set c := (2 * π) ^ 2 + μ with hc
  set L := |K| * (1 + c * (|t - a| + 1) ^ 2) with hL
  have hbd : MeasureTheory.Integrable (fun ξ : E => L * (1 + ‖ξ‖) ^ (-((d + 1 : ℕ) : ℝ)))
      MeasureTheory.volume :=
    (integrable_one_add_norm (E := E) (r := ((d + 1 : ℕ) : ℝ))
      (by push_cast; exact lt_add_one _)).const_mul _
  have hK' : ∀ (ξ : E) s, ‖sourceHat F f ξ s‖ ≤ |K| * (1 + ‖ξ‖) ^ (-((d + 3 : ℕ) : ℝ)) :=
    fun ξ s => (hK s ξ).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  have hchar : Continuous fun ξ : E => (𝐞 (inner ℝ ξ x) : ℂ) :=
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp
      (continuous_id.inner continuous_const))
  have hnorm : ∀ (ξ : E) (v : F), ‖(𝐞 (inner ℝ ξ x) : ℂ) • v‖ = ‖v‖ := fun ξ v => by
    rw [norm_smul, Circle.norm_coe, one_mul]
  -- the pointwise bound for all times in the ball of radius one
  have hbound : ∀ (ξ : E) (t' : ℝ), |t' - a| ≤ |t - a| + 1 →
      ‖sourceHat F f ξ t' - (dispersion μ ξ ^ 2) • freqSolution F f μ a ξ t'‖ ≤
        L * (1 + ‖ξ‖) ^ (-((d + 1 : ℕ) : ℝ)) := by
    intro ξ t' ht'
    have hr : 1 ≤ 1 + ‖ξ‖ := by linarith [norm_nonneg ξ]
    have hrpos : 0 < 1 + ‖ξ‖ := by linarith
    have hs := hK' ξ t'
    have hu := norm_freqSolution_le hK' μ a ξ t'
    have hw := dispersion_sq_le hμ ξ
    have hexp : (1 + ‖ξ‖) ^ (-((d + 3 : ℕ) : ℝ)) ≤ (1 + ‖ξ‖) ^ (-((d + 1 : ℕ) : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hr (by push_cast; linarith)
    have hmul : (1 + ‖ξ‖) ^ (2 : ℕ) * (1 + ‖ξ‖) ^ (-((d + 3 : ℕ) : ℝ)) =
        (1 + ‖ξ‖) ^ (-((d + 1 : ℕ) : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hrpos]
      congr 1; push_cast; ring
    have hab : |t' - a| * |t' - a| ≤ (|t - a| + 1) ^ 2 := by
      have := abs_nonneg (t' - a); nlinarith
    calc ‖sourceHat F f ξ t' - (dispersion μ ξ ^ 2) • freqSolution F f μ a ξ t'‖
        ≤ ‖sourceHat F f ξ t'‖ + ‖(dispersion μ ξ ^ 2) • freqSolution F f μ a ξ t'‖ :=
          norm_sub_le _ _
      _ ≤ |K| * (1 + ‖ξ‖) ^ (-((d + 3 : ℕ) : ℝ)) +
          dispersion μ ξ ^ 2 * (|K| * (1 + ‖ξ‖) ^ (-((d + 3 : ℕ) : ℝ)) * (|t' - a| * |t' -
            a|)) := by
          refine add_le_add hs ?_
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          exact mul_le_mul_of_nonneg_left (hu.trans_eq (by ring)) (sq_nonneg _)
      _ ≤ |K| * (1 + ‖ξ‖) ^ (-((d + 1 : ℕ) : ℝ)) +
          c * (1 + ‖ξ‖) ^ 2 * (|K| * (1 + ‖ξ‖) ^ (-((d + 3 : ℕ) : ℝ)) * (|t - a| + 1) ^ 2) := by
          have hp : 0 ≤ |K| * (1 + ‖ξ‖) ^ (-((d + 3 : ℕ) : ℝ)) := by positivity
          refine add_le_add (mul_le_mul_of_nonneg_left hexp (abs_nonneg _)) ?_
          exact mul_le_mul hw (mul_le_mul_of_nonneg_left hab hp)
            (by positivity) (by positivity)
      _ = L * (1 + ‖ξ‖) ^ (-((d + 1 : ℕ) : ℝ)) := by
          rw [hL]
          have := hmul
          calc _ = |K| * (1 + ‖ξ‖) ^ (-((d + 1 : ℕ) : ℝ)) +
                c * (|K| * (|t - a| + 1) ^ 2) *
                  ((1 + ‖ξ‖) ^ 2 * (1 + ‖ξ‖) ^ (-((d + 3 : ℕ) : ℝ))) := by ring
            _ = _ := by rw [this]; ring
  have hmeas1 : ∀ t', MeasureTheory.AEStronglyMeasurable
      (fun ξ : E => (𝐞 (inner ℝ ξ x) : ℂ) • freqSolution1 F f μ a ξ t') MeasureTheory.volume :=
    fun t' => (hchar.smul (continuous_freqSolution1_xi F f μ a t')).aestronglyMeasurable
  have hmeas2 : MeasureTheory.AEStronglyMeasurable
      (fun ξ : E => (𝐞 (inner ℝ ξ x) : ℂ) •
        (sourceHat F f ξ t - (dispersion μ ξ ^ 2) • freqSolution F f μ a ξ t))
      MeasureTheory.volume := by
    refine (hchar.smul ?_).aestronglyMeasurable
    exact ((continuous_fourier_slice F f).comp (continuous_const.prodMk continuous_id)).sub
      (((continuous_dispersion (E := E) μ).pow 2).smul (continuous_freqSolution_xi F f μ a t))
  have hint1 : MeasureTheory.Integrable
      (fun ξ : E => (𝐞 (inner ℝ ξ x) : ℂ) • freqSolution1 F f μ a ξ t) MeasureTheory.volume := by
    refine ((integrable_one_add_norm (E := E) (r := ((d + 1 : ℕ) : ℝ))
      (by push_cast; exact lt_add_one _)).const_mul (|K| * |t - a|)).mono' (hmeas1 t)
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [hnorm]
    refine (norm_freqSolution1_le hK' μ a ξ t).trans ?_
    have hr : 1 ≤ 1 + ‖ξ‖ := by linarith [norm_nonneg ξ]
    have hexp : (1 + ‖ξ‖) ^ (-((d + 3 : ℕ) : ℝ)) ≤ (1 + ‖ξ‖) ^ (-((d + 1 : ℕ) : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hr (by push_cast; linarith)
    calc _ = |t - a| * (|K| * (1 + ‖ξ‖) ^ (-((d + 3 : ℕ) : ℝ))) := by ring
      _ ≤ |t - a| * (|K| * (1 + ‖ξ‖) ^ (-((d + 1 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp (abs_nonneg _)) (abs_nonneg _)
      _ = _ := by ring
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t' ξ => (𝐞 (inner ℝ ξ x) : ℂ) • freqSolution1 F f μ a ξ t')
    (F' := fun t' ξ => (𝐞 (inner ℝ ξ x) : ℂ) •
      (sourceHat F f ξ t' - (dispersion μ ξ ^ 2) • freqSolution F f μ a ξ t'))
    (bound := fun ξ => L * (1 + ‖ξ‖) ^ (-((d + 1 : ℕ) : ℝ)))
    (Metric.ball_mem_nhds t one_pos) (Filter.Eventually.of_forall hmeas1) hint1
    (by simpa using hmeas2) ?_ hbd ?_).2
  · refine Filter.Eventually.of_forall fun ξ t' ht' => ?_
    rw [hnorm]
    apply hbound
    have := Metric.mem_ball.1 ht'
    rw [Real.dist_eq] at this
    calc |t' - a| = |(t' - t) + (t - a)| := by ring_nf
      _ ≤ |t' - t| + |t - a| := abs_add_le _ _
      _ ≤ _ := by linarith
  · exact Filter.Eventually.of_forall fun ξ t' _ =>
      (hasDerivAt_freqSolution1 F f μ a ξ t').const_smul _

/-- Fourier inversion for the source: the inverse Fourier integral of the Fourier transformed
slice is the source. -/
lemma integral_sourceHat (t : ℝ) (x : E) :
    ∫ ξ : E, (𝐞 (inner ℝ ξ x) : ℂ) • sourceHat F f ξ t = f (t, x) := by
  have h := congrArg (fun g : 𝓢(E, F) => g x)
    (FourierTransform.fourierInv_fourier_eq (E := 𝓢(E, F)) (F := 𝓢(E, F)) (slice F f t))
  simp only [slice_apply] at h
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq] at h
  simpa [sourceHat, Circle.smul_def] using h

omit [CompleteSpace F] in
/-- The weighted per-frequency solution is integrable in the frequency. -/
lemma integrable_norm_pow_mul_freqSolution (μ a t : ℝ) {n : ℕ} (hn : n ≤ 2) :
    MeasureTheory.Integrable (fun ξ : E => ‖ξ‖ ^ n * ‖freqSolution F f μ a ξ t‖)
      MeasureTheory.volume := by
  set d := Module.finrank ℝ E
  obtain ⟨K, hK⟩ := exists_fourier_decay_pow F f (d + 3)
  have hK' : ∀ (ξ : E) s, ‖sourceHat F f ξ s‖ ≤ |K| * (1 + ‖ξ‖) ^ (-((d + 3 : ℕ) : ℝ)) :=
    fun ξ s => (hK s ξ).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  have hbd : MeasureTheory.Integrable
      (fun ξ : E => (|K| * (|t - a| * |t - a|)) * (1 + ‖ξ‖) ^ (-((d + 1 : ℕ) : ℝ)))
      MeasureTheory.volume :=
    (integrable_one_add_norm (E := E) (r := ((d + 1 : ℕ) : ℝ))
      (by push_cast; exact lt_add_one _)).const_mul _
  refine hbd.mono' ?_ (Filter.Eventually.of_forall fun ξ => ?_)
  · exact ((continuous_norm.pow n).mul
      (continuous_norm.comp (continuous_freqSolution_xi F f μ a t))).aestronglyMeasurable
  · have hr : 1 ≤ 1 + ‖ξ‖ := by linarith [norm_nonneg ξ]
    have hrpos : 0 < 1 + ‖ξ‖ := by linarith
    have hu := norm_freqSolution_le hK' μ a ξ t
    have hn' : ‖ξ‖ ^ n ≤ (1 + ‖ξ‖) ^ 2 :=
      (pow_le_pow_left₀ (norm_nonneg _) (by linarith) n).trans
        (pow_le_pow_right₀ hr hn)
    have hmul : (1 + ‖ξ‖) ^ (2 : ℕ) * (1 + ‖ξ‖) ^ (-((d + 3 : ℕ) : ℝ)) =
        (1 + ‖ξ‖) ^ (-((d + 1 : ℕ) : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hrpos]
      congr 1; push_cast; ring
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖ξ‖ ^ n * ‖freqSolution F f μ a ξ t‖
        ≤ (1 + ‖ξ‖) ^ 2 * (|K| * (1 + ‖ξ‖) ^ (-((d + 3 : ℕ) : ℝ)) * |t - a| * |t - a|) :=
          mul_le_mul hn' hu (norm_nonneg _) (by positivity)
      _ = (|K| * (|t - a| * |t - a|)) *
            ((1 + ‖ξ‖) ^ (2 : ℕ) * (1 + ‖ξ‖) ^ (-((d + 3 : ℕ) : ℝ))) := by ring
      _ = _ := by rw [hmul]

/-- The retarded solution of the Klein–Gordon equation with the source `f`. -/
def solution (μ : ℝ) (t : ℝ) (x : E) : F :=
  duhamel F f (fun r ξ => multiplier r μ ξ) t x

omit [CompleteSpace F] in
lemma solution_eq {μ : ℝ} {a : ℝ} (ha : ∀ s ≤ a, s ∉ Prod.fst '' tsupport f) {t : ℝ}
    (hat : a ≤ t) (x : E) :
    solution F f μ t x = ∫ ξ : E, (𝐞 (inner ℝ ξ x) : ℂ) • freqSolution F f μ a ξ t := by
  unfold solution
  rw [duhamel_eq_integral_fourier F f (fun r ξ => multiplier r μ ξ)
    (continuous_multiplier_uncurry μ)
    (fun R => ⟨R, fun r ξ hr => (norm_multiplier_le r μ ξ).trans hr⟩) ha hat x]
  simp only [freqSolution, sourceHat, Circle.smul_def]

/-- The retarded solution solves the Klein–Gordon equation `(∂ₜ² - Δ + μ) u = f`. -/
lemma solution_equation {μ : ℝ} (hμ : 0 ≤ μ) {a : ℝ}
    (ha : ∀ s ≤ a, s ∉ Prod.fst '' tsupport f) {t : ℝ} (hat : a < t) (x : E) :
    deriv (deriv fun τ => solution F f μ τ x) t - Δ (fun y => solution F f μ t y) x +
        μ • solution F f μ t x = f (t, x) := by
  -- the time derivatives
  have hd1 : ∀ τ, a < τ → HasDerivAt (fun τ' => solution F f μ τ' x)
      (∫ ξ : E, (𝐞 (inner ℝ ξ x) : ℂ) • freqSolution1 F f μ a ξ τ) τ := by
    intro τ hτ
    refine (hasDerivAt_solution_time F f (μ := μ) a τ x).congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds hτ] with τ' hτ'
    exact solution_eq F f ha hτ'.le x
  have hderiv : deriv (fun τ => solution F f μ τ x) =ᶠ[nhds t]
      fun τ => ∫ ξ : E, (𝐞 (inner ℝ ξ x) : ℂ) • freqSolution1 F f μ a ξ τ := by
    filter_upwards [lt_mem_nhds hat] with τ hτ using (hd1 τ hτ).deriv
  have hdd : deriv (deriv fun τ => solution F f μ τ x) t =
      ∫ ξ : E, (𝐞 (inner ℝ ξ x) : ℂ) •
        (sourceHat F f ξ t - (dispersion μ ξ ^ 2) • freqSolution F f μ a ξ t) := by
    rw [hderiv.deriv_eq]
    exact (hasDerivAt_solution_time1 F f hμ a t x).deriv
  -- the Laplacian
  have hsp : (fun y => solution F f μ t y) =
      fun y => ∫ ξ : E, (𝐞 (inner ℝ ξ y) : ℂ) • freqSolution F f μ a ξ t :=
    funext fun y => solution_eq F f ha hat.le y
  have hlap := laplacian_fourierInvIntegral
    (h := fun ξ => freqSolution F f μ a ξ t)
    (continuous_freqSolution_xi F f μ a t).aestronglyMeasurable
    (fun n hn => integrable_norm_pow_mul_freqSolution F f μ a t hn) x
  rw [hdd, hsp, hlap, solution_eq F f ha hat.le x]
  -- integrability of the three pieces
  have hchar : Continuous fun ξ : E => (𝐞 (inner ℝ ξ x) : ℂ) :=
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp
      (continuous_id.inner continuous_const))
  have hnorm : ∀ (ξ : E) (v : F), ‖(𝐞 (inner ℝ ξ x) : ℂ) • v‖ = ‖v‖ := fun ξ v => by
    rw [norm_smul, Circle.norm_coe, one_mul]
  obtain ⟨A, hAdef⟩ : ∃ A : E → F, ∀ ξ, A ξ = (𝐞 (inner ℝ ξ x) : ℂ) • freqSolution F f μ a ξ t :=
    ⟨fun ξ => (𝐞 (inner ℝ ξ x) : ℂ) • freqSolution F f μ a ξ t, fun _ => rfl⟩
  have hAfun : A = fun ξ => (𝐞 (inner ℝ ξ x) : ℂ) • freqSolution F f μ a ξ t := funext hAdef
  have hAc : Continuous A := by
    rw [hAfun]; exact hchar.smul (continuous_freqSolution_xi F f μ a t)
  have hA : MeasureTheory.Integrable A MeasureTheory.volume := by
    refine (integrable_norm_pow_mul_freqSolution F f μ a t (n := 0) (by norm_num)).mono'
      hAc.aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
    simp [hAdef, hnorm]
  have hA2 : MeasureTheory.Integrable (fun ξ => (((‖ξ‖ ^ 2 : ℝ)) : ℂ) • A ξ)
      MeasureTheory.volume := by
    refine (integrable_norm_pow_mul_freqSolution F f μ a t (n := 2) le_rfl).mono'
      ((Complex.continuous_ofReal.comp (continuous_norm.pow 2)).smul hAc).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simp [hAdef, hnorm]
  have hsc : Continuous fun ξ : E => sourceHat F f ξ t := (𝓕 (slice F f t)).continuous
  have hB : MeasureTheory.Integrable
      (fun ξ : E => (𝐞 (inner ℝ ξ x) : ℂ) • sourceHat F f ξ t) MeasureTheory.volume := by
    obtain ⟨K, hK⟩ := exists_fourier_decay F f
    refine ((integrable_one_add_norm (E := E)
      (r := ((Module.finrank ℝ E + 1 : ℕ) : ℝ)) (by push_cast; exact lt_add_one _)).const_mul
        |K|).mono' (hchar.smul hsc).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [hnorm]
    exact (hK t ξ).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  -- pointwise rewriting of the integrands, with complex scalars
  set c : ℂ := (((2 * π) ^ 2 : ℝ) : ℂ) with hcdef
  have hP : ∀ ξ : E, (𝐞 (inner ℝ ξ x) : ℂ) •
      (sourceHat F f ξ t - (dispersion μ ξ ^ 2) • freqSolution F f μ a ξ t) =
      (𝐞 (inner ℝ ξ x) : ℂ) • sourceHat F f ξ t - c • ((((‖ξ‖ ^ 2 : ℝ)) : ℂ) • A ξ) -
        ((μ : ℝ) : ℂ) • A ξ := by
    intro ξ
    have hω : dispersion μ ξ ^ 2 = (2 * π) ^ 2 * ‖ξ‖ ^ 2 + μ := Real.sq_sqrt (by positivity)
    rw [← Complex.coe_smul, hω]
    rw [hAdef]
    simp only [hcdef]
    push_cast
    module
  have hQ : ∀ ξ : E, (-((2 * π) ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) • A ξ =
      -(c • ((((‖ξ‖ ^ 2 : ℝ)) : ℂ) • A ξ)) := by
    intro ξ
    simp only [hcdef]
    push_cast
    module
  have e1 : (∫ ξ : E, (𝐞 (inner ℝ ξ x) : ℂ) •
        (sourceHat F f ξ t - (dispersion μ ξ ^ 2) • freqSolution F f μ a ξ t)) =
      f (t, x) - c • (∫ ξ : E, (((‖ξ‖ ^ 2 : ℝ)) : ℂ) • A ξ) - ((μ : ℝ) : ℂ) • (∫ ξ : E, A ξ) := by
    have h1 : (fun ξ : E => (𝐞 (inner ℝ ξ x) : ℂ) •
        (sourceHat F f ξ t - (dispersion μ ξ ^ 2) • freqSolution F f μ a ξ t)) =
        fun ξ => (𝐞 (inner ℝ ξ x) : ℂ) • sourceHat F f ξ t -
          c • ((((‖ξ‖ ^ 2 : ℝ)) : ℂ) • A ξ) - ((μ : ℝ) : ℂ) • A ξ := funext hP
    have iC : MeasureTheory.Integrable
        (fun ξ : E => c • ((((‖ξ‖ ^ 2 : ℝ)) : ℂ) • A ξ)) MeasureTheory.volume := hA2.smul c
    have iM : MeasureTheory.Integrable (fun ξ : E => ((μ : ℝ) : ℂ) • A ξ) MeasureTheory.volume :=
      hA.smul _
    have iBC : MeasureTheory.Integrable (fun ξ : E => (𝐞 (inner ℝ ξ x) : ℂ) • sourceHat F f ξ t -
        c • ((((‖ξ‖ ^ 2 : ℝ)) : ℂ) • A ξ)) MeasureTheory.volume := hB.sub iC
    rw [h1, MeasureTheory.integral_sub iBC iM, MeasureTheory.integral_sub hB iC,
      MeasureTheory.integral_smul, MeasureTheory.integral_smul, integral_sourceHat F f t x]
  have e2 : (∫ ξ : E, (-((2 * π) ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) •
        ((𝐞 (inner ℝ ξ x) : ℂ) • freqSolution F f μ a ξ t)) =
      -(c • (∫ ξ : E, (((‖ξ‖ ^ 2 : ℝ)) : ℂ) • A ξ)) := by
    have h2 : (fun ξ : E => (-((2 * π) ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) •
        ((𝐞 (inner ℝ ξ x) : ℂ) • freqSolution F f μ a ξ t)) =
        fun ξ => -(c • ((((‖ξ‖ ^ 2 : ℝ)) : ℂ) • A ξ)) := by
      funext ξ
      rw [← hAdef ξ]
      exact hQ ξ
    rw [h2, MeasureTheory.integral_neg, MeasureTheory.integral_smul]
  have e3 : (∫ ξ : E, (𝐞 (inner ℝ ξ x) : ℂ) • freqSolution F f μ a ξ t) = ∫ ξ : E, A ξ := by
    rw [hAfun]
  rw [e1, e2, e3, ← Complex.coe_smul]
  module
end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] (f : 𝓓((⊤ : Opens (ℝ × E)), F))

omit [CompleteSpace F] in
lemma propagatedSlice_eq_sineEvolution {μ : ℝ} (hμ : 0 ≤ μ) (r s : ℝ) (x : E) :
    propagatedSlice F f (fun r ξ => multiplier r μ ξ) r s x =
      sineEvolution F r μ (slice F f s) x := by
  rw [sineEvolution_apply_eq F r hμ]
  rfl

/-- The advanced solution: the retarded solution of the time-reflected source, reflected back. -/
def advancedSolution (μ : ℝ) (t : ℝ) (x : E) : F := solution F (reflect F f) μ (-t) x

/-- The advanced solution solves the Klein–Gordon equation `(∂ₜ² - Δ + μ) u = f`. -/
lemma advancedSolution_equation {μ : ℝ} (hμ : 0 ≤ μ) (t : ℝ) (x : E) :
    deriv (deriv fun τ => advancedSolution F f μ τ x) t -
      Δ (fun y => advancedSolution F f μ t y) x + μ • advancedSolution F f μ t x = f (t, x) := by
  obtain ⟨a₀, ha₀⟩ := exists_timeBound F (reflect F f)
  set a := min a₀ (-t - 1) with ha
  have ha' : ∀ s ≤ a, s ∉ Prod.fst '' tsupport (reflect F f) := fun s hs =>
    ha₀ s (hs.trans (min_le_left _ _))
  have hat : a < -t := by have := min_le_right a₀ (-t - 1); linarith
  have h := solution_equation F (reflect F f) hμ ha' hat x
  have e1 : (deriv fun τ => advancedSolution F f μ τ x) =
      fun τ => -deriv (fun σ => solution F (reflect F f) μ σ x) (-τ) := by
    funext τ
    exact deriv_comp_neg (fun σ => solution F (reflect F f) μ σ x) τ
  have e2 : deriv (deriv fun τ => advancedSolution F f μ τ x) t =
      deriv (deriv fun σ => solution F (reflect F f) μ σ x) (-t) := by
    rw [e1, deriv.fun_neg, deriv_comp_neg (deriv fun σ => solution F (reflect F f) μ σ x) t]; simp
  rw [e2]
  simpa [advancedSolution] using h

omit [CompleteSpace F] in
lemma integrableOn_sineEvolution_slice {μ : ℝ} (hμ : 0 ≤ μ) (t : ℝ) (x : E) :
    MeasureTheory.IntegrableOn (fun s => sineEvolution F (t - s) μ (slice F f s) x)
      (Set.Iic t) := by
  have := integrable_duhamel F f (fun r ξ => multiplier r μ ξ)
    (continuous_multiplier_uncurry μ)
    (fun R => ⟨R, fun r ξ hr => (norm_multiplier_le r μ ξ).trans hr⟩) t x
  simp_rw [propagatedSlice_eq_sineEvolution F f hμ] at this
  exact this.integrableOn

omit [CompleteSpace F] in
lemma solution_eq_integral {μ : ℝ} (hμ : 0 ≤ μ) (t : ℝ) (x : E) :
    solution F f μ t x = ∫ s in Set.Iic t, sineEvolution F (t - s) μ (slice F f s) x := by
  unfold solution duhamel
  simp_rw [propagatedSlice_eq_sineEvolution F f hμ]

omit [CompleteSpace F] in
lemma solution_add {μ : ℝ} (hμ : 0 ≤ μ) (g : 𝓓((⊤ : Opens (ℝ × E)), F)) (t : ℝ) (x : E) :
    solution F (f + g) μ t x = solution F f μ t x + solution F g μ t x := by
  simp_rw [solution_eq_integral F _ hμ, slice_add, map_add, add_apply]
  exact MeasureTheory.integral_add (integrableOn_sineEvolution_slice F f hμ t x)
    (integrableOn_sineEvolution_slice F g hμ t x)

omit [CompleteSpace F] in
lemma solution_smul {μ : ℝ} (hμ : 0 ≤ μ) (c : ℝ) (t : ℝ) (x : E) :
    solution F (c • f) μ t x = c • solution F f μ t x := by
  simp_rw [solution_eq_integral F _ hμ, slice_smul]
  rw [← MeasureTheory.integral_smul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Iic fun s _ => ?_
  rw [← Complex.coe_smul c (slice F f s), map_smul, smul_apply, Complex.coe_smul]

/-- The Klein–Gordon operator `∂ₜ² - Δ + μ` on compact spacetime test fields. -/
def testOperator (μ : ℝ) : 𝓓((⊤ : Opens (ℝ × E)), F) :=
  dt F (dt F f) - spatialLaplacian F f + μ • f

lemma slice_testOperator (μ s : ℝ) :
    slice F (testOperator F f μ) s = slice F (dt F (dt F f)) s +
      frequencySqOperator F μ (slice F f s) := by
  rw [frequencySqOperator_eq]
  have hs : slice F (testOperator F f μ) s =
      slice F (dt F (dt F f)) s - slice F (spatialLaplacian F f) s + μ • slice F f s := by
    ext x; rfl
  rw [hs, slice_spatialLaplacian]
  abel

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
/-- The compact source operator agrees pointwise with the Klein–Gordon differential expression. -/
lemma testOperator_apply (μ t : ℝ) (x : E) :
    testOperator F f μ (t, x) = deriv (deriv (fun s => f (s, x))) t -
      (Δ (fun y => f (t, y))) x + μ • f (t, x) := by
  have hd : deriv (fun s => f (s, x)) = fun s => dt F f (s, x) :=
    funext fun s => (hasDerivAt_time F f s x).deriv
  rw [hd, (hasDerivAt_time F (dt F f) t x).deriv]
  have hl : spatialLaplacian F f (t, x) = (Δ (fun y => f (t, y))) x := by
    change slice F (spatialLaplacian F f) t x = _
    rw [slice_spatialLaplacian, SchwartzMap.laplacian_apply]
    rfl
  change dt F (dt F f) (t, x) - spatialLaplacian F f (t, x) + μ • f (t, x) = _
  rw [hl]

lemma fourier_frequencySqOperator (μ : ℝ) (g : 𝓢(E, F)) (ξ : E) :
    𝓕 (frequencySqOperator F μ g) ξ = frequencySq μ ξ • 𝓕 g ξ := by
  simp only [frequencySqOperator, SchwartzMap.fourierMultiplierCLM_apply,
    FourierTransform.fourier_fourierInv_eq]
  exact SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_frequencySq μ) _ ξ

/-- The compact test-field operator becomes the forced oscillator operator at each frequency. -/
lemma sourceHat_testOperator {μ : ℝ} (hμ : 0 ≤ μ) (ξ : E) (s : ℝ) :
    sourceHat F (testOperator F f μ) ξ s =
      sourceHat F (dt F (dt F f)) ξ s + dispersion μ ξ ^ 2 • sourceHat F f ξ s := by
  simp only [sourceHat, slice_testOperator, FourierTransform.fourier_add, add_apply,
    fourier_frequencySqOperator]
  have hω : dispersion μ ξ ^ 2 = (2 * π) ^ 2 * ‖ξ‖ ^ 2 + μ := Real.sq_sqrt (by positivity)
  rw [hω]
  exact congrArg (𝓕 (slice F (dt F (dt F f)) s) ξ + ·) (Complex.coe_smul _ _)

/-- The retarded Fourier mode recovers a test field with vanishing initial Cauchy data. -/
lemma freqSolution_testOperator {μ : ℝ} (hμ : 0 ≤ μ) (ξ : E) (a t : ℝ)
    (ha : a ∉ Prod.fst '' tsupport f) (ha' : a ∉ Prod.fst '' tsupport (dt F f)) :
    freqSolution F (testOperator F f μ) μ a ξ t = sourceHat F f ξ t := by
  rw [freqSolution_eq]
  have he : sourceHat F (testOperator F f μ) ξ = fun s =>
      sourceHat F (dt F (dt F f)) ξ s + dispersion μ ξ ^ 2 • sourceHat F f ξ s :=
    funext (sourceHat_testOperator F f hμ ξ)
  rw [he]
  apply duhamelOsc_operator_of_initial_zero
  · exact fun s => hasDerivAt_fourier_slice F f ξ s
  · exact fun s => hasDerivAt_fourier_slice F (dt F f) ξ s
  · exact continuous_sourceHat F (dt F (dt F f)) ξ
  · simp [sourceHat, slice_eq_zero_of_notMem F f ha]
  · simp [slice_eq_zero_of_notMem F (dt F f) ha']

/-- Applying the retarded Green operator to the Klein–Gordon source of a compact test field
recovers that field. -/
lemma solution_testOperator {μ : ℝ} (hμ : 0 ≤ μ) (t : ℝ) (x : E) :
    solution F (testOperator F f μ) μ t x = f (t, x) := by
  obtain ⟨a₀, ha₀⟩ := exists_timeBound F f
  obtain ⟨a₁, ha₁⟩ := exists_timeBound F (dt F f)
  obtain ⟨a₂, ha₂⟩ := exists_timeBound F (testOperator F f μ)
  let a := min (min a₀ a₁) (min a₂ t)
  have h0 : a ≤ a₀ := (min_le_left _ _).trans (min_le_left _ _)
  have h1 : a ≤ a₁ := (min_le_left _ _).trans (min_le_right _ _)
  have h2 : a ≤ a₂ := (min_le_right _ _).trans (min_le_left _ _)
  have ht : a ≤ t := (min_le_right _ _).trans (min_le_right _ _)
  rw [solution_eq F (testOperator F f μ) (fun s hs => ha₂ s (hs.trans h2)) ht x]
  simp_rw [freqSolution_testOperator F f hμ _ a t (ha₀ a h0) (ha₁ a h1), sourceHat]
  have he : (∫ ξ : E, (𝐞 (inner ℝ ξ x) : ℂ) • 𝓕 (slice F f t) ξ) =
      (𝓕⁻ (𝓕 (slice F f t))) x := by
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq]
    simp only [Circle.smul_def]
  rw [he, FourierTransform.fourierInv_fourier_eq, slice_apply]

/-- The retarded field solves the sourced equation at every spacetime point. -/
lemma solution_equation_at {μ : ℝ} (hμ : 0 ≤ μ) (t : ℝ) (x : E) :
    deriv (deriv (fun s => solution F f μ s x)) t -
      (Δ (fun y => solution F f μ t y)) x + μ • solution F f μ t x = f (t, x) := by
  obtain ⟨a, ha⟩ := exists_timeBound F f
  apply solution_equation F f hμ (a := min a (t - 1))
    (fun s hs => ha s (hs.trans (min_le_left _ _)))
  have := min_le_right a (t - 1)
  linarith

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
/-- Time reflection commutes with the compact Klein–Gordon operator. -/
lemma testOperator_reflect (μ : ℝ) :
    testOperator F (reflect F f) μ = reflect F (testOperator F f μ) := by
  simp only [testOperator, dt_dt_reflect, spatialLaplacian_reflect]
  ext p
  rfl

/-- Applying the advanced Green operator to the Klein–Gordon source of a compact test field
recovers that field. -/
lemma advancedSolution_testOperator {μ : ℝ} (hμ : 0 ≤ μ) (t : ℝ) (x : E) :
    advancedSolution F (testOperator F f μ) μ t x = f (t, x) := by
  rw [advancedSolution, ← testOperator_reflect, solution_testOperator F (reflect F f) hμ]
  simp
end

end KleinGordon
