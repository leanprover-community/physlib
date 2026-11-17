/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.DimensionRaising.SineEvolution

/-!

# Dimension raising for the retarded solution

The retarded solution in `d + 2` space dimensions is `-(1 / (2π ρ)) ∂ρ` of the one in `d` dimensions
for sources that are radial in the extra variables.

## i. Overview

The identity on the slices (`hasDerivAt_sineEvolution_radial`) passes through the Duhamel integral.
The integrand is bounded uniformly in the time. It vanishes outside the compact time support of the
source. So the derivative in the radius commutes with the time integral.

## ii. Key results

- `norm_sineEvolution_slice_le` : the sine evolution of the slices is bounded uniformly in time.
- `continuous_sineEvolution_slice` : the sine evolution of the slices is continuous in time.
- `hasDerivAt_solution_radial` : dimension raising for the retarded solution.

## iii. Table of contents

- A. Bounds in time
- B. The retarded solution

## iv. References

None.

## A. Bounds in time

- `exists_bound_integrand` : the Fourier integrand is bounded uniformly in the time.
- `norm_sineEvolution_slice_le` : the sine evolution of the slices is bounded uniformly in time.
- `continuous_sineEvolution_slice` : the sine evolution of the slices is continuous in time.

## B. The retarded solution

- `hasDerivAt_solution_radial` : dimension raising for the retarded solution.
-/

@[expose] public section

noncomputable section

open scoped FourierTransform SchwartzMap Distributions
open MeasureTheory TopologicalSpace TimeSlice

namespace KleinGordon

section Bounds

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E]

/-- The Fourier integrand of the sine evolution of the slice at time `s` is bounded uniformly. -/
lemma exists_bound_integrand {μ : ℝ} (ψ : 𝓓((⊤ : Opens (ℝ × E)), ℂ)) (t : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (s : ℝ) (z ξ : E), ‖(𝐞 (inner ℝ ξ z) : ℂ) •
      (multiplier (t - s) μ ξ • 𝓕 (slice ℂ ψ s) ξ)‖ ≤
        A * (1 + ‖ξ‖) ^ (-((Module.finrank ℝ E + 1 : ℕ) : ℝ)) := by
  obtain ⟨K, hK⟩ := exists_fourier_decay ℂ ψ
  obtain ⟨R, hR⟩ := (isCompact_timeSupport ℂ ψ).isBounded.exists_norm_le
  have hK0 : 0 ≤ K := by
    have := hK 0 0
    have h0 := norm_nonneg ((𝓕 (slice ℂ ψ 0)) 0)
    simp at this
    linarith
  refine ⟨(|t| + max R 0) * K, by positivity, fun s z ξ => ?_⟩
  by_cases hs : s ∈ Prod.fst '' tsupport ψ
  · have hsR : |s| ≤ max R 0 := by
      have := (hR s hs).trans (le_max_left R 0)
      simpa using this
    have hm : ‖multiplier (t - s) μ ξ‖ ≤ |t| + max R 0 :=
      (norm_multiplier_le (t - s) μ ξ).trans ((abs_sub _ _).trans (by linarith))
    rw [norm_smul, Circle.norm_coe, one_mul, norm_smul]
    have h1 := hK s ξ
    calc ‖multiplier (t - s) μ ξ‖ * ‖(𝓕 (slice ℂ ψ s)) ξ‖
        ≤ (|t| + max R 0) * (K * (1 + ‖ξ‖) ^ (-((Module.finrank ℝ E + 1 : ℕ) : ℝ))) := by
          gcongr
      _ = _ := by ring
  · have : slice ℂ ψ s = 0 := slice_eq_zero_of_notMem ℂ ψ hs
    simp [this]
    positivity

/-- The sine evolution of the slices is bounded, and vanishes outside the time support. -/
lemma norm_sineEvolution_slice_le {μ : ℝ} (hμ : 0 ≤ μ) (ψ : 𝓓((⊤ : Opens (ℝ × E)), ℂ)) (t : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (s : ℝ) (z : E), ‖sineEvolution ℂ (t - s) μ (slice ℂ ψ s) z‖ ≤
      (Prod.fst '' tsupport ψ).indicator (fun _ => B) s := by
  obtain ⟨A, hA0, hA⟩ := exists_bound_integrand (μ := μ) ψ t
  have hn : (Module.finrank ℝ E : ℝ) < ((Module.finrank ℝ E + 1 : ℕ) : ℝ) := by
    push_cast; linarith
  have hint : Integrable (fun ξ : E => A * (1 + ‖ξ‖) ^ (-((Module.finrank ℝ E + 1 : ℕ) : ℝ))) :=
    (integrable_one_add_norm hn).const_mul A
  refine ⟨∫ ξ : E, A * (1 + ‖ξ‖) ^ (-((Module.finrank ℝ E + 1 : ℕ) : ℝ)),
    integral_nonneg fun ξ => by positivity, fun s z => ?_⟩
  by_cases hs : s ∈ Prod.fst '' tsupport ψ
  · rw [Set.indicator_of_mem hs, sineEvolution_apply_eq ℂ (t - s) hμ]
    refine norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall fun ξ => ?_)
    simpa [Circle.smul_def] using hA s z ξ
  · rw [Set.indicator_of_notMem hs, slice_eq_zero_of_notMem ℂ ψ hs]
    simp

/-- The sine evolution of the slices is continuous in the time. -/
lemma continuous_sineEvolution_slice {μ : ℝ} (hμ : 0 ≤ μ) (ψ : 𝓓((⊤ : Opens (ℝ × E)), ℂ)) (t : ℝ)
    (z : E) : Continuous fun s : ℝ => sineEvolution ℂ (t - s) μ (slice ℂ ψ s) z := by
  obtain ⟨A, hA0, hA⟩ := exists_bound_integrand (μ := μ) ψ t
  have hn : (Module.finrank ℝ E : ℝ) < ((Module.finrank ℝ E + 1 : ℕ) : ℝ) := by
    push_cast; linarith
  have hint : Integrable (fun ξ : E => A * (1 + ‖ξ‖) ^ (-((Module.finrank ℝ E + 1 : ℕ) : ℝ))) :=
    (integrable_one_add_norm hn).const_mul A
  simp_rw [sineEvolution_apply_eq ℂ _ hμ]
  have hcs : ∀ ξ : E, Continuous fun s : ℝ => 𝓕 (slice ℂ ψ s) ξ := fun ξ =>
    (continuous_fourier_slice ℂ ψ).comp (continuous_id.prodMk continuous_const)
  have hm : ∀ ξ : E, Continuous fun s : ℝ => multiplier (t - s) μ ξ := fun ξ => by
    unfold multiplier
    exact Complex.continuous_ofReal.comp (Real.continuous_sincPropagator.comp
      ((continuous_const.sub continuous_id).prodMk continuous_const))
  refine continuous_of_dominated (bound := fun ξ : E =>
    A * (1 + ‖ξ‖) ^ (-((Module.finrank ℝ E + 1 : ℕ) : ℝ))) (fun s => ?_) (fun s => ?_) hint ?_
  · have hc : Continuous fun ξ : E => (𝐞 (inner ℝ ξ z) : ℂ) :=
      continuous_subtype_val.comp (Real.continuous_fourierChar.comp
        (continuous_id.inner continuous_const))
    have hmm : Continuous fun ξ : E => multiplier (t - s) μ ξ := by
      unfold multiplier dispersion
      exact Complex.continuous_ofReal.comp (Real.continuous_sincPropagator.comp
        (continuous_const.prodMk (by fun_prop)))
    have hf : Continuous fun ξ : E => 𝓕 (slice ℂ ψ s) ξ := (𝓕 (slice ℂ ψ s)).continuous
    simp only [Circle.smul_def, smul_eq_mul]
    exact (hc.mul (hmm.mul hf)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun ξ => by simpa [Circle.smul_def] using hA s z ξ
  · refine Filter.Eventually.of_forall fun ξ => ?_
    simp only [Circle.smul_def, smul_eq_mul]
    exact continuous_const.mul ((hm ξ).mul (hcs ξ))

/-- **Dimension raising for the retarded solution.** Let `ψ'` be a source on `E × ℝ²` that is
radial in the space variables at each time and let `ψb` be its integral over the plane. The
retarded solution of `ψb` along a ray has the derivative `-(2π ρ)` times the retarded solution of
`ψ'` at distance `ρ`. This is `G_{d+2} = -(1 / (2π r)) ∂ᵣ G_d` for every `d` and every mass. -/
lemma hasDerivAt_solution_radial {μ : ℝ} (hμ : 0 ≤ μ)
    (ψ' : 𝓓((⊤ : Opens (ℝ × WithLp 2 (E × EuclideanSpace ℝ (Fin 2)))), ℂ))
    (ψb : 𝓓((⊤ : Opens (ℝ × E)), ℂ)) (hrad : ∀ s, Function.IsRadial (slice ℂ ψ' s))
    (hψb : ∀ s x, ψb (s, x) = ∫ y : EuclideanSpace ℝ (Fin 2), ψ' (s, WithLp.toLp 2 (x, y)))
    {e : E} (he : ‖e‖ = 1) (t : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    HasDerivAt (fun τ : ℝ => solution ℂ ψb μ t (τ • e))
      (-(2 * Real.pi * ρ : ℝ) • solution ℂ ψ' μ t (WithLp.toLp 2 (ρ • e, 0))) ρ := by
  obtain ⟨B', hB'0, hB'⟩ := norm_sineEvolution_slice_le hμ ψ' t
  obtain ⟨B, hB0, hB⟩ := norm_sineEvolution_slice_le hμ ψb t
  have hT' : IsCompact (Prod.fst '' tsupport ψ') := isCompact_timeSupport ℂ ψ'
  have hT : IsCompact (Prod.fst '' tsupport ψb) := isCompact_timeSupport ℂ ψb
  have hind' : Integrable ((Prod.fst '' tsupport ψ').indicator fun _ : ℝ => 2 * Real.pi *
      (ρ + ρ / 2) * B') (volume.restrict (Set.Iic t)) :=
    ((integrableOn_const hT'.measure_lt_top.ne).integrable_indicator hT'.measurableSet).integrableOn
  have hind : Integrable ((Prod.fst '' tsupport ψb).indicator fun _ : ℝ => B)
      (volume.restrict (Set.Iic t)) :=
    ((integrableOn_const hT.measure_lt_top.ne).integrable_indicator hT.measurableSet).integrableOn
  have hball : Metric.ball ρ (ρ / 2) ∈ nhds ρ := Metric.ball_mem_nhds ρ (half_pos hρ)
  have hpos : ∀ τ ∈ Metric.ball ρ (ρ / 2), 0 < τ ∧ |τ| ≤ ρ + ρ / 2 := fun τ hτ => by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hτ
    exact ⟨by linarith [hτ.1], by rw [abs_of_pos (by linarith [hτ.1])]; linarith [hτ.2]⟩
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Iic t))
    (F := fun (τ : ℝ) (s : ℝ) => sineEvolution ℂ (t - s) μ (slice ℂ ψb s) (τ • e))
    (F' := fun (τ : ℝ) (s : ℝ) => -(2 * Real.pi * τ : ℝ) •
      sineEvolution ℂ (t - s) μ (slice ℂ ψ' s) (WithLp.toLp 2 (τ • e, 0)))
    (x₀ := ρ) (s := Metric.ball ρ (ρ / 2))
    (bound := (Prod.fst '' tsupport ψ').indicator fun _ : ℝ => 2 * Real.pi * (ρ + ρ / 2) * B')
    hball ?_ ?_ ?_ ?_ hind' ?_
  · rw [show (fun τ : ℝ => solution ℂ ψb μ t (τ • e)) = fun τ : ℝ => ∫ s in Set.Iic t,
        sineEvolution ℂ (t - s) μ (slice ℂ ψb s) (τ • e) from
      funext fun τ => solution_eq_integral ℂ ψb hμ t (τ • e),
      solution_eq_integral ℂ ψ' hμ t, ← integral_smul]
    exact key.2
  · exact Filter.Eventually.of_forall fun τ =>
      (continuous_sineEvolution_slice hμ ψb t (τ • e)).aestronglyMeasurable
  · refine Integrable.mono' hind
      (continuous_sineEvolution_slice hμ ψb t (ρ • e)).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun s => hB s (ρ • e)
  · exact ((continuous_sineEvolution_slice hμ ψ' t (WithLp.toLp 2 (ρ • e, 0))).const_smul
      (-(2 * Real.pi * ρ : ℝ))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun s τ hτ => ?_
    obtain ⟨hτ0, hτ1⟩ := hpos τ hτ
    have h1 := hB' s (WithLp.toLp 2 (τ • e, 0))
    by_cases hs : s ∈ Prod.fst '' tsupport ψ'
    · rw [Set.indicator_of_mem hs] at h1 ⊢
      rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
      have hτ1' : τ ≤ ρ + ρ / 2 := (le_abs_self τ).trans hτ1
      have h2 : 2 * Real.pi * τ * ‖sineEvolution ℂ (t - s) μ (slice ℂ ψ' s)
          (WithLp.toLp 2 (τ • e, 0))‖ ≤ 2 * Real.pi * (ρ + ρ / 2) * B' := by
        gcongr
      exact h2
    · rw [Set.indicator_of_notMem hs] at h1 ⊢
      have : ‖sineEvolution ℂ (t - s) μ (slice ℂ ψ' s) (WithLp.toLp 2 (τ • e, 0))‖ = 0 :=
        le_antisymm h1 (norm_nonneg _)
      rw [norm_smul, this, mul_zero]
  · refine Filter.Eventually.of_forall fun s τ hτ => ?_
    obtain ⟨hτ0, -⟩ := hpos τ hτ
    exact hasDerivAt_sineEvolution_radial hμ (t - s) (slice ℂ ψ' s) (hrad s) (slice ℂ ψb s)
      (fun x => by simp [hψb]) he hτ0

end Bounds

end KleinGordon
