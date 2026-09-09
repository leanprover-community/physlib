/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.BoundedIntegral
public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.Conjugation
public import Mathlib.MeasureTheory.VectorMeasure.SetIntegral

/-!

# The vector-measure integral against a scalar matrix coefficient

`boundedIntegral` computes the operator `∫ f dμS` and then pairs it against test vectors; this
file records that, for a *bounded* multiplier, testing first and integrating second gives the
same answer: `⟪y, (∫ f dμS) x⟫ = ∫ f d(μS.scalarMeasure x y)`, where the right-hand side is
Mathlib's `VectorMeasure.integral` against the complex scalar measure `μS.scalarMeasure x y`
(`ScalarMeasure.lean`). That identity, `boundedIntegralOfUniformApprox_inner`, is what lets
`weakIntegral`/`complexWeakIntegral` be defined directly as ordinary vector-measure integrals of
possibly-*unbounded* multipliers `f` — the weak statement of the eventual unbounded reconstruction
law `T = ∫ λ dE(λ)`, testable on a single pair of vectors without needing `f(T)` itself to be a
bounded (or even densely-defined) operator on all of `H`.

## Main definitions

- `weakIntegral`, `complexWeakIntegral` : `∫ f d⟪y, μS(·)x⟫`, for real- and complex-valued `f`.
- `unitaryConjSpectralMeasure_weakIntegral` : compatibility with unitary transport
  (`Conjugation.lean`).

-/

@[expose] public section

noncomputable section

open scoped Topology InnerProductSpace Function
open ContinuousLinearMap ContinuousLinearMapWOT MeasureTheory Set

namespace QuantumMechanics

namespace WOTSpectralMeasure

variable {α : Type*} [MeasurableSpace α]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (μS : WOTSpectralMeasure α H)

/-! ## A. Bounded integrals agree with the vector-measure integral -/

lemma boundedIntegralOfUniformApprox_inner
    [Nonempty α]
    {f : α → ℂ} {s : ℕ → SimpleFunc α ℂ}
    (hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - f x‖ < ε)
    (hsBound : ∃ C : ℝ, ∀ n x, ‖s n x‖ ≤ C)
    (x y : H)
    (hfinite : IsFiniteMeasure (μS.scalarMeasure x y).variation) :
    ⟪y, boundedIntegralOfUniformApprox μS f s hs x⟫_ℂ =
      ∫ᵛ z, f z ∂[ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ);
        μS.scalarMeasure x y] := by
  let μ := μS.scalarMeasure x y
  let B : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℂ
  let _ : IsFiniteMeasure μ.variation := hfinite
  have hmeas : ∀ n, AEStronglyMeasurable (s n) μ.variation := by
    intro n
    exact (s n).measurable.aestronglyMeasurable
  have hbound : ∃ C : ℝ, ∀ᶠ n in Filter.atTop, ∀ᵐ z ∂μ.variation, ‖s n z‖ ≤ C := by
    rcases hsBound with ⟨C, hC⟩
    exact ⟨C, Filter.Eventually.of_forall (fun n => Filter.Eventually.of_forall (hC n))⟩
  have hlim : ∀ᵐ z ∂μ.variation,
      Filter.Tendsto (fun n => s n z) Filter.atTop (𝓝 (f z)) := by
    filter_upwards [] with z
    rw [Metric.tendsto_atTop]
    intro ε hε
    rcases hs ε hε with ⟨N, hN⟩
    exact ⟨N, fun n hn => by simpa only [dist_eq_norm] using hN n hn z⟩
  have hint :
      Filter.Tendsto (fun n => ∫ᵛ z, s n z ∂[B; μ]) Filter.atTop
        (𝓝 (∫ᵛ z, f z ∂[B; μ])) := by
    exact MeasureTheory.VectorMeasure.tendsto_integral_filter_of_norm_le_const
      (μ := μ) (B := B) (Filter.Eventually.of_forall hmeas) hbound hlim
  have hsimple : ∀ n,
      ∫ᵛ z, s n z ∂[B; μ] =
        ⟪y, simpleIntegral μS (s n) x⟫_ℂ := by
    intro n
    rcases hsBound with ⟨C, hC⟩
    let a₀ : α := Classical.choice (inferInstance : Nonempty α)
    have hC0 : 0 ≤ C := (norm_nonneg (s n a₀)).trans (hC n a₀)
    have hi : Integrable (s n) μ.variation :=
      Integrable.of_bound (s n).measurable.aestronglyMeasurable C
        (Filter.Eventually.of_forall (hC n))
    rw [VectorMeasure.integral_eq_setToFun]
    rw [setToFun_simpleFunc (dominatedFinMeasAdditive_cbmApplyMeasure μ B) (s n) hi]
    rw [simpleIntegral_inner]
    apply Finset.sum_congr rfl
    intro z hz
    rfl
  have hclm := (simpleIntegral_toCLM_cauchySeq μS hs).tendsto_limUnder
  have hclm' : Filter.Tendsto
      (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n))) Filter.atTop
      (𝓝 (ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS f s hs))) := by
    rw [boundedIntegralOfUniformApprox_eq_limUnder]
    exact hclm
  have hoperator :
      Filter.Tendsto
        (fun n => ⟪y, simpleIntegral μS (s n) x⟫_ℂ) Filter.atTop
        (𝓝 (⟪y, boundedIntegralOfUniformApprox μS f s hs x⟫_ℂ)) := by
    have hev : Continuous (fun A : H →L[ℂ] H => ⟪y, A x⟫_ℂ) := by fun_prop
    exact hev.continuousAt.tendsto.comp hclm'
  have hsimple' :
      Filter.Tendsto (fun n => ∫ᵛ z, s n z ∂[B; μ]) Filter.atTop
        (𝓝 (⟪y, boundedIntegralOfUniformApprox μS f s hs x⟫_ℂ)) := by
    simpa only [hsimple] using hoperator
  exact tendsto_nhds_unique hsimple' hint

/-! ## B. The weak integral of a possibly-unbounded multiplier -/

/-- The pairing is real-scalar multiplication on the complex scalar measure. -/
def weakIntegral (f : α → ℝ) (x y : H) : ℂ :=
  ∫ᵛ z, f z ∂[ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ);
    μS.scalarMeasure x y]

/-- The complex weak integral of a complex-valued spectral multiplier. The real-valued integral
above is retained for the self-adjoint reconstruction API; this companion is the bounded-unitary
side of the Cayley construction. -/
def complexWeakIntegral (f : α → ℂ) (x y : H) : ℂ :=
  ∫ᵛ z, f z ∂[ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ);
    μS.scalarMeasure x y]

lemma weakIntegral_map {β : Type*} [MeasurableSpace β]
    (f : α → β) (hf : Measurable f) (g : β → ℝ)
    (x y : H) (hgm : AEStronglyMeasurable g ((μS.scalarMeasure x y).variation.map f))
    (hgi : (μS.scalarMeasure x y).Integrable (g ∘ f)) :
    (μS.map f hf).weakIntegral g x y = μS.weakIntegral (g ∘ f) x y := by
  unfold weakIntegral
  rw [scalarMeasure_map]
  exact VectorMeasure.integral_map hf hgm hgi

lemma complexWeakIntegral_map {β : Type*} [MeasurableSpace β]
    (f : α → β) (hf : Measurable f) (g : β → ℂ)
    (x y : H) (hgm : AEStronglyMeasurable g ((μS.scalarMeasure x y).variation.map f))
    (hgi : (μS.scalarMeasure x y).Integrable (g ∘ f)) :
    (μS.map f hf).complexWeakIntegral g x y =
      μS.complexWeakIntegral (g ∘ f) x y := by
  unfold complexWeakIntegral
  rw [scalarMeasure_map]
  exact VectorMeasure.integral_map hf hgm hgi

lemma unitaryConjSpectralMeasure_weakIntegral
    {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    (u : H ≃ₗᵢ[ℂ] H') (μS : WOTSpectralMeasure α H) (f : α → ℝ) (x y : H') :
    (unitaryConjSpectralMeasure u μS).weakIntegral f x y =
      μS.weakIntegral f (u.symm x) (u.symm y) := by
  unfold weakIntegral
  rw [unitaryConjSpectralMeasure_scalarMeasure]

end WOTSpectralMeasure

end QuantumMechanics

end
