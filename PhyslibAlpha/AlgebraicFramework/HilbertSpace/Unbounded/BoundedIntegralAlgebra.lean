/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.BoundedIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!

# Algebra of the bounded weak-operator spectral integral

`boundedIntegral` (`BoundedIntegral.lean`) is well-defined independently of the choice of uniform
approximating sequence (`boundedIntegral_eq_of_uniform_approx`), which is what makes it possible
to prove it is a `*`-homomorphism from bounded measurable functions to `H →WOT[ℂ] H`: additive
(`boundedIntegral_add`), multiplicative (`boundedIntegral_mul`), star-compatible
(`boundedIntegral_star`), unital (`boundedIntegral_const`), and an isometry on the vector-state
norm (`boundedIntegral_norm_sq_eq_integral`, the operator-integral analogue of Plancherel). The
functional calculus this gives is exactly the bounded piece of what the spectral theorem is meant
to supply once the unbounded case is built: `f ↦ f(T)` for bounded Borel `f`, with no unbounded
operator `T` needed yet since everything here is stated directly against `μS`.

`ext_of_boundedIntegral_eq` upgrades the scalar-measure extensionality of `ScalarMeasure.lean` to
extensionality by the integral itself: two spectral measures agreeing on every bounded Borel
integral must already agree pointwise on measurable sets (specializing to the indicator function
recovers `ext_of_scalarMeasure_eq`).

## Main definitions

- `boundedIntegral_add`, `boundedIntegral_mul`, `boundedIntegral_star`, `boundedIntegral_const` :
  the `boundedIntegral` functional calculus is a unital `*`-homomorphism.
- `boundedIntegral_norm_sq_eq_integral` : `‖(boundedIntegral f) x‖² = ∫ |f|² dμₓ`.
- `ext_of_boundedIntegral_eq` : a spectral measure is determined by its bounded integrals.

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

/-! ## A. Independence from the approximating sequence -/

lemma boundedIntegral_eq_of_uniform_approx [Nonempty α]
    {f : α → ℂ} (hf : Measurable f) (hbdd : ∃ C, ∀ x, ‖f x‖ ≤ C)
    {s : ℕ → SimpleFunc α ℂ}
    (hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - f x‖ < ε) :
    boundedIntegral μS f hf hbdd = boundedIntegralOfUniformApprox μS f s hs := by
  let s₀ : ℕ → SimpleFunc α ℂ :=
    Classical.choose (exists_uniform_simple_approx hf hbdd)
  have hs₀ : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s₀ n x - f x‖ < ε :=
    (Classical.choose_spec (exists_uniform_simple_approx hf hbdd)).1
  unfold boundedIntegral
  dsimp [s₀]
  exact boundedIntegralOfUniformApprox_eq_of_same_target μS hs₀ hs

lemma boundedIntegral_eq_of_same_target [Nonempty α]
    {f : α → ℂ} {s t : ℕ → SimpleFunc α ℂ}
    (hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - f x‖ < ε)
    (ht : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖t n x - f x‖ < ε)
    (hf : Measurable f) (hbdd : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    boundedIntegralOfUniformApprox μS f s hs = boundedIntegral μS f hf hbdd := by
  symm
  rw [boundedIntegral_eq_of_uniform_approx μS hf hbdd ht]
  exact boundedIntegralOfUniformApprox_eq_of_same_target μS ht hs

lemma boundedIntegral_norm_le [Nonempty α]
    {f : α → ℂ} (hf : Measurable f) (hbdd : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    ∃ C : ℝ, ‖ContinuousLinearMapWOT.toCLM (boundedIntegral μS f hf hbdd)‖ ≤ C := by
  rcases Classical.choose_spec (exists_uniform_simple_approx hf hbdd) with ⟨hs, ⟨C, hC⟩⟩
  refine ⟨C, ?_⟩
  rw [boundedIntegral_eq_of_uniform_approx μS hf hbdd hs]
  exact boundedIntegralOfUniformApprox_norm_le μS _ _ hs hC

lemma boundedIntegral_norm_sq [Nonempty α]
    {f : α → ℂ} (hf : Measurable f) (hbdd : ∃ C, ∀ x, ‖f x‖ ≤ C) (x : H) :
    ENNReal.ofReal (‖boundedIntegral μS f hf hbdd x‖ ^ 2) =
      ∫⁻ z, ENNReal.ofReal (‖f z‖ ^ 2) ∂μS.diagonalMeasure x := by
  let s : ℕ → SimpleFunc α ℂ :=
    Classical.choose (exists_uniform_simple_approx hf hbdd)
  have hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ z, ‖s n z - f z‖ < ε :=
    (Classical.choose_spec (exists_uniform_simple_approx hf hbdd)).1
  have hsBound : ∃ C : ℝ, ∀ n z, ‖s n z‖ ≤ C :=
    (Classical.choose_spec (exists_uniform_simple_approx hf hbdd)).2
  have hclm : Filter.Tendsto
      (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n))) Filter.atTop
      (𝓝 (ContinuousLinearMapWOT.toCLM (boundedIntegral μS f hf hbdd))) := by
    rw [boundedIntegral_eq_of_uniform_approx μS hf hbdd hs]
    rw [boundedIntegralOfUniformApprox_eq_limUnder]
    exact (simpleIntegral_toCLM_cauchySeq μS hs).tendsto_limUnder
  have hvec : Filter.Tendsto (fun n => simpleIntegral μS (s n) x) Filter.atTop
      (𝓝 (boundedIntegral μS f hf hbdd x)) := by
    have hev : Continuous (fun A : H →L[ℂ] H => A x) := by fun_prop
    exact hev.continuousAt.tendsto.comp hclm
  have hnorm : Filter.Tendsto
      (fun n => ENNReal.ofReal (‖simpleIntegral μS (s n) x‖ ^ 2)) Filter.atTop
      (𝓝 (ENNReal.ofReal (‖boundedIntegral μS f hf hbdd x‖ ^ 2))) := by
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((continuous_norm.pow 2).continuousAt.tendsto.comp hvec)
  let μ : Measure α := μS.diagonalMeasure x
  let F : ℕ → α → ENNReal := fun n z => ENNReal.ofReal (‖s n z‖ ^ 2)
  let F₀ : α → ENNReal := fun z => ENNReal.ofReal (‖f z‖ ^ 2)
  have hFmeas : ∀ n, Measurable (F n) := by
    intro n
    dsimp [F]
    fun_prop
  have hC0 : ∃ C : ℝ, 0 ≤ C ∧ ∀ n z, ‖s n z‖ ≤ C := by
    rcases hsBound with ⟨C, hC⟩
    have hC0 : 0 ≤ C := by
      let a₀ : α := Classical.choice (inferInstance : Nonempty α)
      exact (norm_nonneg (s 0 a₀)).trans (hC 0 a₀)
    exact ⟨C, hC0, hC⟩
  rcases hC0 with ⟨C, hC0, hC⟩
  have hbound : ∀ n, F n ≤ᵐ[μ] (fun _ : α => ENNReal.ofReal (C ^ 2)) := by
    intro n
    filter_upwards [] with z
    dsimp [F]
    apply ENNReal.ofReal_le_ofReal
    exact (sq_le_sq₀ (norm_nonneg (s n z)) hC0).mpr (hC n z)
  have hfin : (∫⁻ z, ENNReal.ofReal (C ^ 2) ∂μ) ≠ (⊤ : ENNReal) := by
    rw [lintegral_const, μS.diagonalMeasure_univ]
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    exact ENNReal.ofReal_ne_top
  have hlim : ∀ᵐ z ∂μ, Filter.Tendsto (fun n => F n z) Filter.atTop (𝓝 (F₀ z)) := by
    filter_upwards [] with z
    have hz : Filter.Tendsto (fun n => s n z) Filter.atTop (𝓝 (f z)) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      rcases hs ε hε with ⟨N, hN⟩
      exact ⟨N, fun n hn => by simpa only [dist_eq_norm] using hN n hn z⟩
    have hnorm' : Filter.Tendsto (fun n => ‖s n z‖) Filter.atTop (𝓝 ‖f z‖) :=
      continuous_norm.continuousAt.tendsto.comp hz
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((continuous_id.pow 2).continuousAt.tendsto.comp hnorm')
  have hlintegral : Filter.Tendsto (fun n => ∫⁻ z, F n z ∂μ) Filter.atTop
      (𝓝 (∫⁻ z, F₀ z ∂μ)) :=
    MeasureTheory.tendsto_lintegral_of_dominated_convergence
      (fun _ : α => ENNReal.ofReal (C ^ 2)) hFmeas hbound hfin hlim
  have hlintegral' : Filter.Tendsto
      (fun n => ENNReal.ofReal (‖simpleIntegral μS (s n) x‖ ^ 2)) Filter.atTop
      (𝓝 (∫⁻ z, ENNReal.ofReal (‖f z‖ ^ 2) ∂μS.diagonalMeasure x)) := by
    simpa only [F, F₀, μ, μS.simpleIntegral_norm_sq_eq_lintegral] using hlintegral
  exact tendsto_nhds_unique hnorm hlintegral'

lemma boundedIntegral_norm_le_of_bound [Nonempty α]
    {f : α → ℂ} (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (hCf : ∀ x, ‖f x‖ ≤ C) :
    ‖ContinuousLinearMapWOT.toCLM
      (boundedIntegral μS f hf (⟨C, hCf⟩ : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C))‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_iff hC |>.2
  intro x
  have hsq : ∀ z, ‖f z‖ ^ 2 ≤ C ^ 2 := by
    intro z
    exact (sq_le_sq₀ (norm_nonneg (f z)) hC).mpr (hCf z)
  have hpoint : ∀ z, ENNReal.ofReal (‖f z‖ ^ 2) ≤ ENNReal.ofReal (C ^ 2) := by
    intro z
    exact ENNReal.ofReal_le_ofReal (hsq z)
  have hlin : (∫⁻ z, ENNReal.ofReal (‖f z‖ ^ 2)
      ∂μS.diagonalMeasure x) ≤ ENNReal.ofReal (C ^ 2 * ‖x‖ ^ 2) := by
    calc
      (∫⁻ z, ENNReal.ofReal (‖f z‖ ^ 2) ∂μS.diagonalMeasure x) ≤
          ∫⁻ _ : α, ENNReal.ofReal (C ^ 2) ∂μS.diagonalMeasure x :=
        lintegral_mono_ae (Filter.Eventually.of_forall hpoint)
      _ = ENNReal.ofReal (C ^ 2 * ‖x‖ ^ 2) := by
        rw [lintegral_const, μS.diagonalMeasure_univ,
          ← ENNReal.ofReal_mul (sq_nonneg C)]
  have hnormsq : ENNReal.ofReal
      (‖boundedIntegral μS f hf (⟨C, hCf⟩ : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) x‖ ^ 2) ≤
      ENNReal.ofReal (C ^ 2 * ‖x‖ ^ 2) := by
    rw [boundedIntegral_norm_sq]
    exact hlin
  have hreal : ‖boundedIntegral μS f hf
      (⟨C, hCf⟩ : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) x‖ ^ 2 ≤
      C ^ 2 * ‖x‖ ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg C) (sq_nonneg ‖x‖))).mp hnormsq
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  calc
    ‖boundedIntegral μS f hf
        (⟨C, hCf⟩ : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) x‖ ^ 2 ≤
        C ^ 2 * ‖x‖ ^ 2 := hreal
    _ = (C * ‖x‖) ^ 2 := by ring

lemma boundedIntegral_norm_sq_eq_integral [Nonempty α]
    {f : α → ℂ} (hf : Measurable f) (hbdd : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) (x : H) :
    ‖boundedIntegral μS f hf hbdd x‖ ^ 2 =
      ∫ z, ‖f z‖ ^ 2 ∂μS.diagonalMeasure x := by
  rcases hbdd with ⟨C, hCf⟩
  let a₀ : α := Classical.choice (inferInstance : Nonempty α)
  have hC : 0 ≤ C := (norm_nonneg (f a₀)).trans (hCf a₀)
  have hfi : Integrable (fun z : α => ‖f z‖ ^ 2) (μS.diagonalMeasure x) := by
    apply Integrable.of_bound (hf.norm.pow_const 2).aestronglyMeasurable (C ^ 2)
    filter_upwards [] with z
    simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖f z‖))] using
      (sq_le_sq₀ (norm_nonneg (f z)) hC).mpr (hCf z)
  have hpos : 0 ≤ᵐ[μS.diagonalMeasure x] (fun z : α => ‖f z‖ ^ 2) :=
    Filter.Eventually.of_forall (fun z => sq_nonneg _)
  have hconvert : ENNReal.ofReal (∫ z, ‖f z‖ ^ 2 ∂μS.diagonalMeasure x) =
      ∫⁻ z, ENNReal.ofReal (‖f z‖ ^ 2) ∂μS.diagonalMeasure x :=
    ofReal_integral_eq_lintegral_ofReal hfi hpos
  have hmain := boundedIntegral_norm_sq μS hf (⟨C, hCf⟩ : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) x
  rw [← hconvert] at hmain
  exact (ENNReal.ofReal_eq_ofReal_iff (sq_nonneg _)
    (integral_nonneg (fun z => sq_nonneg (‖f z‖)))).mp hmain

/-! ## B. The algebra of the integral -/

private lemma boundedIntegralOfUniformApprox_add [Nonempty α]
    {f g : α → ℂ} {s t : ℕ → SimpleFunc α ℂ}
    (hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - f x‖ < ε)
    (ht : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖t n x - g x‖ < ε)
    (hsg : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x,
      ‖(s n + t n) x - (f + g) x‖ < ε) :
    boundedIntegralOfUniformApprox μS (f + g) (fun n => s n + t n) hsg =
      boundedIntegralOfUniformApprox μS f s hs +
        boundedIntegralOfUniformApprox μS g t ht := by
  apply ContinuousLinearMapWOT.toCLM_injective
  have hfs : Filter.Tendsto
      (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n))) Filter.atTop
      (𝓝 (ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS f s hs))) := by
    rw [boundedIntegralOfUniformApprox_eq_limUnder]
    exact (simpleIntegral_toCLM_cauchySeq μS hs).tendsto_limUnder
  have hgt : Filter.Tendsto
      (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (t n))) Filter.atTop
      (𝓝 (ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS g t ht))) := by
    rw [boundedIntegralOfUniformApprox_eq_limUnder]
    exact (simpleIntegral_toCLM_cauchySeq μS ht).tendsto_limUnder
  have hsum : Filter.Tendsto
      (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n)) +
        ContinuousLinearMapWOT.toCLM (simpleIntegral μS (t n))) Filter.atTop
      (𝓝 (ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS f s hs) +
        ContinuousLinearMapWOT.toCLM
          (boundedIntegralOfUniformApprox μS g t ht))) := hfs.add hgt
  have hsum' : Filter.Tendsto
      (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS ((s + t) n))) Filter.atTop
      (𝓝 (ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS (f + g) (fun n => s n + t n) hsg))) := by
    rw [boundedIntegralOfUniformApprox_eq_limUnder]
    exact (simpleIntegral_toCLM_cauchySeq μS hsg).tendsto_limUnder
  have hsum'' : Filter.Tendsto
      (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n)) +
        ContinuousLinearMapWOT.toCLM (simpleIntegral μS (t n))) Filter.atTop
      (𝓝 (ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS (f + g) (fun n => s n + t n) hsg))) := by
    simpa only [Pi.add_apply, simpleIntegral_add, ContinuousLinearMapWOT.toCLM_add] using hsum'
  exact tendsto_nhds_unique hsum'' hsum

private lemma boundedIntegralOfUniformApprox_neg [Nonempty α]
    {f : α → ℂ} {s : ℕ → SimpleFunc α ℂ}
    (hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - f x‖ < ε)
    (hneg : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x,
      ‖(-s n) x - (-f x)‖ < ε) :
    boundedIntegralOfUniformApprox μS (fun x => -f x) (fun n => -s n) hneg =
      -boundedIntegralOfUniformApprox μS f s hs := by
  apply ContinuousLinearMapWOT.toCLM_injective
  have hfs : Filter.Tendsto
      (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n))) Filter.atTop
      (𝓝 (ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS f s hs))) := by
    rw [boundedIntegralOfUniformApprox_eq_limUnder]
    exact (simpleIntegral_toCLM_cauchySeq μS hs).tendsto_limUnder
  have hneg' : Filter.Tendsto
      (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS ((-s) n))) Filter.atTop
      (𝓝 (ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS (fun x => -f x) (fun n => -s n) hneg))) := by
    rw [boundedIntegralOfUniformApprox_eq_limUnder]
    exact (simpleIntegral_toCLM_cauchySeq μS hneg).tendsto_limUnder
  have hneg'' : Filter.Tendsto
      (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS ((-s) n))) Filter.atTop
      (𝓝 (-ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS f s hs))) := by
    simpa only [Pi.neg_apply, simpleIntegral_neg, ContinuousLinearMapWOT.toCLM_neg] using hfs.neg
  exact tendsto_nhds_unique hneg' hneg''

lemma boundedIntegral_neg [Nonempty α]
    {f : α → ℂ} (hf : Measurable f) (hbf : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    boundedIntegral μS (fun x => -f x) (continuous_neg.measurable.comp hf)
        (by
          rcases hbf with ⟨C, hC⟩
          exact ⟨C, fun x => by simpa using hC x⟩) =
      -boundedIntegral μS f hf hbf := by
  classical
  rcases exists_uniform_simple_approx hf hbf with ⟨s, hs, hsB⟩
  have hneg : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x,
      ‖(-s n) x - (-(f x))‖ < ε := by
    intro ε hε
    rcases hs ε hε with ⟨N, hN⟩
    refine ⟨N, fun n hn x => ?_⟩
    change ‖-s n x - -f x‖ < ε
    calc
      ‖-s n x - -f x‖ = ‖-(s n x - f x)‖ := by congr 1; ring
      _ = ‖s n x - f x‖ := norm_neg _
      _ < ε := hN n hn x
  calc
    boundedIntegral μS (fun x => -f x) (continuous_neg.measurable.comp hf) _ =
        boundedIntegralOfUniformApprox μS (fun x => -f x) (fun n => -s n) hneg :=
      boundedIntegral_eq_of_uniform_approx μS (continuous_neg.measurable.comp hf) _ hneg
    _ = -boundedIntegralOfUniformApprox μS f s hs :=
      boundedIntegralOfUniformApprox_neg μS hs hneg
    _ = -boundedIntegral μS f hf hbf := by
      rw [boundedIntegral_eq_of_uniform_approx μS hf hbf hs]

lemma boundedIntegral_add [Nonempty α]
    {f g : α → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hbf : ∃ C, ∀ x, ‖f x‖ ≤ C) (hbg : ∃ C, ∀ x, ‖g x‖ ≤ C) :
    boundedIntegral μS (f + g) (hf.add hg)
        (by
          rcases hbf with ⟨Cf, hCf⟩
          rcases hbg with ⟨Cg, hCg⟩
          refine ⟨Cf + Cg, fun x => ?_⟩
          exact (norm_add_le _ _).trans (add_le_add (hCf x) (hCg x))) =
      boundedIntegral μS f hf hbf + boundedIntegral μS g hg hbg := by
  classical
  rcases exists_uniform_simple_approx hf hbf with ⟨s, hs, hsB⟩
  rcases exists_uniform_simple_approx hg hbg with ⟨t, ht, htB⟩
  have hsg : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x,
      ‖(s n + t n) x - (f + g) x‖ < ε := by
    intro ε hε
    rcases hs (ε / 2) (by linarith) with ⟨Ns, hNs⟩
    rcases ht (ε / 2) (by linarith) with ⟨Nt, hNt⟩
    refine ⟨max Ns Nt, fun n hn x => ?_⟩
    simp only [Pi.add_apply, SimpleFunc.add_apply]
    calc
      ‖(s n x + t n x) - (f x + g x)‖ =
          ‖(s n x - f x) + (t n x - g x)‖ := by ring_nf
      _ ≤ ‖s n x - f x‖ + ‖t n x - g x‖ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add
        (hNs n (le_trans (le_max_left _ _) hn) x)
        (hNt n (le_trans (le_max_right _ _) hn) x)
      _ = ε := by ring
  rw [boundedIntegral_eq_of_uniform_approx μS (hf.add hg) _ hsg,
    boundedIntegral_eq_of_uniform_approx μS hf hbf hs,
    boundedIntegral_eq_of_uniform_approx μS hg hbg ht]
  exact boundedIntegralOfUniformApprox_add μS hs ht hsg

lemma boundedIntegral_const [Nonempty α] (c : ℂ) :
    boundedIntegral μS (fun _ : α => c) measurable_const
        (⟨‖c‖, fun _ => le_rfl⟩) = c • (1 : H →WOT[ℂ] H) := by
  let s : ℕ → SimpleFunc α ℂ := fun _ => SimpleFunc.const α c
  have hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - (fun _ : α => c) x‖ < ε := by
    intro ε hε
    exact ⟨0, fun n hn x => by simp [s, hε]⟩
  rw [boundedIntegral_eq_of_uniform_approx μS measurable_const
    (⟨‖c‖, fun _ => le_rfl⟩) hs]
  apply ContinuousLinearMapWOT.toCLM_injective
  have hconst := boundedIntegralOfUniformApprox_eq_limUnder μS
    (fun _ : α => c) s hs
  rw [hconst]
  rw [show (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n))) =
      (fun _ => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s 0))) by
        funext n; rfl]
  have hlim : Filter.Tendsto
      (fun _ : ℕ => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s 0))) Filter.atTop
      (𝓝 (ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s 0)))) := tendsto_const_nhds
  rw [hlim.limUnder_eq]
  change ContinuousLinearMapWOT.toCLM (simpleIntegral μS (SimpleFunc.const α c)) =
    ContinuousLinearMapWOT.toCLM (c • (1 : H →WOT[ℂ] H))
  rw [simpleIntegral_const]

lemma boundedIntegral_congr [Nonempty α]
    {f g : α → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hbf : ∃ C, ∀ x, ‖f x‖ ≤ C) (hbg : ∃ C, ∀ x, ‖g x‖ ≤ C)
    (hfg : ∀ x, f x = g x) :
    boundedIntegral μS f hf hbf = boundedIntegral μS g hg hbg := by
  rcases exists_uniform_simple_approx hf hbf with ⟨s, hs, hsB⟩
  have hs' : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - g x‖ < ε := by
    intro ε hε
    rcases hs ε hε with ⟨N, hN⟩
    refine ⟨N, fun n hn x => ?_⟩
    rw [← hfg x]
    exact hN n hn x
  exact (boundedIntegral_eq_of_uniform_approx μS hf hbf hs).trans
    (boundedIntegral_eq_of_uniform_approx μS hg hbg hs').symm

lemma boundedIntegral_indicator [Nonempty α] {S : Set α} (hS : MeasurableSet S) :
    boundedIntegral μS (S.indicator (fun _ : α => (1 : ℂ)))
        (measurable_const.indicator hS)
        (⟨1, fun x => by by_cases hx : x ∈ S <;> simp [hx]⟩) = μS S := by
  let s : ℕ → SimpleFunc α ℂ := fun _ =>
    SimpleFunc.piecewise S hS (SimpleFunc.const α (1 : ℂ))
      (SimpleFunc.const α (0 : ℂ))
  have hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x,
      ‖s n x - S.indicator (fun _ : α => (1 : ℂ)) x‖ < ε := by
    intro ε hε
    refine ⟨0, fun n hn x => ?_⟩
    rw [show s n = SimpleFunc.piecewise S hS
      (SimpleFunc.const α (1 : ℂ)) (SimpleFunc.const α (0 : ℂ)) by rfl]
    rw [SimpleFunc.coe_piecewise hS]
    simp only [SimpleFunc.coe_const, Function.const_zero, Set.piecewise_eq_indicator]
    change ‖S.indicator (fun _ : α => (1 : ℂ)) x -
      S.indicator (fun _ : α => (1 : ℂ)) x‖ < ε
    simp only [sub_self, norm_zero]
    exact hε
  rw [boundedIntegral_eq_of_uniform_approx μS (measurable_const.indicator hS)
    (⟨1, fun x => by by_cases hx : x ∈ S <;> simp [hx]⟩) hs]
  apply ContinuousLinearMapWOT.toCLM_injective
  rw [boundedIntegralOfUniformApprox_eq_limUnder μS _ s hs]
  rw [show (fun n : ℕ => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n))) =
      (fun _ : ℕ => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s 0))) by
        funext n; rfl]
  rw [tendsto_const_nhds.limUnder_eq]
  change ContinuousLinearMapWOT.toCLM (simpleIntegral μS
      (SimpleFunc.piecewise S hS (SimpleFunc.const α (1 : ℂ))
        (SimpleFunc.const α (0 : ℂ)))) = ContinuousLinearMapWOT.toCLM (μS S)
  rw [simpleIntegral_piecewise_indicator]

/-! ## C. Extensionality by the integral -/

/-- A bounded spectral integral determines a weak spectral measure. In particular, this gives a
usable uniqueness principle for any construction which agrees with the canonical integral on
bounded Borel multipliers. -/
theorem ext_of_boundedIntegral_eq [Nonempty α]
    {μS νS : WOTSpectralMeasure α H}
    (h : ∀ (f : α → ℂ) (hf : Measurable f) (hfb : ∃ C : ℝ, ∀ a, ‖f a‖ ≤ C),
      μS.boundedIntegral f hf hfb = νS.boundedIntegral f hf hfb) :
    μS = νS := by
  apply ext_of_scalarMeasure_eq
  intro x y
  apply MeasureTheory.VectorMeasure.ext
  intro S hS
  have h₁ := h (S.indicator (fun _ : α => (1 : ℂ)))
    (measurable_const.indicator hS) (by
      refine ⟨1, fun a => ?_⟩
      by_cases ha : a ∈ S <;> simp [Set.indicator, ha])
  have h₂ := congrArg (fun A : H →WOT[ℂ] H => ⟪y, A x⟫_ℂ) h₁
  simpa [boundedIntegral_indicator μS hS, boundedIntegral_indicator νS hS,
    scalarMeasure_apply] using h₂

lemma boundedIntegral_sub [Nonempty α]
    {f g : α → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hbf : ∃ C, ∀ x, ‖f x‖ ≤ C) (hbg : ∃ C, ∀ x, ‖g x‖ ≤ C) :
    boundedIntegral μS (f - g) (hf.sub hg)
        (by
          rcases hbf with ⟨Cf, hCf⟩
          rcases hbg with ⟨Cg, hCg⟩
          refine ⟨Cf + Cg, fun x => ?_⟩
          exact (norm_sub_le _ _).trans (add_le_add (hCf x) (hCg x))) =
      boundedIntegral μS f hf hbf - boundedIntegral μS g hg hbg := by
  have hsubBound : ∃ C, ∀ x, ‖(f - g) x‖ ≤ C := by
    rcases hbf with ⟨Cf, hCf⟩
    rcases hbg with ⟨Cg, hCg⟩
    refine ⟨Cf + Cg, fun x => ?_⟩
    exact (norm_sub_le _ _).trans (add_le_add (hCf x) (hCg x))
  have hg' : Measurable (fun x => -g x) := continuous_neg.measurable.comp hg
  have hbg' : ∃ C, ∀ x, ‖-g x‖ ≤ C := by
    rcases hbg with ⟨C, hC⟩
    exact ⟨C, fun x => by simpa using hC x⟩
  have hneg := boundedIntegral_neg μS hg hbg
  have hadd := boundedIntegral_add μS hf hg' hbf hbg'
  have haddBound : ∃ C, ∀ x, ‖(f + (fun x => -g x)) x‖ ≤ C := by
    rcases hbf with ⟨Cf, hCf⟩
    rcases hbg' with ⟨Cg, hCg⟩
    refine ⟨Cf + Cg, fun x => ?_⟩
    exact (norm_add_le _ _).trans (add_le_add (hCf x) (hCg x))
  calc
    boundedIntegral μS (f - g) (hf.sub hg) hsubBound =
        boundedIntegral μS f hf hbf +
          boundedIntegral μS (fun x => -g x) hg' hbg' := by
      calc
        boundedIntegral μS (f - g) (hf.sub hg) hsubBound =
            boundedIntegral μS (f + (fun x => -g x))
              (hf.add hg') haddBound := by
          apply boundedIntegral_congr μS (hf.sub hg) (hf.add hg') hsubBound haddBound
          intro x
          simp [Pi.sub_apply, sub_eq_add_neg]
        _ = boundedIntegral μS f hf hbf +
            boundedIntegral μS (fun x => -g x)
              hg' hbg' := by exact hadd
    _ = boundedIntegral μS f hf hbf - boundedIntegral μS g hg hbg := by rw [hneg, sub_eq_add_neg]

private lemma boundedIntegralOfUniformApprox_mul [Nonempty α]
    {f g : α → ℂ} {s t : ℕ → SimpleFunc α ℂ}
    (hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - f x‖ < ε)
    (ht : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖t n x - g x‖ < ε)
    (hprod : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x,
      ‖(s n * t n) x - (f * g) x‖ < ε) :
    boundedIntegralOfUniformApprox μS (f * g) (fun n => s n * t n) hprod =
      boundedIntegralOfUniformApprox μS f s hs *
        boundedIntegralOfUniformApprox μS g t ht := by
  apply ContinuousLinearMapWOT.toCLM_injective
  have hfs : Filter.Tendsto
      (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n))) Filter.atTop
      (𝓝 (ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS f s hs))) := by
    rw [boundedIntegralOfUniformApprox_eq_limUnder]
    exact (simpleIntegral_toCLM_cauchySeq μS hs).tendsto_limUnder
  have hgt : Filter.Tendsto
      (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (t n))) Filter.atTop
      (𝓝 (ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS g t ht))) := by
    rw [boundedIntegralOfUniformApprox_eq_limUnder]
    exact (simpleIntegral_toCLM_cauchySeq μS ht).tendsto_limUnder
  have hmul : Filter.Tendsto
      (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n)) *
        ContinuousLinearMapWOT.toCLM (simpleIntegral μS (t n))) Filter.atTop
      (𝓝 (ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS f s hs) *
        ContinuousLinearMapWOT.toCLM (boundedIntegralOfUniformApprox μS g t ht))) :=
    hfs.mul hgt
  have hprod' : Filter.Tendsto
      (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS ((s * t) n))) Filter.atTop
      (𝓝 (ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS (f * g) (fun n => s n * t n) hprod))) := by
    rw [boundedIntegralOfUniformApprox_eq_limUnder]
    exact (simpleIntegral_toCLM_cauchySeq μS hprod).tendsto_limUnder
  have hprod'' : Filter.Tendsto
      (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n)) *
        ContinuousLinearMapWOT.toCLM (simpleIntegral μS (t n))) Filter.atTop
      (𝓝 (ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS (f * g) (fun n => s n * t n) hprod))) := by
    apply hprod'.congr'
    filter_upwards [] with n
    change ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n * t n)) =
      ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n)) *
        ContinuousLinearMapWOT.toCLM (simpleIntegral μS (t n))
    rw [simpleIntegral_mul, ContinuousLinearMapWOT.toCLM_mul]
  exact tendsto_nhds_unique hprod'' hmul

lemma boundedIntegral_mul [Nonempty α]
    {f g : α → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hbf : ∃ C, ∀ x, ‖f x‖ ≤ C) (hbg : ∃ C, ∀ x, ‖g x‖ ≤ C) :
    boundedIntegral μS (f * g) (hf.mul hg)
        (by
          rcases hbf with ⟨Cf, hCf⟩
          rcases hbg with ⟨Cg, hCg⟩
          let a₀ : α := Classical.choice (inferInstance : Nonempty α)
          have hCf0 : 0 ≤ Cf := (norm_nonneg (f a₀)).trans (hCf a₀)
          refine ⟨Cf * Cg, fun x => ?_⟩
          rw [Pi.mul_apply, norm_mul]
          exact mul_le_mul (hCf x) (hCg x) (norm_nonneg _) hCf0) =
      boundedIntegral μS f hf hbf * boundedIntegral μS g hg hbg := by
  classical
  rcases hbf with ⟨Cf, hCf⟩
  rcases hbg with ⟨Cg, hCg⟩
  let hbf' : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := ⟨Cf, hCf⟩
  let hbg' : ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C := ⟨Cg, hCg⟩
  rcases exists_uniform_simple_approx hf hbf' with ⟨sf, hsf, hsfB⟩
  rcases exists_uniform_simple_approx hg hbg' with ⟨sg, hsg, hsgB⟩
  rcases hsfB with ⟨Cs, hCs⟩
  let a₀ : α := Classical.choice (inferInstance : Nonempty α)
  have hCs0 : 0 ≤ Cs := (norm_nonneg (sf 0 a₀)).trans (hCs 0 a₀)
  have hCg0 : 0 ≤ Cg := (norm_nonneg (g a₀)).trans (hCg a₀)
  have hD0 : 0 < Cs + Cg + 1 := by linarith
  have hprod : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x,
      ‖(sf n * sg n) x - (f * g) x‖ < ε := by
    intro ε hε
    let δ : ℝ := ε / (2 * (Cs + Cg + 1))
    have hδ : 0 < δ := by dsimp [δ]; positivity
    rcases hsf δ hδ with ⟨Nf, hNf⟩
    rcases hsg δ hδ with ⟨Ng, hNg⟩
    refine ⟨max Nf Ng, fun n hn x => ?_⟩
    simp only [SimpleFunc.mul_apply, Pi.mul_apply]
    have hsferr : ‖sf n x - f x‖ < δ := hNf n (le_trans (le_max_left _ _) hn) x
    have hsgerr : ‖sg n x - g x‖ < δ := hNg n (le_trans (le_max_right _ _) hn) x
    have hdecomp : sf n x * sg n x - f x * g x =
        sf n x * (sg n x - g x) + (sf n x - f x) * g x := by ring
    calc
      ‖sf n x * sg n x - f x * g x‖ =
          ‖sf n x * (sg n x - g x) + (sf n x - f x) * g x‖ := by rw [hdecomp]
      _ ≤ ‖sf n x‖ * ‖sg n x - g x‖ +
          ‖sf n x - f x‖ * ‖g x‖ := by
            calc
              _ ≤ ‖sf n x * (sg n x - g x)‖ +
                  ‖(sf n x - f x) * g x‖ := norm_add_le _ _
              _ = _ := by rw [norm_mul, norm_mul]
      _ ≤ Cs * δ + δ * Cg := by
        exact add_le_add
          (mul_le_mul (hCs n x) (le_of_lt hsgerr) (norm_nonneg _) hCs0)
          (mul_le_mul (le_of_lt hsferr) (hCg x) (norm_nonneg _) hδ.le)
      _ < ε := by
        calc
          Cs * δ + δ * Cg = (Cs + Cg) * δ := by ring
          _ ≤ (Cs + Cg + 1) * δ := by
            exact mul_le_mul_of_nonneg_right (by linarith) hδ.le
          _ = ε / 2 := by dsimp [δ]; field_simp
          _ < ε := by linarith
  rw [boundedIntegral_eq_of_uniform_approx μS (hf.mul hg) _ hprod,
    boundedIntegral_eq_of_uniform_approx μS hf hbf' hsf,
    boundedIntegral_eq_of_uniform_approx μS hg hbg' hsg]
  exact boundedIntegralOfUniformApprox_mul μS hsf hsg hprod

lemma boundedIntegral_smul [Nonempty α] (c : ℂ) {f : α → ℂ} (hf : Measurable f)
    (hbf : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    boundedIntegral μS (fun x => c * f x)
        (measurable_const.mul hf)
        (by
          rcases hbf with ⟨C, hC⟩
          refine ⟨‖c‖ * C, fun x => ?_⟩
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg c)) =
      c • boundedIntegral μS f hf hbf := by
  have hmul := boundedIntegral_mul μS measurable_const hf
    (⟨‖c‖, fun _ => le_rfl⟩) hbf
  rw [boundedIntegral_const] at hmul
  change boundedIntegral μS ((fun _ : α => c) * f) _ _ = _
  have hone : (c • (1 : H →WOT[ℂ] H)) * boundedIntegral μS f hf hbf =
      c • boundedIntegral μS f hf hbf := by
    ext x
    simp [ContinuousLinearMapWOT.mul_apply]
  rw [← hone]
  exact hmul

private lemma boundedIntegralOfUniformApprox_star [Nonempty α]
    {f : α → ℂ} {s : ℕ → SimpleFunc α ℂ}
    (hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - f x‖ < ε)
    (hstar : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x,
      ‖(star (s n)) x - star (f x)‖ < ε) :
    boundedIntegralOfUniformApprox μS (fun x => star (f x)) (fun n => star (s n)) hstar =
      star (boundedIntegralOfUniformApprox μS f s hs) := by
  apply ContinuousLinearMapWOT.toCLM_injective
  have hfs : Filter.Tendsto
      (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n))) Filter.atTop
      (𝓝 (ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS f s hs))) := by
    rw [boundedIntegralOfUniformApprox_eq_limUnder]
    exact (simpleIntegral_toCLM_cauchySeq μS hs).tendsto_limUnder
  have hstarlim : Filter.Tendsto
      (fun n => star (ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n)))) Filter.atTop
      (𝓝 (star (ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS f s hs)))) :=
    continuous_star.continuousAt.tendsto.comp hfs
  have hstar' : Filter.Tendsto
      (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (star (s n)))) Filter.atTop
      (𝓝 (ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS (fun x => star (f x)) (fun n => star (s n))
          hstar))) := by
    rw [boundedIntegralOfUniformApprox_eq_limUnder]
    exact (simpleIntegral_toCLM_cauchySeq μS hstar).tendsto_limUnder
  have hstar'' : Filter.Tendsto
      (fun n => star (ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n)))) Filter.atTop
      (𝓝 (ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS (fun x => star (f x)) (fun n => star (s n))
          hstar))) := by
    convert hstar' using 1
    · funext n
      rw [simpleIntegral_star]
      apply ContinuousLinearMap.ext
      intro x
      rfl
  exact tendsto_nhds_unique hstar'' hstarlim

lemma boundedIntegral_star [Nonempty α]
    {f : α → ℂ} (hf : Measurable f) (hbf : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    boundedIntegral μS (fun x => star (f x)) (continuous_star.measurable.comp hf)
        (by
          rcases hbf with ⟨C, hC⟩
          exact ⟨C, fun x => by simpa using hC x⟩) =
      star (boundedIntegral μS f hf hbf) := by
  classical
  rcases exists_uniform_simple_approx hf hbf with ⟨s, hs, hsB⟩
  have hstar : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x,
      ‖(star (s n)) x - star (f x)‖ < ε := by
    intro ε hε
    rcases hs ε hε with ⟨N, hN⟩
    refine ⟨N, fun n hn x => ?_⟩
    change ‖star ((s n) x) - star (f x)‖ < ε
    rw [← star_sub, norm_star]
    exact hN n hn x
  calc
    boundedIntegral μS (fun x => star (f x)) (continuous_star.measurable.comp hf) _ =
        boundedIntegralOfUniformApprox μS (fun x => star (f x)) (fun n => star (s n)) hstar :=
      boundedIntegral_eq_of_uniform_approx μS (continuous_star.measurable.comp hf) _ hstar
    _ = star (boundedIntegralOfUniformApprox μS f s hs) :=
      boundedIntegralOfUniformApprox_star μS hs hstar
    _ = star (boundedIntegral μS f hf hbf) := by
      rw [boundedIntegral_eq_of_uniform_approx μS hf hbf hs]

end WOTSpectralMeasure

end QuantumMechanics

end
