/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.RetardedKernel.BoundaryValue
public import PhyslibAlpha.Mathematics.Fourier.Marginal
public import PhyslibAlpha.Mathematics.Fourier.SchwartzDecay
public import PhyslibAlpha.Mathematics.SpecialFunctions.SincPropagator.Resolvent

/-!

# The Fourier form of the tempered retarded kernel

The retarded kernel on Schwartz functions is the boundary value of the resolvent integrated
against the spacetime Fourier transform.

## i. Overview

The pairing of the spacetime Fourier transform with the resolvent at the complexified frequency
`2π w + i ε` is continuous on Schwartz space for each `ε > 0`. The bound is `2 / ε²` times the
`L¹` norm of the transform. For test functions the pairing is the damped kernel. The damped kernel
is bounded by a Schwartz seminorm that does not depend on `ε`. So the pairings converge on all
Schwartz functions to the tempered kernel. No principal value analysis near the mass shell is
needed.

## ii. Key results

- `fourierPairing` : the pairing of the spacetime Fourier transform with the resolvent.
- `norm_fourierPairing_le` : the pairing is bounded by `2 / ε²` times the `L¹` norm of the
  transform.
- `fourierPairing_eq_integral_integral` : the pairing as an iterated integral over `ξ` and `w`.
- `fourierPairing_ofTestFunction` : on test functions the pairing is the damped kernel.
- `exists_abs_dampedKernel_le` : the damped kernel is bounded by a Schwartz seminorm uniformly in
  `ε`.
- `exists_abs_fourierPairing_le` : the same bound on all Schwartz functions.
- `tendsto_fourierPairing` : the tempered kernel is the boundary value `ε → 0+` of the pairing
  for every real Schwartz function.

## iii. Table of contents

- A. The split space and the resolvent
- B. The pairing
- C. Test functions
- D. The boundary value on Schwartz space

## iv. References

None.

## A. The split space and the resolvent

- `SplitSpace` : time and space with the Euclidean product norm.

## B. The pairing

- `splitSource` : a real Schwartz function of spacetime as a complex one of the split space.
- `spacetimeFourier` : the spacetime Fourier transform.
- `fourierPairing` : the pairing with the resolvent.
- `continuous_pairingRe` : the pairing is continuous on Schwartz space for each `ε > 0`.

## C. Test functions

- `fourierPairing_ofTestFunction` : on test functions the pairing is the damped kernel.
- `exists_abs_dampedKernel_le` : the uniform bound.

## D. The boundary value on Schwartz space

- `exists_abs_fourierPairing_le` : the uniform bound on Schwartz space by closure.
- `tendsto_fourierPairing` : the boundary value.
-/

@[expose] public section

noncomputable section

open scoped SchwartzMap FourierTransform ContDiff Distributions
open SchwartzMap MeasureTheory TestFunction TimeSlice TopologicalSpace KleinGordon.Spacetime

namespace KleinGordon

/-- Time and space with the Euclidean product norm. -/
abbrev SplitSpace (d : ℕ) := WithLp 2 (ℝ × Space d)

variable {d : ℕ}

/-- The resolvent as a function on the split space. -/
def splitResolvent (μ ε : ℝ) (p : SplitSpace d) : ℂ := resolvent μ ε p.ofLp.1 p.ofLp.2

lemma norm_splitResolvent_le {μ : ℝ} {ε : ℝ} (hε : 0 < ε) (p : SplitSpace d) :
    ‖splitResolvent μ ε p‖ ≤ 2 / ε ^ 2 := by
  have hA : (0 : ℝ) ≤ dispersion μ p.ofLp.2 ^ 2 := sq_nonneg _
  have h := Real.norm_resolvent_le_two_div hA hε (2 * Real.pi * p.ofLp.1)
  unfold splitResolvent resolvent
  push_cast at h
  exact h

lemma continuous_splitResolvent {μ : ℝ} {ε : ℝ} (hε : 0 < ε) :
    Continuous (splitResolvent (d := d) μ ε) := by
  unfold splitResolvent resolvent
  refine continuous_const.div ?_ fun p => ?_
  · have h1 : Continuous fun p : SplitSpace d => (dispersion μ p.ofLp.2 : ℂ) :=
      Complex.continuous_ofReal.comp ((continuous_dispersion μ).comp
        (continuous_snd.comp (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (Space d)).continuous))
    have h2 : Continuous fun p : SplitSpace d => (p.ofLp.1 : ℂ) :=
      Complex.continuous_ofReal.comp
        (continuous_fst.comp (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (Space d)).continuous)
    fun_prop
  · intro h
    have := Real.half_sq_le_norm_den (sq_nonneg (dispersion μ p.ofLp.2)) hε (2 * Real.pi * p.ofLp.1)
    push_cast at this
    rw [h, norm_zero] at this
    have : 0 < ε ^ 2 / 2 := by positivity
    linarith

/-- Split space and spacetime are the same vector space. -/
def splitEquiv (d : ℕ) : SplitSpace d ≃L[ℝ] SpaceTime d :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (Space d)).trans (coordinates d).symm

/-- A real Schwartz function of spacetime as a complex Schwartz function of the split space. -/
def splitSource (d : ℕ) : 𝓢(SpaceTime d, ℝ) →L[ℝ] 𝓢(SplitSpace d, ℂ) :=
  (SchwartzMap.postcompCLM (E := SplitSpace d) (Complex.ofRealCLM : ℝ →L[ℝ] ℂ)) ∘L
    SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (splitEquiv d)

lemma splitSource_apply (φ : 𝓢(SpaceTime d, ℝ)) (p : SplitSpace d) :
    splitSource d φ p = (φ (splitEquiv d p) : ℂ) := rfl

/-- The spacetime Fourier transform of a real Schwartz function. -/
def spacetimeFourier (d : ℕ) : 𝓢(SpaceTime d, ℝ) →L[ℝ] 𝓢(SplitSpace d, ℂ) :=
  SchwartzMap.fourierTransformCLM ℝ ∘L splitSource d

lemma spacetimeFourier_apply (φ : 𝓢(SpaceTime d, ℝ)) (p : SplitSpace d) :
    spacetimeFourier d φ p = 𝓕 (splitSource d φ) p := rfl

/-- **The pairing of the transform with the resolvent.** -/
def fourierPairing (μ ε : ℝ) (φ : 𝓢(SpaceTime d, ℝ)) : ℂ :=
  ∫ p : SplitSpace d, spacetimeFourier d φ p * splitResolvent μ ε p

lemma integrable_mul_splitResolvent {μ ε : ℝ} (hε : 0 < ε) (g : 𝓢(SplitSpace d, ℂ)) :
    Integrable fun p : SplitSpace d => g p * splitResolvent μ ε p := by
  refine Integrable.mono' (g.integrable.norm.mul_const (2 / ε ^ 2)) ?_ ?_
  · exact g.continuous.aestronglyMeasurable.mul
      (continuous_splitResolvent (μ := μ) hε).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun p => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_splitResolvent_le hε p) (norm_nonneg _)

/-- The real part of the pairing as a real linear functional. -/
def pairingRe (μ : ℝ) {ε : ℝ} (hε : 0 < ε) : 𝓢(SpaceTime d, ℝ) →ₗ[ℝ] ℝ where
  toFun φ := (fourierPairing μ ε φ).re
  map_add' φ ψ := by
    simp only [fourierPairing, map_add, add_apply, add_mul]
    rw [integral_add (integrable_mul_splitResolvent hε _) (integrable_mul_splitResolvent hε _)]
    simp
  map_smul' c φ := by
    simp only [fourierPairing, map_smul, smul_apply, smul_mul_assoc, integral_smul,
      RingHom.id_apply, Complex.smul_re, smul_eq_mul]

lemma pairingRe_apply (μ : ℝ) {ε : ℝ} (hε : 0 < ε) (φ : 𝓢(SpaceTime d, ℝ)) :
    pairingRe μ hε φ = (fourierPairing μ ε φ).re := rfl

lemma norm_fourierPairing_le {μ ε : ℝ} (hε : 0 < ε) (φ : 𝓢(SpaceTime d, ℝ)) :
    ‖fourierPairing μ ε φ‖ ≤ (2 / ε ^ 2) * ∫ p : SplitSpace d, ‖𝓕 (splitSource d φ) p‖ := by
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le ((𝓕 (splitSource d φ)).integrable.norm.const_mul _)
    (Filter.Eventually.of_forall fun p => ?_)
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (norm_splitResolvent_le hε p) (norm_nonneg _)

/-- The transform of the transported test function is the transform on split space. -/
lemma timeFourier_eq_fourier (φ : 𝓓((⊤ : Opens (SpaceTime d)), ℝ)) (w : ℝ) (ξ : Space d) :
    timeFourier (sourceEquiv ℂ (TestFunction.postcompCLM Complex.ofRealCLM φ)) w ξ =
      𝓕 (splitSource d (ofTestFunction φ)) (WithLp.toLp 2 (w, ξ)) := by
  rw [EuclideanProd.fourier_eq_integral_integral, timeFourier, SchwartzMap.fourier_coe,
    Real.fourier_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [spaceFourierSchwartz]
  rfl

/-- **The pairing as an iterated integral.** -/
lemma fourierPairing_eq_integral_integral {μ ε : ℝ} (hε : 0 < ε) (φ : 𝓢(SpaceTime d, ℝ)) :
    fourierPairing μ ε φ = ∫ ξ : Space d, ∫ w : ℝ,
      spacetimeFourier d φ (WithLp.toLp 2 (w, ξ)) * resolvent μ ε w ξ := by
  unfold fourierPairing
  have hint := EuclideanProd.integrable_withLp_prod (integrable_mul_splitResolvent (μ := μ) hε
    (spacetimeFourier d φ))
  rw [EuclideanProd.integral_withLp_prod, Measure.volume_eq_prod,
    integral_prod_symm _ (by rwa [← Measure.volume_eq_prod])]
  rfl

/-- **For test functions the pairing is the damped kernel.** -/
lemma fourierPairing_ofTestFunction {m ε : ℝ} (hε : 0 < ε)
    (φ : 𝓓((⊤ : Opens (SpaceTime d)), ℝ)) :
    fourierPairing (m ^ 2) ε (ofTestFunction φ) =
      dampedKernel (m ^ 2) ε (sourceEquiv ℂ (TestFunction.postcompCLM Complex.ofRealCLM φ)) := by
  rw [dampedKernel_eq (sq_nonneg m) hε, fourierPairing_eq_integral_integral hε]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [spacetimeFourier_apply, resolvent, timeFourier_eq_fourier]

/-- **The damped kernel is bounded uniformly in the damping.** -/
lemma exists_abs_dampedKernel_le (d : ℕ) (m : ℝ) :
    ∃ (q : Seminorm ℝ 𝓢(SpaceTime d, ℝ)) (C : ℝ), Continuous q ∧ 0 ≤ C ∧
      ∀ (ε : ℝ), 0 ≤ ε → ∀ φ : 𝓓((⊤ : Opens (SpaceTime d)), ℝ),
        |(dampedKernel (m ^ 2) ε
          (sourceEquiv ℂ (TestFunction.postcompCLM Complex.ofRealCLM φ))).re| ≤
          C * q (ofTestFunction φ) := by
  obtain ⟨N, C₀, hC₀, hC⟩ := exists_norm_integral_sineEvolution_le (E := Space d) (sq_nonneg m)
  obtain ⟨A, hA0, hA⟩ := exists_weighted_bound_sourceEquiv d N
  obtain ⟨q, hqc, hq⟩ := exists_seminorm_weighted_le d N
  refine ⟨q, C₀ * (A * 2 ^ (N + 1)), hqc, by positivity, fun ε hε φ => ?_⟩
  refine (Complex.abs_re_le_norm _).trans ?_
  have hM : ∀ n ≤ N, ∀ y : SpaceTime d, (1 + ‖y‖) ^ N * ‖iteratedFDeriv ℝ n φ y‖ ≤
      2 ^ (N + 1) * q (ofTestFunction φ) := hq φ
  calc _ ≤ C₀ * (A * (2 ^ (N + 1) * q (ofTestFunction φ))) :=
        hC _ _ ε hε fun n hn y => hA φ _ hM n hn y
    _ = _ := by ring

/-- The test functions are dense in Schwartz space. -/
lemma continuous_pairingRe (μ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Continuous fun φ : 𝓢(SpaceTime d, ℝ) => (fourierPairing μ ε φ).re := by
  obtain ⟨S, C, hC0, hC⟩ := SchwartzMap.exists_integral_norm_fourier_le (E := SplitSpace d) ℂ
  let r : 𝓢(SpaceTime d, ℝ) → ℝ := fun φ =>
    (2 / ε ^ 2) * (C * ∑ i ∈ S, schwartzSeminormFamily ℂ (SplitSpace d) ℂ i (splitSource d φ))
  have hr : Continuous r := by
    refine continuous_const.mul (continuous_const.mul (continuous_finsetSum _ fun i _ => ?_))
    exact ((schwartz_withSeminorms ℂ (SplitSpace d) ℂ).continuous_seminorm i).comp
      (splitSource d).continuous
  have hbound : ∀ φ : 𝓢(SpaceTime d, ℝ), |pairingRe μ hε φ| ≤ r φ := fun φ => by
    refine (Complex.abs_re_le_norm _).trans ((norm_fourierPairing_le hε φ).trans ?_)
    refine mul_le_mul_of_nonneg_left ((hC _).trans ?_) (by positivity)
    refine mul_le_mul_of_nonneg_left ?_ hC0
    refine Seminorm.finset_sup_apply_le (Finset.sum_nonneg fun i _ => apply_nonneg _ _)
      fun i hi => ?_
    exact Finset.single_le_sum (f := fun i => schwartzSeminormFamily ℂ (SplitSpace d) ℂ i
      (splitSource d φ)) (fun i _ => apply_nonneg _ _) hi
  have hr0 : r 0 = 0 := by simp [r]
  refine continuous_of_continuousAt_zero (pairingRe μ hε).toAddMonoidHom ?_
  rw [ContinuousAt, map_zero]
  exact squeeze_zero_norm hbound (hr0 ▸ hr.tendsto 0)

/-- **The pairing is bounded on all Schwartz functions uniformly in `ε`.** -/
lemma exists_abs_fourierPairing_le (d : ℕ) (m : ℝ) :
    ∃ (q : Seminorm ℝ 𝓢(SpaceTime d, ℝ)) (C : ℝ), Continuous q ∧ 0 ≤ C ∧
      ∀ (ε : ℝ), 0 < ε → ∀ φ : 𝓢(SpaceTime d, ℝ),
        |(fourierPairing (m ^ 2) ε φ).re| ≤ C * q φ := by
  obtain ⟨q, C, hqc, hC0, hC⟩ := exists_abs_dampedKernel_le d m
  refine ⟨q, C, hqc, hC0, fun ε hε φ => ?_⟩
  have hclosed : IsClosed {φ : 𝓢(SpaceTime d, ℝ) | |(fourierPairing (m ^ 2) ε φ).re| ≤ C * q φ} :=
    isClosed_le ((continuous_pairingRe (m ^ 2) hε).abs) (continuous_const.mul hqc)
  have hsub : Set.range (ofTestFunction (V := SpaceTime d)) ⊆
      {φ : 𝓢(SpaceTime d, ℝ) | |(fourierPairing (m ^ 2) ε φ).re| ≤ C * q φ} := by
    rintro _ ⟨ψ, rfl⟩
    show |(fourierPairing (m ^ 2) ε (ofTestFunction ψ)).re| ≤ _
    rw [fourierPairing_ofTestFunction hε]
    exact hC ε hε.le ψ
  exact (closure_minimal hsub hclosed) (
    (denseRange_ofTestFunction (V := SpaceTime d)).closure_eq ▸ Set.mem_univ φ)

/-- **Fourier form of the tempered retarded kernel.** For every real Schwartz function `φ` the
tempered kernel is the limit for `ε → 0+` of the integral of the spacetime Fourier transform of
`φ` against `1 / (ω_ξ² - (2π w + i ε)²)`. -/
lemma tendsto_fourierPairing (m : ℝ) (φ : 𝓢(SpaceTime d, ℝ)) :
    Filter.Tendsto (fun ε : ℝ => (fourierPairing (m ^ 2) ε φ).re) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (temperedKernel d m φ)) := by
  obtain ⟨q, C, hqc, hC0, hC⟩ := exists_abs_fourierPairing_le d m
  rw [Metric.tendsto_nhds]
  intro η hη
  let U : Set 𝓢(SpaceTime d, ℝ) := {ψ | C * q (φ - ψ) < η / 3} ∩
    {ψ | |temperedKernel d m (φ - ψ)| < η / 3}
  have hU : IsOpen U := by
    refine IsOpen.inter (isOpen_lt (continuous_const.mul (hqc.comp (continuous_const.sub
      continuous_id))) continuous_const) (isOpen_lt ?_ continuous_const)
    exact ((temperedKernel d m).continuous.comp (continuous_const.sub continuous_id)).abs
  have hφU : φ ∈ U := by
    refine ⟨?_, ?_⟩ <;> simp [hη]
  obtain ⟨ψ, hψ⟩ := (denseRange_ofTestFunction (V := SpaceTime d)).exists_mem_open hU ⟨φ, hφU⟩
  have hlim : Filter.Tendsto (fun ε : ℝ => (fourierPairing (m ^ 2) ε (ofTestFunction ψ)).re)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (temperedKernel d m (ofTestFunction ψ))) := by
    rw [temperedKernel_apply, retardedPointSource_zero_eq]
    refine ((Complex.continuous_re.tendsto _).comp (tendsto_dampedKernel (sq_nonneg m) _)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simp [fourierPairing_ofTestFunction hε]
  have hev := Metric.tendsto_nhds.1 hlim (η / 3) (by positivity)
  filter_upwards [hev, self_mem_nhdsWithin] with ε hε1 hε2
  have hε0 : 0 < ε := hε2
  have hlin : (fourierPairing (m ^ 2) ε φ).re =
      (fourierPairing (m ^ 2) ε (φ - ofTestFunction ψ)).re +
      (fourierPairing (m ^ 2) ε (ofTestFunction ψ)).re := by
    have := (pairingRe (m ^ 2) hε0).map_sub φ (ofTestFunction ψ)
    simp only [pairingRe_apply] at this
    linarith
  have h1 := hC ε hε0 (φ - ofTestFunction ψ)
  have h2 : C * q (φ - ofTestFunction ψ) < η / 3 := hψ.1
  have h3 : |temperedKernel d m (φ - ofTestFunction ψ)| < η / 3 := hψ.2
  rw [map_sub] at h3
  rw [Real.dist_eq] at hε1 ⊢
  have h5 : temperedKernel d m φ = temperedKernel d m (φ - ofTestFunction ψ) +
      temperedKernel d m (ofTestFunction ψ) := by
    rw [← map_add]
    simp
  rw [hlin, h5]
  have h1' := abs_le.1 h1
  have h3' := abs_lt.1 h3
  have h4 := abs_lt.1 hε1
  rw [abs_lt]
  constructor <;> linarith [h1'.1, h1'.2, h3'.1, h3'.2, h4.1, h4.2]

end KleinGordon
