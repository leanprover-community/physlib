/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.Smoothness

/-!

# Cutoff responses of compact sources

## i. Overview

Cutting the response off by a test function is continuous in the source.

## ii. Key results

- `solutionEvaluation` : Evaluation of the retarded response at a fixed event is continuous in the
  native LF topology.
- `advancedSolutionEvaluation` : Evaluation of the advanced response is continuous in the native LF
  source topology.
- `cutoffSolutionSupported` : A compactly cut off retarded response is continuous between
  fixed-support source and target spaces in every derivative seminorm.
- `cutoffSolution` : Multiplying the retarded Fourier response by a compact smooth cutoff is
  continuous on the native LF test-function space.
- `cutoffAdvancedSolution` : A compactly cut off advanced response is continuous on native smooth
  tests.

## iii. Table of contents

- A. Continuous seminorm bounds for Fourier sources
- B. Continuous source bounds for parameter derivatives
- C. Continuous compactly cut off Green responses
- D. Continuous compactly cut off advanced response

## iv. References

None.

## A. Continuous seminorm bounds for Fourier sources

- `solutionEvaluation` : Evaluation of the retarded response at a fixed event is continuous in the
  native LF topology.
- `advancedSolutionEvaluation` : Evaluation of the advanced response is continuous in the native LF
  source topology.

Lemmas: `exists_solution_supported_seminorm`, `solutionEvaluation_apply`,
`advancedSolutionEvaluation_apply`.

## B. Continuous source bounds for parameter derivatives

Lemmas: `exists_integrand_derivative_supported_seminorm`,
`exists_integral_derivative_supported_seminorm`, `exists_solution_derivative_supported_seminorm`.

## C. Continuous compactly cut off Green responses

- `cutoffSolutionSupported` : A compactly cut off retarded response is continuous between
  fixed-support source and target spaces in every derivative seminorm.
- `cutoffSolution` : Multiplying the retarded Fourier response by a compact smooth cutoff is
  continuous on the native LF test-function space.

Lemmas: `cutoffSolution_apply`.

## D. Continuous compactly cut off advanced response

- `cutoffAdvancedSolution` : A compactly cut off advanced response is continuous on native smooth
  tests.

Lemmas: `cutoffAdvancedSolution_apply`.

-/

@[expose] public section

noncomputable section

open scoped FourierTransform Distributions ContDiff NNReal Real
open ParametricIntegral TestFunction TimeSlice TopologicalSpace Topology MeasureTheory
universe u

namespace KleinGordon

section
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (F : Type u) [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F]

/-- On bounded time intervals the response is controlled by a continuous source seminorm,
uniformly over every spatial observation point. -/
lemma exists_solution_supported_seminorm (K : Compacts (ℝ × E)) {μ : ℝ} (hμ : 0 ≤ μ)
    (T : ℝ) :
    ∃ q : Seminorm ℝ (ContDiffMapSupportedIn (ℝ × E) F ⊤ K), Continuous q ∧
      ∀ (f : ContDiffMapSupportedIn (ℝ × E) F ⊤ K) (p : ℝ × E), |p.1| ≤ T →
        ‖solution F (supportedSource F K f) μ p.1 p.2‖ ≤ q f := by
  let N := Module.finrank ℝ E + 1
  obtain ⟨q, hqc, hq⟩ := exists_fourier_decay_supported_seminorm F K N
  obtain ⟨R₀, hR₀⟩ := K.isCompact.isBounded.exists_norm_le
  let R := max R₀ 0
  have hR0 : 0 ≤ R := le_max_right _ _
  have hR : ∀ y ∈ K, ‖y‖ ≤ R := fun y hy => (hR₀ y hy).trans (le_max_left _ _)
  let L := |T| + R + 1
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let ν := (MeasureTheory.volume.restrict (Set.Ioc 0 L)).prod (MeasureTheory.volume :
    MeasureTheory.Measure E)
  let B : ℝ × E → ℝ := fun z => L * (1 + ‖z.2‖) ^ (-(N : ℝ))
  have hBi : MeasureTheory.Integrable B ν :=
    ((integrable_one_add_norm (E := E) (r := (N : ℝ)) (by simp [N])).const_mul L).comp_snd _
  have hM : 0 ≤ ∫ z, B z ∂ν := MeasureTheory.integral_nonneg fun z => by dsimp [B]; positivity
  let M : ℝ≥0 := ⟨∫ z, B z ∂ν, hM⟩
  refine ⟨M • q, hqc.const_smul M, fun f p hp => ?_⟩
  have ha : ∀ s ≤ -R - 1, s ∉ Prod.fst '' tsupport (supportedSource F K f) := by
    rintro s hs ⟨y, hy, hys⟩
    change y ∈ tsupport f at hy
    have hn := (norm_fst_le y).trans (hR y (f.tsupport_subset hy))
    rw [hys] at hn
    have := (abs_le.mp hn).1
    linarith
  have hpL : p.1 - L ≤ -R - 1 := by
    dsimp [L]
    linarith [(le_abs_self p.1).trans (hp.trans (le_abs_self T))]
  rw [solution_eq_integral_solutionIntegrand F (supportedSource F K f) hμ hL ha p hpL]
  have hb : ∀ᵐ z ∂ν, ‖solutionIntegrand F (supportedSource F K f) μ p z‖ ≤ q f * B z := by
    have hz : ∀ᵐ z : ℝ × E ∂ν, z.1 ∈ Set.Ioc 0 L :=
      MeasureTheory.Measure.quasiMeasurePreserving_fst.ae
        (MeasureTheory.ae_restrict_mem measurableSet_Ioc)
    filter_upwards [hz] with z hz
    simp only [solutionIntegrand, norm_smul, Circle.norm_coe, one_mul]
    calc
      _ ≤ L * (q f * (1 + ‖z.2‖) ^ (-(N : ℝ))) :=
        mul_le_mul ((norm_multiplier_le _ _ _).trans (by rw [abs_of_pos hz.1]; exact hz.2))
          (hq f _ _) (norm_nonneg _) hL
      _ = _ := by dsimp [B]; ring
  calc
    _ ≤ ∫ z, q f * B z ∂ν := MeasureTheory.norm_integral_le_of_norm_le (hBi.const_mul (q f)) hb
    _ = q f * ∫ z, B z ∂ν := MeasureTheory.integral_const_mul _ _
    _ = _ := by change q f * (∫ z, B z ∂ν) = (∫ z, B z ∂ν) * q f; ring

/-- Evaluation of the retarded response at a fixed event is continuous in the native LF topology. -/
def solutionEvaluation {μ : ℝ} (hμ : 0 ≤ μ) (p : ℝ × E) :
    𝓓((⊤ : Opens (ℝ × E)), F) →L[ℝ] F :=
  TestFunction.mkCLM ℝ (fun f => solution F f μ p.1 p.2)
    (fun f g => solution_add F f hμ g p.1 p.2)
    (fun c f => solution_smul F f hμ c p.1 p.2) (by
      intro K hK
      obtain ⟨q, hqc, hq⟩ := exists_solution_supported_seminorm F K hμ |p.1|
      let L : ContDiffMapSupportedIn (ℝ × E) F ⊤ K →ₗ[ℝ] F := {
        toFun f := solution F (supportedSource F K f) μ p.1 p.2
        map_add' f g := by
          rw [map_add]
          exact solution_add F _ hμ _ _ _
        map_smul' c f := by
          rw [map_smul]
          exact solution_smul F _ hμ c _ _ }
      obtain ⟨S, c, hc, hbound⟩ := Seminorm.bound_of_continuous
        (ContDiffMapSupportedIn.withSeminorms ℝ (ℝ × E) F ⊤ K) q hqc
      have hL : Continuous L := WithSeminorms.continuous_normedSpace_rng F
        (ContDiffMapSupportedIn.withSeminorms ℝ (ℝ × E) F ⊤ K) L
        ⟨S, c, fun f => (hq f p le_rfl).trans (hbound f)⟩
      exact hL)

@[simp]
lemma solutionEvaluation_apply {μ : ℝ} (hμ : 0 ≤ μ) (p : ℝ × E)
    (f : 𝓓((⊤ : Opens (ℝ × E)), F)) :
    solutionEvaluation F hμ p f = solution F f μ p.1 p.2 := rfl

/-- Evaluation of the advanced response is continuous in the native LF source topology. -/
def advancedSolutionEvaluation {μ : ℝ} (hμ : 0 ≤ μ) (p : ℝ × E) :
    𝓓((⊤ : Opens (ℝ × E)), F) →L[ℝ] F :=
  (solutionEvaluation F hμ (-p.1, p.2)).comp (reflectSourceCLM F)

@[simp]
lemma advancedSolutionEvaluation_apply {μ : ℝ} (hμ : 0 ≤ μ) (p : ℝ × E)
    (f : 𝓓((⊤ : Opens (ℝ × E)), F)) :
    advancedSolutionEvaluation F hμ p f = advancedSolution F f μ p.1 p.2 := by
  change solution F (reflectSourceCLM F f) μ (-p.1) p.2 = _
  rw [reflectSourceCLM_eq]
  rfl

omit [CompleteSpace F] in
/-- Every parameter derivative of the Fourier integrand has a continuous source bound. -/
lemma exists_integrand_derivative_supported_seminorm (K : Compacts (ℝ × E))
    (μ : ℝ) (k N : ℕ) (R : ℝ≥0) :
    ∃ q : Seminorm ℝ (ContDiffMapSupportedIn (ℝ × E) F ⊤ K), Continuous q ∧
      ∀ (f : ContDiffMapSupportedIn (ℝ × E) F ⊤ K) (p z : ℝ × E), |z.1| ≤ R →
        ‖iteratedFDeriv ℝ k (fun w => solutionIntegrand F (supportedSource F K f) μ w z) p‖ ≤
          q f * (1 + ‖z.2‖) ^ (-(N : ℝ)) := by
  choose q hqc hq using fun i => exists_char_timeDeriv_supported_seminorm F K i (k - i) N
  let Q : Seminorm ℝ (ContDiffMapSupportedIn (ℝ × E) F ⊤ K) :=
    ∑ i ∈ Finset.range (k + 1), ((k.choose i : ℝ≥0) * R) • q i
  refine ⟨Q, ?_, fun f p z hz => ?_⟩
  · change Continuous (fun f => Q f)
    simp only [Q, _root_.sum_apply, smul_apply]
    exact continuous_finsetSum _ fun i hi => (hqc i).const_smul _
  · refine (norm_iteratedFDeriv_solutionIntegrand_le F (supportedSource F K f) μ k p z).trans ?_
    simp only [Q, _root_.sum_apply, smul_apply, NNReal.smul_def, NNReal.coe_mul,
      NNReal.coe_natCast, smul_eq_mul, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    calc
      _ = (k.choose i : ℝ) * |z.1| * ((2 * π * ‖z.2‖) ^ i *
          ‖iteratedDeriv (k - i) (fun s => 𝓕 (slice F (supportedSource F K f) s) z.2) (p.1 -
            z.1)‖) := by ring
      _ ≤ (k.choose i : ℝ) * R * (q i f * (1 + ‖z.2‖) ^ (-(N : ℝ))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hz (Nat.cast_nonneg _))
          (hq i f (p.1 - z.1) z.2) (by positivity) (by positivity)
      _ = _ := by ring

/-- Every derivative of a fixed-interval Fourier response is controlled continuously by the source.
-/
lemma exists_integral_derivative_supported_seminorm (K : Compacts (ℝ × E))
    {μ : ℝ} (hμ : 0 ≤ μ) (k : ℕ) (R : ℝ≥0) :
    ∃ q : Seminorm ℝ (ContDiffMapSupportedIn (ℝ × E) F ⊤ K), Continuous q ∧
      ∀ (f : ContDiffMapSupportedIn (ℝ × E) F ⊤ K) (p : ℝ × E),
        ‖iteratedFDeriv ℝ k (fun w => ∫ z : ℝ × E, solutionIntegrand F (supportedSource F K f) μ w z
          ∂((volume.restrict (Set.Ioc 0 (R : ℝ))).prod volume)) p‖ ≤ q f := by
  let N := Module.finrank ℝ E + 1
  choose q hqc hq using fun j => exists_integrand_derivative_supported_seminorm F K μ j N R
  let ν := (volume.restrict (Set.Ioc 0 (R : ℝ))).prod (volume : Measure E)
  let B : ℝ × E → ℝ := fun z => (1 + ‖z.2‖) ^ (-(N : ℝ))
  have hBi : Integrable B ν :=
    (integrable_one_add_norm (E := E) (r := (N : ℝ)) (by simp [N])).comp_snd _
  let M : ℝ≥0 := ⟨∫ z, B z ∂ν, integral_nonneg (fun z => by dsimp [B]; positivity)⟩
  refine ⟨M • q k, (hqc k).const_smul M, fun f p => ?_⟩
  have hz : ∀ᵐ z : ℝ × E ∂ν, z.1 ∈ Set.Ioc 0 (R : ℝ) :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
  have hb : ∀ j, ∀ᵐ z ∂ν, ∀ w,
      ‖iteratedFDeriv ℝ j (fun w => solutionIntegrand F (supportedSource F K f) μ w z) w‖ ≤ q j f *
        B z := by
    intro j
    filter_upwards [hz] with z hz w
    exact hq j f w z (by rw [abs_of_pos hz.1]; exact hz.2)
  have hm : ∀ j w, AEStronglyMeasurable
      (fun z => iteratedFDeriv ℝ j (fun w => solutionIntegrand F (supportedSource F K f) μ w z) w)
        ν := by
    intro j w
    exact ((continuous_iteratedFDeriv_partial _
      (contDiff_solutionIntegrand_joint F (supportedSource F K f) hμ) j).comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  calc
    _ ≤ ∫ z, q k f * B z ∂ν := norm_iteratedFDeriv_integral_le ν k F _
      (fun j z => q j f * B z)
      (fun z => contDiff_solutionIntegrand_p F (supportedSource F K f) hμ z)
      hm (fun j => hBi.const_mul (q j f)) hb p
    _ = q k f * ∫ z, B z ∂ν := integral_const_mul _ _
    _ = _ := by change q k f * (∫ z, B z ∂ν) = (∫ z, B z ∂ν) * q k f; ring

/-- Every spacetime derivative of the retarded field is controlled by a continuous source seminorm
on bounded time intervals, uniformly in the spatial observation point. -/
lemma exists_solution_derivative_supported_seminorm (K : Compacts (ℝ × E))
    {μ : ℝ} (hμ : 0 ≤ μ) (k : ℕ) (T : ℝ) :
    ∃ q : Seminorm ℝ (ContDiffMapSupportedIn (ℝ × E) F ⊤ K), Continuous q ∧
      ∀ (f : ContDiffMapSupportedIn (ℝ × E) F ⊤ K) (p : ℝ × E), |p.1| ≤ T →
        ‖iteratedFDeriv ℝ k (fun w => solution F (supportedSource F K f) μ w.1 w.2) p‖ ≤ q f := by
  obtain ⟨R₀, hR₀⟩ := K.isCompact.isBounded.exists_norm_le
  let R := max R₀ 0
  have hR0 : 0 ≤ R := le_max_right _ _
  have hR : ∀ y ∈ K, ‖y‖ ≤ R := fun y hy => (hR₀ y hy).trans (le_max_left _ _)
  let L : ℝ≥0 := ⟨|T| + R + 2, by positivity⟩
  obtain ⟨q, hqc, hq⟩ := exists_integral_derivative_supported_seminorm F K hμ k L
  refine ⟨q, hqc, fun f p hp => ?_⟩
  have ha : ∀ s ≤ -R - 1, s ∉ Prod.fst '' tsupport (supportedSource F K f) := by
    rintro s hs ⟨y, hy, hys⟩
    change y ∈ tsupport f at hy
    have hn := (norm_fst_le y).trans (hR y (f.tsupport_subset hy))
    rw [hys] at hn
    have := (abs_le.mp hn).1
    linarith
  have hpL : p.1 < -R - 1 + L := by
    change p.1 < -R - 1 + (|T| + R + 2)
    linarith [(le_abs_self p.1).trans (hp.trans (le_abs_self T))]
  have he : (fun w : ℝ × E => solution F (supportedSource F K f) μ w.1 w.2) =ᶠ[𝓝 p]
      (fun w => ∫ z : ℝ × E, solutionIntegrand F (supportedSource F K f) μ w z
        ∂((volume.restrict (Set.Ioc 0 (L : ℝ))).prod volume)) := by
    filter_upwards [continuous_fst.continuousAt.eventually (gt_mem_nhds hpL)] with w hw
    exact solution_eq_integral_solutionIntegrand F (supportedSource F K f) hμ (R := (L : ℝ)) L.2 ha
      w ((sub_le_iff_le_add).mpr hw.le)
  rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
  exact hq f p

/-- A compactly cut off retarded response is continuous between fixed-support source and target
spaces in every derivative seminorm. -/
def cutoffSolutionSupported {μ : ℝ} (hμ : 0 ≤ μ) (K₁ K₂ : Compacts (ℝ × E))
    (χ : ContDiffMapSupportedIn (ℝ × E) ℝ ⊤ K₂) :
    ContDiffMapSupportedIn (ℝ × E) F ⊤ K₁ →L[ℝ] ContDiffMapSupportedIn (ℝ × E) F ⊤ K₂ :=
  ContDiffMapSupportedIn.mkCLM ℝ
    (fun f p => χ p • solution F (supportedSource F K₁ f) μ p.1 p.2)
    (fun f g p => by rw [map_add, solution_add F _ hμ, smul_add])
    (fun c f p => by rw [map_smul, solution_smul F _ hμ]; exact smul_comm _ _ _)
    (fun f => χ.contDiff.smul (contDiff_solution F (supportedSource F K₁ f) hμ))
    (fun f p hp => by simp only [χ.zero_on_compl hp, zero_smul, Pi.zero_apply])
    (fun n hn => by
      obtain ⟨R, hR⟩ := K₂.isCompact.isBounded.exists_norm_le
      choose q hqc hq using fun j => exists_solution_derivative_supported_seminorm F K₁ hμ j R
      let a : ℕ → ℝ≥0 := fun i =>
        ⟨ContDiffMapSupportedIn.seminorm ℝ (ℝ × E) ℝ ⊤ K₂ i χ, apply_nonneg _ _⟩
      let Q : Seminorm ℝ (ContDiffMapSupportedIn (ℝ × E) F ⊤ K₁) :=
        ∑ i ∈ Finset.range (n + 1), ((n.choose i : ℝ≥0) * a i) • q (n - i)
      have hQc : Continuous Q := by
        change Continuous (fun f => Q f)
        simp only [Q, _root_.sum_apply, smul_apply]
        exact continuous_finsetSum _ fun i hi => (hqc (n - i)).const_smul _
      obtain ⟨S, c, hc, hbound⟩ := Seminorm.bound_of_continuous
        (ContDiffMapSupportedIn.withSeminorms ℝ (ℝ × E) F ⊤ K₁) Q hQc
      refine ⟨S, c, c.2, fun f p hp => ?_⟩
      have hpR : |p.1| ≤ R := (norm_fst_le p).trans (hR p hp)
      have hb : ‖iteratedFDeriv ℝ n
          (fun w => χ w • solution F (supportedSource F K₁ f) μ w.1 w.2) p‖ ≤ Q f := by
        refine (norm_iteratedFDeriv_smul_le χ.contDiff
          (contDiff_solution F (supportedSource F K₁ f) hμ) p (by simp : (n : ℕ∞ω) ≤ ∞)).trans ?_
        simp only [Q, _root_.sum_apply, smul_apply, NNReal.smul_def, smul_eq_mul]
        change _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ContDiffMapSupportedIn.seminorm ℝ (ℝ × E) ℝ ⊤ K₂ i χ * q (n - i) f
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left
            (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ) (Nat.cast_nonneg
              _))
          (hq (n - i) f p hpR) (norm_nonneg _) (by positivity)
      exact hb.trans (hbound f))

/-- Multiplying the retarded Fourier response by a compact smooth cutoff is continuous on the
native LF test-function space. -/
def cutoffSolution {μ : ℝ} (hμ : 0 ≤ μ) (χ : 𝓓((⊤ : Opens (ℝ × E)), ℝ)) :
    𝓓((⊤ : Opens (ℝ × E)), F) →L[ℝ] 𝓓((⊤ : Opens (ℝ × E)), F) :=
  TestFunction.mkCLM ℝ (fun f => {
    toFun p := χ p • solution F f μ p.1 p.2
    contDiff' := χ.contDiff.smul (contDiff_solution F f hμ)
    hasCompactSupport' := χ.hasCompactSupport.smul_right
    tsupport_subset' := fun _ _ => trivial })
    (fun f g => by
      ext p
      change χ p • solution F (f + g) μ p.1 p.2 = _
      rw [solution_add F f hμ, smul_add]
      rfl)
    (fun c f => by
      ext p
      change χ p • solution F (c • f) μ p.1 p.2 = c • (χ p • solution F f μ p.1 p.2)
      rw [solution_smul F f hμ]
      exact smul_comm _ _ _) (by
      intro K hK
      let Kχ : Compacts (ℝ × E) := ⟨tsupport χ, χ.hasCompactSupport⟩
      let χK : ContDiffMapSupportedIn (ℝ × E) ℝ ⊤ Kχ :=
        ⟨χ, χ.contDiff, fun p hp => image_eq_zero_of_notMem_tsupport hp⟩
      exact (TestFunction.ofSupportedInCLM ℝ (Ω := ⊤) (by simp)).continuous.comp
        (cutoffSolutionSupported F hμ K Kχ χK).continuous)

@[simp]
lemma cutoffSolution_apply {μ : ℝ} (hμ : 0 ≤ μ) (χ : 𝓓((⊤ : Opens (ℝ × E)), ℝ))
    (f : 𝓓((⊤ : Opens (ℝ × E)), F)) (p : ℝ × E) :
    cutoffSolution F hμ χ f p = χ p • solution F f μ p.1 p.2 := rfl

/-- A compactly cut off advanced response is continuous on native smooth tests. -/
def cutoffAdvancedSolution {μ : ℝ} (hμ : 0 ≤ μ) (χ : 𝓓((⊤ : Opens (ℝ × E)), ℝ)) :
    𝓓((⊤ : Opens (ℝ × E)), F) →L[ℝ] 𝓓((⊤ : Opens (ℝ × E)), F) :=
  (precompLinearEquivCLM (timeReflectionCLE E)).comp
    ((cutoffSolution F hμ (precompLinearEquivCLM (timeReflectionCLE E) χ)).comp
      (precompLinearEquivCLM (timeReflectionCLE E)))

@[simp]
lemma cutoffAdvancedSolution_apply {μ : ℝ} (hμ : 0 ≤ μ) (χ : 𝓓((⊤ : Opens (ℝ × E)), ℝ))
    (f : 𝓓((⊤ : Opens (ℝ × E)), F)) (p : ℝ × E) :
    cutoffAdvancedSolution F hμ χ f p = χ p • advancedSolution F f μ p.1 p.2 := by
  change χ (-(-p.1), p.2) • solution F (reflect F f) μ (-p.1) p.2 = _
  simp only [neg_neg]
  rfl
end

end KleinGordon
