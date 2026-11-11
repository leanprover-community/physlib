/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Mathematics.Calculus.ParametricIntegral
public import PhyslibAlpha.Mathematics.Distribution.TimeSlice
public import PhyslibAlpha.Mathematics.Fourier.Integral

/-!

# Smoothness and bounds of time slices

The Fourier transform of the slices depends smoothly on time and space.

## i. Overview

The Fourier transform of the slices depends smoothly on time and space. The seminorms of the slices
are bounded by seminorms of the source.

## ii. Key results

- `fourierIntegrand` : The integrand of the partial Fourier transform, as a function of the
  parameter `(s, ξ)` and the position `y`.
- `supportedSource` : The native continuous inclusion of fixed-support sources into all compact test
  sources.
- `supportedDt` : Time differentiation is a continuous endomorphism of every fixed-support source
  space.
- `hasDerivAt_fourier_slice` : The time derivative of the Fourier transformed slice is the Fourier
  transformed slice of the time derivative.

## iii. Table of contents

- A. The time dependence of the Fourier transformed slices
- B. Joint smoothness of the Fourier transformed slices
- C. Smoothness of the retarded solution
- D. Continuous seminorm bounds for Fourier sources
- E. Continuous source bounds for parameter derivatives

## iv. References

None.

## A. The time dependence of the Fourier transformed slices

Lemmas: `hasDerivAt_fourier_slice`, `deriv_fourier_slice`, `iteratedDeriv_fourier_slice`,
`contDiff_fourier_slice`, `exists_iteratedDeriv_fourier_slice_bound`.

## B. Joint smoothness of the Fourier transformed slices

- `fourierIntegrand` : The integrand of the partial Fourier transform, as a function of the
  parameter `(s, ξ)` and the position `y`.

Lemmas: `contDiff_fourierIntegrand`, `fourierIntegrand_eq_zero`, `contDiff_fourier_slice_joint`.

## C. Smoothness of the retarded solution

Lemmas: `contDiff_fourier_slice_joint_infty`.

## D. Continuous seminorm bounds for Fourier sources

- `supportedSource` : The native continuous inclusion of fixed-support sources into all compact test
  sources.

Lemmas: `seminorm_slice_supported_le`, `exists_fourier_supported_seminorm`,
`exists_fourier_decay_supported_seminorm`.

## E. Continuous source bounds for parameter derivatives

- `supportedDt` : Time differentiation is a continuous endomorphism of every fixed-support source
  space.

Lemmas: `supportedSource_dt`, `supportedSource_iterate_dt`,
`exists_timeDeriv_fourier_supported_seminorm`, `exists_char_timeDeriv_supported_seminorm`.

-/

@[expose] public section

noncomputable section

open scoped SchwartzMap FourierTransform Distributions ContDiff Real NNReal
open FourierIntegral ParametricIntegral TopologicalSpace Topology MeasureTheory
universe u

namespace TimeSlice

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] (f : 𝓓((⊤ : Opens (ℝ × E)), F))

omit [CompleteSpace F] in
/-- The time derivative of the Fourier transformed slice is the Fourier transformed slice of the
time derivative. -/
lemma hasDerivAt_fourier_slice (ξ : E) (s : ℝ) :
    HasDerivAt (fun r => 𝓕 (slice F f r) ξ) (𝓕 (slice F (dt F f) s) ξ) s := by
  simp_rw [fourier_slice_apply]
  obtain ⟨R, hR0, hR⟩ := exists_radius F (dt F f)
  obtain ⟨M, hM⟩ := exists_bound_iteratedFDeriv F (dt F f) 0
  have hchar : Continuous fun y : E => (𝐞 (-inner ℝ y ξ) : ℂ) :=
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp
      ((continuous_id.inner continuous_const).neg))
  have hnorm : ∀ (y : E) (v : F), ‖(𝐞 (-inner ℝ y ξ) : ℂ) • v‖ = ‖v‖ := fun y v => by
    rw [norm_smul, Circle.norm_coe, one_mul]
  have hf : ∀ r, Continuous fun y : E => f (r, y) := fun r => f.continuous.comp (by fun_prop)
  have hdf : ∀ r, Continuous fun y : E => dt F f (r, y) := fun r =>
    (dt F f).continuous.comp (by fun_prop)
  simp only [Circle.smul_def]
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun r y => (𝐞 (-inner ℝ y ξ) : ℂ) • f (r, y))
    (F' := fun r y => (𝐞 (-inner ℝ y ξ) : ℂ) • dt F f (r, y))
    (bound := (Metric.closedBall (0 : E) R).indicator fun _ => max M 0)
    (Metric.ball_mem_nhds s one_pos)
    (Filter.Eventually.of_forall fun r => (hchar.smul (hf r)).aestronglyMeasurable)
    ?_ (hchar.smul (hdf s)).aestronglyMeasurable ?_ ?_ ?_).2
  · refine (hchar.smul (hf s)).integrable_of_hasCompactSupport ?_
    exact (hasCompactSupport_slice F f s).mono fun y hy => by
      simp only [Function.mem_support] at hy ⊢
      intro h; exact hy (by simp [h])
  · refine Filter.Eventually.of_forall fun y r _ => ?_
    rw [hnorm]
    by_cases hy : ‖y‖ ≤ R
    · rw [Set.indicator_of_mem (by simpa using hy)]
      exact (by simpa using hM (r, y) : ‖dt F f (r, y)‖ ≤ M).trans (le_max_left _ _)
    · have : dt F f (r, y) = 0 := by
        by_contra h
        exact hy ((norm_snd_le (r, y)).trans (hR _ (subset_tsupport _ h)))
      rw [this, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => le_max_right _ _) _
  · exact (MeasureTheory.integrableOn_const (MeasureTheory.measure_closedBall_lt_top
      (x := (0 : E)) (r := R)).ne).integrable_indicator measurableSet_closedBall
  · exact Filter.Eventually.of_forall fun y r _ =>
      ((hasDerivAt_time F f r y).const_smul (𝐞 (-inner ℝ y ξ) : ℂ))

omit [CompleteSpace F] in
lemma deriv_fourier_slice (ξ : E) :
    deriv (fun r => 𝓕 (slice F f r) ξ) = fun s => 𝓕 (slice F (dt F f) s) ξ :=
  funext fun s => (hasDerivAt_fourier_slice F f ξ s).deriv

omit [CompleteSpace F] in
/-- The `k`-th time derivative of the Fourier transformed slice. -/
lemma iteratedDeriv_fourier_slice (ξ : E) (k : ℕ) :
    ∀ f : 𝓓((⊤ : Opens (ℝ × E)), F), iteratedDeriv k (fun r => 𝓕 (slice F f r) ξ) =
      fun s => 𝓕 (slice F ((dt F)^[k] f) s) ξ := by
  induction k with
  | zero => intro f; rfl
  | succ k ih =>
    intro f
    rw [iteratedDeriv_succ', deriv_fourier_slice, ih (dt F f), Function.iterate_succ_apply]

omit [CompleteSpace F] in
lemma contDiff_fourier_slice (ξ : E) (n : ℕ) :
    ∀ f : 𝓓((⊤ : Opens (ℝ × E)), F), ContDiff ℝ n (fun r => 𝓕 (slice F f r) ξ) := by
  induction n with
  | zero =>
    intro f
    exact contDiff_zero.2 (continuous_fourier_slice F f |>.comp
      (continuous_id.prodMk continuous_const))
  | succ n ih =>
    intro f
    push_cast
    rw [contDiff_succ_iff_deriv]
    refine ⟨fun s => (hasDerivAt_fourier_slice F f ξ s).differentiableAt, fun h => ?_, ?_⟩
    · exact absurd h (by simp)
    · rw [deriv_fourier_slice]; exact ih (dt F f)

omit [CompleteSpace F] in
/-- All time derivatives of the Fourier transformed slice decay rapidly, uniformly in time. -/
lemma exists_iteratedDeriv_fourier_slice_bound (k N : ℕ) :
    ∃ K : ℝ, ∀ (ξ : E) (s : ℝ), ‖iteratedDeriv k (fun r => 𝓕 (slice F f r) ξ) s‖ ≤
      K * (1 + ‖ξ‖) ^ (-(N : ℝ)) := by
  obtain ⟨K, hK⟩ := exists_fourier_decay_pow F ((dt F)^[k] f) N
  exact ⟨K, fun ξ s => by rw [iteratedDeriv_fourier_slice F ξ k f]; exact hK s ξ⟩
end

section
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (F : Type u) [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] (f : 𝓓((⊤ : Opens (ℝ × E)), F))

/-- The integrand of the partial Fourier transform, as a function of the parameter `(s, ξ)` and the
position `y`. -/
def fourierIntegrand (z : (ℝ × E) × E) : F := (𝐞 (-inner ℝ z.2 z.1.2) : ℂ) • f (z.1.1, z.2)

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] in
lemma contDiff_fourierIntegrand : ContDiff ℝ ∞ (fourierIntegrand F f) := by
  unfold fourierIntegrand
  have h1 : ContDiff ℝ ∞ fun z : (ℝ × E) × E => (𝐞 (-inner ℝ z.2 z.1.2) : ℂ) := by
    have hin : ContDiff ℝ ∞ fun z : (ℝ × E) × E => (inner ℝ z.2 z.1.2 : ℝ) :=
      ContDiff.inner ℝ contDiff_snd (contDiff_snd.comp contDiff_fst)
    have e : (fun z : (ℝ × E) × E => (𝐞 (-inner ℝ z.2 z.1.2) : ℂ)) = fun z =>
        Complex.exp ((((2 * π * (-inner ℝ z.2 z.1.2) : ℝ)) : ℂ) * Complex.I) := by
      funext z; rw [Real.fourierChar_apply]
    rw [e]
    have h3 : ContDiff ℝ ∞ fun z : (ℝ × E) × E => (2 * π * (-inner ℝ z.2 z.1.2) : ℝ) :=
      contDiff_const.mul hin.neg
    have h4 : ContDiff ℝ ∞ fun z : (ℝ × E) × E => (((2 * π * (-inner ℝ z.2 z.1.2) : ℝ)) : ℂ) :=
      Complex.ofRealCLM.contDiff.comp h3
    have hexp : ContDiff ℝ ∞ Complex.exp := ContDiff.restrict_scalars ℝ (𝕜' := ℂ)
      Complex.contDiff_exp
    exact hexp.comp (h4.mul contDiff_const)
  have h2 : ContDiff ℝ ∞ fun z : (ℝ × E) × E => f (z.1.1, z.2) :=
    f.contDiff.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
  exact h1.smul h2

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] in
lemma fourierIntegrand_eq_zero {R : ℝ} (hR : ∀ y ∈ tsupport f, ‖y‖ ≤ R) {y : E} (hy : R < ‖y‖)
    (q : ℝ × E) : fourierIntegrand F f ((q), y) = 0 := by
  unfold fourierIntegrand
  have : f (q.1, y) = 0 := by
    by_contra h
    exact absurd ((norm_snd_le (q.1, y)).trans (hR _ (subset_tsupport _ h))) (not_le.2 hy)
  simp [this]

/-- The partial Fourier transform of a spacetime test function is jointly smooth in the time and
the frequency. -/
lemma contDiff_fourier_slice_joint (n : ℕ) :
    ContDiff ℝ n (fun p : ℝ × E => 𝓕 (slice F f p.1) p.2) := by
  rw [contDiff_iff_contDiffAt]
  intro p₀
  obtain ⟨R, hR0, hR⟩ := exists_radius F f
  have hH := contDiff_fourierIntegrand F f
  have hmain : ContDiffOn ℝ n (fun p : ℝ × E => ∫ y : E, fourierIntegrand F f (p, y))
      (Metric.ball p₀ 1) := by
    refine contDiffOn_integral MeasureTheory.volume Metric.isOpen_ball n F
      (fun p y => fourierIntegrand F f (p, y)) (fun y => ?_) (fun k hk p => ?_) (fun k hk => ?_)
    · exact (hH.of_le (by exact_mod_cast le_top)).comp (contDiff_id.prodMk contDiff_const)
    · have := (continuous_iteratedFDeriv_partial (fourierIntegrand F f) hH k).comp
        (continuous_const.prodMk continuous_id : Continuous fun y : E => (p, y))
      exact this.aestronglyMeasurable
    · have hc := (continuous_iteratedFDeriv_partial (fourierIntegrand F f) hH k).norm
      obtain ⟨C, hC⟩ := ((isCompact_closedBall p₀ 1).prod (isCompact_closedBall (0 : E)
        R)).exists_bound_of_continuousOn
        hc.continuousOn
      refine ⟨(Metric.closedBall (0 : E) R).indicator fun _ => max C 0, ?_, ?_⟩
      · exact (MeasureTheory.integrableOn_const (MeasureTheory.measure_closedBall_lt_top
          (x := (0 : E)) (r := R)).ne).integrable_indicator measurableSet_closedBall
      · refine Filter.Eventually.of_forall fun y p hp => ?_
        by_cases hy : ‖y‖ ≤ R
        · rw [Set.indicator_of_mem (by simpa using hy)]
          have := hC (p, y) ⟨Metric.ball_subset_closedBall hp, by simpa using hy⟩
          exact le_trans (by simpa using this) (le_max_left _ _)
        · have hz : (fun q : ℝ × E => fourierIntegrand F f (q, y)) = 0 := by
            funext q; exact fourierIntegrand_eq_zero F f hR (not_le.1 hy) q
          rw [hz]
          have h0 : iteratedFDeriv ℝ k (0 : ℝ × E → F) p = 0 := by
            rw [show (0 : ℝ × E → F) = fun _ => 0 from rfl, iteratedFDeriv_fun_zero]; rfl
          rw [h0, norm_zero]
          exact Set.indicator_nonneg (fun _ _ => le_max_right _ _) _
  have : (fun p : ℝ × E => 𝓕 (slice F f p.1) p.2) =
      fun p => ∫ y : E, fourierIntegrand F f (p, y) := by
    funext p; rw [fourier_slice_apply]; rfl
  rw [this]
  exact hmain.contDiffAt (Metric.ball_mem_nhds p₀ one_pos)

lemma contDiff_fourier_slice_joint_infty :
    ContDiff ℝ ∞ (fun p : ℝ × E => 𝓕 (slice F f p.1) p.2) :=
  contDiff_infty.2 (contDiff_fourier_slice_joint F f)
end

section
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (F : Type u) [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F]

/-- The native continuous inclusion of fixed-support sources into all compact test sources. -/
def supportedSource (K : Compacts (ℝ × E)) :
    ContDiffMapSupportedIn (ℝ × E) F ⊤ K →L[ℝ] 𝓓((⊤ : Opens (ℝ × E)), F) :=
  TestFunction.ofSupportedInCLM ℝ (by simp)

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] in
/-- Every slice seminorm is controlled by a native spacetime source seminorm. -/
lemma seminorm_slice_supported_le (K : Compacts (ℝ × E)) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ p ∈ K, ‖p‖ ≤ R) (f : ContDiffMapSupportedIn (ℝ × E) F ⊤ K)
    (k j : ℕ) (s : ℝ) :
    SchwartzMap.seminorm ℂ k j (slice F (supportedSource F K f) s) ≤
      R ^ k * ContDiffMapSupportedIn.seminorm ℝ (ℝ × E) F ⊤ K j f := by
  refine SchwartzMap.seminorm_le_bound ℂ k j _ (by positivity) fun x => ?_
  have h2 := norm_iteratedFDeriv_slice_le F (supportedSource F K f) j s x
  change ‖iteratedFDeriv ℝ j (slice F (supportedSource F K f) s) x‖ ≤
    ‖iteratedFDeriv ℝ j f (s, x)‖ at h2
  by_cases hx : (s, x) ∈ K
  · have hxR : ‖x‖ ≤ R := (norm_snd_le (s, x)).trans (hR _ hx)
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hxR k)
      (h2.trans (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ))
      (norm_nonneg _) (pow_nonneg hR0 _)
  · have hz : iteratedFDeriv ℝ j f (s, x) = 0 := f.iteratedFDeriv_zero_on_compl hx
    have hn : ‖iteratedFDeriv ℝ j (slice F (supportedSource F K f) s) x‖ = 0 :=
      le_antisymm (h2.trans (by simp [hz])) (norm_nonneg _)
    rw [hn, mul_zero]
    positivity

omit [CompleteSpace F] in
/-- Fourier moments of all fixed-support sources are controlled by one continuous seminorm. -/
lemma exists_fourier_supported_seminorm (K : Compacts (ℝ × E)) (N : ℕ) :
    ∃ q : Seminorm ℝ (ContDiffMapSupportedIn (ℝ × E) F ⊤ K), Continuous q ∧
      ∀ (f : ContDiffMapSupportedIn (ℝ × E) F ⊤ K) (s : ℝ) (ξ : E),
        ‖ξ‖ ^ N * ‖𝓕 (slice F (supportedSource F K f) s) ξ‖ ≤ q f := by
  let p : Seminorm ℂ 𝓢(E, F) :=
    (SchwartzMap.seminorm ℂ N 0).comp (SchwartzMap.fourierTransformCLM ℂ).toLinearMap
  have hp : Continuous p :=
    ((schwartz_withSeminorms ℂ E F).continuous_seminorm (N, 0)).comp
      (SchwartzMap.fourierTransformCLM ℂ).continuous
  obtain ⟨S, c, hc, hS⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ E F) p hp
  obtain ⟨R₀, hR₀⟩ := K.isCompact.isBounded.exists_norm_le
  let R : ℝ≥0 := ⟨max R₀ 0, le_max_right _ _⟩
  have hR : ∀ y ∈ K, ‖y‖ ≤ (R : ℝ) := fun y hy => (hR₀ y hy).trans (le_max_left _ _)
  let q : Seminorm ℝ (ContDiffMapSupportedIn (ℝ × E) F ⊤ K) :=
    c • ∑ i ∈ S, (R ^ i.1) • ContDiffMapSupportedIn.seminorm ℝ (ℝ × E) F ⊤ K i.2
  refine ⟨q, ?_, fun f s ξ => ?_⟩
  · change Continuous (fun f => q f)
    simp only [q, smul_apply, _root_.sum_apply]
    exact (continuous_finsetSum S fun (i : ℕ × ℕ) hi =>
      ((ContDiffMapSupportedIn.withSeminorms ℝ (ℝ × E) F ⊤ K).continuous_seminorm i.2).const_smul
        (R ^ i.1)).const_smul c
  · have hsup : (S.sup (schwartzSeminormFamily ℂ E F)) (slice F (supportedSource F K f) s) ≤
        ∑ i ∈ S, (R : ℝ) ^ i.1 * ContDiffMapSupportedIn.seminorm ℝ (ℝ × E) F ⊤ K i.2 f := by
      apply Seminorm.finset_sup_apply_le (Finset.sum_nonneg fun i hi => by positivity)
      intro i hi
      exact (seminorm_slice_supported_le F K R.2 hR f i.1 i.2 s).trans
        (Finset.single_le_sum (f := fun i : ℕ × ℕ => (R : ℝ) ^ i.1 *
          ContDiffMapSupportedIn.seminorm ℝ (ℝ × E) F ⊤ K i.2 f) (fun j hj => by positivity) hi)
    calc
      _ ≤ SchwartzMap.seminorm ℂ N 0 (𝓕 (slice F (supportedSource F K f) s)) := by
        simpa using SchwartzMap.le_seminorm ℂ N 0 (𝓕 (slice F (supportedSource F K f) s)) ξ
      _ ≤ (c • S.sup (schwartzSeminormFamily ℂ E F)) (slice F (supportedSource F K f) s) := hS _
      _ ≤ q f := by
        simp only [q, smul_apply, _root_.sum_apply, NNReal.smul_def, smul_eq_mul,
          NNReal.coe_pow]
        exact mul_le_mul_of_nonneg_left hsup c.2

omit [CompleteSpace F] in
/-- A continuous source seminorm controls arbitrary polynomial Fourier decay uniformly in time. -/
lemma exists_fourier_decay_supported_seminorm (K : Compacts (ℝ × E)) (N : ℕ) :
    ∃ q : Seminorm ℝ (ContDiffMapSupportedIn (ℝ × E) F ⊤ K), Continuous q ∧
      ∀ (f : ContDiffMapSupportedIn (ℝ × E) F ⊤ K) (s : ℝ) (ξ : E),
        ‖𝓕 (slice F (supportedSource F K f) s) ξ‖ ≤ q f * (1 + ‖ξ‖) ^ (-(N : ℝ)) := by
  obtain ⟨q0, hq0c, hq0⟩ := exists_fourier_supported_seminorm F K 0
  obtain ⟨qN, hqNc, hqN⟩ := exists_fourier_supported_seminorm F K N
  refine ⟨(2 ^ (N - 1) : ℝ≥0) • (q0 + qN), (hq0c.add hqNc).const_smul _, fun f s ξ => ?_⟩
  simp only [smul_apply, add_apply, NNReal.smul_def, NNReal.coe_pow, NNReal.coe_ofNat, smul_eq_mul]
  have hpos : 0 < (1 + ‖ξ‖) ^ N := by positivity
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hpos]
  have h2 := add_pow_le (zero_le_one' ℝ) (norm_nonneg ξ) N
  calc
    _ ≤ ‖𝓕 (slice F (supportedSource F K f) s) ξ‖ *
        (2 ^ (N - 1) * (1 ^ N + ‖ξ‖ ^ N)) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = 2 ^ (N - 1) * (‖ξ‖ ^ 0 * ‖𝓕 (slice F (supportedSource F K f) s) ξ‖ +
        ‖ξ‖ ^ N * ‖𝓕 (slice F (supportedSource F K f) s) ξ‖) := by ring
    _ ≤ _ := by
      gcongr
      · exact hq0 f s ξ
      · exact hqN f s ξ

/-- Time differentiation is a continuous endomorphism of every fixed-support source space. -/
def supportedDt (K : Compacts (ℝ × E)) :
    ContDiffMapSupportedIn (ℝ × E) F ⊤ K →L[ℝ] ContDiffMapSupportedIn (ℝ × E) F ⊤ K :=
  (ContDiffMapSupportedIn.postcompCLM (ContinuousLinearMap.apply ℝ F (1, (0 : E)))).comp
    (ContDiffMapSupportedIn.fderivCLM ℝ ⊤ ⊤)

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] in
lemma supportedSource_dt (K : Compacts (ℝ × E)) (f : ContDiffMapSupportedIn (ℝ × E) F ⊤ K) :
    supportedSource F K (supportedDt F K f) = dt F (supportedSource F K f) := by
  ext p
  rw [dt_apply, ((supportedSource F K f).contDiff.differentiable (by simp) p).lineDeriv_eq_fderiv]
  change ((ContDiffMapSupportedIn.fderivCLM ℝ ⊤ ⊤ f) p) (1, (0 : E)) = _
  rw [ContDiffMapSupportedIn.fderivCLM_apply_of_le ℝ f (by simp)]
  rfl

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] in
lemma supportedSource_iterate_dt (K : Compacts (ℝ × E)) (j : ℕ)
    (f : ContDiffMapSupportedIn (ℝ × E) F ⊤ K) :
    supportedSource F K ((supportedDt F K)^[j] f) = (dt F)^[j] (supportedSource F K f) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', supportedSource_dt, ih]

omit [CompleteSpace F] in
/-- Time derivatives of Fourier slices are bounded by continuous source seminorms. -/
lemma exists_timeDeriv_fourier_supported_seminorm (K : Compacts (ℝ × E)) (j N : ℕ) :
    ∃ q : Seminorm ℝ (ContDiffMapSupportedIn (ℝ × E) F ⊤ K), Continuous q ∧
      ∀ (f : ContDiffMapSupportedIn (ℝ × E) F ⊤ K) (s : ℝ) (ξ : E),
        ‖iteratedDeriv j (fun r => 𝓕 (slice F (supportedSource F K f) r) ξ) s‖ ≤
          q f * (1 + ‖ξ‖) ^ (-(N : ℝ)) := by
  obtain ⟨q, hqc, hq⟩ := exists_fourier_decay_supported_seminorm F K N
  let D := (supportedDt F K) ^ j
  refine ⟨q.comp D.toLinearMap, hqc.comp D.continuous, fun f s ξ => ?_⟩
  rw [iteratedDeriv_fourier_slice F ξ j (supportedSource F K f), ← supportedSource_iterate_dt F K j
    f]
  simpa [D, Seminorm.comp_apply, FunLike.coe_pow_eq_iterate, Module.End.pow_apply] using hq
    ((supportedDt F K)^[j] f) s ξ

omit [CompleteSpace F] in
lemma exists_char_timeDeriv_supported_seminorm (K : Compacts (ℝ × E)) (i j N : ℕ) :
    ∃ q : Seminorm ℝ (ContDiffMapSupportedIn (ℝ × E) F ⊤ K), Continuous q ∧
      ∀ (f : ContDiffMapSupportedIn (ℝ × E) F ⊤ K) (s : ℝ) (ξ : E),
        (2 * π * ‖ξ‖) ^ i *
          ‖iteratedDeriv j (fun r => 𝓕 (slice F (supportedSource F K f) r) ξ) s‖ ≤
            q f * (1 + ‖ξ‖) ^ (-(N : ℝ)) := by
  obtain ⟨q, hqc, hq⟩ := exists_timeDeriv_fourier_supported_seminorm F K j (i + N)
  let C : ℝ≥0 := ⟨(2 * π) ^ i, by positivity⟩
  refine ⟨C • q, hqc.const_smul C, fun f s ξ => ?_⟩
  calc
    _ ≤ (2 * π * ‖ξ‖) ^ i * (q f * (1 + ‖ξ‖) ^ (-((i + N : ℕ) : ℝ))) := by
      exact mul_le_mul_of_nonneg_left (hq f s ξ) (by positivity)
    _ = q f * ((2 * π * ‖ξ‖) ^ i * (1 + ‖ξ‖) ^ (-((i + N : ℕ) : ℝ))) := by ring
    _ ≤ q f * ((2 * π) ^ i * (1 + ‖ξ‖) ^ (-(N : ℝ))) :=
      mul_le_mul_of_nonneg_left (char_pow_mul_decay_le ξ i N) (apply_nonneg _ _)
    _ = _ := by change q f * _ = ((2 * π) ^ i * q f) * _; ring
end

end TimeSlice
