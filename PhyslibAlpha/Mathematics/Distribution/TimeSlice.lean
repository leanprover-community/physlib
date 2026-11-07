/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import PhyslibAlpha.Mathematics.Distribution.TestFunction

/-!

# Time slices of test functions

A test function on time and space has a Schwartz function as its slice at a fixed time.

## i. Overview

A test function on time and space has a Schwartz function as its slice at a fixed time. Time and
space derivatives and the time reflection commute with slicing.

## ii. Key results

- `slice` : The slice `f(s, ·)` of a spacetime test function at the time `s` is a Schwartz function.
- `timeReflect` : Reflection in time.
- `reflect` : The time-reflected test function.
- `dt` : The time derivative of a spacetime test function.
- `reflectSourceCLM` : Time reflection acts continuously on the native compact source space.
- `timeReflectionCLE` : Time reflection on time-space coordinates.
- `dx` : Spatial differentiation of a spacetime test field in the direction `m`.
- `spatialLaplacian` : The spatial Laplacian on compact spacetime test fields.

## iii. Table of contents

- A. Time slices of test functions
- B. Causal support of the retarded solution
- C. The time dependence of the Fourier transformed slices
- D. Continuous seminorm bounds for Fourier sources
- E. Continuous compactly cut off advanced response
- F. The two-sided Klein–Gordon inverse on compact test fields

## iv. References

None.

## A. Time slices of test functions

- `slice` : The slice `f(s, ·)` of a spacetime test function at the time `s` is a Schwartz function.

Lemmas: `isClosedEmbedding_prodMk`, `hasCompactSupport_slice`, `contDiff_slice`, `slice_apply`,
`norm_iteratedFDeriv_slice_le`, `exists_bound_iteratedFDeriv`, `exists_radius`,
`exists_seminorm_slice_le`, `exists_fourier_bound`, `exists_fourier_decay_pow` and more.

## B. Causal support of the retarded solution

- `timeReflect` : Reflection in time.
- `reflect` : The time-reflected test function.

Lemmas: `timeReflect_apply`, `reflect_apply`, `tsupport_reflect`, `slice_add`, `slice_smul`.

## C. The time dependence of the Fourier transformed slices

- `dt` : The time derivative of a spacetime test function.

Lemmas: `dt_apply`, `hasDerivAt_time`.

## D. Continuous seminorm bounds for Fourier sources

- `reflectSourceCLM` : Time reflection acts continuously on the native compact source space.

Lemmas: `reflectSourceCLM_eq`.

## E. Continuous compactly cut off advanced response

- `timeReflectionCLE` : Time reflection on time-space coordinates.

Lemmas: `timeReflectionCLE_apply`.

## F. The two-sided Klein–Gordon inverse on compact test fields

- `dx` : Spatial differentiation of a spacetime test field in the direction `m`.
- `spatialLaplacian` : The spatial Laplacian on compact spacetime test fields.

Lemmas: `slice_dx`, `slice_spatialLaplacian`, `dt_reflect`, `dt_neg`, `dt_dt_reflect`,
`slice_reflect`, `dx_reflect`, `spatialLaplacian_reflect`.

-/

@[expose] public section

noncomputable section

open scoped SchwartzMap FourierTransform Distributions ContDiff Laplacian NNReal
open TestFunction TopologicalSpace Topology MeasureTheory LineDeriv
universe u

namespace TimeSlice

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F]
variable (f : 𝓓((⊤ : Opens (ℝ × E)), F))

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma isClosedEmbedding_prodMk (s : ℝ) : IsClosedEmbedding fun x : E => (s, x) := by
  refine ⟨isEmbedding_prodMkRight s, ?_⟩
  have : Set.range (fun x : E => (s, x)) = {s} ×ˢ Set.univ := by
    ext ⟨a, b⟩; simp [eq_comm]
  rw [this]
  exact isClosed_singleton.prod isClosed_univ

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] in
lemma hasCompactSupport_slice (s : ℝ) : HasCompactSupport fun x : E => f (s, x) :=
  f.hasCompactSupport.comp_isClosedEmbedding (isClosedEmbedding_prodMk s)

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] in
lemma contDiff_slice (s : ℝ) : ContDiff ℝ ∞ fun x : E => f (s, x) :=
  f.contDiff.comp (contDiff_const.prodMk contDiff_id)

/-- The slice `f(s, ·)` of a spacetime test function at the time `s` is a Schwartz function. -/
def slice (s : ℝ) : 𝓢(E, F) :=
  (hasCompactSupport_slice F f s).toSchwartzMap (contDiff_slice F f s)

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] in
@[simp]
lemma slice_apply (s : ℝ) (x : E) : slice F f s x = f (s, x) := rfl

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] in
/-- The derivatives of a slice are bounded by the derivatives of the spacetime function. -/
lemma norm_iteratedFDeriv_slice_le (p : ℕ) (s : ℝ) (x : E) :
    ‖iteratedFDeriv ℝ p (fun x : E => f (s, x)) x‖ ≤ ‖iteratedFDeriv ℝ p f (s, x)‖ := by
  have h : (fun x : E => f (s, x)) =
      (fun y : ℝ × E => f (y + (s, 0))) ∘ (ContinuousLinearMap.inr ℝ ℝ E) := by
    funext x; simp
  have hd : ContDiff ℝ ∞ (fun y : ℝ × E => f (y + (s, 0))) :=
    f.contDiff.comp (contDiff_id.add contDiff_const)
  rw [h, ContinuousLinearMap.iteratedFDeriv_comp_right _ hd x (by exact_mod_cast le_top),
    iteratedFDeriv_comp_add_right]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have h1 : ∏ _i : Fin p, ‖ContinuousLinearMap.inr ℝ ℝ E‖ ≤ 1 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_one₀ (ContinuousLinearMap.opNorm_nonneg _)
      (ContinuousLinearMap.norm_inr_le_one ..)
  calc _ ≤ ‖iteratedFDeriv ℝ p f ((ContinuousLinearMap.inr ℝ ℝ E) x + (s, 0))‖ * 1 :=
        le_trans (by gcongr) (le_of_eq rfl)
    _ = _ := by simp [add_comm]

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] in
lemma exists_bound_iteratedFDeriv (p : ℕ) :
    ∃ M : ℝ, ∀ y : ℝ × E, ‖iteratedFDeriv ℝ p f y‖ ≤ M := by
  have hc : Continuous fun y : ℝ × E => ‖iteratedFDeriv ℝ p f y‖ :=
    (f.contDiff.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm
  have hs : HasCompactSupport fun y : ℝ × E => ‖iteratedFDeriv ℝ p f y‖ :=
    (f.hasCompactSupport.iteratedFDeriv p).norm
  obtain ⟨M, hM⟩ := hc.bounded_above_of_compact_support hs
  exact ⟨M, fun y => by simpa using hM y⟩

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] in
lemma exists_radius : ∃ R : ℝ, 0 ≤ R ∧ ∀ y ∈ tsupport f, ‖y‖ ≤ R := by
  obtain ⟨R, hR⟩ := f.hasCompactSupport.isCompact.isBounded.exists_norm_le
  exact ⟨max R 0, le_max_right _ _, fun y hy => (hR y hy).trans (le_max_left _ _)⟩

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] in
/-- The Schwartz seminorms of the slices are bounded uniformly in the time. -/
lemma exists_seminorm_slice_le (k p : ℕ) :
    ∃ C : ℝ, ∀ s, SchwartzMap.seminorm ℂ k p (slice F f s) ≤ C := by
  obtain ⟨M, hM⟩ := exists_bound_iteratedFDeriv F f p
  obtain ⟨R, hR0, hR⟩ := exists_radius F f
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  refine ⟨R ^ k * max M 0, fun s => ?_⟩
  refine SchwartzMap.seminorm_le_bound ℂ k p _ (by positivity) fun x => ?_
  have h2 : ‖iteratedFDeriv ℝ p (slice F f s) x‖ ≤ ‖iteratedFDeriv ℝ p f (s, x)‖ :=
    norm_iteratedFDeriv_slice_le F f p s x
  by_cases hx : (s, x) ∈ tsupport f
  · have h1 : ‖x‖ ≤ R := (norm_snd_le (s, x)).trans (hR _ hx)
    have h3 : ‖iteratedFDeriv ℝ p (slice F f s) x‖ ≤ max M 0 :=
      h2.trans ((hM _).trans (le_max_left _ _))
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h1 k) h3 (norm_nonneg _) (by positivity)
  · have h0 : iteratedFDeriv ℝ p f (s, x) = 0 := by
      by_contra h
      exact hx (support_iteratedFDeriv_subset (𝕜 := ℝ) (n := p) (Function.mem_support.2 h))
    have : ‖iteratedFDeriv ℝ p (slice F f s) x‖ = 0 :=
      le_antisymm (h2.trans (by simp [h0])) (norm_nonneg _)
    rw [this, mul_zero]
    positivity

omit [CompleteSpace F] in
/-- The Fourier transforms of the slices decay uniformly in the time. -/
lemma exists_fourier_bound (N : ℕ) :
    ∃ C : ℝ, ∀ s (ξ : E), ‖ξ‖ ^ N * ‖𝓕 (slice F f s) ξ‖ ≤ C := by
  let q : Seminorm ℂ 𝓢(E, F) :=
    (SchwartzMap.seminorm ℂ N 0).comp (SchwartzMap.fourierTransformCLM ℂ).toLinearMap
  have hq : Continuous q :=
    ((schwartz_withSeminorms ℂ E F).continuous_seminorm (N, 0)).comp
      (SchwartzMap.fourierTransformCLM ℂ).continuous
  obtain ⟨S, c, -, hS⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ E F) q hq
  choose B hB using fun i : ℕ × ℕ => exists_seminorm_slice_le F f i.1 i.2
  let T : ℝ := ∑ i ∈ S, max (B i) 0
  have hT : 0 ≤ T := Finset.sum_nonneg fun i _ => le_max_right _ _
  refine ⟨c * T, fun s ξ => ?_⟩
  have h1 : (S.sup (schwartzSeminormFamily ℂ E F)) (slice F f s) ≤ T := by
    refine Seminorm.finset_sup_apply_le hT fun i hi => ?_
    calc _ ≤ B i := hB i s
      _ ≤ max (B i) 0 := le_max_left _ _
      _ ≤ T := Finset.single_le_sum (f := fun i => max (B i) 0) (fun j _ => le_max_right _ _) hi
  calc ‖ξ‖ ^ N * ‖𝓕 (slice F f s) ξ‖
      ≤ SchwartzMap.seminorm ℂ N 0 (𝓕 (slice F f s)) := by
        simpa using SchwartzMap.le_seminorm ℂ N 0 (𝓕 (slice F f s)) ξ
    _ = q (slice F f s) := rfl
    _ ≤ (c • S.sup (schwartzSeminormFamily ℂ E F)) (slice F f s) := hS _
    _ ≤ c * T := by
        simp only [smul_apply, NNReal.smul_def, smul_eq_mul]
        exact mul_le_mul_of_nonneg_left h1 c.2

omit [CompleteSpace F] in
/-- Polynomial decay of any order of the Fourier transforms of the slices, uniformly in the
time. -/
lemma exists_fourier_decay_pow (N : ℕ) :
    ∃ K : ℝ, ∀ s (ξ : E), ‖𝓕 (slice F f s) ξ‖ ≤ K * (1 + ‖ξ‖) ^ (-(N : ℝ)) := by
  obtain ⟨C₀, h₀⟩ := exists_fourier_bound F f 0
  obtain ⟨C₁, h₁⟩ := exists_fourier_bound F f N
  refine ⟨2 ^ (N - 1) * (C₀ + C₁), fun s ξ => ?_⟩
  have hpos : 0 < (1 + ‖ξ‖) ^ N := by positivity
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv,
    le_div_iff₀ hpos]
  have h2 := add_pow_le (zero_le_one' ℝ) (norm_nonneg ξ) N
  calc ‖𝓕 (slice F f s) ξ‖ * (1 + ‖ξ‖) ^ N
      ≤ ‖𝓕 (slice F f s) ξ‖ * (2 ^ (N - 1) * (1 ^ N + ‖ξ‖ ^ N)) :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = 2 ^ (N - 1) * (‖ξ‖ ^ 0 * ‖𝓕 (slice F f s) ξ‖ + ‖ξ‖ ^ N * ‖𝓕 (slice F f s) ξ‖) := by ring
    _ ≤ 2 ^ (N - 1) * (C₀ + C₁) := by
        gcongr
        · exact h₀ s ξ
        · exact h₁ s ξ

omit [CompleteSpace F] in
lemma exists_fourier_decay :
    ∃ K : ℝ, ∀ s (ξ : E), ‖𝓕 (slice F f s) ξ‖ ≤ K * (1 + ‖ξ‖) ^ (-((Module.finrank ℝ E + 1 : ℕ) :
      ℝ)) :=
  exists_fourier_decay_pow F f _

omit [CompleteSpace F] in
lemma fourier_slice_apply (s : ℝ) (ξ : E) :
    𝓕 (slice F f s) ξ = ∫ x : E, 𝐞 (-inner ℝ x ξ) • f (s, x) := by
  rw [SchwartzMap.fourier_coe, Real.fourier_eq]
  rfl

omit [CompleteSpace F] in
lemma continuous_fourier_slice :
    Continuous fun p : ℝ × E => 𝓕 (slice F f p.1) p.2 := by
  simp_rw [fourier_slice_apply]
  obtain ⟨R, hR0, hR⟩ := exists_radius F f
  obtain ⟨M, hM⟩ := exists_bound_iteratedFDeriv F f 0
  have hf : ∀ s : ℝ, Continuous fun x : E => f (s, x) := fun s => f.continuous.comp (by fun_prop)
  refine MeasureTheory.continuous_of_dominated
    (bound := (Metric.closedBall (0 : E) R).indicator fun _ => M) ?_ ?_ ?_ ?_
  · intro p
    exact (Continuous.aestronglyMeasurable
      ((Real.continuous_fourierChar.comp
        ((continuous_id.inner continuous_const).neg)).smul (hf p.1)))
  · intro p
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Circle.norm_smul]
    by_cases hx : (p.1, x) ∈ tsupport f
    · have hxR : x ∈ Metric.closedBall (0 : E) R := by
        rw [mem_closedBall_zero_iff]; exact (norm_snd_le (p.1, x)).trans (hR _ hx)
      rw [Set.indicator_of_mem hxR]
      simpa using hM (p.1, x)
    · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => (norm_nonneg _).trans (by simpa using hM (p.1, 0))) _
  · exact (MeasureTheory.integrableOn_const (MeasureTheory.measure_closedBall_lt_top
      (x := (0 : E)) (r := R)).ne).integrable_indicator measurableSet_closedBall
  · refine Filter.Eventually.of_forall fun x => ?_
    have h1 : Continuous fun p : ℝ × E => (inner ℝ x p.2 : ℝ) := continuous_const.inner
      continuous_snd
    have h2 : Continuous fun p : ℝ × E => f (p.1, x) := f.continuous.comp (by fun_prop)
    exact (Real.continuous_fourierChar.comp h1.neg).smul h2

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] in
lemma slice_eq_zero_of_notMem {s : ℝ} (hs : s ∉ Prod.fst '' tsupport f) : slice F f s = 0 := by
  ext x
  have : (s, x) ∉ tsupport f := fun h => hs ⟨(s, x), h, rfl⟩
  simp [image_eq_zero_of_notMem_tsupport this]

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] in
/-- The time support of a spacetime test function is compact. -/
lemma isCompact_timeSupport : IsCompact (Prod.fst '' tsupport f) :=
  f.hasCompactSupport.isCompact.image continuous_fst
end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] (f : 𝓓((⊤ : Opens (ℝ × E)), F))

/-- Reflection in time. -/
def timeReflect : ℝ × E ≃ₜ ℝ × E :=
  Homeomorph.prodCongr (Homeomorph.neg ℝ) (Homeomorph.refl E)

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
@[simp] lemma timeReflect_apply (p : ℝ × E) : timeReflect p = (-p.1, p.2) := rfl

/-- The time-reflected test function. -/
def reflect : 𝓓((⊤ : Opens (ℝ × E)), F) where
  toFun p := f (-p.1, p.2)
  contDiff' := f.contDiff.comp ((contDiff_fst.neg).prodMk contDiff_snd)
  hasCompactSupport' := f.hasCompactSupport.comp_homeomorph timeReflect
  tsupport_subset' := fun _ _ => trivial

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] in
@[simp] lemma reflect_apply (p : ℝ × E) : reflect F f p = f (-p.1, p.2) := rfl

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] in
/-- Time reflection is an involution. -/
lemma reflect_reflect : reflect F (reflect F f) = f := by
  ext p
  simp

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] in
lemma tsupport_reflect : tsupport (reflect F f) = timeReflect ⁻¹' tsupport f := by
  have : (⇑(reflect F f)) = (⇑f) ∘ timeReflect := rfl
  rw [this, tsupport, tsupport, Function.support_comp_eq_preimage, ← Homeomorph.preimage_closure]

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] in
lemma slice_add (g : 𝓓((⊤ : Opens (ℝ × E)), F)) (s : ℝ) :
    slice F (f + g) s = slice F f s + slice F g s := by
  ext x; rfl

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] in
lemma slice_smul (c : ℝ) (s : ℝ) : slice F (c • f) s = c • slice F f s := by
  ext x; rfl

/-- The time derivative of a spacetime test function. -/
def dt : 𝓓((⊤ : Opens (ℝ × E)), F) :=
  (TestFunction.lineDerivCLM ℝ ((1 : ℝ), (0 : E)) f : 𝓓((⊤ : Opens (ℝ × E)), F))

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] in
lemma dt_apply (p : ℝ × E) : dt F f p = lineDeriv ℝ f p ((1 : ℝ), (0 : E)) := by
  unfold dt
  rw [TestFunction.lineDerivCLM_apply_of_le (by simp)]

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] in
lemma hasDerivAt_time (s : ℝ) (y : E) : HasDerivAt (fun r : ℝ => f (r, y)) (dt F f (s, y)) s := by
  rw [dt_apply]
  have h : HasFDerivAt f (fderiv ℝ f (s, y)) (s, y) :=
    ((f.contDiff.differentiable (by simp)) (s, y)).hasFDerivAt
  have h2 : HasDerivAt (fun r : ℝ => (r, y)) ((1 : ℝ), (0 : E)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s y)
  have := h.comp_hasDerivAt s h2
  rw [(h.differentiableAt).lineDeriv_eq_fderiv]
  exact this
end

section
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (F : Type u) [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F]

/-- Time reflection acts continuously on the native compact source space. -/
def reflectSourceCLM :
    𝓓((⊤ : Opens (ℝ × E)), F) →L[ℝ] 𝓓((⊤ : Opens (ℝ × E)), F) :=
  precompLinearEquivCLM
    ((ContinuousLinearEquiv.neg ℝ (M := ℝ)).prodCongr (ContinuousLinearEquiv.refl ℝ E))

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] in
lemma reflectSourceCLM_eq (f : 𝓓((⊤ : Opens (ℝ × E)), F)) :
    reflectSourceCLM F f = reflect F f := by
  ext p
  rfl

/-- Time reflection on time-space coordinates. -/
def timeReflectionCLE (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (ℝ × E) ≃L[ℝ] (ℝ × E) :=
  (ContinuousLinearEquiv.neg ℝ).prodCongr (ContinuousLinearEquiv.refl ℝ E)

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
@[simp] lemma timeReflectionCLE_apply (p : ℝ × E) : timeReflectionCLE E p = (-p.1, p.2) := rfl
end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] (f : 𝓓((⊤ : Opens (ℝ × E)), F))

/-- Spatial differentiation of a spacetime test field in the direction `m`. -/
def dx (m : E) : 𝓓((⊤ : Opens (ℝ × E)), F) :=
  TestFunction.lineDerivCLM ℝ ((0 : ℝ), m) f

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] in
lemma slice_dx (m : E) (s : ℝ) : slice F (dx F f m) s = ∂_{m} (slice F f s) := by
  ext x
  rw [slice_apply, dx, TestFunction.lineDerivCLM_apply_of_le (by simp),
    (f.contDiff.differentiable (by simp) (s, x)).lineDeriv_eq_fderiv,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hf := (f.contDiff.differentiable (by simp) (s, x)).hasFDerivAt
  have hi : HasFDerivAt (fun y : E => (s, y)) (ContinuousLinearMap.inr ℝ ℝ E) x :=
    (hasFDerivAt_const s x).prodMk (hasFDerivAt_id x)
  have hc := (hf.comp x hi).fderiv
  exact (congrArg (fun L : E →L[ℝ] F => L m) hc).symm

/-- The spatial Laplacian on compact spacetime test fields. -/
def spatialLaplacian : 𝓓((⊤ : Opens (ℝ × E)), F) :=
  ∑ i, dx F (dx F f (stdOrthonormalBasis ℝ E i)) (stdOrthonormalBasis ℝ E i)

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma slice_spatialLaplacian (s : ℝ) :
    slice F (spatialLaplacian F f) s = Δ (slice F f s) := by
  rw [SchwartzMap.laplacian_eq_sum (stdOrthonormalBasis ℝ E)]
  have hs : ∀ (g : Fin (Module.finrank ℝ E) → 𝓓((⊤ : Opens (ℝ × E)), F)),
      slice F (∑ i, g i) s = ∑ i, slice F (g i) s := by
    intro g; ext x; simp [slice_apply]
  rw [spatialLaplacian, hs]
  simp_rw [slice_dx]

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] in
lemma dt_reflect : dt F (reflect F f) = -reflect F (dt F f) := by
  ext p
  have h1 := hasDerivAt_time F (reflect F f) p.1 p.2
  have h2 := (hasDerivAt_time F f (-p.1) p.2).scomp p.1 (hasDerivAt_id p.1).neg
  simpa using h1.unique h2

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] in
lemma dt_neg : dt F (-f) = -dt F f := map_neg (TestFunction.lineDerivCLM ℝ (1, (0 : E))) f

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] in
lemma dt_dt_reflect : dt F (dt F (reflect F f)) = reflect F (dt F (dt F f)) := by
  rw [dt_reflect, dt_neg, dt_reflect]
  ext p
  simp

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] in
lemma slice_reflect (s : ℝ) : slice F (reflect F f) s = slice F f (-s) := by
  ext x; rfl

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] in
lemma dx_reflect (m : E) : dx F (reflect F f) m = reflect F (dx F f m) := by
  ext p
  change slice F (dx F (reflect F f) m) p.1 p.2 = slice F (dx F f m) (-p.1) p.2
  rw [slice_dx, slice_dx, slice_reflect]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma spatialLaplacian_reflect :
    spatialLaplacian F (reflect F f) = reflect F (spatialLaplacian F f) := by
  simp only [spatialLaplacian, dx_reflect]
  ext p
  simp [reflect_apply]
end

end TimeSlice
