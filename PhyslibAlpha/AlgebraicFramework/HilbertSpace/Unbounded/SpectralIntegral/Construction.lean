/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.SelfAdjointSpectralTheorem
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
public import Mathlib.MeasureTheory.VectorMeasure.SetIntegral

/-!
# Canonical unbounded spectral integrals: construction

Builds the maximal spectral integral of a real-valued measurable function against a
`WOTSpectralMeasure`, as the limit of its truncations, and shows the resulting operator is
densely defined, closable, symmetric, and essentially self-adjoint. Continued in
`SpectralIntegral/SpecTheorem.lean`, which proves this operator is in fact self-adjoint and
assembles the domain-aware self-adjoint spectral theorem.
-/

@[expose] public section

noncomputable section

open scoped Topology InnerProductSpace Function
open ContinuousLinearMap ContinuousLinearMapWOT MeasureTheory Set
open QuantumMechanics.WOTSpectralMeasure

namespace QuantumMechanics.WOTSpectralMeasure

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
/-- The bounded real spectral variable truncated to `[-n,n]`. -/
def truncationFunction (n : ℕ) : ℝ → ℂ :=
  (Set.Icc (-(n : ℝ)) (n : ℝ)).indicator (fun r : ℝ => (r : ℂ))

/-- The real-truncation indicator function, real-valued, at cutoff `n`. -/
def realTruncationFunction (n : ℕ) : ℝ → ℝ :=
  (Set.Icc (-(n : ℝ)) (n : ℝ)).indicator id

/-- The spectral cutoff set `[-n, n]`. -/
def spectralCutoffSet (n : ℕ) : Set ℝ := Set.Icc (-(n : ℝ)) (n : ℝ)

lemma spectralCutoffSet_mono : Monotone spectralCutoffSet := by
  intro n m hnm r hr
  have hnmR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  exact ⟨le_trans (neg_le_neg hnmR) hr.1, le_trans hr.2 hnmR⟩

lemma spectralCutoffSet_iUnion : ⋃ n, spectralCutoffSet n = Set.univ := by
  ext r
  simp only [mem_iUnion, mem_Icc, mem_univ, iff_true]
  obtain ⟨n, hn⟩ := exists_nat_ge |r|
  exact ⟨n, neg_le_of_abs_le hn, le_trans (le_abs_self r) hn⟩

lemma truncationFunction_measurable (n : ℕ) : Measurable (truncationFunction n) := by
  exact Complex.measurable_ofReal.indicator measurableSet_Icc

lemma truncationFunction_bounded (n : ℕ) :
    ∃ C : ℝ, ∀ r, ‖truncationFunction n r‖ ≤ C := by
  refine ⟨n, fun r => ?_⟩
  by_cases hr : r ∈ Set.Icc (-(n : ℝ)) (n : ℝ)
  · rw [truncationFunction, Set.indicator_of_mem hr]
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr hr
  · simp [truncationFunction, hr]

lemma realTruncationFunction_measurable (n : ℕ) :
    Measurable (realTruncationFunction n) := by
  exact measurable_id.indicator measurableSet_Icc

lemma realTruncationFunction_bounded (n : ℕ) :
    ∃ C : ℝ, ∀ r, |realTruncationFunction n r| ≤ C := by
  refine ⟨n, fun r => ?_⟩
  by_cases hr : r ∈ Set.Icc (-(n : ℝ)) (n : ℝ)
  · rw [realTruncationFunction, Set.indicator_of_mem hr]
    exact abs_le.mpr hr
  · simp [realTruncationFunction, hr]

lemma realTruncationFunction_complex_eq (n : ℕ) :
    (fun r => (realTruncationFunction n r : ℂ)) = truncationFunction n := by
  funext r
  by_cases hr : r ∈ Set.Icc (-(n : ℝ)) (n : ℝ) <;>
    simp [realTruncationFunction, truncationFunction, hr]

lemma truncationFunction_eventually_eq (r : ℝ) :
    ∀ᶠ n : ℕ in Filter.atTop, truncationFunction n r = (r : ℂ) := by
  obtain ⟨N, hN⟩ := exists_nat_ge |r|
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  have hnr : |r| ≤ (n : ℝ) := le_trans hN (by exact_mod_cast hn)
  rw [truncationFunction, Set.indicator_of_mem]
  exact abs_le.mp hnr

lemma truncationFunction_tendsto (r : ℝ) :
    Filter.Tendsto (fun n : ℕ => truncationFunction n r) Filter.atTop (𝓝 (r : ℂ)) := by
  exact tendsto_nhds_of_eventually_eq (truncationFunction_eventually_eq r)

lemma truncationIntegral_inner_tendsto_complexWeakIntegral
    (μS : WOTSpectralMeasure ℝ H) (x y : H)
    (hfi : (μS.scalarMeasure x y).Integrable id) :
    Filter.Tendsto
      (fun n : ℕ => ∫ᵛ r, truncationFunction n r ∂[
        ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); μS.scalarMeasure x y])
      Filter.atTop (𝓝 (μS.complexWeakIntegral (fun r : ℝ => (r : ℂ)) x y)) := by
  let ν := μS.scalarMeasure x y
  have hbound : Integrable (fun r : ℝ => |r|) ν.variation := by
    simpa [ν, Real.norm_eq_abs] using hfi.norm
  have hdom : Filter.Tendsto
      (fun n : ℕ => ∫ᵛ r, truncationFunction n r ∂[
        ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); ν])
      Filter.atTop (𝓝 (∫ᵛ r, (r : ℂ) ∂[
        ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); ν])) := by
    apply MeasureTheory.VectorMeasure.tendsto_integral_of_dominated_convergence
      (μ := ν) (B := ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ))
      (fun r : ℝ => |r|)
    · intro n
      exact (truncationFunction_measurable n).aestronglyMeasurable
    · exact hbound
    · intro n
      filter_upwards [] with r
      by_cases hr : r ∈ Set.Icc (-(n : ℝ)) (n : ℝ)
      · simp [truncationFunction, Set.indicator_of_mem hr, Complex.norm_real,
          Real.norm_eq_abs]
      · simp [truncationFunction, Set.indicator, hr]
    · filter_upwards [] with r
      exact truncationFunction_tendsto r
  convert hdom using 1
  simpa [WOTSpectralMeasure.complexWeakIntegral, ν] using hdom

@[nolint synTaut]
lemma integral_indicator_real_eq_complex
    {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.VectorMeasure α ℂ)
    (c : ℝ) (s : Set α) :
    (∫ᵛ x, s.indicator (fun _ => (c : ℂ)) x
      ∂[ContinuousLinearMap.lsmul ℝ ℂ; μ]) =
      ∫ᵛ x, (s.indicator (fun _ => c) x : ℂ)
        ∂[ContinuousLinearMap.lsmul ℝ ℂ; μ] := by
  have hfun : (fun x => s.indicator (fun _ => (c : ℂ)) x) =
      (fun x => (s.indicator (fun _ => c) x : ℂ)) := by
    simpa [Function.comp_def] using
      (Set.indicator_comp_of_zero (s := s) (f := fun _ : α => c)
        (g := Complex.ofRealCLM) Complex.ofRealCLM.map_zero)
  exact congrArg (fun f : α → ℂ =>
    ∫ᵛ x, f x ∂[ContinuousLinearMap.lsmul ℝ ℂ; μ]) hfun

lemma integral_real_eq_complex
    {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.VectorMeasure α ℂ)
    {g : α → ℝ} (hg : μ.Integrable g) :
    ∫ᵛ x, g x ∂[ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ); μ] =
      ∫ᵛ x, (g x : ℂ) ∂[ContinuousLinearMap.lsmul ℝ ℂ; μ] := by
  apply hg.induction (P := fun f =>
    ∫ᵛ x, f x ∂[ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ); μ] =
      ∫ᵛ x, Complex.ofRealCLM (f x)
        ∂[ContinuousLinearMap.lsmul ℝ ℂ; μ])
  · intro c s hs hfinite
    change μ.variation s < ⊤ at hfinite
    have hfinite' : IsFiniteMeasure (μ.variation.restrict s) := by
      exact MeasureTheory.isFiniteMeasure_restrict.mpr hfinite.ne
    letI := hfinite'
    calc
      ∫ᵛ x, s.indicator (fun _ => c) x
          ∂[ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ); μ] =
          (ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ)) c (μ s) :=
        VectorMeasure.integral_indicator_const c hs
      _ = (ContinuousLinearMap.lsmul ℝ ℂ) (c : ℂ) (μ s) := by
        simp [ContinuousLinearMap.lsmul_apply]
      _ = ∫ᵛ x, s.indicator (fun _ => (c : ℂ)) x
          ∂[ContinuousLinearMap.lsmul ℝ ℂ; μ] :=
        (VectorMeasure.integral_indicator_const (c : ℂ) hs).symm
      _ = ∫ᵛ x, Complex.ofRealCLM (s.indicator (fun _ => c) x)
          ∂[ContinuousLinearMap.lsmul ℝ ℂ; μ] := by
        simpa [Function.comp_def] using congrArg (fun f : α → ℂ =>
          ∫ᵛ x, f x ∂[ContinuousLinearMap.lsmul ℝ ℂ; μ])
          (Set.indicator_comp_of_zero (s := s) (f := fun _ : α => c)
            (g := Complex.ofRealCLM) Complex.ofRealCLM.map_zero)
  · intro f k _ hf hk hfP hkP
    change (∫ᵛ x, f x + k x ∂[ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ); μ]) = _
    rw [VectorMeasure.integral_fun_add (μ := μ)
      (B := ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ)) hf hk]
    have hfunadd : (fun x => Complex.ofRealCLM ((f + k) x)) =
        (fun x => Complex.ofRealCLM (f x) + Complex.ofRealCLM (k x)) := by
      funext x
      simp [Pi.add_apply, map_add]
    rw [hfunadd]
    have hfC : μ.Integrable (fun x => Complex.ofRealCLM (f x)) := by
      exact hf.norm.mono'
        (Complex.ofRealCLM.continuous.comp_aestronglyMeasurable hf.aestronglyMeasurable)
        (by
          filter_upwards with x
          simp [Complex.norm_real, Real.norm_eq_abs])
    have hkC : μ.Integrable (fun x => Complex.ofRealCLM (k x)) := by
      exact hk.norm.mono'
        (Complex.ofRealCLM.continuous.comp_aestronglyMeasurable hk.aestronglyMeasurable)
        (by
          filter_upwards with x
          simp [Complex.norm_real, Real.norm_eq_abs])
    rw [VectorMeasure.integral_fun_add (μ := μ)
      (B := ContinuousLinearMap.lsmul ℝ ℂ) hfC hkC]
    rw [hfP, hkP]
  · apply isClosed_eq
    · exact MeasureTheory.VectorMeasure.continuous_integral
    · have hcont := (MeasureTheory.VectorMeasure.continuous_integral
        (μ := μ) (B := ContinuousLinearMap.lsmul ℝ ℂ)).comp
        (Complex.ofRealCLM.compLpL 1 μ.variation).continuous
      convert hcont using 1
      funext f
      apply VectorMeasure.integral_congr_ae
      exact (Complex.ofRealCLM.coeFn_compLpL f).symm
  · intro f k hfk hf hfP
    calc
      ∫ᵛ x, k x ∂[ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ); μ] =
          ∫ᵛ x, f x ∂[ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ); μ] :=
        VectorMeasure.integral_congr_ae (μ := μ)
          (B := ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ)) hfk.symm
      _ = ∫ᵛ x, (f x : ℂ) ∂[ContinuousLinearMap.lsmul ℝ ℂ; μ] := hfP
      _ = ∫ᵛ x, (k x : ℂ) ∂[ContinuousLinearMap.lsmul ℝ ℂ; μ] := by
        apply VectorMeasure.integral_congr_ae (μ := μ)
          (B := ContinuousLinearMap.lsmul ℝ ℂ)
        filter_upwards [hfk] with x hx
        exact congrArg Complex.ofReal hx

/-- The bounded operator obtained by integrating the `n`-th truncated spectral variable. -/
noncomputable def truncationIntegral (μS : WOTSpectralMeasure ℝ H) (n : ℕ) : H →WOT[ℂ] H :=
  boundedIntegral μS (truncationFunction n) (truncationFunction_measurable n)
    (truncationFunction_bounded n)

lemma truncationIntegral_sub_apply (μS : WOTSpectralMeasure ℝ H) (n m : ℕ) (x : H) :
    truncationIntegral μS n x - truncationIntegral μS m x =
      boundedIntegral μS (fun r => truncationFunction n r - truncationFunction m r)
        ((truncationFunction_measurable n).sub (truncationFunction_measurable m))
        (by
          rcases truncationFunction_bounded n with ⟨Cn, hCn⟩
          rcases truncationFunction_bounded m with ⟨Cm, hCm⟩
          refine ⟨Cn + Cm, fun r => ?_⟩
          exact (norm_sub_le _ _).trans (add_le_add (hCn r) (hCm r))) x := by
  change truncationIntegral μS n x - truncationIntegral μS m x =
    boundedIntegral μS (truncationFunction n - truncationFunction m) _ _ x
  exact (congrArg (fun A : H →WOT[ℂ] H => A x)
    (boundedIntegral_sub μS (truncationFunction_measurable n)
      (truncationFunction_measurable m) (truncationFunction_bounded n)
      (truncationFunction_bounded m))).symm

lemma diagonalMeasure_add_le (μS : WOTSpectralMeasure ℝ H) (x y : H) :
    μS.diagonalMeasure (x + y) ≤
      (μS.diagonalMeasure x + μS.diagonalMeasure x) +
        (μS.diagonalMeasure y + μS.diagonalMeasure y) := by
  refine (Measure.le_iff').2 (fun S => ?_)
  have h := congrArg (fun ν : Measure ℝ => ν S)
    (μS.diagonalMeasure_parallelogram x y)
  rw [Measure.add_apply, Measure.add_apply, Measure.add_apply, Measure.add_apply] at h
  calc
    μS.diagonalMeasure (x + y) S ≤
        μS.diagonalMeasure (x + y) S + μS.diagonalMeasure (x - y) S :=
      le_add_of_nonneg_right (by positivity)
    _ = ((μS.diagonalMeasure x + μS.diagonalMeasure x) +
        (μS.diagonalMeasure y + μS.diagonalMeasure y)) S := h

lemma spectralSquareMomentDomain_zero (μS : WOTSpectralMeasure ℝ H) :
    (0 : H) ∈ spectralSquareMomentDomain μS := by
  rw [mem_spectralSquareMomentDomain_iff]
  have hzero : (0 : H) = (0 : ℂ) • (0 : H) := by simp
  rw [hzero, μS.diagonalMeasure_smul]
  simpa [norm_zero, pow_two] using (integrable_zero_measure :
    Integrable (fun r : ℝ => r ^ 2) (0 : Measure ℝ))

lemma spectralSquareMomentDomain_add (μS : WOTSpectralMeasure ℝ H) {x y : H}
    (hx : x ∈ spectralSquareMomentDomain μS)
    (hy : y ∈ spectralSquareMomentDomain μS) :
    x + y ∈ spectralSquareMomentDomain μS := by
  rw [mem_spectralSquareMomentDomain_iff] at hx hy ⊢
  apply Integrable.mono_measure
    ((hx.add_measure hx).add_measure (hy.add_measure hy))
  exact diagonalMeasure_add_le μS x y

lemma spectralSquareMomentDomain_smul (μS : WOTSpectralMeasure ℝ H) (c : ℂ) {x : H}
    (hx : x ∈ spectralSquareMomentDomain μS) :
    c • x ∈ spectralSquareMomentDomain μS := by
  rw [mem_spectralSquareMomentDomain_iff, μS.diagonalMeasure_smul]
  apply Integrable.mono_measure (hx.smul_measure ENNReal.ofReal_ne_top)
  exact le_rfl

/-- The square-moment domain is a complex submodule, so the maximal spectral integral can be
defined as a `LinearPMap` rather than merely as a pointwise partial function. -/
def spectralSquareMomentSubmodule (μS : WOTSpectralMeasure ℝ H) : Submodule ℂ H where
  carrier := spectralSquareMomentDomain μS
  zero_mem' := spectralSquareMomentDomain_zero μS
  add_mem' := spectralSquareMomentDomain_add μS
  smul_mem' := spectralSquareMomentDomain_smul μS

lemma truncationIntegral_sub_norm_sq (μS : WOTSpectralMeasure ℝ H) (n m : ℕ) (x : H) :
    ENNReal.ofReal (‖truncationIntegral μS n x - truncationIntegral μS m x‖ ^ 2) =
      ∫⁻ r, ENNReal.ofReal
        (‖truncationFunction n r - truncationFunction m r‖ ^ 2)
        ∂μS.diagonalMeasure x := by
  rw [truncationIntegral_sub_apply]
  exact boundedIntegral_norm_sq μS
    ((truncationFunction_measurable n).sub (truncationFunction_measurable m))
        (by
      rcases truncationFunction_bounded n with ⟨Cn, hCn⟩
      rcases truncationFunction_bounded m with ⟨Cm, hCm⟩
      exact ⟨Cn + Cm, fun r =>
        (norm_sub_le _ _).trans (add_le_add (hCn r) (hCm r))⟩) x

lemma truncationIntegral_sub_norm_sq_le (μS : WOTSpectralMeasure ℝ H) (n m : ℕ) (x : H) :
    ENNReal.ofReal (‖truncationIntegral μS n x - truncationIntegral μS m x‖ ^ 2) ≤
      2 * (∫⁻ r, ENNReal.ofReal
        (‖truncationFunction n r - (r : ℂ)‖ ^ 2) ∂μS.diagonalMeasure x) +
        2 * (∫⁻ r, ENNReal.ofReal
          (‖truncationFunction m r - (r : ℂ)‖ ^ 2) ∂μS.diagonalMeasure x) := by
  let a : ℝ → ℝ := fun r => ‖truncationFunction n r - (r : ℂ)‖ ^ 2
  let b : ℝ → ℝ := fun r => ‖truncationFunction m r - (r : ℂ)‖ ^ 2
  have ha : Measurable a :=
    (((truncationFunction_measurable n).sub Complex.measurable_ofReal).norm.pow_const 2)
  have hb : Measurable b :=
    (((truncationFunction_measurable m).sub Complex.measurable_ofReal).norm.pow_const 2)
  have hpoint : ∀ r, ENNReal.ofReal
      (‖truncationFunction n r - truncationFunction m r‖ ^ 2) ≤
        ENNReal.ofReal (2 * a r + 2 * b r) := by
    intro r
    apply ENNReal.ofReal_le_ofReal
    have hnorm : ‖truncationFunction n r - truncationFunction m r‖ ≤
        ‖truncationFunction n r - (r : ℂ)‖ +
          ‖truncationFunction m r - (r : ℂ)‖ := by
      calc
        ‖truncationFunction n r - truncationFunction m r‖ =
            ‖(truncationFunction n r - (r : ℂ)) -
              (truncationFunction m r - (r : ℂ))‖ := by
                congr 1 <;> ring
        _ ≤ _ := norm_sub_le _ _
    dsimp [a, b]
    have hc : 0 ≤ ‖truncationFunction n r - truncationFunction m r‖ := norm_nonneg _
    have hab : 0 ≤ ‖truncationFunction n r - (r : ℂ)‖ +
        ‖truncationFunction m r - (r : ℂ)‖ := by positivity
    have hsquare := (sq_le_sq₀ hc hab).2 hnorm
    nlinarith [sq_nonneg
      (‖truncationFunction n r - (r : ℂ)‖ -
        ‖truncationFunction m r - (r : ℂ)‖)]
  calc
    ENNReal.ofReal (‖truncationIntegral μS n x - truncationIntegral μS m x‖ ^ 2) =
        ∫⁻ r, ENNReal.ofReal
          (‖truncationFunction n r - truncationFunction m r‖ ^ 2)
          ∂μS.diagonalMeasure x := truncationIntegral_sub_norm_sq μS n m x
    _ ≤ ∫⁻ r, ENNReal.ofReal (2 * a r + 2 * b r) ∂μS.diagonalMeasure x :=
      lintegral_mono hpoint
    _ = 2 * (∫⁻ r, ENNReal.ofReal (a r) ∂μS.diagonalMeasure x) +
        2 * (∫⁻ r, ENNReal.ofReal (b r) ∂μS.diagonalMeasure x) := by
      have hsplit : ∀ r, ENNReal.ofReal (2 * a r + 2 * b r) =
          2 * ENNReal.ofReal (a r) + 2 * ENNReal.ofReal (b r) := by
        intro r
        rw [ENNReal.ofReal_add (by positivity) (by positivity)]
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
        norm_num
      have hameas : Measurable (fun r => ENNReal.ofReal (a r)) :=
        ENNReal.continuous_ofReal.measurable.comp ha
      have hbmeas : Measurable (fun r => ENNReal.ofReal (b r)) :=
        ENNReal.continuous_ofReal.measurable.comp hb
      simp_rw [hsplit]
      rw [lintegral_add_left (by fun_prop), lintegral_const_mul 2 hameas,
        lintegral_const_mul 2 hbmeas]

lemma truncation_error_lintegral_tendsto_zero
    (μS : WOTSpectralMeasure ℝ H) (x : H)
    (hx : Integrable (fun r : ℝ => r ^ 2) (μS.diagonalMeasure x)) :
    Filter.Tendsto
      (fun n : ℕ => ∫⁻ r, ENNReal.ofReal
        (‖truncationFunction n r - (r : ℂ)‖ ^ 2) ∂μS.diagonalMeasure x)
      Filter.atTop (𝓝 0) := by
  let μ : Measure ℝ := μS.diagonalMeasure x
  let F : ℕ → ℝ → ENNReal := fun n r =>
    ENNReal.ofReal (‖truncationFunction n r - (r : ℂ)‖ ^ 2)
  have hFmeas : ∀ n, Measurable (F n) := by
    intro n
    change Measurable (fun r : ℝ => ENNReal.ofReal
      (‖truncationFunction n r - (r : ℂ)‖ ^ 2))
    exact ENNReal.continuous_ofReal.measurable.comp
      (((truncationFunction_measurable n).sub Complex.measurable_ofReal).norm.pow_const 2)
  have hbound : ∀ n, ∀ᵐ r ∂μ, F n r ≤ ENNReal.ofReal (4 * r ^ 2) := by
    intro n
    filter_upwards [] with r
    dsimp [F]
    apply ENNReal.ofReal_le_ofReal
    by_cases hr : r ∈ Set.Icc (-(n : ℝ)) (n : ℝ)
    · simp [truncationFunction, Set.indicator_of_mem hr]
      positivity
    · simp [truncationFunction, Set.indicator, hr]
      have hsq : ‖(r : ℂ)‖ ^ 2 ≤ 4 * r ^ 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        rw [sq_abs]
        nlinarith [sq_nonneg r]
      simpa [norm_neg] using hsq
  have hdom : Integrable (fun r : ℝ => 4 * r ^ 2) μ := by
    simpa only [smul_eq_mul] using hx.const_mul 4
  have hfin : (∫⁻ r, ENNReal.ofReal (4 * r ^ 2) ∂μ) ≠ (⊤ : ENNReal) := by
    exact (hdom.lintegral_lt_top).ne
  let F₀ : ℝ → ENNReal := fun _ => 0
  have hlim : ∀ᵐ r ∂μ, Filter.Tendsto (fun n : ℕ => F n r) Filter.atTop (𝓝 (F₀ r)) := by
    filter_upwards [] with r
    have htrunc := truncationFunction_tendsto r
    have hdiff : Filter.Tendsto
        (fun n : ℕ => truncationFunction n r - (r : ℂ)) Filter.atTop (𝓝 0) := by
      simpa using htrunc.sub (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℕ => (r : ℂ)) Filter.atTop (𝓝 (r : ℂ)))
    have hnorm : Filter.Tendsto
        (fun n : ℕ => ‖truncationFunction n r - (r : ℂ)‖ ^ 2)
          Filter.atTop (𝓝 (0 ^ 2)) := by
      simpa [Function.comp_def] using
        (continuous_norm.pow 2).continuousAt.tendsto.comp hdiff
    change Filter.Tendsto (fun n : ℕ => ENNReal.ofReal
      (‖truncationFunction n r - (r : ℂ)‖ ^ 2)) Filter.atTop (𝓝 (F₀ r))
    have hout := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hnorm
    simpa [F, F₀, Function.comp_def] using hout
  have hmain : Filter.Tendsto (fun n : ℕ => ∫⁻ r, F n r ∂μ) Filter.atTop
      (𝓝 (∫⁻ r, F₀ r ∂μ)) := by
    apply MeasureTheory.tendsto_lintegral_filter_of_dominated_convergence
      (fun r => ENNReal.ofReal (4 * r ^ 2))
    · filter_upwards [] with n
      exact hFmeas n
    · filter_upwards [] with n
      exact hbound n
    · exact hfin
    · exact hlim
  simpa [F, F₀, μ] using hmain

lemma truncationIntegral_cauchy (μS : WOTSpectralMeasure ℝ H) {x : H}
    (hx : x ∈ spectralSquareMomentDomain μS) :
    CauchySeq (fun n : ℕ => truncationIntegral μS n x) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  let A : ℕ → ENNReal := fun n => ∫⁻ r, ENNReal.ofReal
    (‖truncationFunction n r - (r : ℂ)‖ ^ 2) ∂μS.diagonalMeasure x
  have hA : Filter.Tendsto A Filter.atTop (𝓝 0) := by
    simpa [A] using truncation_error_lintegral_tendsto_zero μS x hx
  have hq : 0 < ε ^ 2 / 8 := by positivity
  have hsmall : ∀ᶠ n : ℕ in Filter.atTop, A n < ENNReal.ofReal (ε ^ 2 / 8) := by
    apply hA.eventually
    exact Iio_mem_nhds ((ENNReal.ofReal_pos).2 hq)
  rcases (Filter.eventually_atTop.1 hsmall) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn m hm
  have hnA := hN n hn
  have hmA := hN m hm
  have hsum : 2 * A n + 2 * A m < ENNReal.ofReal (ε ^ 2) := by
    calc
          2 * A n + 2 * A m <
          2 * ENNReal.ofReal (ε ^ 2 / 8) +
            2 * ENNReal.ofReal (ε ^ 2 / 8) := by
              gcongr <;> norm_num
      _ = ENNReal.ofReal (ε ^ 2 / 2) := by
        have htwo (q : ℝ) : (2 : ENNReal) * ENNReal.ofReal q =
            ENNReal.ofReal (2 * q) := by
          calc
            (2 : ENNReal) * ENNReal.ofReal q =
                ENNReal.ofReal 2 * ENNReal.ofReal q := by norm_num
            _ = ENNReal.ofReal (2 * q) :=
              (ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2)).symm
        calc
          2 * ENNReal.ofReal (ε ^ 2 / 8) +
              2 * ENNReal.ofReal (ε ^ 2 / 8) =
              ENNReal.ofReal (2 * (ε ^ 2 / 8)) +
                ENNReal.ofReal (2 * (ε ^ 2 / 8)) := by
                  congr 1
                  · exact htwo _
                  · exact htwo _
          _ = ENNReal.ofReal (2 * (ε ^ 2 / 8) + 2 * (ε ^ 2 / 8)) :=
            (ENNReal.ofReal_add (by positivity) (by positivity)).symm
          _ = ENNReal.ofReal (ε ^ 2 / 2) := by congr 1 <;> ring
      _ < ENNReal.ofReal (ε ^ 2) := by
        exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by nlinarith)
  have hnormsq : ENNReal.ofReal
      (‖truncationIntegral μS n x - truncationIntegral μS m x‖ ^ 2) <
        ENNReal.ofReal (ε ^ 2) :=
    (truncationIntegral_sub_norm_sq_le μS n m x).trans_lt hsum
  have hnormsq' : ‖truncationIntegral μS n x - truncationIntegral μS m x‖ ^ 2 < ε ^ 2 :=
    (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hnormsq
  have hnorm : ‖truncationIntegral μS n x - truncationIntegral μS m x‖ < ε :=
    (sq_lt_sq₀ (norm_nonneg _) (le_of_lt hε)).mp hnormsq'
  simpa [dist_eq_norm] using hnorm

lemma truncation_norm_lintegral_tendsto
    (μS : WOTSpectralMeasure ℝ H) (x : H)
    (hx : Integrable (fun r : ℝ => r ^ 2) (μS.diagonalMeasure x)) :
    Filter.Tendsto
      (fun n : ℕ => ∫⁻ r, ENNReal.ofReal
        (‖truncationFunction n r‖ ^ 2) ∂μS.diagonalMeasure x)
      Filter.atTop
      (𝓝 (∫⁻ r, ENNReal.ofReal (r ^ 2) ∂μS.diagonalMeasure x)) := by
  let μ : Measure ℝ := μS.diagonalMeasure x
  let F : ℕ → ℝ → ENNReal := fun n r =>
    ENNReal.ofReal (‖truncationFunction n r‖ ^ 2)
  let F₀ : ℝ → ENNReal := fun r => ENNReal.ofReal (r ^ 2)
  have hFmeas : ∀ n, Measurable (F n) := by
    intro n
    exact ENNReal.continuous_ofReal.measurable.comp
      ((truncationFunction_measurable n).norm.pow_const 2)
  have hbound : ∀ n, ∀ᵐ r ∂μ, F n r ≤ F₀ r := by
    intro n
    filter_upwards [] with r
    dsimp [F, F₀]
    apply ENNReal.ofReal_le_ofReal
    by_cases hr : r ∈ Set.Icc (-(n : ℝ)) (n : ℝ)
    · simp [truncationFunction, Set.indicator_of_mem hr, Complex.norm_real,
        Real.norm_eq_abs]
    · simp [truncationFunction, Set.indicator, hr]
      positivity
  have hfin : (∫⁻ r, F₀ r ∂μ) ≠ (⊤ : ENNReal) := by
    exact (hx.lintegral_lt_top).ne
  have hlim : ∀ᵐ r ∂μ, Filter.Tendsto (fun n : ℕ => F n r) Filter.atTop
      (𝓝 (F₀ r)) := by
    filter_upwards [] with r
    exact tendsto_nhds_of_eventually_eq (by
      filter_upwards [truncationFunction_eventually_eq r] with n hn
      have hnormsq : ‖(r : ℂ)‖ₑ ^ 2 = ENNReal.ofReal (r ^ 2) := by
        rw [← ofReal_norm_eq_enorm (r : ℂ), pow_two,
          ← ENNReal.ofReal_mul (norm_nonneg (r : ℂ))]
        simp [Complex.norm_real, Real.norm_eq_abs]
        congr 1
        ring
      simp [F, F₀, hn, hnormsq])
  have hmain : Filter.Tendsto (fun n : ℕ => ∫⁻ r, F n r ∂μ) Filter.atTop
      (𝓝 (∫⁻ r, F₀ r ∂μ)) := by
    apply MeasureTheory.tendsto_lintegral_filter_of_dominated_convergence
      (fun r => ENNReal.ofReal (r ^ 2))
    · filter_upwards [] with n
      exact hFmeas n
    · filter_upwards [] with n
      exact hbound n
    · exact hfin
    · exact hlim
  simpa [F, F₀, μ] using hmain

/-- The limit of the truncated spectral integrals, for `x` in the finite-second-moment domain. -/
noncomputable def truncationLimit (μS : WOTSpectralMeasure ℝ H)
    (x : spectralSquareMomentSubmodule μS) : H :=
  Filter.atTop.limUnder (fun n : ℕ => truncationIntegral μS n x)

lemma truncationLimit_tendsto (μS : WOTSpectralMeasure ℝ H)
    (x : spectralSquareMomentSubmodule μS) :
    Filter.Tendsto (fun n : ℕ => truncationIntegral μS n x) Filter.atTop
      (𝓝 (truncationLimit μS x)) := by
  exact (truncationIntegral_cauchy μS x.property).tendsto_limUnder

lemma truncationLimit_add (μS : WOTSpectralMeasure ℝ H)
    (x y : spectralSquareMomentSubmodule μS) :
    truncationLimit μS (x + y) = truncationLimit μS x + truncationLimit μS y := by
  have hxy := (truncationLimit_tendsto μS x).add (truncationLimit_tendsto μS y)
  exact tendsto_nhds_unique (truncationLimit_tendsto μS (x + y))
    (by
      convert hxy using 1
      funext n
      simpa using (ContinuousLinearMapWOT.toCLM (truncationIntegral μS n)).map_add
        (x : H) (y : H))

lemma truncationLimit_smul (μS : WOTSpectralMeasure ℝ H)
    (c : ℂ) (x : spectralSquareMomentSubmodule μS) :
    truncationLimit μS (c • x) = c • truncationLimit μS x := by
  have hcx := (truncationLimit_tendsto μS x).const_smul c
  exact tendsto_nhds_unique (truncationLimit_tendsto μS (c • x))
    (by
      convert hcx using 1
      funext n
      simpa using (ContinuousLinearMapWOT.toCLM (truncationIntegral μS n)).map_smul c
        (x : H))

lemma truncationIntegral_norm_sq (μS : WOTSpectralMeasure ℝ H) (n : ℕ) (x : H) :
    ENNReal.ofReal (‖truncationIntegral μS n x‖ ^ 2) =
      ∫⁻ r, ENNReal.ofReal (‖truncationFunction n r‖ ^ 2)
        ∂μS.diagonalMeasure x := by
  exact boundedIntegral_norm_sq μS (truncationFunction_measurable n)
    (truncationFunction_bounded n) x

lemma truncationIntegral_star (μS : WOTSpectralMeasure ℝ H) (n : ℕ) :
    star (truncationIntegral μS n) = truncationIntegral μS n := by
  rw [truncationIntegral]
  have h := boundedIntegral_star μS (truncationFunction_measurable n)
    (truncationFunction_bounded n)
  symm
  calc
    boundedIntegral μS (truncationFunction n) (truncationFunction_measurable n)
        (truncationFunction_bounded n) =
        boundedIntegral μS (fun r => star (truncationFunction n r)) _ _ := by
      congr 1
      funext r
      by_cases hr : r ∈ Set.Icc (-(n : ℝ)) (n : ℝ)
      · simp [truncationFunction, Set.indicator_of_mem hr]
      · simp [truncationFunction, Set.indicator, hr]
    _ = star (boundedIntegral μS (truncationFunction n)
        (truncationFunction_measurable n) (truncationFunction_bounded n)) := h

lemma truncationIntegral_inner_swap (μS : WOTSpectralMeasure ℝ H) (n : ℕ)
    (x y : H) :
    ⟪truncationIntegral μS n x, y⟫_ℂ = ⟪x, truncationIntegral μS n y⟫_ℂ := by
  have hstar := congrArg (fun A : H →WOT[ℂ] H => A y) (truncationIntegral_star μS n)
  rw [ContinuousLinearMapWOT.star_apply] at hstar
  exact (ContinuousLinearMap.adjoint_inner_right
    (ContinuousLinearMapWOT.toCLM (truncationIntegral μS n)) x y).symm.trans
    (by rw [← ContinuousLinearMap.star_eq_adjoint, hstar])

/-- The maximal operator obtained from a real weak spectral measure by norm convergence of bounded
truncations.  Its domain is exactly the square-moment submodule. -/
noncomputable def maximalSpectralIntegral
    (μS : WOTSpectralMeasure ℝ H) : H →ₗ.[ℂ] H :=
  LinearPMap.mk (spectralSquareMomentSubmodule μS)
    { toFun := truncationLimit μS
      map_add' := truncationLimit_add μS
      map_smul' := truncationLimit_smul μS }

lemma maximalSpectralIntegral_isSymmetric (μS : WOTSpectralMeasure ℝ H) :
    (maximalSpectralIntegral μS).IsSymmetric := by
  change (maximalSpectralIntegral μS).IsFormalAdjoint (maximalSpectralIntegral μS)
  intro x y
  have htx : Filter.Tendsto (fun n : ℕ => truncationIntegral μS n x) Filter.atTop
      (𝓝 (truncationLimit μS x)) := truncationLimit_tendsto μS x
  have hty : Filter.Tendsto (fun n : ℕ => truncationIntegral μS n y) Filter.atTop
      (𝓝 (truncationLimit μS y)) := truncationLimit_tendsto μS y
  have hxy := Filter.Tendsto.inner (𝕜 := ℂ) htx
    (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (y : H)) Filter.atTop
      (𝓝 (y : H)))
  have hyx := Filter.Tendsto.inner (𝕜 := ℂ)
    (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (x : H)) Filter.atTop
      (𝓝 (x : H))) hty
  have hseq : (fun n : ℕ => ⟪truncationIntegral μS n (x : H), (y : H)⟫_ℂ) =
      (fun n : ℕ => ⟪(x : H), truncationIntegral μS n (y : H)⟫_ℂ) := by
    funext n
    exact truncationIntegral_inner_swap μS n (x : H) (y : H)
  have hyx' := hyx
  rw [← hseq] at hyx'
  exact tendsto_nhds_unique hxy hyx'
@[nolint unusedArguments]

lemma spectralCutoff_mem_spectralSquareMomentDomain
    (μS : WOTSpectralMeasure ℝ H) (x : H) {C : ℝ} (hC : 0 ≤ C) :
    μS (Set.Icc (-C) C) x ∈ spectralSquareMomentDomain μS := by
  let K : Set ℝ := Set.Icc (-C) C
  have hK : MeasurableSet K := measurableSet_Icc
  have hKc : MeasurableSet Kᶜ := hK.compl
  have hzero : μS Kᶜ (μS K x) = 0 := by
    have hmul : μS Kᶜ * μS K = 0 :=
      μS.comp_of_disjoint disjoint_compl_left hKc hK
    exact congrArg (fun A : H →WOT[ℂ] H => A x) hmul
  have hdiagKc : μS.diagonalMeasure (μS K x) Kᶜ = 0 := by
    rw [μS.diagonalMeasure_apply_eq_norm_sq _ _ hKc, hzero]
    simp
  rw [mem_spectralSquareMomentDomain_iff]
  have hK_ae : ∀ᵐ r ∂μS.diagonalMeasure (μS K x), r ∈ K := by
    rw [ae_iff]
    have hset : {r : ℝ | r ∉ K} = Kᶜ := by rfl
    rw [hset]
    exact hdiagKc
  apply Integrable.of_bound (by fun_prop) (C ^ 2)
  filter_upwards [hK_ae] with r hr
  change |r ^ 2| ≤ C ^ 2
  rw [abs_of_nonneg (sq_nonneg r)]
  exact sq_le_sq' hr.1 hr.2

lemma diagonalMeasure_cutoff_compl_tendsto_zero
    (μS : WOTSpectralMeasure ℝ H) (x : H) :
    Filter.Tendsto
      (fun n : ℕ => μS.diagonalMeasure x (spectralCutoffSet n)ᶜ)
      Filter.atTop (𝓝 0) := by
  have hμ := MeasureTheory.tendsto_measure_iUnion_atTop
    (μ := μS.diagonalMeasure x) spectralCutoffSet_mono
  have hμ' : Filter.Tendsto
      (fun n : ℕ => μS.diagonalMeasure x (spectralCutoffSet n)) Filter.atTop
      (𝓝 (μS.diagonalMeasure x Set.univ)) := by
    simpa [Function.comp_def, spectralCutoffSet_iUnion] using hμ
  have hcomp : ∀ n, μS.diagonalMeasure x (spectralCutoffSet n)ᶜ =
      μS.diagonalMeasure x Set.univ - μS.diagonalMeasure x (spectralCutoffSet n) := by
    intro n
    exact MeasureTheory.measure_compl measurableSet_Icc
      (measure_lt_top (μS.diagonalMeasure x) (spectralCutoffSet n)).ne
  have hpair : Filter.Tendsto
      (fun n : ℕ => (μS.diagonalMeasure x Set.univ,
        μS.diagonalMeasure x (spectralCutoffSet n))) Filter.atTop
      (𝓝 (μS.diagonalMeasure x Set.univ, μS.diagonalMeasure x Set.univ)) := by
    exact tendsto_const_nhds.prodMk_nhds hμ'
  have hsub' := (ENNReal.tendsto_sub
      (Or.inl (μS.diagonalMeasure_isFinite x).measure_univ_lt_top.ne)).comp hpair
  simpa [Function.comp_def, hcomp] using hsub'

lemma spectralCutoff_tendsto (μS : WOTSpectralMeasure ℝ H) (x : H) :
    Filter.Tendsto
      (fun n : ℕ => μS (spectralCutoffSet n) x) Filter.atTop (𝓝 x) := by
  apply (Metric.tendsto_atTop.2)
  intro ε hε
  have htail := (diagonalMeasure_cutoff_compl_tendsto_zero μS x).eventually
    (Iio_mem_nhds ((ENNReal.ofReal_pos).2 (sq_pos_of_pos hε)))
  rcases Filter.eventually_atTop.1 htail with ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  have hdecomp : μS (spectralCutoffSet n) x +
      μS (spectralCutoffSet n)ᶜ x = x := by
    have h := congrArg (fun A : H →WOT[ℂ] H => A x)
      (MeasureTheory.VectorMeasure.of_union
        (v := μS.toVectorMeasure) (A := spectralCutoffSet n)
          (B := (spectralCutoffSet n)ᶜ) disjoint_compl_right measurableSet_Icc
          measurableSet_Icc.compl)
    simpa [Set.union_compl_self, μS.univ] using h.symm
  have hdiff : x - μS (spectralCutoffSet n) x =
      μS (spectralCutoffSet n)ᶜ x := by
    calc
      x - μS (spectralCutoffSet n) x =
          (μS (spectralCutoffSet n) x + μS (spectralCutoffSet n)ᶜ x) -
            μS (spectralCutoffSet n) x := by rw [hdecomp]
      _ = μS (spectralCutoffSet n)ᶜ x := by abel
  have hnormsq : ENNReal.ofReal
      (‖x - μS (spectralCutoffSet n) x‖ ^ 2) =
      μS.diagonalMeasure x (spectralCutoffSet n)ᶜ := by
    rw [hdiff]
    exact (μS.diagonalMeasure_apply_eq_norm_sq x (spectralCutoffSet n)ᶜ
      measurableSet_Icc.compl).symm
  have hlt : ENNReal.ofReal
      (‖x - μS (spectralCutoffSet n) x‖ ^ 2) < ENNReal.ofReal (ε ^ 2) := by
    rw [hnormsq]
    exact hN n hn
  have hsq : ‖x - μS (spectralCutoffSet n) x‖ ^ 2 < ε ^ 2 :=
    (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hlt
  simpa [dist_eq_norm, norm_sub_rev] using
    (sq_lt_sq₀ (norm_nonneg _) (le_of_lt hε)).mp hsq

lemma maximalSpectralIntegral_hasDenseDomain (μS : WOTSpectralMeasure ℝ H) :
    (maximalSpectralIntegral μS).HasDenseDomain := by
  rw [LinearPMap.hasDenseDomain_def, Metric.dense_iff]
  intro x ε hε
  rcases (Metric.tendsto_atTop.1 (spectralCutoff_tendsto μS x) ε hε) with ⟨N, hN⟩
  let z := μS (spectralCutoffSet N) x
  refine ⟨z, hN N le_rfl, ?_⟩
  exact spectralCutoff_mem_spectralSquareMomentDomain μS x
    (by positivity)

lemma maximalSpectralIntegral_isClosable (μS : WOTSpectralMeasure ℝ H) :
    (maximalSpectralIntegral μS).IsClosable := by
  apply LinearPMap.isClosable_of_exists_dense_formalAdjoint
    (maximalSpectralIntegral_hasDenseDomain μS)
  exact ⟨maximalSpectralIntegral μS,
    maximalSpectralIntegral_hasDenseDomain μS,
    LinearPMap.isSymmetric_def.mp (maximalSpectralIntegral_isSymmetric μS)⟩

lemma maximalSpectralIntegral_isUnbounded (μS : WOTSpectralMeasure ℝ H) :
    (maximalSpectralIntegral μS).IsUnbounded :=
  ⟨maximalSpectralIntegral_hasDenseDomain μS,
    maximalSpectralIntegral_isClosable μS⟩

lemma maximalSpectralIntegral_closure_isClosed (μS : WOTSpectralMeasure ℝ H) :
    (maximalSpectralIntegral μS).closure.IsClosed :=
  (maximalSpectralIntegral_isClosable μS).closure_isClosed

lemma maximalSpectralIntegral_closure_isSymmetric (μS : WOTSpectralMeasure ℝ H) :
    (maximalSpectralIntegral μS).closure.IsSymmetric :=
  (maximalSpectralIntegral_isSymmetric μS).closure
    (maximalSpectralIntegral_hasDenseDomain μS)

lemma maximalSpectralIntegral_isEssentiallySelfAdjoint_iff (μS : WOTSpectralMeasure ℝ H) :
    (maximalSpectralIntegral μS).IsEssentiallySelfAdjoint ↔
      IsSelfAdjoint (maximalSpectralIntegral μS).closure := Iff.rfl

/-- The Cayley/resolvent endpoint for the canonical PVM realization.

The measure-theoretic construction supplies symmetry and density.  Once a concrete argument proves
that both shifted operators have full range, the standard von Neumann range criterion turns the
canonical realization itself into a self-adjoint operator.  This is the reusable interface for
ODE, Nelson, and multiplication-model proofs of essential self-adjointness. -/
lemma maximalSpectralIntegral_isSelfAdjoint_of_range_eq_top
    (μS : WOTSpectralMeasure ℝ H)
    (hadd : (maximalSpectralIntegral μS + Complex.I • (1 : H →ₗ.[ℂ] H)).toFun.range = ⊤)
    (hsub : (maximalSpectralIntegral μS - Complex.I • (1 : H →ₗ.[ℂ] H)).toFun.range = ⊤) :
    IsSelfAdjoint (maximalSpectralIntegral μS) := by
  exact LinearPMap.IsSymmetric.isSelfAdjoint_of_range_eq_top
    (maximalSpectralIntegral_isSymmetric μS)
    (maximalSpectralIntegral_hasDenseDomain μS) hadd hsub

/-- The closure of the canonical PVM realization is self-adjoint under the same resolvent
surjectivity hypotheses.  The stronger conclusion is exposed separately because downstream
models usually start with an operator on a smaller core and identify its closure with this
canonical realization. -/
lemma maximalSpectralIntegral_closure_eq_self
    (μS : WOTSpectralMeasure ℝ H)
    (hadd : (maximalSpectralIntegral μS + Complex.I • (1 : H →ₗ.[ℂ] H)).toFun.range = ⊤)
    (hsub : (maximalSpectralIntegral μS - Complex.I • (1 : H →ₗ.[ℂ] H)).toFun.range = ⊤) :
    (maximalSpectralIntegral μS).closure = maximalSpectralIntegral μS := by
  have hself := maximalSpectralIntegral_isSelfAdjoint_of_range_eq_top μS hadd hsub
  exact hself.isClosed.closure_eq

lemma maximalSpectralIntegral_isEssentiallySelfAdjoint_of_range_eq_top
    (μS : WOTSpectralMeasure ℝ H)
    (hadd : (maximalSpectralIntegral μS + Complex.I • (1 : H →ₗ.[ℂ] H)).toFun.range = ⊤)
    (hsub : (maximalSpectralIntegral μS - Complex.I • (1 : H →ₗ.[ℂ] H)).toFun.range = ⊤) :
    (maximalSpectralIntegral μS).IsEssentiallySelfAdjoint := by
  rw [maximalSpectralIntegral_isEssentiallySelfAdjoint_iff]
  rw [maximalSpectralIntegral_closure_eq_self μS hadd hsub]
  exact maximalSpectralIntegral_isSelfAdjoint_of_range_eq_top μS hadd hsub

lemma maximalSpectralIntegral_norm_sq (μS : WOTSpectralMeasure ℝ H)
    (x : H) (hx : x ∈ (maximalSpectralIntegral μS).domain) :
    ENNReal.ofReal (‖(maximalSpectralIntegral μS) ⟨x, hx⟩‖ ^ 2) =
      ∫⁻ r, ENNReal.ofReal (r ^ 2) ∂μS.diagonalMeasure x := by
  let xd : spectralSquareMomentSubmodule μS := ⟨x, hx⟩
  have hvec := truncationLimit_tendsto μS xd
  have hnorm : Filter.Tendsto
      (fun n : ℕ => ENNReal.ofReal (‖truncationIntegral μS n x‖ ^ 2))
      Filter.atTop (𝓝 (ENNReal.ofReal (‖truncationLimit μS xd‖ ^ 2))) := by
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((continuous_norm.pow 2).continuousAt.tendsto.comp hvec)
  have hleft : Filter.Tendsto
      (fun n : ℕ => ENNReal.ofReal (‖truncationIntegral μS n x‖ ^ 2))
      Filter.atTop (𝓝 (∫⁻ r, ENNReal.ofReal (r ^ 2) ∂μS.diagonalMeasure x)) := by
    convert truncation_norm_lintegral_tendsto μS x xd.property using 1
    funext n
    exact truncationIntegral_norm_sq μS n x
  have heq := tendsto_nhds_unique hnorm hleft
  simpa [maximalSpectralIntegral, xd] using heq

@[simp] lemma maximalSpectralIntegral_domain (μS : WOTSpectralMeasure ℝ H) :
    (maximalSpectralIntegral μS).domain = spectralSquareMomentSubmodule μS := rfl

lemma maximalSpectralIntegral_apply (μS : WOTSpectralMeasure ℝ H)
    (x : H) (hx : x ∈ (maximalSpectralIntegral μS).domain) :
    (maximalSpectralIntegral μS) ⟨x, hx⟩ = truncationLimit μS ⟨x, hx⟩ := rfl
@[nolint unusedArguments]

lemma scalarMeasure_inner_projection (μS : WOTSpectralMeasure ℝ H)
    (x y : H) (S : Set ℝ) (hS : MeasurableSet S) :
    ⟪y, μS S x⟫_ℂ = ⟪μS S y, μS S x⟫_ℂ := by
  let p : H →L[ℂ] H := ContinuousLinearMapWOT.toCLM (μS S)
  have hmul : p * p = p := by
    exact congrArg ContinuousLinearMapWOT.toCLM (μS.isStarProjection S).isIdempotentElem
  have hstar : ContinuousLinearMap.adjoint p = p := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact congrArg ContinuousLinearMapWOT.toCLM (μS.isStarProjection S).isSelfAdjoint
  change ⟪y, p x⟫_ℂ = ⟪p y, p x⟫_ℂ
  calc
    ⟪y, p x⟫_ℂ = ⟪ContinuousLinearMap.adjoint p y, x⟫_ℂ :=
      (ContinuousLinearMap.adjoint_inner_left p x y).symm
    _ = ⟪p y, x⟫_ℂ := by rw [hstar]
    _ = ⟪p y, p x⟫_ℂ := by
      have h := ContinuousLinearMap.adjoint_inner_right p (p y) x
      rw [hstar] at h
      have hpy : p (p y) = p y := by
        exact congrArg (fun q : H →L[ℂ] H => q y) hmul
      rw [hpy] at h
      exact h.symm

lemma scalarMeasure_variation_le_diagonal_add (μS : WOTSpectralMeasure ℝ H)
    (x y : H) :
    (μS.scalarMeasure x y).variation ≤ μS.diagonalMeasure x + μS.diagonalMeasure y := by
  apply MeasureTheory.VectorMeasure.variation_le_of_forall_enorm_le
  intro S hS
  rw [μS.scalarMeasure_apply x y S]
  rw [← ofReal_norm]
  rw [MeasureTheory.Measure.add_apply _ _ S, μS.diagonalMeasure_apply_eq_norm_sq x S hS,
    μS.diagonalMeasure_apply_eq_norm_sq y S hS]
  rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hinner := norm_inner_le_norm (𝕜 := ℂ) (μS S y) (μS S x)
  have hproj := scalarMeasure_inner_projection μS x y S hS
  rw [hproj]
  nlinarith [sq_nonneg ‖μS S y‖, sq_nonneg ‖μS S x‖]

lemma scalarMeasure_isFiniteVariation (μS : WOTSpectralMeasure ℝ H)
    (x y : H) : IsFiniteMeasure (μS.scalarMeasure x y).variation := by
  apply MeasureTheory.isFiniteMeasure_of_le
    (μS.diagonalMeasure x + μS.diagonalMeasure y)
  exact scalarMeasure_variation_le_diagonal_add μS x y

lemma truncationIntegral_inner_tendsto_weakIntegral
    (μS : WOTSpectralMeasure ℝ H) (x y : H)
    (hfi : (μS.scalarMeasure x y).Integrable id) :
    Filter.Tendsto
      (fun n : ℕ => ∫ᵛ r, realTruncationFunction n r ∂[
        ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ); μS.scalarMeasure x y])
      Filter.atTop (𝓝 (μS.weakIntegral id x y)) := by
  let ν := μS.scalarMeasure x y
  letI := scalarMeasure_isFiniteVariation μS x y
  have hlimit : μS.complexWeakIntegral (fun r : ℝ => (r : ℂ)) x y =
      μS.weakIntegral id x y := by
    unfold WOTSpectralMeasure.complexWeakIntegral WOTSpectralMeasure.weakIntegral
    exact (integral_real_eq_complex ν hfi).symm
  have hcomplex := truncationIntegral_inner_tendsto_complexWeakIntegral μS x y hfi
  rw [hlimit] at hcomplex
  apply hcomplex.congr'
  filter_upwards [] with n
  have htrunc : ν.Integrable (realTruncationFunction n) := by
    rcases realTruncationFunction_bounded n with ⟨C, hC⟩
    apply Integrable.of_bound
      (realTruncationFunction_measurable n).aestronglyMeasurable C
    filter_upwards [] with r
    simpa [Real.norm_eq_abs] using hC r
  have hreal := integral_real_eq_complex ν htrunc
  calc
    ∫ᵛ r, truncationFunction n r ∂[
        ContinuousLinearMap.lsmul ℝ ℂ; ν] =
        ∫ᵛ r, Complex.ofRealCLM (realTruncationFunction n r) ∂[
          ContinuousLinearMap.lsmul ℝ ℂ; ν] := by
      have hfun : (fun r => truncationFunction n r) =
          (fun r => Complex.ofRealCLM (realTruncationFunction n r)) := by
        funext r
        simpa [Complex.ofRealCLM_apply] using
          congrFun (realTruncationFunction_complex_eq n).symm r
      exact congrArg (fun f : ℝ → ℂ =>
        ∫ᵛ r, f r ∂[ContinuousLinearMap.lsmul ℝ ℂ; ν]) hfun
    _ = ∫ᵛ r, realTruncationFunction n r ∂[
        ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ); ν] := hreal.symm

lemma boundedIntegral_inner
    {α : Type*} [MeasurableSpace α] [Nonempty α]
    (μS : WOTSpectralMeasure α H) {f : α → ℂ} (hf : Measurable f)
    (hfb : ∃ C : ℝ, ∀ a, ‖f a‖ ≤ C) (x y : H)
    (hfinite : IsFiniteMeasure (μS.scalarMeasure x y).variation) :
    ⟪y, boundedIntegral μS f hf hfb x⟫_ℂ =
      ∫ᵛ a, f a ∂[ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ);
        μS.scalarMeasure x y] := by
  let s : ℕ → SimpleFunc α ℂ :=
    Classical.choose (exists_uniform_simple_approx hf hfb)
  have hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ a, ‖s n a - f a‖ < ε :=
    (Classical.choose_spec (exists_uniform_simple_approx hf hfb)).1
  have hsBound : ∃ C : ℝ, ∀ n a, ‖s n a‖ ≤ C :=
    (Classical.choose_spec (exists_uniform_simple_approx hf hfb)).2
  rw [boundedIntegral_eq_of_uniform_approx μS hf hfb hs]
  exact boundedIntegralOfUniformApprox_inner μS hs hsBound x y hfinite

lemma truncationIntegral_inner (μS : WOTSpectralMeasure ℝ H) (n : ℕ)
    (x y : H) :
    ⟪y, truncationIntegral μS n x⟫_ℂ =
      ∫ᵛ r, truncationFunction n r ∂[ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ);
        μS.scalarMeasure x y] := by
  exact boundedIntegral_inner μS (truncationFunction_measurable n)
    (truncationFunction_bounded n) x y (scalarMeasure_isFiniteVariation μS x y)

lemma maximalSpectralIntegral_weak_truncation_reconstruction
    (μS : WOTSpectralMeasure ℝ H) (x : H)
    (hx : x ∈ (maximalSpectralIntegral μS).domain) (y : H) :
    Filter.Tendsto
      (fun n : ℕ => ∫ᵛ r, truncationFunction n r ∂[
        ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); μS.scalarMeasure x y])
      Filter.atTop (𝓝 (⟪y, (maximalSpectralIntegral μS) ⟨x, hx⟩⟫_ℂ)) := by
  have hvec := truncationLimit_tendsto μS
    (⟨x, hx⟩ : spectralSquareMomentSubmodule μS)
  have hinner := Filter.Tendsto.inner (𝕜 := ℂ)
    (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (y : H)) Filter.atTop (𝓝 y)) hvec
  have hinner' : Filter.Tendsto
      (fun n : ℕ => ⟪y, truncationIntegral μS n x⟫_ℂ) Filter.atTop
      (𝓝 (⟪y, (maximalSpectralIntegral μS) ⟨x, hx⟩⟫_ℂ)) := by
    simpa [maximalSpectralIntegral, truncationLimit] using hinner
  apply hinner'.congr'
  filter_upwards [] with n
  exact truncationIntegral_inner μS n x y

/-! ### Measurable real functional calculus

The maximal construction is not tied to the coordinate function.  For a measurable real
multiplier `f`, push the PVM forward along `f` and apply the same construction to the new
spectral variable.  This is the concrete operator realization of the representation-free
`PVM.map` operation used by the affiliated-observable API. -/

/-- The maximal unbounded operator obtained by integrating a measurable real function against a
weak spectral measure.  It is defined by PVM pushforward, so no second truncation construction is
needed for each multiplier. -/
noncomputable def measurableSpectralIntegral (μS : WOTSpectralMeasure ℝ H)
    (f : ℝ → ℝ) (hf : Measurable f) : H →ₗ.[ℂ] H :=
  maximalSpectralIntegral (μS.map f hf)

@[simp]
theorem measurableSpectralIntegral_id (μS : WOTSpectralMeasure ℝ H) :
    measurableSpectralIntegral μS id measurable_id = maximalSpectralIntegral μS := by
  unfold measurableSpectralIntegral
  rw [μS.map_id]

lemma measurableSpectralIntegral_comp
    (μS : WOTSpectralMeasure ℝ H) (f g : ℝ → ℝ)
    (hf : Measurable f) (hg : Measurable g) :
    measurableSpectralIntegral (μS.map f hf) g hg =
      measurableSpectralIntegral μS (g ∘ f) (hg.comp hf) := by
  change maximalSpectralIntegral ((μS.map f hf).map g hg) =
    maximalSpectralIntegral (μS.map (g ∘ f) (hg.comp hf))
  apply congrArg maximalSpectralIntegral
  exact WOTSpectralMeasure.map_map (μS := μS) (f := f) (g := g) hf hg

@[simp]
lemma measurableSpectralIntegral_domain (μS : WOTSpectralMeasure ℝ H)
    (f : ℝ → ℝ) (hf : Measurable f) :
    (measurableSpectralIntegral μS f hf).domain =
      spectralSquareMomentSubmodule (μS.map f hf) := by
  rfl

/-- The domain of `∫ f dE` is exactly the square-integrability domain of `f` against every
vector-state spectral measure. -/
lemma mem_measurableSpectralIntegral_domain_iff (μS : WOTSpectralMeasure ℝ H)
    (f : ℝ → ℝ) (hf : Measurable f) (x : H) :
    x ∈ (measurableSpectralIntegral μS f hf).domain ↔
      Integrable (fun r : ℝ => f r ^ 2) (μS.diagonalMeasure x) := by
  change x ∈ spectralSquareMomentDomain (μS.map f hf) ↔ _
  rw [mem_spectralSquareMomentDomain_iff,
    μS.diagonalMeasure_map f hf]
  have h := integrable_map_measure (μ := μS.diagonalMeasure x)
    ((measurable_id.pow_const 2).aestronglyMeasurable) hf.aemeasurable
  simpa [Function.comp_def] using h

/-- A bounded measurable real multiplier has no unbounded domain restriction.  This is the
bounded-to-unbounded boundary in the reusable calculus: the same pushforward construction handles
both cases, and boundedness turns its square-moment domain into `⊤`. -/
lemma measurableSpectralIntegral_domain_eq_top_of_bounded
    (μS : WOTSpectralMeasure ℝ H) (f : ℝ → ℝ) (hf : Measurable f)
    (hfb : ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, |f r| ≤ C) :
    (measurableSpectralIntegral μS f hf).domain = ⊤ := by
  apply Submodule.eq_top_iff'.2
  intro x
  rw [mem_measurableSpectralIntegral_domain_iff μS f hf x]
  rcases hfb with ⟨C, hC, hfb⟩
  apply Integrable.of_bound (hf.pow_const 2).aestronglyMeasurable (C ^ 2)
  filter_upwards [] with r
  simpa [Real.norm_eq_abs, abs_pow] using
    (sq_le_sq₀ (abs_nonneg (f r)) hC).2 (hfb r)

/-- Weak reconstruction for a measurable real multiplier.  The only integrability assumption is
the natural one on the original scalar spectral measure; the pushforward identity transports it
to the coordinate function of the new PVM. -/
lemma measurableSpectralIntegral_inner_eq_complexWeakIntegral
    (μS : WOTSpectralMeasure ℝ H) (f : ℝ → ℝ) (hf : Measurable f)
    (x : H) (hx : x ∈ (measurableSpectralIntegral μS f hf).domain) (y : H)
    (hfi : (μS.scalarMeasure x y).Integrable f) :
    ⟪y, (measurableSpectralIntegral μS f hf) ⟨x, hx⟩⟫_ℂ =
      μS.complexWeakIntegral (fun r : ℝ => (f r : ℂ)) x y := by
  have hfi' : ((μS.map f hf).scalarMeasure x y).Integrable id := by
    rw [μS.scalarMeasure_map f hf]
    have h := VectorMeasure.Integrable.map
      (measurable_id.aestronglyMeasurable) hfi
    simpa [Function.comp_def] using h
  have hmax := maximalSpectralIntegral_weak_truncation_reconstruction
    (μS.map f hf) x hx y
  have hlim := truncationIntegral_inner_tendsto_complexWeakIntegral
    (μS.map f hf) x y hfi'
  have hinner :
      ⟪y, (maximalSpectralIntegral (μS.map f hf)) ⟨x, hx⟩⟫_ℂ =
        (μS.map f hf).complexWeakIntegral (fun r : ℝ => (r : ℂ)) x y :=
    tendsto_nhds_unique hmax hlim
  have hfiC : (μS.scalarMeasure x y).Integrable (fun r : ℝ => (f r : ℂ)) := by
    exact hfi.ofReal
  have hmap := μS.complexWeakIntegral_map f hf
    (fun r : ℝ => (r : ℂ)) x y
    Complex.measurable_ofReal.aestronglyMeasurable hfiC
  simpa [measurableSpectralIntegral, Function.comp_def] using hinner.trans hmap

/-- On bounded real multipliers, the bounded WOT integral and the maximal unbounded
realization are the same operator.  This is the concrete bridge between the bounded Borel
calculus and the square-moment construction; the proof is by matrix coefficients, using the
bounded integral's weak integral formula and the measurable multiplier reconstruction theorem. -/
theorem boundedIntegral_ofReal_eq_measurableSpectralIntegral
    (μS : WOTSpectralMeasure ℝ H) (f : ℝ → ℝ) (hf : Measurable f)
    (hfb : ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, |f r| ≤ C) (x : H) :
    boundedIntegral μS (fun r : ℝ => (f r : ℂ))
        (Complex.measurable_ofReal.comp hf)
        (by
          rcases hfb with ⟨C, hC, hCbound⟩
          exact ⟨C, fun r => by
            simpa [Complex.norm_real, Real.norm_eq_abs] using hCbound r⟩) x =
      (measurableSpectralIntegral μS f hf)
        ⟨x, by
          rw [measurableSpectralIntegral_domain_eq_top_of_bounded μS f hf hfb]
          exact Submodule.mem_top⟩ := by
  apply ext_inner_left ℂ
  intro y
  letI : IsFiniteMeasure (μS.scalarMeasure x y).variation :=
    scalarMeasure_isFiniteVariation μS x y
  have hfi : (μS.scalarMeasure x y).Integrable f := by
    rcases hfb with ⟨C, hC, hCbound⟩
    have hnorm : ∀ r : ℝ, ‖f r‖ ≤ C := by
      intro r
      simpa [Real.norm_eq_abs] using hCbound r
    apply Integrable.of_bound hf.aestronglyMeasurable C
    exact Filter.Eventually.of_forall hnorm
  have hbounded := boundedIntegral_inner μS
    (Complex.measurable_ofReal.comp hf)
    (by
      rcases hfb with ⟨C, hC, hCbound⟩
      exact ⟨C, fun r => by
        simpa [Complex.norm_real, Real.norm_eq_abs] using hCbound r⟩) x y
      (scalarMeasure_isFiniteVariation μS x y)
  have hunbounded := measurableSpectralIntegral_inner_eq_complexWeakIntegral μS f hf x
    (by
      rw [measurableSpectralIntegral_domain_eq_top_of_bounded μS f hf hfb]
      exact Submodule.mem_top) y hfi
  exact hbounded.trans hunbounded.symm

/-! ### Convergence of bounded spectral multipliers

The next lemma is the reusable norm-convergence principle behind the resolvent construction.  It
only uses the PVM norm-square identity, so it is also useful for bounded functional calculus
approximations unrelated to the Cayley transform.
-/

lemma boundedIntegral_tendsto_of_pointwise_tendsto_of_bound
    {α : Type*} [MeasurableSpace α] [Nonempty α]
    (μS : WOTSpectralMeasure α H)
    {f : α → ℂ} {g : ℕ → α → ℂ} (x : H)
    (hf : Measurable f) (hg : ∀ n, Measurable (g n))
    (hfb : ∃ C : ℝ, ∀ a, ‖f a‖ ≤ C)
    (hgb : ∃ C : ℝ, ∀ n a, ‖g n a‖ ≤ C)
    (hlim : ∀ a, Filter.Tendsto (fun n => g n a) Filter.atTop (𝓝 (f a))) :
    Filter.Tendsto
      (fun n => boundedIntegral μS (g n) (hg n) (by
        rcases hgb with ⟨C, hC⟩
        exact ⟨C, hC n⟩) x)
      Filter.atTop
      (𝓝 (boundedIntegral μS f hf hfb x)) := by
  have hfb_keep := hfb
  rcases hfb with ⟨Cf, hCf⟩
  rcases hgb with ⟨Cg, hCg⟩
  let C : ℝ := max Cf Cg
  have hC0 : 0 ≤ C := by
    let a₀ : α := Classical.choice (inferInstance : Nonempty α)
    exact (norm_nonneg (f a₀)).trans ((hCf a₀).trans (le_max_left _ _))
  have hCfC : ∀ a, ‖f a‖ ≤ C := fun a => (hCf a).trans (le_max_left _ _)
  have hCgC : ∀ n a, ‖g n a‖ ≤ C := fun n a => (hCg n a).trans (le_max_right _ _)
  let μ : Measure α := μS.diagonalMeasure x
  let F : ℕ → α → ENNReal := fun n a =>
    ENNReal.ofReal (‖g n a - f a‖ ^ 2)
  have hFmeas : ∀ n, Measurable (F n) := by
    intro n
    exact ENNReal.continuous_ofReal.measurable.comp
      (((hg n).sub hf).norm.pow_const 2)
  have hbound : ∀ n, ∀ᵐ a ∂μ, F n a ≤ ENNReal.ofReal ((2 * C) ^ 2) := by
    intro n
    filter_upwards [] with a
    dsimp [F]
    apply ENNReal.ofReal_le_ofReal
    have hnorm : ‖g n a - f a‖ ≤ 2 * C := by
      exact (norm_sub_le _ _).trans (by linarith [hCgC n a, hCfC a])
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hnorm
  have hfin : (∫⁻ a, ENNReal.ofReal ((2 * C) ^ 2) ∂μ) ≠ (⊤ : ENNReal) := by
    rw [lintegral_const, μS.diagonalMeasure_univ]
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    exact ENNReal.ofReal_ne_top
  have hpoint : ∀ᵐ a ∂μ,
      Filter.Tendsto (fun n : ℕ => F n a) Filter.atTop (𝓝 0) := by
    filter_upwards [] with a
    have hdiff : Filter.Tendsto (fun n : ℕ => g n a - f a)
        Filter.atTop (𝓝 0) := by
      simpa using (hlim a).sub (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℕ => f a) Filter.atTop (𝓝 (f a)))
    have hnorm : Filter.Tendsto (fun n : ℕ => ‖g n a - f a‖ ^ 2)
        Filter.atTop (𝓝 (0 ^ 2)) := by
      convert (continuous_norm.pow 2).continuousAt.tendsto.comp hdiff using 1
      congr 1
      norm_num
    change Filter.Tendsto (fun n : ℕ => ENNReal.ofReal
      (‖g n a - f a‖ ^ 2)) Filter.atTop (𝓝 0)
    convert ENNReal.continuous_ofReal.continuousAt.tendsto.comp hnorm using 1
    simp [Function.comp_def]
    norm_num
  have hlin : Filter.Tendsto (fun n : ℕ => ∫⁻ a, F n a ∂μ)
      Filter.atTop (𝓝 0) := by
    simpa using
      (MeasureTheory.tendsto_lintegral_filter_of_dominated_convergence
        (fun _ : α => ENNReal.ofReal ((2 * C) ^ 2))
        (by filter_upwards [] with n; exact hFmeas n)
        (by filter_upwards [] with n; exact hbound n) hfin hpoint)
  have hnormsq : ∀ n, ENNReal.ofReal
      (‖boundedIntegral μS (g n) (hg n) (⟨C, hCgC n⟩) x -
        boundedIntegral μS f hf (⟨C, hCfC⟩) x‖ ^ 2) = ∫⁻ a, F n a ∂μ := by
    intro n
    have hsub := boundedIntegral_sub μS (hg n) hf (⟨C, hCgC n⟩) (⟨C, hCfC⟩)
    have heq := congrArg (fun A : H →WOT[ℂ] H => A x) hsub
    calc
      _ = ENNReal.ofReal
          (‖boundedIntegral μS (g n - f) ((hg n).sub hf) _ x‖ ^ 2) := by
        rw [heq]
        rfl
      _ = ∫⁻ a, ENNReal.ofReal (‖(g n - f) a‖ ^ 2)
          ∂μS.diagonalMeasure x := boundedIntegral_norm_sq μS ((hg n).sub hf) _ x
      _ = ∫⁻ a, F n a ∂μ := by rfl
  have hnorm : Filter.Tendsto (fun n : ℕ =>
      ‖boundedIntegral μS (g n) (hg n) (⟨C, hCgC n⟩) x -
        boundedIntegral μS f hf (⟨C, hCfC⟩) x‖) Filter.atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hsmall := hlin.eventually (Iio_mem_nhds
      ((ENNReal.ofReal_pos).2 (sq_pos_of_pos hε)))
    rcases Filter.eventually_atTop.1 hsmall with ⟨N, hN⟩
    refine ⟨N, fun n hn => ?_⟩
    have hlt : ENNReal.ofReal
        (‖boundedIntegral μS (g n) (hg n) (⟨C, hCgC n⟩) x -
          boundedIntegral μS f hf (⟨C, hCfC⟩) x‖ ^ 2) <
        ENNReal.ofReal (ε ^ 2) := by
      rw [hnormsq n]
      exact hN n hn
    have hsq : ‖boundedIntegral μS (g n) (hg n) (⟨C, hCgC n⟩) x -
        boundedIntegral μS f hf (⟨C, hCfC⟩) x‖ ^ 2 < ε ^ 2 :=
      (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hlt
    simpa [dist_eq_norm] using
      (sq_lt_sq₀ (norm_nonneg _) (le_of_lt hε)).mp hsq
  rw [tendsto_iff_norm_sub_tendsto_zero]
  convert hnorm using 1

end QuantumMechanics.WOTSpectralMeasure
