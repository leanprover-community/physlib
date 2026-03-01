/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.SpaceAndTime.Space.Slice
/-!

# Constant slice distributions

## i. Overview

In this module we define the lift of distributions on `Space d` to distributions
on `Space d.succ` which are constant between slices in the `i`th direction.

This is used, for example, to define distributions which are translationally invariant
in the `i`th direction.

Examples of distributions which can be constructed in this way include the dirac deltas for
lines and planes, rather then points.

## ii. Key results

- `sliceSchwartz` : The continuous linear map which takes a Schwartz map on
  `Space d.succ` and gives a Schwartz map on `Space d` by integrating over the `i`th direction.
- `constantSliceDist` : The distribution on `Space d.succ` formed by a distribution on `Space d`
  which is translationally invariant in the `i`th direction.

## iii. Table of contents

- A. Schwartz maps
  - A.1. Bounded condition for derivatives of Schwartz maps on slices
  - A.2. Integrability for of Schwartz maps on slices
  - A.3. Continiuity of integrations of slices of Schwartz maps
  - A.4. Derivative of integrations of slices of Schwartz maps
  - A.5. Differentiability as a slices of Schwartz maps
  - A.6. Smoothness as slices of Schwartz maps
  - A.7. Iterated derivatives of integrations of slices of Schwartz maps
  - A.8. The map integrating over one component of a Schwartz map
- B. Constant slice distribution
  - B.1. Derivative of constant slice distributions

## iv. References

-/
open SchwartzMap NNReal
noncomputable section

variable (𝕜 : Type) {E F F' : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup F'] [NormedSpace ℝ E] [NormedSpace ℝ F]

namespace Space

open MeasureTheory Real

/-!

## A. Schwartz maps

-/

/-!

### A.1. Bounded condition for derivatives of Schwartz maps on slices

-/

lemma schwartzMap_slice_bound {n m} {d : ℕ} (i : Fin d.succ) :
    ∃ rt, ∀ (η : 𝓢(Space d.succ, ℝ)), ∃ k,
    Integrable (fun x : ℝ => ‖((1 + ‖x‖) ^ rt)⁻¹‖) volume ∧
    (∀ (x : Space d), ∀ r, ‖(slice i).symm (r, x)‖ ^ m *
      ‖iteratedFDeriv ℝ n ⇑η ((slice i).symm (r, x))‖ ≤ k * ‖(1 + ‖r‖) ^ (rt)‖⁻¹)
      ∧ k = (2 ^ (rt + m, n).1 * ((Finset.Iic (rt + m, n)).sup
        fun m => SchwartzMap.seminorm ℝ m.1 m.2) η) := by
  obtain ⟨rt, hrt⟩ : ∃ r, Integrable (fun x : ℝ => ‖((1 + ‖x‖) ^ r)⁻¹‖) volume := by
      obtain ⟨r, h⟩ := Measure.HasTemperateGrowth.exists_integrable (μ := volume (α := ℝ))
      use r
      convert h using 1
      funext x
      simp only [norm_inv, norm_pow, Real.norm_eq_abs, Real.rpow_neg_natCast, zpow_neg,
        zpow_natCast, inv_inj]
      rw [abs_of_nonneg (by positivity)]
  use rt
  intro η
  have h0 := one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (rt + m, n))
      (k := rt + m) (n := n) le_rfl (le_rfl) η
  simp at h0
  let k := 2 ^ (rt + m, n).1 *
    ((Finset.Iic (rt + m, n)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) η
  refine ⟨k, ⟨hrt, fun x r => ?_, by rfl⟩⟩
  trans k * ‖(1 + ‖((slice i).symm (r, x))‖) ^ rt‖⁻¹; swap
  · refine mul_le_mul_of_nonneg (by rfl) ?_ (by positivity) (by positivity)
    by_cases rt = 0
    · subst rt
      simp
    refine inv_anti₀ ?_ ?_
    · simp only [norm_eq_abs, norm_pow]
      rw [abs_of_nonneg (by positivity)]
      positivity
    simp only [norm_pow, Real.norm_eq_abs, Nat.succ_eq_add_one]
    refine pow_le_pow_left₀ (by positivity) ?_ rt
    rw [abs_of_nonneg (by positivity)]
    conv_rhs => rw [abs_of_nonneg (by positivity)]
    simp only [add_le_add_iff_left]
    exact abs_right_le_norm_slice_symm i r x
  refine (le_mul_inv_iff₀ ?_).mpr (le_trans ?_ (h0 ((slice i).symm (r, x))))
  · simp
    by_cases hr : rt = 0
    · subst rt
      simp
    positivity
  trans (‖((slice i).symm (r, x))‖ ^ m * ‖(1 + ‖((slice i).symm (r, x))‖) ^ rt‖) *
    ‖iteratedFDeriv ℝ n ⇑η (((slice i).symm (r, x)))‖
  · apply le_of_eq
    simp [mul_assoc]
    left
    ring
  apply mul_le_mul_of_nonneg _ (by rfl) (by positivity) (by positivity)
  trans (1 + ‖((slice i).symm (r, x))‖) ^ m * (1 + ‖((slice i).symm (r, x))‖) ^ rt
  · refine mul_le_mul_of_nonneg ?_ ?_ (by positivity) (by positivity)
    · apply pow_le_pow_left₀ (by positivity) ?_ m
      simp
    · simp
      rw [abs_of_nonneg (by positivity)]
  apply le_of_eq
  ring_nf

/-!

### A.2. Integrability for of Schwartz maps on slices

-/

@[fun_prop]
lemma schwartzMap_mul_iteratedFDeriv_integrable_slice_symm {d : ℕ} (n m : ℕ)
    (η : 𝓢(Space d.succ, ℝ))
    (x : Space d) (i : Fin d.succ) :
    Integrable (fun r => ‖(slice i).symm (r, x)‖ ^ m *
    ‖iteratedFDeriv ℝ n ⇑η ((slice i).symm (r, x))‖) volume := by
  obtain ⟨rt, hrt⟩ := schwartzMap_slice_bound (m := m) (n := n) (d := d) i
  obtain ⟨k, hrt, hbound, k_eq⟩ := hrt η
  apply Integrable.mono' (g := fun t => k * ‖(1 + ‖t‖) ^ (rt)‖⁻¹)
  · apply Integrable.const_mul
    convert hrt using 1
    simp
  · apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · fun_prop
    apply Continuous.norm
    apply Continuous.comp'
    apply ContDiff.continuous_iteratedFDeriv (n := (n + 1 : ℕ))
    exact Nat.cast_le.mpr (by omega)
    have hη := η.smooth'
    apply hη.of_le (ENat.LEInfty.out)
    fun_prop
  · filter_upwards with t
    apply le_trans _ (hbound x t)
    apply le_of_eq
    simp only [Nat.succ_eq_add_one, norm_mul, norm_pow, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
    simp

lemma schwartzMap_integrable_slice_symm {d : ℕ} (i : Fin d.succ) (η : 𝓢(Space d.succ, ℝ))
    (x : Space d) : Integrable (fun r => η ((slice i).symm (r, x))) volume := by
  apply (schwartzMap_mul_iteratedFDeriv_integrable_slice_symm 0 0 η x i).congr'
  · fun_prop
  · simp

set_option maxSynthPendingDepth 10000 in
lemma schwartzMap_fderiv_integrable_slice_symm {d : ℕ} (η : 𝓢(Space d.succ, ℝ)) (x : Space d)
    (i : Fin d.succ) :
    Integrable (fun r => fderiv ℝ (fun x => η (((slice i).symm (r, x)))) x) volume := by
  apply Integrable.mono' (g := fun r =>
    ‖iteratedFDeriv ℝ 1 ⇑η ((slice i).symm (r, x))‖ * ‖(slice i).symm.toContinuousLinearMap.comp
          (ContinuousLinearMap.prod (0 : Space d →L[ℝ] ℝ) (ContinuousLinearMap.id ℝ (Space d)))‖)
  · apply Integrable.mul_const
    simpa using (schwartzMap_mul_iteratedFDeriv_integrable_slice_symm 1 0 η x i)
  · apply Continuous.aestronglyMeasurable
    refine Continuous.fderiv_one ?_ ?_
    · exact (η.smooth'.of_le (by simp)).comp ((slice i).symm.contDiff)
    · fun_prop
  · filter_upwards with r
    calc _
        _ ≤ ‖(fderiv ℝ ⇑η (((slice i).symm (r, x))))‖ *
          ‖fderiv ℝ (fun x => (slice i).symm (r, x)) x‖ := by
          rw [fderiv_comp' _ _ (by fun_prop)]; swap
          · apply Differentiable.differentiableAt
            exact η.smooth'.differentiable (by simp)
          exact ContinuousLinearMap.opNorm_comp_le (fderiv ℝ ⇑η (((slice i).symm (r, x)))) _
        _ ≤ ‖iteratedFDeriv ℝ 1 (⇑η) ((((slice i).symm (r, x))))‖ *
            ‖fderiv ℝ (fun x => (slice i).symm (r, x)) x‖ := by
          apply le_of_eq
          congr 1
          simp only [Nat.succ_eq_add_one]
          rw [← iteratedFDerivWithin_univ, norm_iteratedFDerivWithin_one, fderivWithin_univ]
          exact uniqueDiffWithinAt_univ
        _ ≤ ‖iteratedFDeriv ℝ 1 (⇑η) ((((slice i).symm (r, x))))‖
            * ‖(slice i).symm.toContinuousLinearMap.comp
          (ContinuousLinearMap.prod (0 : Space d →L[ℝ] ℝ)
          (ContinuousLinearMap.id ℝ (Space d)))‖ := by
            apply le_of_eq
            congr
            rw [fderiv_comp', DifferentiableAt.fderiv_prodMk (by fun_prop) (by fun_prop)]
            simp only [Nat.succ_eq_add_one, fderiv_slice_symm, fderiv_fun_const, Pi.zero_apply,
              fderiv_id']
            fun_prop
            fun_prop

@[fun_prop]
lemma schwartzMap_fderiv_left_integrable_slice_symm {d : ℕ} (η : 𝓢(Space d.succ, ℝ)) (x : Space d)
    (i : Fin d.succ) :
    Integrable (fun r => fderiv ℝ (fun r => η (((slice i).symm (r, x)))) r 1) volume := by
  conv_lhs =>
    enter [r]
    simp only [Nat.succ_eq_add_one, one_mul]
    change fderiv ℝ (η ∘ fun r => ((slice i).symm (r, x))) r 1
    rw [fderiv_comp _ (by
      apply Differentiable.differentiableAt
      exact η.smooth'.differentiable (by simp))
      (by fun_prop)]
    simp only [Nat.succ_eq_add_one, ContinuousLinearMap.coe_comp', Function.comp_apply,
      fderiv_slice_symm_left_apply]
    change (SchwartzMap.evalCLM ℝ (Space d.succ) ℝ (((slice i).symm (1, 0)))).comp
      (SchwartzMap.fderivCLM ℝ (Space d.succ) ℝ) η (((slice i).symm (r, x)))
    rw [← SchwartzMap.lineDerivOpCLM_eq]
  exact schwartzMap_integrable_slice_symm _ _ _

@[fun_prop]
lemma schwartzMap_iteratedFDeriv_norm_slice_symm_integrable {n} {d : ℕ} (η : 𝓢(Space d.succ, ℝ))
    (x : Space d) (i : Fin d.succ) :
    Integrable (fun r => ‖iteratedFDeriv ℝ n ⇑η (((slice i).symm (r, x)))‖) volume := by
  convert schwartzMap_mul_iteratedFDeriv_integrable_slice_symm n 0 η x i using 1
  funext t
  simp

@[fun_prop]
lemma schwartzMap_iteratedFDeriv_slice_symm_integrable {n} {d : ℕ} (η : 𝓢(Space d.succ, ℝ))
    (x : Space d) (i : Fin d.succ) :
    Integrable (fun r => iteratedFDeriv ℝ n ⇑η (((slice i).symm (r, x)))) volume := by
  rw [← MeasureTheory.integrable_norm_iff]
  · fun_prop
  · apply Continuous.aestronglyMeasurable
    apply Continuous.comp'
    apply ContDiff.continuous_iteratedFDeriv (n := (n + 1 : ℕ))
    exact Nat.cast_le.mpr (by omega)
    have hη := η.smooth'
    apply hη.of_le (ENat.LEInfty.out)
    fun_prop

/-!

### A.3. Continiuity of integrations of slices of Schwartz maps
-/

lemma continuous_schwartzMap_slice_integral {d} (i : Fin d.succ) (η : 𝓢(Space d.succ, ℝ)) :
    Continuous (fun x : Space d => ∫ r : ℝ, η ((slice i).symm (r, x))) := by
  obtain ⟨rt, hrt⟩ := schwartzMap_slice_bound (m := 0) (n := 0) (d := d) i
  obtain ⟨k, hrt, hbound, k_eq⟩ := hrt η
  apply MeasureTheory.continuous_of_dominated (bound := fun t => k * ‖(1 + ‖t‖) ^ (rt)‖⁻¹)
  · intro x
    fun_prop
  · intro x
    filter_upwards with t
    simpa using hbound x t
  · apply Integrable.const_mul
    convert hrt using 1
    funext t
    simp
  · filter_upwards with t
    fun_prop

/-!

### A.4. Derivative of integrations of slices of Schwartz maps

-/

lemma schwartzMap_slice_integral_hasFDerivAt {d : ℕ} (η : 𝓢(Space d.succ, ℝ)) (i : Fin d.succ)
    (x₀ : Space d) :
    HasFDerivAt (fun x => ∫ (r : ℝ), η ((slice i).symm (r, x)))
      (∫ (r : ℝ), fderiv ℝ (fun x : Space d => η ((slice i).symm (r, x))) x₀) x₀ := by
  let F : Space d → ℝ → ℝ := fun x r => η ((slice i).symm (r, x))
  let F' : Space d → ℝ → Space d →L[ℝ] ℝ :=
    fun x₀ r => fderiv ℝ (fun x : Space d => η ((slice i).symm (r, x))) x₀
  have hF : ∀ t, ∀ x, HasFDerivAt (F · t) (F' x t) x := by
    intro t x
    dsimp [F, F']
    refine DifferentiableAt.hasFDerivAt ?_
    have hf := η.smooth'
    apply Differentiable.differentiableAt
    apply Differentiable.comp
    · exact hf.differentiable (by simp)
    · fun_prop
  obtain ⟨rt, hrt⟩ := schwartzMap_slice_bound (m := 0) (n := 1) (d := d) i
  obtain ⟨k, hrt, hbound, k_eq⟩ := hrt η
  suffices h1 : HasFDerivAt (fun x => ∫ (a : ℝ), F x a) (∫ (a : ℝ), F' x₀ a) x₀ by exact h1
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (bound := fun t => (k * ‖(slice i).symm.toContinuousLinearMap.comp
          (ContinuousLinearMap.prod (0 : Space d →L[ℝ] ℝ) (ContinuousLinearMap.id ℝ (Space d)))‖)
          * ‖(1 + ‖t‖) ^ (rt)‖⁻¹)
  · exact Filter.univ_mem' (hF (F x₀ 0))
  · filter_upwards with x
    fun_prop
  · simp [F]
    exact schwartzMap_integrable_slice_symm i η x₀
  · simp [F']
    apply Continuous.aestronglyMeasurable
    refine Continuous.fderiv_one ?_ ?_
    · apply ContDiff.comp
      change ContDiff ℝ 1 η
      apply η.smooth'.of_le (by simp)
      apply ContDiff.comp
      · exact ContinuousLinearEquiv.contDiff (slice i).symm
      · fun_prop
    · fun_prop
  · filter_upwards with r
    intro x _
    calc _
        _ ≤ ‖(fderiv ℝ ⇑η (((slice i).symm (r, x))))‖ *
          ‖fderiv ℝ (fun x => (slice i).symm (r, x)) x‖ := by
          simp [F']
          rw [fderiv_comp' _ _ (by fun_prop)]; swap
          · apply Differentiable.differentiableAt
            exact η.smooth'.differentiable (by simp)
          exact ContinuousLinearMap.opNorm_comp_le (fderiv ℝ ⇑η (((slice i).symm (r, x)))) _
        _ ≤ ‖iteratedFDeriv ℝ 1 (⇑η) ((((slice i).symm (r, x))))‖ *
            ‖fderiv ℝ (fun x => (slice i).symm (r, x)) x‖ := by
          apply le_of_eq
          congr 1
          simp only [Nat.succ_eq_add_one]
          rw [← iteratedFDerivWithin_univ, norm_iteratedFDerivWithin_one, fderivWithin_univ]
          exact uniqueDiffWithinAt_univ
        _ ≤ k * (|1 + ‖r‖| ^ rt)⁻¹ * ‖fderiv ℝ (fun x => (slice i).symm (r, x)) x‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          simpa using hbound x r
        _ ≤ k * (|1 + ‖r‖| ^ rt)⁻¹ * ‖(slice i).symm.toContinuousLinearMap.comp
          (ContinuousLinearMap.prod (0 : Space d →L[ℝ] ℝ)
          (ContinuousLinearMap.id ℝ (Space d)))‖ := by
          apply le_of_eq
          congr 1
          rw [fderiv_comp', DifferentiableAt.fderiv_prodMk (by fun_prop) (by fun_prop)]
          simp only [Nat.succ_eq_add_one, fderiv_slice_symm, fderiv_fun_const, Pi.zero_apply,
            fderiv_id']
          fun_prop
          fun_prop
    apply le_of_eq
    simp only [norm_eq_abs, Nat.succ_eq_add_one, norm_pow]
    ring
  · apply Integrable.const_mul
    convert hrt using 1
    funext t
    simp
  · filter_upwards with t
    intro x _
    exact hF t x

/-!

### A.5. Differentiability as a slices of Schwartz maps

-/

lemma schwartzMap_slice_integral_differentiable {d : ℕ} (η : 𝓢(Space d.succ, ℝ))
    (i : Fin d.succ) :
    Differentiable ℝ (fun x => ∫ (r : ℝ), η ((slice i).symm (r, x))) :=
  fun x => (schwartzMap_slice_integral_hasFDerivAt η i x).differentiableAt

/-!

### A.6. Smoothness as slices of Schwartz maps

-/

lemma schwartzMap_slice_integral_contDiff {d : ℕ} (n : ℕ) (η : 𝓢(Space d.succ, ℝ))
    (i : Fin d.succ) :
    ContDiff ℝ n (fun x => ∫ (r : ℝ), η ((slice i).symm (r, x))) := by
  revert η
  induction n with
  | zero =>
    intro η
    simp only [Nat.succ_eq_add_one, CharP.cast_eq_zero, contDiff_zero]
    exact continuous_schwartzMap_slice_integral i η
  | succ n ih =>
    intro η
    simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
    rw [contDiff_succ_iff_hasFDerivAt]
    use fun x₀ => (∫ (r : ℝ), fderiv ℝ (fun x : Space d => η ((slice i).symm (r, x))) x₀)
    apply And.intro
    · rw [contDiff_clm_apply_iff]
      intro y
      have hl : (fun x => (∫ (r : ℝ), fderiv ℝ (fun x => η (((slice i).symm (r, x)))) x) y) =
          fun x => (∫ (r : ℝ), fderiv ℝ (fun x => η (((slice i).symm (r, x)))) x y) := by
        funext x
        simp only [Nat.succ_eq_add_one]
        rw [ContinuousLinearMap.integral_apply]
        exact schwartzMap_fderiv_integrable_slice_symm η x i
      rw [hl]
      have hl2 : (fun x => ∫ (r : ℝ), (fderiv ℝ (fun x => η (((slice i).symm (r, x)))) x) y)=
          fun x => ∫ (r : ℝ), LineDeriv.lineDerivOpCLM ℝ _ ((slice i).symm (0, y)) η
            (((slice i).symm (r, x))) := by
        funext x
        congr
        funext t
        simp only [Nat.succ_eq_add_one, LineDeriv.lineDerivOpCLM_apply]
        rw [fderiv_comp']
        simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
          fderiv_slice_symm_right_apply, Nat.succ_eq_add_one]
        rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
        · apply Differentiable.differentiableAt
          exact η.smooth'.differentiable (by simp)
        fun_prop
      rw [hl2]
      apply ih
    · exact fun x => schwartzMap_slice_integral_hasFDerivAt η i x
/-!

### A.7. Iterated derivatives of integrations of slices of Schwartz maps

-/

lemma schwartzMap_slice_integral_iteratedFDeriv_apply {d : ℕ} (n : ℕ) (η : 𝓢(Space d.succ, ℝ))
    (i : Fin d.succ) :
    ∀ x, ∀ y, iteratedFDeriv ℝ n (fun x => ∫ (r : ℝ), η ((slice i).symm (r, x))) x y =
      ∫ (r : ℝ), (iteratedFDeriv ℝ n η ((slice i).symm (r, x)))
      (fun j => (slice i).symm (0, y j)) := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    intro x y
    calc _
      _ = ((fderiv ℝ (fun x => iteratedFDeriv ℝ n
          (fun x => ∫ (r : ℝ), η ((slice i).symm (r, x))) x (Fin.tail y)) x) (y 0)) := by
        rw [iteratedFDeriv_succ_apply_left]
        refine Eq.symm (fderiv_continuousMultilinear_apply_const_apply ?_ (Fin.tail y) (y 0))
        apply Differentiable.differentiableAt
        apply (schwartzMap_slice_integral_contDiff (n + 1) η i).differentiable_iteratedFDeriv
        refine Nat.cast_lt.mpr ?_
        omega
      _ = (fderiv ℝ (fun x => ∫ (r : ℝ), (iteratedFDeriv ℝ n (⇑η) ((slice i).symm (r, x)))
          fun j => (slice i).symm (0, Fin.tail y j)) x) (y 0) := by
        conv_lhs =>
          enter [1, 2, x]
          rw [ih]
      _ = (fderiv ℝ (fun x => ∫ (r : ℝ), (LineDeriv.iteratedLineDerivOpCLM ℝ 𝓢(Space d.succ, ℝ)
          (fun j => (slice i).symm (0, Fin.tail y j)) η (((slice i).symm (r, x)))))) x (y 0) := by
        congr
        funext x
        congr
        funext t
        erw [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
      _ = ∫ (r : ℝ), (fderiv ℝ (fun x => ((LineDeriv.iteratedLineDerivOpCLM ℝ _ fun j =>
          (slice i).symm (0, Fin.tail y j)) η)
          ((slice i).symm (r, x))) x) (y 0) := by
        rw [(schwartzMap_slice_integral_hasFDerivAt _ i x).fderiv]
        rw [ContinuousLinearMap.integral_apply]
        exact
          schwartzMap_fderiv_integrable_slice_symm
            ((LineDeriv.iteratedLineDerivOpCLM ℝ _ fun j => (slice i).symm (0, Fin.tail y j)) η) x i
    congr
    funext r
    calc _
        _ = (fderiv ℝ (fun x => (iteratedFDeriv ℝ n (⇑η) ((slice i).symm (r, x))
            (fun j => (slice i).symm (0, Fin.tail y j)))) x) (y 0) := by
          congr
          funext x
          erw [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
    rw [iteratedFDeriv_succ_apply_left]
    simp only [Nat.succ_eq_add_one]
    rw [← fderiv_continuousMultilinear_apply_const_apply]
    rw [← fderiv_fun_slice_symm_right_apply]
    rfl
    · apply Differentiable.differentiableAt
      refine Differentiable.continuousMultilinear_apply_const ?_
          (Fin.tail fun j => (slice i).symm (0, y j))
      refine Differentiable.fun_comp ?_ ?_
      apply ContDiff.differentiable_iteratedFDeriv (n := (n + 1 : ℕ))
      refine Nat.cast_lt.mpr ?_
      simp only [lt_add_iff_pos_right, zero_lt_one]
      have hη := η.smooth'
      apply ContDiff.comp
      · exact hη.of_le (by exact ENat.LEInfty.out)
      · fun_prop
      fun_prop
    · apply Differentiable.differentiableAt
      refine Differentiable.fun_comp ?_ ?_
      apply ContDiff.differentiable_iteratedFDeriv (n := (n + 1 : ℕ))
      refine Nat.cast_lt.mpr ?_
      simp only [lt_add_iff_pos_right, zero_lt_one]
      have hη := η.smooth'
      apply ContDiff.comp
      · exact hη.of_le (by exact ENat.LEInfty.out)
      · fun_prop
      fun_prop

lemma schwartzMap_slice_integral_iteratedFDeriv {d : ℕ} (n : ℕ) (η : 𝓢(Space d.succ, ℝ))
    (i : Fin d.succ) (x : Space d) :
    iteratedFDeriv ℝ n (fun x => ∫ (r : ℝ), η ((slice i).symm (r, x))) x
    = (∫ (r : ℝ), iteratedFDeriv ℝ n η ((slice i).symm (r, x))).compContinuousLinearMap
      (fun _ => (slice i).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.prod (0 : Space d →L[ℝ] ℝ) (ContinuousLinearMap.id ℝ (Space d)))) := by
  ext y
  rw [schwartzMap_slice_integral_iteratedFDeriv_apply]
  rw [← ContinuousMultilinearMap.integral_apply]
  rfl
  simp only [Nat.succ_eq_add_one]
  exact schwartzMap_iteratedFDeriv_slice_symm_integrable η x i

lemma schwartzMap_slice_integral_iteratedFDeriv_norm_le {d : ℕ} (n : ℕ) (η : 𝓢(Space d.succ, ℝ))
    (i : Fin d.succ) (x : Space d) :
    ‖iteratedFDeriv ℝ n (fun x => ∫ (r : ℝ), η ((slice i).symm (r, x))) x‖ ≤
        (∫ (r : ℝ), ‖iteratedFDeriv ℝ n η ((slice i).symm (r, x))‖) *
        ‖(slice i).symm.toContinuousLinearMap.comp
          (ContinuousLinearMap.prod (0 : Space d →L[ℝ] ℝ)
          (ContinuousLinearMap.id ℝ (Space d)))‖ ^ n := by
  rw [schwartzMap_slice_integral_iteratedFDeriv]
  apply le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _)
  simp
  refine mul_le_mul ?_ (by rfl) (by positivity) (by positivity)
  exact norm_integral_le_integral_norm fun a => iteratedFDeriv ℝ n ⇑η _

lemma schwartzMap_mul_pow_slice_integral_iteratedFDeriv_norm_le {d : ℕ} (n m : ℕ) (i : Fin d.succ) :
    ∃ rt, ∀ (η : 𝓢(Space d.succ, ℝ)),∀ (x : Space d),
    Integrable (fun x : ℝ => ‖((1 + ‖x‖) ^ rt)⁻¹‖) volume ∧
    ‖x‖ ^ m * ‖iteratedFDeriv ℝ n (fun x => ∫ (r : ℝ), η ((slice i).symm (r, x))) x‖ ≤
        ((∫ (r : ℝ), ‖((1 + ‖r‖) ^ rt)⁻¹‖) *
        ‖(slice i).symm.toContinuousLinearMap.comp
          (ContinuousLinearMap.prod (0 : Space d →L[ℝ] ℝ)
          (ContinuousLinearMap.id ℝ (Space d)))‖ ^ n)
        * (2 ^ (rt + m, n).1 * ((Finset.Iic (rt + m, n)).sup
          fun m => SchwartzMap.seminorm ℝ m.1 m.2) η) := by
  obtain ⟨rt, hrt⟩ := schwartzMap_slice_bound (m := m) (n := n) (d := d) i
  use rt
  intro η x
  obtain ⟨k, hrt, hbound, k_eq⟩ := hrt η
  refine ⟨hrt, ?_⟩
  generalize hk : 2 ^ (rt + m, n).1 * ((Finset.Iic (rt + m, n)).sup
    fun m => SchwartzMap.seminorm ℝ m.1 m.2) η = k' at *
  subst k_eq
  have hk' : 0 ≤ k := by rw [← hk]; positivity
  calc _
      _ ≤ ‖x‖ ^ m * ((∫ (r : ℝ), ‖iteratedFDeriv ℝ n η ((slice i).symm (r, x))‖) *
          ‖(slice i).symm.toContinuousLinearMap.comp
          ((0 : Space d →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Space d)))‖ ^ n) := by
        refine mul_le_mul_of_nonneg (by rfl) ?_ (by positivity) (by positivity)
        exact schwartzMap_slice_integral_iteratedFDeriv_norm_le n η i x
      _ ≤ (∫ (r : ℝ), ‖x‖ ^ m * ‖iteratedFDeriv ℝ n η ((slice i).symm (r, x))‖) *
          ‖(slice i).symm.toContinuousLinearMap.comp
          ((0 : Space d →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Space d)))‖ ^ n := by
        apply le_of_eq
        rw [← mul_assoc, MeasureTheory.integral_const_mul]
      _ ≤ (∫ (r : ℝ), ‖((slice i).symm (r, x))‖ ^ m *
          ‖iteratedFDeriv ℝ n η (((slice i).symm (r, x)))‖) *
          ‖(slice i).symm.toContinuousLinearMap.comp
          ((0 : Space d →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Space d)))‖ ^ n := by
        refine mul_le_mul_of_nonneg ?_ (by rfl) (by positivity) (by positivity)
        refine integral_mono ?_ ?_ ?_
        · apply Integrable.const_mul
          fun_prop
        · fun_prop
        · refine Pi.le_def.mpr ?_
          intro t
          apply mul_le_mul_of_nonneg _ (by rfl) (by positivity) (by positivity)
          refine pow_le_pow_left₀ (by positivity) ?_ m
          simp
      _ ≤ ((∫ (r : ℝ), k * ‖((1 + ‖r‖) ^ rt)⁻¹‖)) *
          ‖(slice i).symm.toContinuousLinearMap.comp
          ((0 : Space d →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Space d)))‖ ^ n := by
        refine mul_le_mul_of_nonneg ?_ (by rfl) (by positivity) (by positivity)
        refine integral_mono ?_ ?_ ?_
        · fun_prop
        · apply Integrable.const_mul
          exact hrt
        · refine Pi.le_def.mpr ?_
          intro t
          convert hbound x t using 1
          simp
  apply le_of_eq
  rw [MeasureTheory.integral_const_mul]
  ring

/-!

### A.8. The map integrating over one component of a Schwartz map

-/

/-- The continuous linear map taking a Schwartz map and integrating over the `i`th component,
  to give a Schwartz map of one dimension lower. -/
def sliceSchwartz {d : ℕ} (i : Fin d.succ) :
    𝓢(Space d.succ, ℝ) →L[ℝ] 𝓢(Space d, ℝ) := by
  refine SchwartzMap.mkCLM (fun η x => ∫ (r : ℝ), η ((slice i).symm (r, x))) ?_ ?_ ?_ ?_
  · intro η1 η2 x
    simp only [Nat.succ_eq_add_one, SchwartzMap.add_apply]
    rw [integral_add]
    · exact schwartzMap_integrable_slice_symm i η1 x
    · exact schwartzMap_integrable_slice_symm i η2 x
  · intro a η x
    simp only [Nat.succ_eq_add_one, SchwartzMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [integral_const_mul]
  · intro η
    simp only [Nat.succ_eq_add_one]
    refine contDiff_infty.mpr ?_
    intro n
    exact schwartzMap_slice_integral_contDiff n η i
  · simp
    intro m n
    obtain ⟨rt, hrt⟩ := schwartzMap_mul_pow_slice_integral_iteratedFDeriv_norm_le
      (d := d) (n := n) (m := m) i
    use (Finset.Iic (rt + m, n))
    use 2 ^ (rt + m, n).1 * (∫ (r : ℝ), ‖((1 + ‖r‖) ^ rt)⁻¹‖) *
        ‖(slice i).symm.toContinuousLinearMap.comp
        ((0 : Space d →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Space d)))‖ ^ n
    apply And.intro
    · positivity
    intro η x
    specialize hrt η x
    obtain ⟨hrt1, hbound⟩ := hrt
    apply le_trans hbound
    apply le_of_eq
    ring_nf
    rfl

lemma sliceSchwartz_apply {d : ℕ} (i : Fin d.succ) (η : 𝓢(Space d.succ, ℝ)) (x : Space d) :
    sliceSchwartz i η x = ∫ (r : ℝ), η ((slice i).symm (r, x)) := by
  rfl
/-!

## B. Constant slice distribution
-/

/-- Distributions on `Space d.succ` from distributions on `Space d` given a
  direction `i`.
  These distributions are constant on slices in the `i` direction.. -/
def constantSliceDist {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] {d : ℕ} (i : Fin d.succ) :
    ((Space d) →d[ℝ] M) →ₗ[ℝ] (Space d.succ) →d[ℝ] M where
  toFun f := f ∘L sliceSchwartz i
  map_add' f g := by
    ext η
    simp
  map_smul' c f := by
    ext η
    simp

lemma constantSliceDist_apply {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {d : ℕ} (i : Fin d.succ) (f : (Space d) →d[ℝ] M) (η : 𝓢(Space d.succ, ℝ)) :
    constantSliceDist i f η = f (sliceSchwartz i η) := by
  rfl

/-!

### B.1. Derivative of constant slice distributions

-/

lemma distDeriv_constantSliceDist_same {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {d : ℕ} (i : Fin d.succ) (f : (Space d) →d[ℝ] M) :
    distDeriv i (constantSliceDist i f) = 0 := by
  ext η
  simp [constantSliceDist_apply, Space.distDeriv_apply, Distribution.fderivD_apply]
  trans f 0; swap
  · simp
  congr
  ext x
  simp [sliceSchwartz_apply]
  calc _
    _ = ∫ r, fderiv ℝ η ((slice i).symm (r, x)) (basis i) := by rfl
    _ = ∫ r, fderiv ℝ (fun r => η ((slice i).symm (r, x))) r 1 := by
        congr
        funext r
        rw [basis_self_eq_slice, fderiv_fun_slice_symm_left_apply]
        apply Differentiable.differentiableAt
        exact η.differentiable
    _ = ∫ (r : ℝ), (fun r => 1) r * fderiv ℝ (fun r => η ((slice i).symm (r, x))) r 1 := by simp
    _ = - ∫ (r : ℝ), fderiv ℝ (fun t => 1) r 1 * (fun r => η ((slice i).symm (r, x))) r := by
      rw [integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable]
      · simp
      · simp
        change Integrable (fun r => fderiv ℝ (fun r => η ((slice i).symm (r, x))) r 1) volume
        fun_prop
      · simp
        exact schwartzMap_integrable_slice_symm i η x
      · fun_prop
      · apply Differentiable.comp
        · exact η.smooth'.differentiable (by simp)
        · fun_prop
  simp

lemma distDeriv_constantSliceDist_succAbove {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {d : ℕ} (i : Fin d.succ) (j : Fin d) (f : (Space d) →d[ℝ] M) :
    distDeriv (i.succAbove j) (constantSliceDist i f) =
    constantSliceDist i (distDeriv j f) := by
  ext η
  simp [constantSliceDist_apply, Space.distDeriv_apply, Distribution.fderivD_apply]
  congr 1
  ext x
  simp [sliceSchwartz_apply]
  change ∫ (r : ℝ), fderiv ℝ η _ _ = fderiv ℝ (fun x => ∫ (r : ℝ), η _) _ _
  rw [(schwartzMap_slice_integral_hasFDerivAt η i x).fderiv]
  rw [ContinuousLinearMap.integral_apply]
  congr
  rw [basis_succAbove_eq_slice]
  funext r
  rw [fderiv_fun_slice_symm_right_apply]
  · apply Differentiable.differentiableAt
    exact η.differentiable
  · exact schwartzMap_fderiv_integrable_slice_symm η x i

end Space
