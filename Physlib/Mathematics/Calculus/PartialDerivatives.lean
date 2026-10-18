/-
Copyright (c) 2026 Michal Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Mogielnicki
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Partial derivatives of functions of time, position and velocity

Splitting derivatives of `L : ℝ × E × E → ℝ` and of families `H : ℝ × ℝ → E`.

## i. Overview

The derivative of `L (τ, q, v)` splits into partial derivatives, and mixed derivatives of `H (s, τ)`
commute.

## ii. Key results

- `fderiv_apply_zero_prod`
- `deriv_fderiv_snd`

## iii. Table of contents

- A. Functions of time, position and velocity
- B. Two-parameter families

## iv. References

* None.
-/

@[expose] public section

open Set
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-!
## A. Functions of time, position and velocity
-/

/-- The `x`-derivative of `L` as a restriction of the total derivative. -/
lemma fderiv_partial_x {L : ℝ × E × E → ℝ} (hL : Differentiable ℝ L) (τ : ℝ) (x v : E) :
    fderiv ℝ (fun y ↦ L (τ, y, v)) x = (fderiv ℝ L (τ, x, v)).comp
      ((0 : E →L[ℝ] ℝ).prod ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] E))) := by
  have hy : HasFDerivAt (fun y : E ↦ (τ, y, v))
      ((0 : E →L[ℝ] ℝ).prod ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] E))) x :=
    (hasFDerivAt_const τ x).prodMk ((hasFDerivAt_id x).prodMk (hasFDerivAt_const v x))
  exact ((hL (τ, x, v)).hasFDerivAt.comp x hy).fderiv

/-- The `v`-derivative of `L` as a restriction of the total derivative. -/
lemma fderiv_partial_v {L : ℝ × E × E → ℝ} (hL : Differentiable ℝ L) (τ : ℝ) (x v : E) :
    fderiv ℝ (fun w ↦ L (τ, x, w)) v = (fderiv ℝ L (τ, x, v)).comp
      ((0 : E →L[ℝ] ℝ).prod ((0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E))) := by
  have hw : HasFDerivAt (fun w : E ↦ (τ, x, w))
      ((0 : E →L[ℝ] ℝ).prod ((0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E))) v :=
    (hasFDerivAt_const τ v).prodMk ((hasFDerivAt_const x v).prodMk (hasFDerivAt_id v))
  exact ((hL (τ, x, v)).hasFDerivAt.comp v hw).fderiv

/-- The total derivative of `L` on `(0, a, b)` splits into its `x` and `v` partials. -/
lemma fderiv_apply_zero_prod {L : ℝ × E × E → ℝ} (hL : Differentiable ℝ L) (τ : ℝ)
    (x v a b : E) :
    fderiv ℝ L (τ, x, v) (0, a, b) =
      fderiv ℝ (fun y ↦ L (τ, y, v)) x a + fderiv ℝ (fun w ↦ L (τ, x, w)) v b := by
  rw [fderiv_partial_x hL, fderiv_partial_v hL]
  simp [← map_add]

private lemma contDiff_fderiv_along {L : ℝ × E × E → ℝ} (hL : ContDiff ℝ ∞ L) {q : ℝ → E}
    (hq : ContDiff ℝ ∞ q) : ContDiff ℝ ∞ fun σ ↦ fderiv ℝ L (σ, q σ, deriv q σ) :=
  (hL.fderiv_right (m := ∞) (by simp)).comp
    (contDiff_id.prodMk (hq.prodMk (contDiff_infty_iff_deriv.1 hq).2))

/-- The `x`-derivative of a smooth Lagrangian along a smooth curve is smooth in time. -/
lemma contDiff_fderiv_partial_x {L : ℝ × E × E → ℝ} (hL : ContDiff ℝ ∞ L) {q : ℝ → E}
    (hq : ContDiff ℝ ∞ q) :
    ContDiff ℝ ∞ fun σ ↦ fderiv ℝ (fun x ↦ L (σ, x, deriv q σ)) (q σ) := by
  simp_rw [fderiv_partial_x (hL.differentiable (by simp))]
  exact (contDiff_fderiv_along hL hq).clm_comp contDiff_const

/-- The `v`-derivative of a smooth Lagrangian along a smooth curve is smooth in time. -/
lemma contDiff_fderiv_partial_v {L : ℝ × E × E → ℝ} (hL : ContDiff ℝ ∞ L) {q : ℝ → E}
    (hq : ContDiff ℝ ∞ q) :
    ContDiff ℝ ∞ fun σ ↦ fderiv ℝ (fun v ↦ L (σ, q σ, v)) (deriv q σ) := by
  simp_rw [fderiv_partial_v (hL.differentiable (by simp))]
  exact (contDiff_fderiv_along hL hq).clm_comp contDiff_const

/-!
## B. Two-parameter families
-/

variable {H : ℝ × ℝ → E}

/-- The directional derivative of a smooth map is smooth. -/
lemma contDiff_fderiv_apply (hH : ContDiff ℝ ∞ H) (v : ℝ × ℝ) :
    ContDiff ℝ ∞ fun p ↦ fderiv ℝ H p v :=
  (hH.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- Mixed partial derivatives of a two-parameter family commute. -/
lemma deriv_fderiv_snd (hH : ContDiff ℝ ∞ H) (s τ : ℝ) :
    deriv (fun σ ↦ fderiv ℝ H (s, σ) (1, 0)) τ =
      fderiv ℝ (fun p ↦ fderiv ℝ H p (0, 1)) (s, τ) (1, 0) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ H) (s, τ) :=
    (hH.fderiv_right (m := 1) (by simp)).differentiable one_ne_zero (s, τ)
  have h1 : HasDerivAt (fun σ : ℝ ↦ (s, σ)) ((0 : ℝ), (1 : ℝ)) τ :=
    (hasDerivAt_const τ s).prodMk (hasDerivAt_id τ)
  have h3 := (hd.hasFDerivAt.comp_hasDerivAt τ h1).clm_apply
    (hasDerivAt_const τ ((1 : ℝ), (0 : ℝ)))
  have h4 : HasFDerivAt (fun p : ℝ × ℝ ↦ fderiv ℝ H p (0, 1))
      ((fderiv ℝ (fderiv ℝ H) (s, τ)).flip ((0 : ℝ), (1 : ℝ))) (s, τ) := by
    simpa using hd.hasFDerivAt.clm_apply (hasFDerivAt_const ((0 : ℝ), (1 : ℝ)) (s, τ))
  have hsymm : IsSymmSndFDerivAt ℝ H (s, τ) := hH.contDiffAt.isSymmSndFDerivAt (by simp)
  rw [h4.fderiv]
  have h5 : deriv (fun σ ↦ fderiv ℝ H (s, σ) (1, 0)) τ = _ := h3.deriv
  rw [h5]
  simp [hsymm ((0 : ℝ), (1 : ℝ)) ((1 : ℝ), (0 : ℝ))]

/-- The `τ`-derivative of `H (s, ·)` is the total derivative applied to `(0, 1)`. -/
lemma fderiv_snd_apply (hH : ContDiff ℝ ∞ H) (s τ : ℝ) :
    deriv (fun σ ↦ H (s, σ)) τ = fderiv ℝ H (s, τ) (0, 1) := by
  have h1 : HasDerivAt (fun σ : ℝ ↦ (s, σ)) ((0 : ℝ), (1 : ℝ)) τ :=
    (hasDerivAt_const τ s).prodMk (hasDerivAt_id τ)
  exact ((hH.differentiable (by simp) (s, τ)).hasFDerivAt.comp_hasDerivAt τ h1).deriv

/-- The `s`-derivative of `H (·, τ)` is the total derivative applied to `(1, 0)`. -/
lemma fderiv_fst_apply (hH : ContDiff ℝ ∞ H) (s τ : ℝ) :
    deriv (fun r ↦ H (r, τ)) s = fderiv ℝ H (s, τ) (1, 0) := by
  have h1 : HasDerivAt (fun r : ℝ ↦ (r, τ)) ((1 : ℝ), (0 : ℝ)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s τ)
  exact ((hH.differentiable (by simp) (s, τ)).hasFDerivAt.comp_hasDerivAt s h1).deriv

/-- If `H (·, a)` is constant, the `s`-derivative of `H` vanishes at `τ = a`. -/
lemma fderiv_fst_apply_eq_zero (hH : ContDiff ℝ ∞ H) {a : ℝ} (h : ∀ s, H (s, a) = H (0, a)) :
    fderiv ℝ H (0, a) (1, 0) = 0 := by
  rw [← fderiv_fst_apply hH 0 a, funext h]
  simp
