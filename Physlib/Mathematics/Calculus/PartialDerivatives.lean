/-
Copyright (c) 2026 Michal Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Mogielnicki
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Physlib.Mathematics.ForMathlib.FDerivCurry

/-!
# Partial derivatives of functions of time, position and velocity

Splitting derivatives of `L : ℝ × E × E → F` and of families `H : ℝ × ℝ → F`.

## i. Overview

The derivative of `L (τ, q, v)` splits into partial derivatives, and mixed derivatives of `H (s, τ)`
commute.

## ii. Key results

- `fderiv_apply_zero_prod`: splitting of the derivative of `L (τ, q, v)`
- `deriv_fderiv_apply_comm`: commutation of mixed derivatives of `H (s, τ)`
- `contDiff_fderiv_partial_x`, `contDiff_fderiv_partial_v`: smoothness of the partials of `L` along
  a curve
- `deriv_snd_eq_fderiv_apply`, `deriv_fst_eq_fderiv_apply`: derivatives of the slices of `H`
- `fderiv_apply_fst_eq_zero`, `fderiv_apply_fst_of_eq_add_smul`: the `s`-derivative of `H` at `τ`

## iii. Table of contents

- A. Functions of time, position and velocity
- B. Two-parameter families

## iv. References

* None.
-/

@[expose] public section

open scoped ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-!
## A. Functions of time, position and velocity
-/

/-- The `x`-derivative of `L` as a restriction of the total derivative. -/
lemma fderiv_partial_x {L : ℝ × E × E → F} {τ : ℝ} {x v : E} (hL : DifferentiableAt ℝ L (τ, x, v)) :
    fderiv ℝ (fun y ↦ L (τ, y, v)) x = (fderiv ℝ L (τ, x, v)).comp
      ((0 : E →L[ℝ] ℝ).prod ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] E))) := by
  have hy : HasFDerivAt (fun y : E ↦ (τ, y, v))
      ((0 : E →L[ℝ] ℝ).prod ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] E))) x :=
    (hasFDerivAt_const τ x).prodMk ((hasFDerivAt_id x).prodMk (hasFDerivAt_const v x))
  exact (hL.hasFDerivAt.comp x hy).fderiv

/-- The `v`-derivative of `L` as a restriction of the total derivative. -/
lemma fderiv_partial_v {L : ℝ × E × E → F} {τ : ℝ} {x v : E} (hL : DifferentiableAt ℝ L (τ, x, v)) :
    fderiv ℝ (fun w ↦ L (τ, x, w)) v = (fderiv ℝ L (τ, x, v)).comp
      ((0 : E →L[ℝ] ℝ).prod ((0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E))) := by
  have hw : HasFDerivAt (fun w : E ↦ (τ, x, w))
      ((0 : E →L[ℝ] ℝ).prod ((0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E))) v :=
    (hasFDerivAt_const τ v).prodMk ((hasFDerivAt_const x v).prodMk (hasFDerivAt_id v))
  exact (hL.hasFDerivAt.comp v hw).fderiv

/-- The total derivative of `L` on `(0, a, b)` splits into its `x` and `v` partials. -/
lemma fderiv_apply_zero_prod {L : ℝ × E × E → F} {τ : ℝ} {x v : E}
    (hL : DifferentiableAt ℝ L (τ, x, v)) (a b : E) :
    fderiv ℝ L (τ, x, v) (0, a, b) =
      fderiv ℝ (fun y ↦ L (τ, y, v)) x a + fderiv ℝ (fun w ↦ L (τ, x, w)) v b := by
  rw [fderiv_partial_x hL, fderiv_partial_v hL]
  simp [← map_add]

private lemma contDiff_fderiv_along {L : ℝ × E × E → F} (hL : ContDiff ℝ ∞ L) {q : ℝ → E}
    (hq : ContDiff ℝ ∞ q) : ContDiff ℝ ∞ fun σ ↦ fderiv ℝ L (σ, q σ, deriv q σ) :=
  (hL.fderiv_right (m := ∞) (by simp)).comp
    (contDiff_id.prodMk (hq.prodMk (contDiff_infty_iff_deriv.1 hq).2))

/-- The `x`-derivative of a smooth Lagrangian along a smooth curve is smooth in time. -/
lemma contDiff_fderiv_partial_x {L : ℝ × E × E → F} (hL : ContDiff ℝ ∞ L) {q : ℝ → E}
    (hq : ContDiff ℝ ∞ q) :
    ContDiff ℝ ∞ fun σ ↦ fderiv ℝ (fun x ↦ L (σ, x, deriv q σ)) (q σ) := by
  simp_rw [fderiv_partial_x (hL.differentiable (by simp) _)]
  exact (contDiff_fderiv_along hL hq).clm_comp contDiff_const

/-- The `v`-derivative of a smooth Lagrangian along a smooth curve is smooth in time. -/
lemma contDiff_fderiv_partial_v {L : ℝ × E × E → F} (hL : ContDiff ℝ ∞ L) {q : ℝ → E}
    (hq : ContDiff ℝ ∞ q) :
    ContDiff ℝ ∞ fun σ ↦ fderiv ℝ (fun v ↦ L (σ, q σ, v)) (deriv q σ) := by
  simp_rw [fderiv_partial_v (hL.differentiable (by simp) _)]
  exact (contDiff_fderiv_along hL hq).clm_comp contDiff_const

/-!
## B. Two-parameter families
-/

variable {H : ℝ × ℝ → F}

/-- Mixed partial derivatives of a two-parameter family, `C²` at the point, commute. -/
lemma deriv_fderiv_apply_comm {s τ : ℝ} (hH : ContDiffAt ℝ 2 H (s, τ)) :
    deriv (fun σ ↦ fderiv ℝ H (s, σ) (1, 0)) τ =
      fderiv ℝ (fun p ↦ fderiv ℝ H p (0, 1)) (s, τ) (1, 0) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ H) (s, τ) :=
    (hH.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have h1 : HasDerivAt (fun σ : ℝ ↦ (s, σ)) ((0 : ℝ), (1 : ℝ)) τ :=
    (hasDerivAt_const τ s).prodMk (hasDerivAt_id τ)
  have h3 := (hd.hasFDerivAt.comp_hasDerivAt τ h1).clm_apply
    (hasDerivAt_const τ ((1 : ℝ), (0 : ℝ)))
  have h4 : HasFDerivAt (fun p : ℝ × ℝ ↦ fderiv ℝ H p (0, 1))
      ((fderiv ℝ (fderiv ℝ H) (s, τ)).flip ((0 : ℝ), (1 : ℝ))) (s, τ) := by
    simpa using hd.hasFDerivAt.clm_apply (hasFDerivAt_const ((0 : ℝ), (1 : ℝ)) (s, τ))
  have hsymm : IsSymmSndFDerivAt ℝ H (s, τ) := hH.isSymmSndFDerivAt (by simp)
  rw [h4.fderiv]
  have h5 : deriv (fun σ ↦ fderiv ℝ H (s, σ) (1, 0)) τ = _ := h3.deriv
  rw [h5]
  simp [hsymm ((0 : ℝ), (1 : ℝ)) ((1 : ℝ), (0 : ℝ))]

/-- The `τ`-derivative of `H (s, ·)` is the total derivative applied to `(0, 1)`. -/
lemma deriv_snd_eq_fderiv_apply {s τ : ℝ} (hH : DifferentiableAt ℝ H (s, τ)) :
    deriv (fun σ ↦ H (s, σ)) τ = fderiv ℝ H (s, τ) (0, 1) := by
  rw [← fderiv_apply_one_eq_deriv]
  exact fderiv_curry_snd H s τ hH 1

/-- The `s`-derivative of `H (·, τ)` is the total derivative applied to `(1, 0)`. -/
lemma deriv_fst_eq_fderiv_apply {s τ : ℝ} (hH : DifferentiableAt ℝ H (s, τ)) :
    deriv (fun r ↦ H (r, τ)) s = fderiv ℝ H (s, τ) (1, 0) := by
  rw [← fderiv_apply_one_eq_deriv]
  exact fderiv_curry_fst H s τ hH 1

/-- If `H (·, a)` is constant, the `s`-derivative of `H` vanishes at `τ = a`. -/
lemma fderiv_apply_fst_eq_zero {a : ℝ} (hH : DifferentiableAt ℝ H (0, a))
    (h : ∀ s, H (s, a) = H (0, a)) : fderiv ℝ H (0, a) (1, 0) = 0 := by
  rw [← deriv_fst_eq_fderiv_apply hH, funext h]
  simp

/-- If `H (s, τ) = c + σ s • v` with `σ' 0 = 1`, the `s`-derivative of `H` at `(0, τ)` is `v`. -/
lemma fderiv_apply_fst_of_eq_add_smul {τ : ℝ} {c v : F} {σ : ℝ → ℝ}
    (hH : DifferentiableAt ℝ H (0, τ)) (hσ : DifferentiableAt ℝ σ 0) (hσ' : deriv σ 0 = 1)
    (h : ∀ s, H (s, τ) = c + σ s • v) : fderiv ℝ H (0, τ) (1, 0) = v := by
  rw [← deriv_fst_eq_fderiv_apply hH, funext h]
  simp [deriv_smul_const hσ, hσ']
