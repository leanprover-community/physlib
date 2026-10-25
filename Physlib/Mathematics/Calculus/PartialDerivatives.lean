/-
Copyright (c) 2026 Michal Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Mogielnicki
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Physlib.Mathematics.ForMathlib.FDerivCurry

/-!
# Partial derivatives on products

Splitting derivatives of functions on `X × Y × Z` and of families `H : ℝ × ℝ → F`.

## i. Overview

The derivative of `f (a, y, z)` splits into partial derivatives, and mixed derivatives of `H (s, τ)`
commute.

## ii. Key results

- `fderiv_apply_zero_prod`: splitting of the derivative of `f (a, y, z)`
- `deriv_fderiv_apply_comm`: commutation of mixed derivatives of `H (s, τ)`

## iii. Table of contents

- A. Functions on a triple product
- B. Two-parameter families

## iv. References

* None.
-/

@[expose] public section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-!
## A. Functions on a triple product
-/

section Triple

variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The derivative in the middle argument of `f` as a restriction of the total derivative. -/
lemma fderiv_partial_snd {f : X × Y × Z → F} {a : X} {y : Y} {z : Z}
    (hf : DifferentiableAt ℝ f (a, y, z)) :
    fderiv ℝ (fun y' ↦ f (a, y', z)) y = (fderiv ℝ f (a, y, z)).comp
      ((0 : Y →L[ℝ] X).prod ((ContinuousLinearMap.id ℝ Y).prod (0 : Y →L[ℝ] Z))) :=
  (hf.hasFDerivAt.comp y
    ((hasFDerivAt_const a y).prodMk ((hasFDerivAt_id y).prodMk (hasFDerivAt_const z y)))).fderiv

/-- The derivative in the last argument of `f` as a restriction of the total derivative. -/
lemma fderiv_partial_thd {f : X × Y × Z → F} {a : X} {y : Y} {z : Z}
    (hf : DifferentiableAt ℝ f (a, y, z)) :
    fderiv ℝ (fun z' ↦ f (a, y, z')) z = (fderiv ℝ f (a, y, z)).comp
      ((0 : Z →L[ℝ] X).prod ((0 : Z →L[ℝ] Y).prod (ContinuousLinearMap.id ℝ Z))) :=
  (hf.hasFDerivAt.comp z
    ((hasFDerivAt_const a z).prodMk ((hasFDerivAt_const y z).prodMk (hasFDerivAt_id z)))).fderiv

/-- The total derivative of `f` on `(0, u, w)` splits into its middle and last partials. -/
lemma fderiv_apply_zero_prod {f : X × Y × Z → F} {a : X} {y : Y} {z : Z}
    (hf : DifferentiableAt ℝ f (a, y, z)) (u : Y) (w : Z) :
    fderiv ℝ f (a, y, z) (0, u, w) =
      fderiv ℝ (fun y' ↦ f (a, y', z)) y u + fderiv ℝ (fun z' ↦ f (a, y, z')) z w := by
  rw [fderiv_partial_snd hf, fderiv_partial_thd hf]
  simp [← map_add]

end Triple

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
  rw [h4.fderiv]
  have h5 : deriv (fun σ ↦ fderiv ℝ H (s, σ) (1, 0)) τ = _ := h3.deriv
  rw [h5]
  simp [hH.isSymmSndFDerivAt (by simp) ((0 : ℝ), (1 : ℝ)) ((1 : ℝ), (0 : ℝ))]
