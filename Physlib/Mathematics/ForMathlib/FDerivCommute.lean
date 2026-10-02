/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
/-!
# Iterated directional derivatives of smooth functions commute

For a smooth function `f`, differentiating along a list of directions gives a result that does not
depend on the order of the list. Mathlib proves the corresponding symmetry of `iteratedFDeriv` only
for analytic functions, so these lemmas can be replaced once it covers smooth functions.

-/

@[expose] public section

open scoped ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The derivative of a smooth function along a fixed direction is smooth. -/
lemma ContDiff.fderiv_apply_const {f : E → F} (hf : ContDiff ℝ ∞ f) (v : E) :
    ContDiff ℝ ∞ (fun x => fderiv ℝ f x v) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- Derivatives of a `C²` function along two directions commute. -/
lemma fderiv_fderiv_apply_comm {f : E → F} (hf : ContDiff ℝ 2 f) (v w : E) :
    (fun x => fderiv ℝ (fun y => fderiv ℝ f y v) x w) =
      (fun x => fderiv ℝ (fun y => fderiv ℝ f y w) x v) := by
  ext x
  rw [fderiv_clm_apply, fderiv_clm_apply]
  · simp only [fderiv_fun_const, Pi.ofNat_apply, ContinuousLinearMap.comp_zero, zero_add,
      ContinuousLinearMap.flip_apply]
    rw [IsSymmSndFDerivAt.eq]
    exact hf.contDiffAt.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  all_goals fun_prop

/-- Differentiating a smooth function along a list of directions does not depend on the order of
  the list. -/
lemma List.Perm.foldl_fderiv_apply {ι : Type*} (b : ι → E) {l₁ l₂ : List ι} (h : l₁.Perm l₂)
    {f : E → F} (hf : ContDiff ℝ ∞ f) :
    l₁.foldl (fun g i x => fderiv ℝ g x (b i)) f =
      l₂.foldl (fun g i x => fderiv ℝ g x (b i)) f := by
  induction h generalizing f with
  | nil => rfl
  | cons i _ ih => exact ih (hf.fderiv_apply_const (b i))
  | swap i j l =>
    simp only [List.foldl_cons]
    rw [fderiv_fderiv_apply_comm (hf.of_le (by simp))]
  | trans _ _ ih₁ ih₂ => exact (ih₁ hf).trans (ih₂ hf)
