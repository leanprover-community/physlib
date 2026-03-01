/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.SpaceAndTime.SpaceTime.Basic
/-!

# Time Derivatives

## i. Overview

In this module we define and prove basic lemmas about derivatives of functions on `Time`.

## ii. Key results

- `deriv` : The derivative of a function `Time → M` at a given time.

## iii. Table of contents

- A. The definition of the derivative
- B. Linearlity properties of the derivative
- C. Derivative of constant functions
- D. Smoothness properties of the derivative
- E. Derivatives of components

## iv. References

-/

namespace Time

variable {M : Type} {d : ℕ} {t : Time}

/-!

## A. The definition of the derivative

-/
/-- Given a function `f : Time → M` the derivative of `f`. -/
noncomputable def deriv [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    (f : Time → M) : Time → M :=
  (fun t => fderiv ℝ f t 1)

@[inherit_doc deriv]
scoped notation "∂ₜ" => deriv

lemma deriv_eq [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    (f : Time → M) (t : Time) : Time.deriv f t = fderiv ℝ f t 1 := rfl

/-!

## B. Linearlity properties of the derivative

-/

lemma deriv_smul (f : Time → EuclideanSpace ℝ (Fin d)) (k : ℝ)
    (hf : Differentiable ℝ f) :
    ∂ₜ (fun t => k • f t) t = k • ∂ₜ (fun t => f t) t := by
  rw [deriv, fderiv_fun_const_smul]
  rfl
  fun_prop

lemma deriv_neg [NormedAddCommGroup M] [NormedSpace ℝ M] (f : Time → M) :
    ∂ₜ (-f) t = -∂ₜ f t := by
  rw [deriv, fderiv_neg]
  rfl

/-!

## C. Derivative of constant functions

-/

@[simp]
lemma deriv_const [NormedAddCommGroup M] [NormedSpace ℝ M] (m : M) :
    ∂ₜ (fun _ => m) t = 0 := by
  rw [deriv]
  simp

/-!

## D. Smoothness properties of the derivative

-/

open MeasureTheory ContDiff InnerProductSpace Time

@[fun_prop]
lemma deriv_differentiable_of_contDiff {M : Type}
    [NormedAddCommGroup M] [NormedSpace ℝ M] (f : Time → M) (hf : ContDiff ℝ ∞ f) :
    Differentiable ℝ (∂ₜ f) := by
  unfold deriv
  change Differentiable ℝ ((fun x => x 1) ∘ (fun t => fderiv ℝ f t))
  apply Differentiable.comp
  · fun_prop
  · rw [contDiff_infty_iff_fderiv, contDiff_infty_iff_fderiv] at hf
    exact hf.2.1

@[fun_prop]
lemma deriv_contDiff_of_contDiff {M : Type}
    [NormedAddCommGroup M] [NormedSpace ℝ M] (f : Time → M) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (∂ₜ f) := by
  unfold deriv
  change ContDiff ℝ ∞ ((fun x => x 1) ∘ (fun t => fderiv ℝ f t))
  apply ContDiff.comp
  · fun_prop
  · fun_prop

/-!

## E. Derivatives of components

-/

lemma differentiable_euclid {f : Time → EuclideanSpace ℝ (Fin n)}
    (hf : ∀ i, Differentiable ℝ (fun t => f t i)) :
    Differentiable ℝ f := by
  rw [differentiable_euclidean]
  fun_prop

lemma deriv_euclid { μ} {f : Time→ EuclideanSpace ℝ (Fin n)}
    (hf : Differentiable ℝ f) (t : Time) :
    deriv (fun t => f t μ) t = deriv (fun t => f t) t μ := by
  rw [deriv_eq]
  change fderiv ℝ (EuclideanSpace.proj μ ∘ fun x => f x) t 1 = _
  rw [fderiv_comp]
  · simp
    rw [← deriv_eq]
  · fun_prop
  · fun_prop

lemma fderiv_euclid { μ} {f : Time→ EuclideanSpace ℝ (Fin n)}
    (hf : Differentiable ℝ f) (t dt : Time) :
    fderiv ℝ (fun t => f t μ) t dt = fderiv ℝ (fun t => f t) t dt μ := by
  change fderiv ℝ (EuclideanSpace.proj μ ∘ fun x => f x) t dt = _
  rw [fderiv_comp]
  · simp
  · fun_prop
  · fun_prop

lemma deriv_lorentzVector {d : ℕ} {f : Time → Lorentz.Vector d}
    (hf : Differentiable ℝ f) (t : Time) (i : Fin 1 ⊕ Fin d) :
    deriv (fun t => f t i) t = deriv (fun t => f t) t i := by
  rw [deriv_eq]
  change fderiv ℝ (Lorentz.Vector.coordCLM i ∘ fun x => f x) t 1 = _
  rw [fderiv_comp]
  · simp
    rw [← deriv_eq]
    rfl
  · fun_prop
  · fun_prop

end Time
