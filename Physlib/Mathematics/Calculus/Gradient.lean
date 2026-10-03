/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
/-!

# Elementary rules for the gradient

## i. Overview

Mathlib defines the gradient `∇ f x` of a real-valued function on a real Hilbert space as the
Riesz representative of its Fréchet derivative, but records no rules for the algebraic operations
on `f` beyond constants. This file collects the elementary rules used throughout the classical
mechanics of Physlib: a gradient is unchanged by adding a constant, it is additive over
differentiable functions, it commutes with multiplication by a constant, the gradient of the
quadratic form `⟪y, y⟫` is `2 • y`, and the gradient of a coordinate functional on Euclidean space
is the corresponding basis vector.

These are the rules needed to differentiate Lagrangians and Hamiltonians of the form
`kinetic − potential` with respect to positions and velocities.

These are rules for Mathlib's `gradient` on an abstract real Hilbert space. They are distinct from
`Physlib.SpaceAndTime.Space.Derivatives.Grad`, whose `Space.grad` is a coordinate-valued operator on
the structure `Space d`; nothing there applies to `EuclideanSpace ℝ (Fin 1)` or to a general inner
product space. The file is deliberately real: two of its rules (`gradient_const_mul` and
`gradient_inner_self`) are specific to real scalars, so the remaining ones are stated over
`ℝ` as well.

## ii. Key results

- `gradient_add_const` : `∇ (f + c) = ∇ f`.
- `gradient_add` : `∇ (f + g) = ∇ f + ∇ g` for differentiable `f` and `g`.
- `gradient_const_mul` : `∇ (c * f) = c • ∇ f` for differentiable `f`.
- `gradient_inner_self` : `∇ (fun y => ⟪y, y⟫) x = 2 • x`.
- `gradient_const_mul_inner_self` : `∇ (fun y => c * ⟪y, y⟫) x = (2 * c) • x`.
- `gradient_coord` : `∇ (fun y => y i) x = EuclideanSpace.single i 1`.
- `gradient_comp_coord` : `∇ (fun y => f (y i)) x = f' • EuclideanSpace.single i 1` when
  `HasDerivAt f f' (x i)`.

## iii. Table of contents

- A. Gradients and constants
- B. Gradients of quadratic forms
- C. Coordinate functionals on Euclidean space

## iv. References

* Mathlib, `Mathlib.Analysis.Calculus.Gradient.Basic`.
-/

@[expose] public section

noncomputable section

open InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-!

## A. Gradients and constants

Adding a constant does not change the Fréchet derivative, hence not the gradient; the gradient is
additive over differentiable functions, and multiplying by a constant scales it.

-/

/-- Adding a constant to a function does not change its gradient. -/
lemma gradient_add_const {f : F → ℝ} (c : ℝ) (x : F) :
    gradient (fun y => f y + c) x = gradient f x := by
  unfold gradient
  rw [fderiv_add_const]

/-- The gradient of a sum of differentiable functions is the sum of their gradients. -/
lemma gradient_add {f g : F → ℝ} {x : F} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    gradient (fun y => f y + g y) x = gradient f x + gradient g x := by
  unfold gradient
  rw [fderiv_fun_add hf hg, map_add]

/-- The gradient of a constant multiple of a differentiable function is the constant multiple of
the gradient. -/
lemma gradient_const_mul {f : F → ℝ} {x : F} (c : ℝ) (hf : DifferentiableAt ℝ f x) :
    gradient (fun y => c * f y) x = c • gradient f x := by
  unfold gradient
  rw [fderiv_const_mul hf, map_smul]

/-!

## B. Gradients of quadratic forms

The quadratic form `y ↦ ⟪y, y⟫` has derivative `v ↦ 2 ⟪x, v⟫` at `x`, whose Riesz representative
is `2 • x`.

-/

/-- The gradient of `y ↦ ⟪y, y⟫` at `x` is `2 • x`. -/
lemma gradient_inner_self (x : F) : gradient (fun y : F => ⟪y, y⟫_ℝ) x = (2 : ℝ) • x := by
  refine ext_inner_right (𝕜 := ℝ) fun y => ?_
  unfold gradient
  rw [toDual_symm_apply,
    fderiv_inner_apply (𝕜 := ℝ) differentiableAt_fun_id differentiableAt_fun_id]
  simp [real_inner_comm, inner_smul_right, two_mul]

/-- The gradient of `y ↦ c * ⟪y, y⟫` at `x` is `(2 * c) • x`. -/
lemma gradient_const_mul_inner_self (c : ℝ) (x : F) :
    gradient (fun y : F => c * ⟪y, y⟫_ℝ) x = (2 * c) • x := by
  rw [gradient_const_mul c (differentiableAt_fun_id.inner ℝ differentiableAt_fun_id),
    gradient_inner_self, smul_smul, mul_comm]

/-!

## C. Coordinate functionals on Euclidean space

The coordinate functional `y ↦ y i` on `EuclideanSpace ℝ ι` is the continuous linear map
`EuclideanSpace.proj i`, whose Riesz representative is the basis vector `EuclideanSpace.single i 1`.

-/

/-- The gradient of the `i`-th coordinate functional on Euclidean space is the `i`-th basis
vector. -/
lemma gradient_coord {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) (x : EuclideanSpace ℝ ι) :
    gradient (fun y : EuclideanSpace ℝ ι => y i) x = EuclideanSpace.single i 1 := by
  have h : HasFDerivAt (fun y : EuclideanSpace ℝ ι => y i)
      (innerSL ℝ (EuclideanSpace.single i (1 : ℝ))) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.congr_fderiv
      (by ext y; simp [EuclideanSpace.inner_single_left])
  exact h.hasGradientAt.gradient.trans ((toDual ℝ _).symm_apply_apply _)

/-- Chain rule for a function of one coordinate: the gradient of `y ↦ f (y i)` at `x` is
`f' • EuclideanSpace.single i 1`, where `f'` is the derivative of `f` at `x i`. -/
lemma gradient_comp_coord {ι : Type*} [Fintype ι] [DecidableEq ι] {f : ℝ → ℝ} {f' : ℝ}
    (i : ι) (x : EuclideanSpace ℝ ι) (hf : HasDerivAt f f' (x i)) :
    gradient (fun y : EuclideanSpace ℝ ι => f (y i)) x = f' • EuclideanSpace.single i 1 := by
  have h : HasFDerivAt (fun y : EuclideanSpace ℝ ι => f (y i))
      (innerSL ℝ (f' • EuclideanSpace.single i (1 : ℝ))) x :=
    (hf.comp_hasFDerivAt x (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt).congr_fderiv
      (by ext y; simp [EuclideanSpace.inner_single_left, smul_eq_mul])
  exact h.hasGradientAt.gradient.trans ((toDual ℝ _).symm_apply_apply _)

end

end
