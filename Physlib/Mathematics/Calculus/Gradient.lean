/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal, Rithwik Ranganathan
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
/-!

# Elementary rules for the gradient

Algebraic and chain rules for gradients of classical-mechanical observables.

## i. Overview

Mathlib defines the gradient `∇ f x` of a real-valued function on a real Hilbert space as the
Riesz representative of its Fréchet derivative, but records no rules for the algebraic operations
on `f` beyond constants. This file collects the elementary rules used throughout the classical
mechanics of Physlib: algebraic and chain rules, together with the gradients of scalar products,
quadratic forms, the norm, and coordinate functionals on Euclidean space.

These are the rules needed to differentiate Lagrangians and Hamiltonians of the form
`kinetic − potential` with respect to positions and velocities.

The `HasGradientAt` rules establish differentiability and the value of the gradient together.
They allow the gradients of conserved quantities in central-force systems, built from
`⟪p, p⟫`, `⟪q, q⟫`, `⟪q, p⟫` and `‖q‖`, to be computed compositionally.

These are rules for Mathlib's `gradient` on an abstract real Hilbert space. They are distinct from
`Physlib.SpaceAndTime.Space.Derivatives.Grad`, whose `Space.grad` is a coordinate-valued operator on
the structure `Space d`; nothing there applies to `EuclideanSpace ℝ (Fin 1)` or to a general inner
product space. The file is deliberately real: two of its rules (`gradient_const_mul` and
`gradient_inner_self`) are specific to real scalars, so the remaining ones are stated over
`ℝ` as well.

## ii. Key results

- `HasGradientAt.add`, `HasGradientAt.sub`, `HasGradientAt.mul`, `HasGradientAt.const_mul` :
  algebraic rules for differentiable observables.
- `HasDerivAt.comp_hasGradientAt` : the chain rule for a real function of an observable.
- `hasGradientAt_inner_left`, `hasGradientAt_inner_right`, `hasGradientAt_inner_self`,
  `hasGradientAt_norm`, `hasGradientAt_coord` : the basic gradients with differentiability.
- `gradient_add_const` : `∇ (f + c) = ∇ f`.
- `gradient_add` : `∇ (f + g) = ∇ f + ∇ g` for differentiable `f` and `g`.
- `gradient_const_mul` : `∇ (c * f) = c • ∇ f` for differentiable `f`.
- `gradient_inner_self` : `∇ (fun y => ⟪y, y⟫) x = 2 • x`.
- `gradient_const_mul_inner_self` : `∇ (fun y => c * ⟪y, y⟫) x = (2 * c) • x`.
- `gradient_coord` : `∇ (fun y => y i) x = EuclideanSpace.single i 1`.
- `gradient_comp_coord` : `∇ (fun y => f (y i)) x = f' • EuclideanSpace.single i 1` when
  `HasDerivAt f f' (x i)`.

## iii. Table of contents

- A. Algebraic rules
- B. The chain rule
- C. Scalar products and quadratic forms
- D. The norm
- E. Coordinate functionals on Euclidean space

## iv. References

* Mathlib, `Mathlib.Analysis.Calculus.Gradient.Basic`.
-/

@[expose] public section

noncomputable section

open InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  {f g : F → ℝ} {f' g' : F} {x : F}

/-!

## A. Algebraic rules

Adding a constant does not change the Fréchet derivative, hence not the gradient; the gradient is
additive over differentiable functions, multiplying by a constant scales it, and products satisfy
the Leibniz rule.

-/

/-- The gradient of a sum is the sum of the gradients. -/
lemma HasGradientAt.add (hf : HasGradientAt f f' x) (hg : HasGradientAt g g' x) :
    HasGradientAt (fun y => f y + g y) (f' + g') x := by
  rw [hasGradientAt_iff_hasFDerivAt] at *
  simp only [map_add]
  exact hf.add hg

/-- The gradient of a difference is the difference of the gradients. -/
lemma HasGradientAt.sub (hf : HasGradientAt f f' x) (hg : HasGradientAt g g' x) :
    HasGradientAt (fun y => f y - g y) (f' - g') x := by
  rw [hasGradientAt_iff_hasFDerivAt] at *
  simp only [map_sub]
  exact hf.sub hg

/-- The gradient of a product is given by the Leibniz rule. -/
lemma HasGradientAt.mul (hf : HasGradientAt f f' x) (hg : HasGradientAt g g' x) :
    HasGradientAt (fun y => f y * g y) (f x • g' + g x • f') x := by
  rw [hasGradientAt_iff_hasFDerivAt] at *
  simp only [map_add, map_smul]
  exact hf.mul hg

/-- The gradient of a constant multiple is the constant multiple of the gradient. -/
lemma HasGradientAt.const_mul (c : ℝ) (hf : HasGradientAt f f' x) :
    HasGradientAt (fun y => c * f y) (c • f') x := by
  rw [hasGradientAt_iff_hasFDerivAt] at *
  simp only [map_smul]
  exact hf.const_mul c

/-- Adding a constant to a function does not change its gradient. -/
lemma gradient_add_const {f : F → ℝ} (c : ℝ) (x : F) :
    gradient (fun y => f y + c) x = gradient f x := by
  unfold gradient
  rw [fderiv_add_const]

/-- The gradient of a sum of differentiable functions is the sum of their gradients. -/
lemma gradient_add {f g : F → ℝ} {x : F} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    gradient (fun y => f y + g y) x = gradient f x + gradient g x := by
  exact (hf.hasGradientAt.add hg.hasGradientAt).gradient

/-- The gradient of a constant multiple of a differentiable function is the constant multiple of
the gradient. -/
lemma gradient_const_mul {f : F → ℝ} {x : F} (c : ℝ) (hf : DifferentiableAt ℝ f x) :
    gradient (fun y => c * f y) x = c • gradient f x := by
  exact (hf.hasGradientAt.const_mul c).gradient

/-!

## B. The chain rule

-/

/-- The gradient of `y ↦ φ (f y)` is `φ'` times the gradient of `f`, for `φ'` the derivative of
`φ` at `f x`. -/
lemma HasDerivAt.comp_hasGradientAt {φ : ℝ → ℝ} {φ' : ℝ} (hf : HasGradientAt f f' x)
    (hφ : HasDerivAt φ φ' (f x)) : HasGradientAt (fun y => φ (f y)) (φ' • f') x := by
  rw [hasGradientAt_iff_hasFDerivAt] at *
  simp only [map_smul]
  exact hφ.comp_hasFDerivAt x hf

/-!

## C. Scalar products and quadratic forms

The quadratic form `y ↦ ⟪y, y⟫` has derivative `v ↦ 2 ⟪x, v⟫` at `x`, whose Riesz representative
is `2 • x`.

-/

/-- The gradient of `y ↦ ⟪a, y⟫` is `a`. -/
lemma hasGradientAt_inner_left (a x : F) : HasGradientAt (fun y : F => ⟪a, y⟫_ℝ) a x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  exact (toDual ℝ F a).hasFDerivAt

/-- The gradient of `y ↦ ⟪y, a⟫` is `a`. -/
lemma hasGradientAt_inner_right (a x : F) : HasGradientAt (fun y : F => ⟪y, a⟫_ℝ) a x := by
  simp_rw [real_inner_comm a]
  exact hasGradientAt_inner_left a x

/-- The gradient of `y ↦ ⟪y, y⟫` at `x` is `2 • x`. -/
lemma gradient_inner_self (x : F) : gradient (fun y : F => ⟪y, y⟫_ℝ) x = (2 : ℝ) • x := by
  refine ext_inner_right (𝕜 := ℝ) fun y => ?_
  unfold gradient
  rw [toDual_symm_apply,
    fderiv_inner_apply (𝕜 := ℝ) differentiableAt_fun_id differentiableAt_fun_id]
  simp [real_inner_comm, inner_smul_right, two_mul]

/-- The gradient of `y ↦ ⟪y, y⟫` is `2 • y`. -/
lemma hasGradientAt_inner_self (x : F) : HasGradientAt (fun y : F => ⟪y, y⟫_ℝ) ((2 : ℝ) • x) x := by
  rw [← gradient_inner_self x]
  exact (differentiableAt_fun_id.inner ℝ differentiableAt_fun_id).hasGradientAt

/-- The gradient of `y ↦ c * ⟪y, y⟫` at `x` is `(2 * c) • x`. -/
lemma gradient_const_mul_inner_self (c : ℝ) (x : F) :
    gradient (fun y : F => c * ⟪y, y⟫_ℝ) x = (2 * c) • x := by
  rw [gradient_const_mul c (differentiableAt_fun_id.inner ℝ differentiableAt_fun_id),
    gradient_inner_self, smul_smul, mul_comm]

/-!

## D. The norm

-/

/-- Away from the origin, the gradient of the norm is the unit vector `‖x‖⁻¹ • x`. -/
lemma hasGradientAt_norm (hx : x ≠ 0) : HasGradientAt (fun y : F => ‖y‖) (‖x‖⁻¹ • x) x := by
  have hs : ⟪x, x⟫_ℝ ≠ 0 := by simpa using hx
  have h := (Real.hasDerivAt_sqrt hs).comp_hasGradientAt (hasGradientAt_inner_self x)
  simp only [← norm_eq_sqrt_real_inner] at h
  convert h using 1
  rw [smul_smul]
  congr 1
  field_simp

/-!

## E. Coordinate functionals on Euclidean space

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

/-- The gradient of the `i`-th coordinate functional on Euclidean space is the `i`-th basis
vector. -/
lemma hasGradientAt_coord {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι)
    (x : EuclideanSpace ℝ ι) :
    HasGradientAt (fun y : EuclideanSpace ℝ ι => y i) (EuclideanSpace.single i 1) x := by
  rw [← gradient_coord i x]
  exact (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.hasGradientAt

/-- Chain rule for a function of one coordinate: the gradient of `y ↦ f (y i)` at `x` is
`f' • EuclideanSpace.single i 1`, where `f'` is the derivative of `f` at `x i`. -/
lemma gradient_comp_coord {ι : Type*} [Fintype ι] [DecidableEq ι] {f : ℝ → ℝ} {f' : ℝ}
    (i : ι) (x : EuclideanSpace ℝ ι) (hf : HasDerivAt f f' (x i)) :
    gradient (fun y : EuclideanSpace ℝ ι => f (y i)) x = f' • EuclideanSpace.single i 1 := by
  exact (hf.comp_hasGradientAt (hasGradientAt_coord i x)).gradient

end

end
