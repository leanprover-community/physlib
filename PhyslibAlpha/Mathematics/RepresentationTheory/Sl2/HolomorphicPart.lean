/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module
/-!
# Holomorphic and antiholomorphic parts of a real Lie algebra homomorphism

A real Lie algebra homomorphism between complex algebras splits into a complex-linear and a
complex-antilinear part, which commute.

## i. Overview

Let `D : A →ₗ⁅ℝ⁆ B` be a real Lie algebra homomorphism between complex associative algebras. It
need not be complex linear, as for the derivative of a representation of `SL(2, ℂ)` regarded as a
real Lie group. Its holomorphic and antiholomorphic parts
`D_L X = (D X - i D (i X)) / 2` and `D_R X = (D X + i D (i X)) / 2` add up to `D`. The first is
complex linear and the second complex antilinear (B), each preserves brackets, and the two
commute (C). So `D` is the sum of two commuting complex representations.

## ii. Key results

- `LieHom.holPart`, `LieHom.antiholPart` : the holomorphic and antiholomorphic parts.
- `LieHom.holPart_add_antiholPart` : the two parts add up to the homomorphism.
- `LieHom.holPart_lie`, `LieHom.antiholPart_lie` : each part preserves brackets.
- `LieHom.holPart_lie_antiholPart` : the two parts commute.

## iii. Table of contents

- A. The definitions
- B. Complex multiples
- C. Brackets

## iv. References

- B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed., Springer (2015).

-/

@[expose] public section

attribute [local instance 100] LieRing.ofAssociativeRing

/-!

## A. The definitions

-/

namespace LieHom

open Complex

variable {A B : Type*} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B] (D : A →ₗ⁅ℝ⁆ B)

/-- The holomorphic part `X ↦ (D X - i D (i X)) / 2` of a real Lie algebra homomorphism between
complex associative algebras. -/
noncomputable def holPart (X : A) : B := (2 : ℂ)⁻¹ • (D X - I • D (I • X))

/-- The antiholomorphic part `X ↦ (D X + i D (i X)) / 2` of a real Lie algebra homomorphism
between complex associative algebras. -/
noncomputable def antiholPart (X : A) : B := (2 : ℂ)⁻¹ • (D X + I • D (I • X))

/-- The homomorphism is the sum of its holomorphic and antiholomorphic parts. -/
lemma holPart_add_antiholPart (X : A) : D.holPart X + D.antiholPart X = D X := by
  simp only [holPart, antiholPart]
  module

/-- The holomorphic part is additive. -/
lemma holPart_add (X Y : A) : D.holPart (X + Y) = D.holPart X + D.holPart Y := by
  simp only [holPart, smul_add, map_add]
  module

/-- The antiholomorphic part is additive. -/
lemma antiholPart_add (X Y : A) :
    D.antiholPart (X + Y) = D.antiholPart X + D.antiholPart Y := by
  simp only [antiholPart, smul_add, map_add]
  module

/-!

## B. Complex multiples

-/

/-- A real Lie algebra homomorphism commutes with real multiples written as complex ones. -/
lemma map_ofReal_smul (r : ℝ) (X : A) : D ((r : ℂ) • X) = (r : ℂ) • D X := by
  rw [Complex.coe_smul, Complex.coe_smul]
  exact D.map_smul' r X

/-- A complex multiple `c X` is mapped to `Re c • D X + Im c • D (i X)`. -/
lemma map_smul_complex (c : ℂ) (X : A) :
    D (c • X) = (c.re : ℂ) • D X + (c.im : ℂ) • D (I • X) := by
  conv_lhs => rw [← Complex.re_add_im c]
  rw [add_smul, mul_smul, map_add, map_ofReal_smul, map_ofReal_smul]

/-- Multiplying twice by `i` negates the image. -/
lemma map_I_smul_I_smul (X : A) : D (I • I • X) = - D X := by
  rw [smul_smul, I_mul_I, neg_one_smul, map_neg]

/-- The holomorphic part is complex linear. -/
lemma holPart_smul (c : ℂ) (X : A) : D.holPart (c • X) = c • D.holPart X := by
  have h2 : D (I • c • X) = (c.re : ℂ) • D (I • X) - (c.im : ℂ) • D X := by
    rw [smul_comm, map_smul_complex, map_I_smul_I_smul, smul_neg, sub_eq_add_neg]
  simp only [holPart]
  rw [map_smul_complex, h2]
  conv_rhs => rw [← Complex.re_add_im c]
  linear_combination (norm := module) ((c.im : ℂ) / 2 * I_sq) • D (I • X)

/-- The antiholomorphic part is complex antilinear. -/
lemma antiholPart_smul (c : ℂ) (X : A) :
    D.antiholPart (c • X) = starRingEnd ℂ c • D.antiholPart X := by
  have h2 : D (I • c • X) = (c.re : ℂ) • D (I • X) - (c.im : ℂ) • D X := by
    rw [smul_comm, map_smul_complex, map_I_smul_I_smul, smul_neg, sub_eq_add_neg]
  have hc : starRingEnd ℂ c = c.re - c.im * I := Complex.ext (by simp) (by simp)
  simp only [antiholPart]
  rw [map_smul_complex, h2, hc]
  linear_combination (norm := module) ((c.im : ℂ) / 2 * I_sq) • D (I • X)

/-!

## C. Brackets

-/

/-- The holomorphic part preserves brackets. -/
lemma holPart_lie (X Y : A) : ⁅D.holPart X, D.holPart Y⁆ = D.holPart ⁅X, Y⁆ := by
  simp only [holPart, smul_lie, lie_smul, sub_lie, lie_sub, ← LieHom.map_lie,
    map_I_smul_I_smul]
  linear_combination (norm := module) ((-1 / 4 : ℂ) * I_sq) • D ⁅X, Y⁆

/-- The antiholomorphic part preserves brackets. -/
lemma antiholPart_lie (X Y : A) :
    ⁅D.antiholPart X, D.antiholPart Y⁆ = D.antiholPart ⁅X, Y⁆ := by
  simp only [antiholPart, smul_lie, lie_smul, add_lie, lie_add, ← LieHom.map_lie,
    map_I_smul_I_smul]
  linear_combination (norm := module) ((-1 / 4 : ℂ) * I_sq) • D ⁅X, Y⁆

/-- The holomorphic and antiholomorphic parts commute with each other. -/
lemma holPart_lie_antiholPart (X Y : A) : ⁅D.holPart X, D.antiholPart Y⁆ = 0 := by
  simp only [holPart, antiholPart, smul_lie, lie_smul, sub_lie, lie_add, ← LieHom.map_lie,
    map_I_smul_I_smul]
  linear_combination (norm := module) ((1 / 4 : ℂ) * I_sq) • D ⁅X, Y⁆

end LieHom
