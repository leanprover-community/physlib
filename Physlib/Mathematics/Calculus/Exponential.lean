/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Derivatives of the exponential in a Banach algebra

The derivatives of `t ↦ exp (t x)` at `0` give the powers of `x`.

## i. Overview

In a complete normed algebra the `n`-th derivative of `t ↦ exp (t x)` is `exp (t x) xⁿ`. For a
continuous linear map `L` the values `L (xⁿ)` are the moments of `x` under `L`. They are the
derivatives at `0` of `t ↦ L (exp (t x))`.

## ii. Key results

- `iteratedDeriv_exp_smul_const` : the `n`-th derivative of `t ↦ exp (t x)` is `exp (t x) xⁿ`.
- `ContinuousLinearMap.iteratedDeriv_comp_exp_smul_const_zero` : the derivatives at `0` of
  `t ↦ L (exp (t x))` are the moments `L (xⁿ)`.

## iii. Table of contents

- A. Iterated derivatives of the exponential

## iv. References

* None.

-/

@[expose] public section

variable {𝕂 𝔸 F : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]
  [NormedAddCommGroup F] [NormedSpace 𝕂 F]

/-! ## A. Iterated derivatives of the exponential -/

/-- The `n`-th derivative of `t ↦ exp (t x)` is `exp (t x) xⁿ`. -/
lemma iteratedDeriv_exp_smul_const (x : 𝔸) (n : ℕ) (t : 𝕂) :
    iteratedDeriv n (fun u : 𝕂 ↦ NormedSpace.exp (u • x)) t = NormedSpace.exp (t • x) * x ^ n := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, funext ih, ((hasDerivAt_exp_smul_const x t).mul_const _).deriv,
      pow_succ', mul_assoc]

/-- The `n`-th derivative of `t ↦ L (exp (t x))` is `L (exp (t x) xⁿ)`. -/
lemma ContinuousLinearMap.iteratedDeriv_comp_exp_smul_const (L : 𝔸 →L[𝕂] F) (x : 𝔸) (n : ℕ)
    (t : 𝕂) : iteratedDeriv n (fun u : 𝕂 ↦ L (NormedSpace.exp (u • x))) t =
      L (NormedSpace.exp (t • x) * x ^ n) := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, funext ih]
    refine (L.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_exp_smul_const x t).mul_const _)).deriv.trans ?_
    rw [pow_succ', ← mul_assoc]

/-- The derivatives at `0` of `t ↦ L (exp (t x))` are the moments `L (xⁿ)`. -/
lemma ContinuousLinearMap.iteratedDeriv_comp_exp_smul_const_zero (L : 𝔸 →L[𝕂] F) (x : 𝔸)
    (n : ℕ) : iteratedDeriv n (fun u : 𝕂 ↦ L (NormedSpace.exp (u • x))) 0 = L (x ^ n) := by
  rw [L.iteratedDeriv_comp_exp_smul_const, zero_smul, NormedSpace.exp_zero, one_mul]
