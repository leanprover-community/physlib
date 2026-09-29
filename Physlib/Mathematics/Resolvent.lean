/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
/-!

# Temperate growth of the resolvent of a non-real complex number

## i. Overview

For `z : ℂ` with `z.im ≠ 0`, every real number lies in the `ℝ`-resolvent set of `z`, so
Mathlib's algebra resolvent `resolvent (R := ℝ) z = fun t : ℝ ↦ Ring.inverse (↑t - z)` is a
globally defined, smooth map `ℝ → ℂ`. Its iterated derivatives have the closed form
`(-1)ⁿ · n! · (resolvent z)ⁿ⁺¹` and are globally bounded by `n! · (|z.im| ^ (n+1))⁻¹`;
consequently the resolvent has temperate growth.

Smoothness and temperate growth are `fun_prop` lemmas, so composed variants such as the
affine reciprocal `t ↦ (z + a·t)⁻¹ = resolvent (-z) (a·t)` follow at call sites by
`fun_prop`.

## ii. Key results

- `mem_resolventSet_of_im_ne_zero` / `resolventSet_eq_univ` : every `t : ℝ` lies in
    `resolventSet ℝ z` when `z.im ≠ 0`, i.e. `t - z` is invertible for all real `t`.
- `norm_resolvent_le` : the global bound `‖resolvent z t‖ ≤ |z.im|⁻¹`.
- `iteratedDeriv_resolvent` : the closed form
    `iteratedDeriv n (resolvent z) = (-1)ⁿ · n! · (resolvent z)ⁿ⁺¹`.
- `norm_iteratedDeriv_resolvent_le` : the explicit derivative bounds
    `‖iteratedDeriv n (resolvent z) t‖ ≤ n! · (|z.im| ^ (n+1))⁻¹`.
- `contDiff_resolvent`, `hasTemperateGrowth_resolvent` : smoothness and temperate growth
    along `ℝ`, both tagged `@[fun_prop]`.

## iii. Table of contents

- A. The resolvent of a non-real complex number along `ℝ`

## iv. References

* None.
-/

@[expose] public section

open scoped ContDiff Nat

namespace Physlib.Resolvent

variable {z : ℂ}

/-!
## A. The resolvent of a non-real complex number along `ℝ`
-/

/-- Every real number lies in the `ℝ`-resolvent set of a non-real complex number:
`t - z` is invertible for all `t : ℝ`. -/
lemma mem_resolventSet_of_im_ne_zero (hz : z.im ≠ 0) (t : ℝ) : t ∈ resolventSet ℝ z := by
  rw [spectrum.mem_resolventSet_iff, isUnit_iff_ne_zero]
  exact fun h ↦ hz (by simpa using congrArg Complex.im h)

/-- The `ℝ`-resolvent set of a non-real complex number is all of `ℝ`. -/
lemma resolventSet_eq_univ (hz : z.im ≠ 0) : resolventSet ℝ z = Set.univ :=
  Set.eq_univ_of_forall (mem_resolventSet_of_im_ne_zero hz)

/-- The resolvent is globally bounded by `|z.im|⁻¹`: the imaginary part of the denominator
`t - z` is exactly `-z.im`. -/
lemma norm_resolvent_le (hz : z.im ≠ 0) (t : ℝ) : ‖resolvent z t‖ ≤ |z.im|⁻¹ := by
  rw [resolvent, Ring.inverse_eq_inv, norm_inv]
  exact inv_anti₀ (abs_pos.mpr hz) (by simpa using Complex.abs_im_le_norm ((algebraMap ℝ ℂ) t - z))

/-- The resolvent of a non-real complex number is smooth along `ℝ`. -/
@[fun_prop]
lemma contDiff_resolvent (hz : z.im ≠ 0) : ContDiff ℝ ∞ (resolvent (R := ℝ) z) := by
  have : resolvent (R := ℝ) z = fun t : ℝ ↦ ((t : ℂ) - z)⁻¹ := funext fun t ↦ Ring.inverse_eq_inv _
  rw [this]
  exact (Complex.ofRealCLM.contDiff.sub contDiff_const).inv fun t ↦
    (spectrum.mem_resolventSet_iff.mp (mem_resolventSet_of_im_ne_zero hz t)).ne_zero

/-- Closed form for the iterated derivatives of the resolvent: the `n`-th derivative is
`(-1)ⁿ · n! · (resolvent z)ⁿ⁺¹`. -/
lemma iteratedDeriv_resolvent (hz : z.im ≠ 0) (n : ℕ) :
    iteratedDeriv n (resolvent (R := ℝ) z)
      = fun t ↦ (-1) ^ n * (n ! : ℂ) * resolvent z t ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    funext t
    have hd := ((spectrum.hasDerivAt_resolvent_const_left
      (mem_resolventSet_of_im_ne_zero hz t)).pow (n + 1)).const_mul ((-1) ^ n * (n ! : ℂ))
    simp only [Pi.pow_apply] at hd
    rw [iteratedDeriv_succ, ih, hd.deriv]
    push_cast [Nat.factorial_succ]
    ring

/-- Every iterated derivative of the resolvent is globally bounded, explicitly by
`n! · (|z.im| ^ (n + 1))⁻¹`. -/
lemma norm_iteratedDeriv_resolvent_le (hz : z.im ≠ 0) (n : ℕ) (t : ℝ) :
    ‖iteratedDeriv n (resolvent z) t‖ ≤ n ! * (|z.im| ^ (n + 1))⁻¹ := by
  calc
    _ = n ! * ‖resolvent z t‖ ^ (n + 1) := by simp [iteratedDeriv_resolvent, hz]
    _ ≤ n ! * (|z.im| ^ (n + 1))⁻¹ := by
      rw [← inv_pow]
      gcongr
      exact norm_resolvent_le hz t

/-- The resolvent of a non-real complex number has temperate growth along `ℝ`. -/
@[fun_prop]
lemma hasTemperateGrowth_resolvent (hz : z.im ≠ 0) :
    Function.HasTemperateGrowth (resolvent (R := ℝ) z) := by
  refine ⟨contDiff_resolvent hz, fun n ↦ ⟨0, n ! * (|z.im| ^ (n + 1))⁻¹, fun t ↦ ?_⟩⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, pow_zero, mul_one]
  exact norm_iteratedDeriv_resolvent_le hz n t

end Physlib.Resolvent
