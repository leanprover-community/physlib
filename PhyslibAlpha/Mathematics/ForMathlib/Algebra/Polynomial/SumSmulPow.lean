/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
/-!
# Vector-valued polynomial functions of a real variable

A polynomial function of a real variable with values in a real vector space vanishes
identically only if all its coefficients vanish.

## i. Overview

A sum `∑ m < n, t ^ m • b m` with coefficients `b m` in a real vector space `V` is a
polynomial function of the real variable `t`. If it vanishes for every `t`, then so does its
pairing with any linear functional on `V`, which is a real polynomial with infinitely many
roots, hence zero. Linear functionals separate the points of `V`, so every coefficient
vanishes.

## ii. Key results

- `eq_zero_of_forall_sum_smul_pow_eq_zero` : the coefficients of an identically vanishing
  polynomial function of a real variable vanish.

## iii. Table of contents

- A. Identically vanishing polynomial functions

## iv. References

* None.

-/

@[expose] public section

/-!

## A. Identically vanishing polynomial functions

-/

/-- A `V`-valued polynomial function of one real variable that vanishes identically has
  vanishing coefficients. Pair with real-linear functionals, which separate points, and use
  that a real polynomial vanishing everywhere is zero. -/
lemma eq_zero_of_forall_sum_smul_pow_eq_zero {V : Type*} [AddCommGroup V] [Module ℝ V]
    {n : ℕ} {b : ℕ → V} (h : ∀ t : ℝ, ∑ m ∈ Finset.range n, t ^ m • b m = 0) :
    ∀ m ∈ Finset.range n, b m = 0 := by
  intro m hm
  rw [← Module.forall_dual_apply_eq_zero_iff ℝ]
  intro f
  have hpz : (∑ j ∈ Finset.range n, Polynomial.C (f (b j)) * Polynomial.X ^ j :
      Polynomial ℝ) = 0 := by
    refine Polynomial.zero_of_eval_zero _ fun t => ?_
    have h1 := congrArg f (h t)
    rw [map_sum, map_zero] at h1
    rw [Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rw [← h1]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul, mul_comm]
  have hcoeff := congrArg (fun q => AddMonoidAlgebra.coeff q m) hpz
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_zero, mul_ite, mul_one, mul_zero] at hcoeff
  rwa [Finset.sum_ite_eq (Finset.range n) m (fun j => f (b j)), ite_eq_left hm] at hcoeff
