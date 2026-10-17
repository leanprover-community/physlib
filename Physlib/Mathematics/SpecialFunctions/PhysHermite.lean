/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges, Tomas Skrivan, Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial
public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Tactic.Cases
public import Mathlib.Topology.Algebra.Polynomial
/-!

# Physicist's Hermite Polynomials

This file may eventually be upstreamed to Mathlib.

## i. Overview

The physicist's Hermite polynomials are a family of orthogonal polynomials defined by the recursion
$H_0(x) = 1$ and $H_{n+1}(x) = 2x\,H_n(x) - H_n'(x)$.
These are a rescaling of the so-called probabalist's Hermite polynomials (`Polynomial.hermite`)
and, up to numerical factors, satisfy all of the same properties.

## ii. Key results

## iii. Table of contents

- A. Recursive definition
- B. Coefficients & degree
- C. Iterated derivatives
- D. As functions `ℝ → ℝ`
  - D.1. Recursion
  - D.2. Parity
  - D.3. Differentiability
  - D.4. Temperate growth
- E. Relationship to Gaussians

## iv. References

* None.
-/

@[expose] public section

namespace Polynomial

open Function Nat

/-!
## A. Recursive definition
-/

/-- The physicist's Hermite polynomials are defined as polynomials over `ℤ` in `X` recursively
  with `physHermite 0 = 1` and

  `physHermite (n + 1) = 2 • X * physHermite n - derivative (physHermite n)`.

  This polynomial will often be cast as a function `ℝ → ℝ` by evaluating the polynomial at `X`.
-/
noncomputable def physHermite : ℕ → Polynomial ℤ
  | 0 => 1
  | n + 1 => 2 • X * physHermite n - derivative (physHermite n)

/-- The defining recursion `physHermite (n + 1) = (2x - d/dx) (physHermite n)`. -/
lemma physHermite_succ (n : ℕ) :
    physHermite (n + 1) = 2 • X * physHermite n - derivative (physHermite n) := by
  simp [physHermite]

/-- The Rodrigues formula `physHermite n = (2x - d/dx)ⁿ 1`. -/
lemma physHermite_eq_iterate (n : ℕ) :
    physHermite n = (fun p => 2 * X * p - derivative p)^[n] 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Function.iterate_succ_apply', ← ih, physHermite_succ]

@[simp]
lemma physHermite_zero : physHermite 0 = C 1 := rfl

@[simp]
lemma physHermite_one : physHermite 1 = 2 * X := by simp [physHermite_succ]

lemma derivative_physHermite_succ : (n : ℕ) →
    derivative (physHermite (n + 1)) = 2 * (n + 1) • physHermite n
  | 0 => by simp [physHermite_one]
  | n + 1 => by
    rw [physHermite_succ]
    simp only [derivative_physHermite_succ n, nsmul_eq_mul, Nat.cast_ofNat, Nat.cast_add,
      Nat.cast_one, derivative_sub, derivative_mul, derivative_ofNat, zero_mul, derivative_X,
      mul_one, zero_add, derivative_add, derivative_natCast, derivative_one, add_zero]
    simp only [physHermite_succ, nsmul_eq_mul]
    ring

lemma derivative_physHermite : (n : ℕ) →
    derivative (physHermite n) = 2 * n • physHermite (n - 1)
  | 0 => by simp
  | n + 1 => by simp [derivative_physHermite_succ]

lemma physHermite_succ' (n : ℕ) :
    physHermite (n + 1) = 2 • X * physHermite n - 2 * n • physHermite (n - 1) := by
  rw [physHermite_succ, derivative_physHermite]

/-!
## B. Coefficients & degree
-/

lemma coeff_physHermite_succ_zero (n : ℕ) :
    coeff (physHermite (n + 1)) 0 = - coeff (physHermite n) 1 := by
  simp [physHermite_succ, coeff_derivative]

lemma coeff_physHermite_succ_succ (n k : ℕ) : coeff (physHermite (n + 1)) (k + 1) =
    2 * coeff (physHermite n) k - (k + 2) * coeff (physHermite n) (k + 2) := by
  rw [physHermite_succ, coeff_sub, smul_mul_assoc, coeff_smul, coeff_X_mul, coeff_derivative,
    mul_comm]
  norm_cast

lemma coeff_physHermite_of_lt {n k : ℕ} (hnk : n < k) : coeff (physHermite n) k = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hnk
  clear hnk
  induction n generalizing k with
  | zero => exact coeff_C
  | succ n ih =>
    rw [coeff_physHermite_succ_succ, add_right_comm, show n + k + 1 + 2 = n + (k + 2) + 1 by ring,
      ih k, ih (k + 2)]
    simp

@[simp]
lemma coeff_physHermite_self (n : ℕ) : coeff (physHermite n) n = 2 ^ n := by
  induction n with
  | zero => exact coeff_C
  | succ n ih =>
    rw [coeff_physHermite_succ_succ, ih, coeff_physHermite_of_lt (by omega), mul_zero, sub_zero,
      ← Int.pow_succ']

@[simp]
lemma degree_physHermite (n : ℕ) : degree (physHermite n) = n := by
  refine degree_eq_of_le_of_coeff_ne_zero ?_ (by simp)
  simp_rw [degree_le_iff_coeff_zero, Nat.cast_lt]
  exact fun _ => coeff_physHermite_of_lt

@[simp]
lemma natDegree_physHermite (n : ℕ) : (physHermite n).natDegree = n :=
  natDegree_eq_of_degree_eq_some (degree_physHermite n)

@[simp]
lemma physHermite_leadingCoeff (n : ℕ) : (physHermite n).leadingCoeff = 2 ^ n := by
  simp [leadingCoeff]

@[simp]
lemma physHermite_ne_zero (n : ℕ) : physHermite n ≠ 0 :=
  leadingCoeff_ne_zero.mp (by simp)

/-!
## C. Iterated derivatives
-/

lemma iterate_derivative_physHermite_of_gt {n m : ℕ} (h : n < m) :
    derivative^[m] (physHermite n) = 0 :=
  iterate_derivative_eq_zero (by simpa using h)

@[simp]
lemma iterate_derivative_physHermite_self (n : ℕ) :
    derivative^[n] (physHermite n) = C (n ! * 2 ^ n : ℤ) := by
  ext m
  rw [Polynomial.coeff_iterate_derivative]
  match m with
  | 0 =>
    rw [Polynomial.coeff_C_zero]
    simp [Nat.descFactorial_self]
  | m + 1 =>
    rw [coeff_physHermite_of_lt (by omega), Polynomial.coeff_C_of_ne_zero (by omega), smul_zero]

/-!
## D. As functions `ℝ → ℝ`
-/

/-- Cast an integer polynomial to a function `ℝ → ℝ` by evaluation of the indeterminant. -/
@[coe]
noncomputable abbrev realEval (p : Polynomial ℤ) : ℝ → ℝ := fun x ↦ p.aeval x

noncomputable instance : CoeFun (Polynomial ℤ) (fun _ ↦ ℝ → ℝ) := ⟨realEval⟩

/-!
### D.1. Recursion
-/

lemma physHermite_zero_coe : (physHermite 0 : ℝ → ℝ) = fun _ ↦ 1 := by ext; simp

/-- The defining recursion for `physHermite` as functions `ℝ → ℝ` (c.f. `physHermite_succ`). -/
lemma physHermite_succ_coe (n : ℕ) :
    (physHermite (n + 1) : ℝ → ℝ) =
      2 • (fun x => x) * (physHermite n : ℝ → ℝ) - deriv (physHermite n) := by
  ext
  simp [physHermite_succ, map_ofNat]

lemma physHermite_succ_apply (n : ℕ) (x : ℝ) :
    physHermite (n + 1) x = 2 * x * physHermite n x - deriv (physHermite n) x := by
  simp [physHermite_succ_coe]

/-- The two-term recursion for `physHermite` as functions `ℝ → ℝ` (c.f. `physHermite_succ'`). -/
lemma physHermite_succ_coe' (n : ℕ) :
    (physHermite (n + 1) : ℝ → ℝ) =
      2 • (fun x => x) * (physHermite n : ℝ → ℝ) - (2 * n) • (physHermite (n - 1) : ℝ → ℝ) := by
  ext
  simp [physHermite_succ', mul_assoc, map_ofNat]

lemma physHermite_succ_apply' (n : ℕ) (x : ℝ) :
    physHermite (n + 1) x = 2 * x * physHermite n x - 2 * n * physHermite (n - 1) x := by
  simp [physHermite_succ_coe']

lemma deriv_physHermite (n : ℕ) : deriv (physHermite n) = 2 * n * physHermite (n - 1) := by
  ext
  simp [derivative_physHermite, map_ofNat, mul_assoc]

lemma iterate_deriv_physHermite_eq_iterate_derivative (n m : ℕ) :
    deriv^[m] (physHermite n) = derivative^[m] (physHermite n) := by
  match m with
  | 0 => simp
  | m + 1 =>
    ext
    simp [Function.iterate_succ_apply', iterate_deriv_physHermite_eq_iterate_derivative n m]

lemma fderiv_physHermite (n : ℕ) (x : ℝ) :
    fderiv ℝ (physHermite n) x = (1 : ℝ →L[ℝ] ℝ).smulRight (deriv (physHermite n) x) := by
  simp

/-!
### D.2. Parity
-/

/-- The `physHermite` polynomials are alternately even and odd. -/
@[simp]
lemma physHermite_neg (n : ℕ) (x : ℝ) : physHermite n (-x) = (-1) ^ n * physHermite n x := by
  match n with
  | 0 => simp
  | 1 => simp [map_ofNat]
  | n + 2 => grind [physHermite_succ_apply', physHermite_neg (n + 1), physHermite_neg n]

lemma physHermite_even {n : ℕ} (hn : Even n) : Function.Even (physHermite n) := by intro; simp [hn]

lemma physHermite_odd {n : ℕ} (hn : Odd n) : Function.Odd (physHermite n) := by intro; simp [hn]

/-!
### D.3. Differentiability
-/

@[fun_prop]
lemma physHermite_differentiable (n : ℕ) : Differentiable ℝ (physHermite n) :=
  Polynomial.differentiable_aeval _

@[fun_prop]
lemma deriv_physHermite_differentiable (n m : ℕ) : Differentiable ℝ (deriv^[m] (physHermite n)) :=
  iterate_deriv_physHermite_eq_iterate_derivative n m ▸ Polynomial.differentiable_aeval _

@[fun_prop]
lemma physHermite_continuous (n : ℕ) : Continuous (physHermite n) := Polynomial.continuous_aeval _

@[fun_prop]
lemma physHermite_contDiff (n : ℕ) (m : WithTop ℕ∞) : ContDiff ℝ m (physHermite n) :=
  Polynomial.contDiff_aeval _ _

/-!
### D.4. Temperate growth
-/

open HasTemperateGrowth in
@[fun_prop]
lemma physHermite_hasTemperateGrowth (n : ℕ) : HasTemperateGrowth (physHermite n) := by
  match n with
  | 0 =>
    rw [physHermite_zero_coe]
    fun_prop
  | n + 1 =>
    rw [physHermite_succ_coe', two_smul, nsmul_eq_mul]
    refine sub ?_ ?_
    · exact mul (by fun_prop) (physHermite_hasTemperateGrowth n)
    · exact mul (const _) (physHermite_hasTemperateGrowth (n - 1))

/-!

## E. Relationship to Gaussians

-/

lemma deriv_gaussian_eq_physHermite_mul_gaussian (n : ℕ) (x : ℝ) :
    deriv^[n] (fun y => Real.exp (- y ^ 2)) x =
    (-1 : ℝ) ^ n * physHermite n x * Real.exp (- x ^ 2) := by
  rw [mul_assoc]
  induction' n with n ih generalizing x
  · simp
  · replace ih : deriv^[n] _ = _ := _root_.funext ih
    have deriv_gaussian :
        deriv (fun y => Real.exp (-(y ^ 2))) x = -2 * x * Real.exp (-(x ^ 2)) := by
      simp [mul_comm]
    rw [Function.iterate_succ_apply', ih, deriv_const_mul_field, deriv_fun_mul, pow_succ (-1 : ℝ),
      deriv_gaussian, physHermite_succ, derivative_physHermite]
    · simp only [Polynomial.deriv_aeval, derivative_physHermite, nsmul_eq_mul, map_mul,
        map_natCast, map_sub, aeval_X, map_ofNat]
      ring
    · fun_prop
    · fun_prop

lemma physHermite_eq_deriv_gaussian (n : ℕ) (x : ℝ) :
    physHermite n x = (-1 : ℝ) ^ n * deriv^[n]
    (fun y => Real.exp (- y ^ 2)) x / Real.exp (- x ^ 2) := by
  rw [deriv_gaussian_eq_physHermite_mul_gaussian]
  simp [← mul_assoc, ← mul_pow, Real.exp_ne_zero]

lemma physHermite_eq_deriv_gaussian' (n : ℕ) (x : ℝ) :
    physHermite n x = (-1 : ℝ) ^ n * deriv^[n] (fun y => Real.exp (- y ^ 2)) x *
    Real.exp (x ^ 2) := by
  rw [physHermite_eq_deriv_gaussian, Real.exp_neg]
  field_simp [Real.exp_ne_zero]

@[fun_prop]
lemma guassian_integrable_polynomial_cons {b c : ℝ} (hb : 0 < b) (P : Polynomial ℤ) :
    MeasureTheory.Integrable fun x : ℝ => (P.aeval (c * x)) * Real.exp (-b * x ^ 2) := by
  simp_rw [Polynomial.aeval_eq_sum_range, Finset.sum_mul]
  refine MeasureTheory.integrable_finsetSum _ fun i _ => ?_
  have h2 : (fun a => P.coeff i • (c * a) ^ i * Real.exp (-b * a ^ 2)) =
      (c ^ i * P.coeff i : ℝ) • (fun x => (x ^ (i : ℝ) * Real.exp (-b * x ^ 2))) := by
    funext x
    simp only [neg_mul, mul_assoc, Real.rpow_natCast, Pi.smul_apply, smul_eq_mul]
    ring
  exact h2 ▸ MeasureTheory.Integrable.smul (c ^ i * P.coeff i : ℝ)
    (integrable_rpow_mul_exp_neg_mul_sq hb (neg_one_lt_zero.trans_le (Nat.cast_nonneg' i)))

@[fun_prop]
lemma guassian_integrable_polynomial {b : ℝ} (hb : 0 < b) (P : Polynomial ℤ) :
    MeasureTheory.Integrable fun x : ℝ => (P.aeval x) * Real.exp (-b * x ^ 2) := by
  simpa using guassian_integrable_polynomial_cons (c := 1) hb P

@[fun_prop]
lemma physHermite_gaussian_integrable (n p m : ℕ) :
    MeasureTheory.Integrable (deriv^[m] (physHermite p) * deriv^[n] fun x => Real.exp (-x ^ 2))
    MeasureTheory.volume := by
  have prod_eq_smul_aeval_mul_gaussian :
      (deriv^[m] (physHermite p) * deriv^[n] fun x => Real.exp (-x ^ 2)) =
      (-1 : ℝ) ^ n • fun x => (derivative^[m] (physHermite p) * physHermite n).aeval x *
      Real.exp (-1 * x ^ 2) := by
    funext x
    rw [iterate_deriv_physHermite_eq_iterate_derivative]
    simp only [Pi.mul_apply, deriv_gaussian_eq_physHermite_mul_gaussian, map_mul, Pi.smul_apply,
      smul_eq_mul, neg_one_mul]
    ring
  exact prod_eq_smul_aeval_mul_gaussian ▸
    MeasureTheory.Integrable.smul _ (guassian_integrable_polynomial Real.zero_lt_one _)

lemma integral_physHermite_mul_physHermite_eq_integral_deriv_exp (n m : ℕ) :
    ∫ x : ℝ, (physHermite n x * physHermite m x) * Real.exp (-x ^ 2) =
    (-1 : ℝ) ^ m * ∫ x : ℝ, (physHermite n x * (deriv^[m] fun x => Real.exp (-x ^ 2)) x) := by
  have h1 (x : ℝ) : (physHermite n x * physHermite m x) * Real.exp (-x ^ 2)
    = (-1 : ℝ) ^ m * (physHermite n x * (deriv^[m] fun x => Real.exp (-x ^ 2)) x) := by
    rw [physHermite_eq_deriv_gaussian' m x, mul_assoc, mul_assoc, ← Real.exp_add, add_neg_cancel,
      Real.exp_zero, mul_one]
    ring
  simp only [h1, MeasureTheory.integral_const_mul]

lemma integral_physHermite_mul_physHermite_eq_integral_deriv_inductive (n m : ℕ) :
    (p : ℕ) → (hpm : p ≤ m) →
    ∫ x : ℝ, (physHermite n x * physHermite m x) * Real.exp (- x ^ 2) =
    (-1 : ℝ) ^ (m - p) * ∫ x : ℝ, (deriv^[p] (physHermite n) x *
    (deriv^[m - p] fun x => Real.exp (-x ^ 2)) x)
  | 0, h => integral_physHermite_mul_physHermite_eq_integral_deriv_exp n m
  | p + 1, h => by
    rw [integral_physHermite_mul_physHermite_eq_integral_deriv_inductive n m p (by omega),
      show m - p = m - (p + 1) + 1 by omega, Function.iterate_succ_apply', pow_succ, mul_assoc,
      Function.iterate_succ_apply']
    congr
    have hl : ∫ (x : ℝ), deriv^[p] (physHermite n) x *
        deriv (deriv^[m - (p + 1)] fun x => Real.exp (-x ^ 2)) x =
        - ∫ (x : ℝ), deriv (deriv^[p] (physHermite n)) x *
        deriv^[m - (p + 1)] (fun x => Real.exp (-x ^ 2)) x := by
      apply MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
      · exact fun _ _ ↦ DifferentiableAt.hasDerivAt (deriv_physHermite_differentiable n p _)
      · intro x
        rw [hasDerivAt_deriv_iff]
        have h1 : (deriv^[m - (p + 1)] fun x => Real.exp (-x ^ 2)) =
            fun x => (-1 : ℝ) ^ (m - (p + 1)) * physHermite (m - (p + 1)) x *
            Real.exp (- x ^ 2) := by
          ext x
          exact deriv_gaussian_eq_physHermite_mul_gaussian (m - (p + 1)) x
        rw [h1]
        fun_prop
      · rw [← Function.iterate_succ_apply' deriv]
        exact physHermite_gaussian_integrable ..
      · rw [← Function.iterate_succ_apply' deriv]
        exact physHermite_gaussian_integrable ..
      · fun_prop
    simp [hl]

lemma integral_physHermite_mul_physHermite_eq_integral_deriv (n m : ℕ) :
    ∫ x : ℝ, (physHermite n x * physHermite m x) * Real.exp (- x ^ 2) =
    ∫ x : ℝ, (deriv^[m] (physHermite n) x * (Real.exp (-x ^ 2))) := by
  simp [integral_physHermite_mul_physHermite_eq_integral_deriv_inductive n m m le_rfl]

lemma physHermite_orthogonal_lt {n m : ℕ} (hnm : n < m) :
    ∫ x : ℝ, (physHermite n x * physHermite m x) * Real.exp (- x ^ 2) = 0 := by
  rw [integral_physHermite_mul_physHermite_eq_integral_deriv]
  simp [iterate_deriv_physHermite_eq_iterate_derivative, iterate_derivative_physHermite_of_gt hnm]

lemma physHermite_orthogonal {n m : ℕ} (hnm : n ≠ m) :
    ∫ x : ℝ, (physHermite n x * physHermite m x) * Real.exp (- x ^ 2) = 0 := by
  obtain h | h := hnm.lt_or_gt
  · exact physHermite_orthogonal_lt h
  · simpa [mul_comm] using physHermite_orthogonal_lt h

lemma physHermite_orthogonal_cons {n m : ℕ} (hnm : n ≠ m) (c : ℝ) :
    ∫ x : ℝ, (physHermite n (c * x) * physHermite m (c * x)) *
    Real.exp (- c ^ 2 * x ^ 2) = 0 := by
  have h := MeasureTheory.Measure.integral_comp_mul_left
    (fun x => physHermite n x * physHermite m x * Real.exp (-x ^ 2)) c
  rw [physHermite_orthogonal hnm, smul_zero] at h
  simpa [mul_pow, neg_mul] using h

lemma physHermite_norm (n : ℕ) :
    ∫ x : ℝ, (physHermite n x * physHermite n x) * Real.exp (- x ^ 2) =
    ↑n ! * 2 ^ n * √Real.pi := by
  rw [integral_physHermite_mul_physHermite_eq_integral_deriv,
    iterate_deriv_physHermite_eq_iterate_derivative]
  simp [MeasureTheory.integral_const_mul, map_ofNat,
    show (∫ x : ℝ, Real.exp (-x ^ 2)) = √Real.pi by simpa using integral_gaussian 1]

lemma physHermite_norm_cons (n : ℕ) (c : ℝ) :
    ∫ x : ℝ, (physHermite n (c * x) * physHermite n (c * x)) * Real.exp (- c ^ 2 * x ^ 2) =
    |c⁻¹| • (↑n ! * 2 ^ n * √Real.pi) := by
  have h := MeasureTheory.Measure.integral_comp_mul_left
    (fun x => physHermite n x * physHermite n x * Real.exp (-x ^ 2)) c
  rw [physHermite_norm] at h
  simpa [mul_pow, neg_mul] using h

lemma polynomial_mem_physHermite_span_induction (P : Polynomial ℤ) : (n : ℕ) →
    (hn : P.natDegree = n) →
    (P : ℝ → ℝ) ∈ Submodule.span ℝ (Set.range (fun n => (physHermite n : ℝ → ℝ)))
  | 0, h => by
    obtain ⟨x, rfl⟩ := natDegree_eq_zero.mp h
    refine Finsupp.mem_span_range_iff_exists_finsupp.mpr ⟨Finsupp.single 0 x, ?_⟩
    funext y
    simp
  | n + 1, h => by
    by_cases hP0 : P = 0
    · grind
    let P' := ((coeff (physHermite (n + 1)) (n + 1)) • P -
        (coeff P (n + 1)) • physHermite (n + 1))
    have hP'mem : (fun x => P'.aeval x) ∈ Submodule.span ℝ
        (Set.range (fun n => (physHermite n : ℝ → ℝ))) := by
      by_cases hP' : P' = 0
      · simp [hP', ← Pi.zero_def]
      · exact polynomial_mem_physHermite_span_induction P' P'.natDegree rfl
    simp only [P'] at hP'mem
    have hl : (fun x => (aeval x) ((physHermite (n + 1)).coeff (n + 1) • P -
        P.coeff (n + 1) • physHermite (n + 1)))
        = (2 ^ (n + 1) : ℝ) • (fun (x : ℝ) => (aeval x) P) - ↑(P.coeff (n + 1) : ℝ) •
        (fun (x : ℝ)=> (aeval x) (physHermite (n + 1))) := by
      funext x
      simp [coeff_physHermite_self, map_ofNat]
    rw [hl, Submodule.sub_mem_iff_left] at hP'mem
    · rwa [Submodule.smul_mem_iff] at hP'mem
      simp
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n + 1, rfl⟩)
decreasing_by
  rw [Polynomial.natDegree_lt_iff_degree_lt]
  · apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
    intro m hm'
    simp only [coeff_physHermite_self, coeff_sub]
    change n + 1 ≤ m at hm'
    rw [coeff_smul, coeff_smul]
    by_cases hm : m = n + 1
    · subst hm
      simp only [smul_eq_mul, coeff_physHermite_self]
      ring
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_physHermite_of_lt (by omega)]
      simp
  · exact hP'

lemma polynomial_mem_physHermite_span (P : Polynomial ℤ) :
    (P : ℝ → ℝ) ∈ Submodule.span ℝ (Set.range (fun n => (physHermite n : ℝ → ℝ))) :=
  polynomial_mem_physHermite_span_induction P P.natDegree rfl

lemma cos_mem_physHermite_span_topologicalClosure (c : ℝ) :
    (fun (x : ℝ) => Real.cos (c * x)) ∈
    (Submodule.span ℝ (Set.range (fun n => (physHermite n : ℝ → ℝ)))).topologicalClosure := by
  have h1 : Filter.Tendsto
      (fun s => fun y => ∑ x ∈ s, (-1) ^ x * (c * y) ^ (2 * x) / ((2 * x)! : ℝ))
      Filter.atTop (nhds (fun x => Real.cos (c * x))) :=
    tendsto_pi_nhds.mpr fun x => Real.hasSum_cos (c * x)
  have h2 (z : Finset ℕ) : (fun y => ∑ x ∈ z, (-1) ^ x * (c * y) ^ (2 * x) / ↑(2 * x)!) ∈
      ↑(Submodule.span ℝ (Set.range (fun n => (physHermite n : ℝ → ℝ)))) := by
    have h0 : (fun y => ∑ x ∈ z, (-1) ^ x * (c * y) ^ (2 * x) / ↑(2 * x)!) =
      ∑ x ∈ z, (((-1) ^ x * c ^ (2 * x) / ↑(2 * x)!) • fun (y : ℝ) => (y) ^ (2 * x)) := by
      funext y
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h0]
    refine Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ ?_
    have hy : (fun (y : ℝ) => y ^ (2 * l)) = fun y => ((X ^ (2 * l) : Polynomial ℤ)).aeval y := by
      ext
      simp
    exact hy ▸ polynomial_mem_physHermite_span _
  exact mem_closure_of_tendsto h1 (Filter.Eventually.of_forall h2)

end Polynomial
