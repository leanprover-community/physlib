/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan, Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Tactic.Cases
/-!

# Physicists Hermite Polynomial

This file may eventually be upstreamed to Mathlib.

-/

@[expose] public section

open Polynomial
namespace PhysLean

/-- The Physicists Hermite polynomial are defined as polynomials over `ℤ` in `X` recursively
  with `physHermite 0 = 1` and

  `physHermite (n + 1) = 2 • X * physHermite n - derivative (physHermite n)`.

  This polynomial will often be cast as a function `ℝ → ℝ` by evaluating the polynomial at `X`.
-/
noncomputable def physHermite : ℕ → Polynomial ℤ
  | 0 => 1
  | n + 1 => 2 • X * physHermite n - derivative (physHermite n)

lemma physHermite_succ (n : ℕ) :
    physHermite (n + 1) = 2 • X * physHermite n - derivative (physHermite n) := by
  simp [physHermite]

lemma physHermite_eq_iterate (n : ℕ) :
    physHermite n = (fun p => 2 * X * p - derivative p)^[n] 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Function.iterate_succ_apply', ← ih, physHermite_succ]

@[simp]
lemma physHermite_zero : physHermite 0 = C 1 := rfl

lemma physHermite_one : physHermite 1 = 2 * X := by simp [physHermite_succ]

lemma derivative_physHermite_succ : (n : ℕ) →
    derivative (physHermite (n + 1)) = 2 * (n + 1) • physHermite n
  | 0 => by
    simp [physHermite_one]
  | n + 1 => by
    rw [physHermite_succ]
    simp only [nsmul_eq_mul, Nat.cast_ofNat, derivative_sub, derivative_mul, derivative_ofNat,
      zero_mul, derivative_X, mul_one, zero_add, Nat.cast_add, Nat.cast_one]
    rw [derivative_physHermite_succ]
    simp only [physHermite_succ, nsmul_eq_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one,
      derivative_mul, derivative_ofNat, zero_mul, derivative_add, derivative_natCast,
      derivative_one, add_zero, zero_add]
    ring

lemma derivative_physHermite : (n : ℕ) →
    derivative (physHermite n) = 2 * n • physHermite (n - 1)
  | 0 => by simp
  | n + 1 => by simp [derivative_physHermite_succ]

lemma physHermite_succ' (n : ℕ) :
    physHermite (n + 1) = 2 • X * physHermite n - 2 * n • physHermite (n - 1) := by
  rw [physHermite_succ, derivative_physHermite]

lemma coeff_physHhermite_succ_zero (n : ℕ) :
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
    have : n + k + 1 + 2 = n + (k + 2) + 1 := by ring
    rw [coeff_physHermite_succ_succ, add_right_comm, this, ih k, ih (k + 2), mul_zero]
    simp

@[simp]
lemma coeff_physHermite_self_succ (n : ℕ) : coeff (physHermite n) n = 2 ^ n := by
  induction n with
  | zero => exact coeff_C
  | succ n ih =>
    rw [coeff_physHermite_succ_succ, ih, coeff_physHermite_of_lt, mul_zero, sub_zero]
    · rw [← Int.pow_succ']
    · simp

@[simp]
lemma degree_physHermite (n : ℕ) : degree (physHermite n) = n := by
  rw [degree_eq_of_le_of_coeff_ne_zero]
  · simp_rw [degree_le_iff_coeff_zero, Nat.cast_lt]
    rintro m hnm
    exact coeff_physHermite_of_lt hnm
  · simp

@[simp]
lemma natDegree_physHermite {n : ℕ} : (physHermite n).natDegree = n :=
  natDegree_eq_of_degree_eq_some (degree_physHermite n)

lemma iterate_derivative_physHermite_of_gt {n m : ℕ} (h : n < m) :
    derivative^[m] (physHermite n) = 0 := by
  refine iterate_derivative_eq_zero ?_
  simpa using h

open Nat

@[simp]
lemma iterate_derivative_physHermite_self {n : ℕ} :
    derivative^[n] (physHermite n) = C ((n ! : ℤ) * 2 ^ n) := by
  refine coeff_inj.mp ?_
  funext m
  rw [Polynomial.coeff_iterate_derivative]
  match m with
  | 0 =>
    rw [Polynomial.coeff_C_zero]
    simp only [zero_add, coeff_physHermite_self_succ, nsmul_eq_mul, mul_eq_mul_right_iff,
      Nat.cast_inj, pow_eq_zero_iff', OfNat.ofNat_ne_zero, ne_eq, false_and, or_false]
    rw [Nat.descFactorial_self]
  | m + 1 =>
    rw [coeff_physHermite_of_lt (by omega), Polynomial.coeff_C_ne_zero (by omega)]
    rfl

@[simp]
lemma physHermite_leadingCoeff {n : ℕ} : (physHermite n).leadingCoeff = 2 ^ n := by
  simp [leadingCoeff]

@[simp]
lemma physHermite_ne_zero {n : ℕ} : physHermite n ≠ 0 := by
  refine leadingCoeff_ne_zero.mp ?_
  simp

instance : CoeFun (Polynomial ℤ) (fun _ ↦ ℝ → ℝ)where
  coe p := fun x => p.aeval x

lemma physHermite_eq_aeval (n : ℕ) (x : ℝ) :
    physHermite n x = (physHermite n).aeval x := rfl

lemma physHermite_zero_apply (x : ℝ) : physHermite 0 x = 1 := by simp

lemma physHermite_pow (n m : ℕ) (x : ℝ) : physHermite n x ^ m = aeval x (physHermite n ^ m) := by
  simp

lemma physHermite_succ_fun (n : ℕ) :
    (physHermite (n + 1) : ℝ → ℝ) = 2 • (fun x => x) *
    (physHermite n : ℝ → ℝ)- (2 * n : ℝ) • (physHermite (n - 1) : ℝ → ℝ) := by
  ext x
  simp [physHermite_succ', aeval, mul_assoc]

lemma physHermite_succ_fun' (n : ℕ) :
    (physHermite (n + 1) : ℝ → ℝ) = fun x => 2 • x *
    physHermite n x -
    (2 * n : ℝ) • physHermite (n - 1) x := by
  ext x
  simp [physHermite_succ', aeval, mul_assoc]

lemma iterated_deriv_physHermite_eq_aeval (n : ℕ) : (m : ℕ) →
    deriv^[m] (physHermite n) = fun x => (derivative^[m] (physHermite n)).aeval x
  | 0 => by simp
  | m + 1 => by
    simp only [Function.iterate_succ_apply']
    rw [iterated_deriv_physHermite_eq_aeval n m]
    funext x
    rw [Polynomial.deriv_aeval]

@[fun_prop]
lemma physHermite_differentiableAt (n : ℕ) (x : ℝ) :
    DifferentiableAt ℝ (physHermite n) x := Polynomial.differentiableAt_aeval (physHermite n)

@[fun_prop]
lemma deriv_physHermite_differentiableAt (n m : ℕ) (x : ℝ) :
    DifferentiableAt ℝ (deriv^[m] (physHermite n)) x := by
  rw [iterated_deriv_physHermite_eq_aeval]
  exact Polynomial.differentiableAt_aeval _

lemma deriv_physHermite (n : ℕ) :
    deriv (physHermite n) = 2 * n * (physHermite (n - 1)) := by
  ext x
  rw [Polynomial.deriv_aeval (physHermite n), derivative_physHermite]
  simp [aeval, mul_assoc]

lemma fderiv_physHermite
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x : E)
    (f : E → ℝ) (hf : DifferentiableAt ℝ f x) (n : ℕ) :
    fderiv ℝ (fun x => physHermite n (f x)) x
    = (2 * n * physHermite (n - 1) (f x)) • fderiv ℝ f x := by
  have h := fderiv_comp (𝕜 := ℝ) (g := physHermite n) (f := f) (hg := by fun_prop)
    (hf := by fun_prop)
  simp +unfoldPartialApp only [Function.comp] at h
  ext dx
  simp only [h, Polynomial.fderiv_aeval, derivative_physHermite, nsmul_eq_mul, map_mul, map_natCast,
    ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, smul_eq_mul, ContinuousLinearMap.coe_smul', Pi.smul_apply]
  rw [aeval, eval₂AlgHom'_apply, eval₂_ofNat]
  ring

@[simp]
lemma deriv_physHermite' (x : ℝ)
    (f : ℝ → ℝ) (hf : DifferentiableAt ℝ f x) (n : ℕ) :
    deriv (fun x => physHermite n (f x)) x
    = (2 * n * physHermite (n - 1) (f x)) * deriv f x := by
  unfold deriv
  rw [fderiv_physHermite (hf := by fun_prop)]
  rfl

lemma physHermite_parity: (n : ℕ) → (x : ℝ) →
    physHermite n (-x) = (-1)^n * physHermite n x
  | 0, x => by simp
  | 1, x => by
    simp [physHermite_one, aeval]
  | n + 2, x => by
    rw [physHermite_succ_fun']
    have h1 := physHermite_parity (n + 1) x
    have h2 := physHermite_parity n x
    simp only [smul_neg, nsmul_eq_mul, cast_ofNat, h1, neg_mul, cast_add, cast_one,
      add_tsub_cancel_right, h2, smul_eq_mul]
    ring

/-!

## Relationship to Gaussians

-/

lemma deriv_gaussian_eq_physHermite_mul_gaussian (n : ℕ) (x : ℝ) :
    deriv^[n] (fun y => Real.exp (- y ^ 2)) x =
    (-1 : ℝ) ^ n * physHermite n x * Real.exp (- x ^ 2) := by
  rw [mul_assoc]
  induction' n with n ih generalizing x
  · rw [Function.iterate_zero_apply, pow_zero, one_mul, physHermite_zero_apply, one_mul]
  · replace ih : deriv^[n] _ = _ := _root_.funext ih
    have deriv_gaussian :
      deriv (fun y => Real.exp (-(y ^ 2))) x = -2 * x * Real.exp (-(x ^ 2)) := by
      rw [deriv_exp (by simp)]
      simp only [deriv.fun_neg', differentiableAt_fun_id, deriv_fun_pow, cast_ofNat,
        Nat.add_one_sub_one, pow_one, deriv_id'', mul_one, mul_neg, neg_mul, neg_inj]
      ring
    rw [Function.iterate_succ_apply', ih, deriv_const_mul_field, deriv_fun_mul, pow_succ (-1 : ℝ),
      deriv_gaussian, physHermite_succ]
    · rw [derivative_physHermite,]
      simp only [neg_mul, mul_neg, mul_one, nsmul_eq_mul, cast_ofNat]
      simp only [Polynomial.deriv_aeval, derivative_physHermite, nsmul_eq_mul, map_mul, map_natCast,
        map_sub, aeval_X]
      simp only [aeval, eval₂AlgHom'_apply, eval₂_ofNat]
      ring
    · exact Polynomial.differentiable_aeval ..
    · simp [DifferentiableAt.exp]

lemma physHermite_eq_deriv_gaussian (n : ℕ) (x : ℝ) :
    physHermite n x = (-1 : ℝ) ^ n * deriv^[n]
    (fun y => Real.exp (- y ^ 2)) x / Real.exp (- x ^ 2) := by
  rw [deriv_gaussian_eq_physHermite_mul_gaussian]
  field_simp [Real.exp_ne_zero]
  simp [← pow_mul]

lemma physHermite_eq_deriv_gaussian' (n : ℕ) (x : ℝ) :
    physHermite n x = (-1 : ℝ) ^ n * deriv^[n] (fun y => Real.exp (- y ^ 2)) x *
    Real.exp (x ^ 2) := by
  rw [physHermite_eq_deriv_gaussian, Real.exp_neg]
  field_simp [Real.exp_ne_zero]

@[fun_prop]
lemma guassian_integrable_polynomial {b : ℝ} (hb : 0 < b) (P : Polynomial ℤ) :
    MeasureTheory.Integrable fun x : ℝ => (P.aeval x) * Real.exp (-b * x ^ 2) := by
  conv =>
    enter [1, x]
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_mul]
  apply MeasureTheory.integrable_finset_sum
  intro i hi
  have h2 : (fun a => P.coeff i • a ^ i * Real.exp (-b * a ^ 2)) =
      (P.coeff i : ℝ) • (fun x => (x ^ (i : ℝ) * Real.exp (-b * x ^ 2))) := by
    funext x
    simp [mul_assoc]
  rw [h2]
  refine MeasureTheory.Integrable.smul (P.coeff i : ℝ) ?_
  apply integrable_rpow_mul_exp_neg_mul_sq
  · exact hb
  · exact lt_of_le_of_lt' (Nat.cast_nonneg' i) neg_one_lt_zero

@[fun_prop]
lemma guassian_integrable_polynomial_cons {b c : ℝ} (hb : 0 < b) (P : Polynomial ℤ) :
    MeasureTheory.Integrable fun x : ℝ => (P.aeval (c * x)) * Real.exp (-b * x ^ 2) := by
  conv =>
    enter [1, x]
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_mul]
  apply MeasureTheory.integrable_finset_sum
  intro i hi
  have h2 : (fun a => P.coeff i • (c * a) ^ i * Real.exp (-b * a ^ 2)) =
      (c ^ i * P.coeff i : ℝ) • (fun x => (x ^ (i : ℝ) * Real.exp (-b * x ^ 2))) := by
    funext x
    simp only [zsmul_eq_mul, neg_mul, mul_assoc, Real.rpow_natCast, Pi.smul_apply, smul_eq_mul]
    ring
  refine h2 ▸ MeasureTheory.Integrable.smul (c ^ i * P.coeff i : ℝ) ?_
  apply integrable_rpow_mul_exp_neg_mul_sq (s := i)
  · exact hb
  · exact lt_of_le_of_lt' (Nat.cast_nonneg' i) neg_one_lt_zero

@[fun_prop]
lemma physHermite_gaussian_integrable (n p m : ℕ) :
    MeasureTheory.Integrable (deriv^[m] (physHermite p) * deriv^[n] fun x => Real.exp (-x ^ 2))
    MeasureTheory.volume := by
  have h1 : (deriv^[m] (physHermite p) * deriv^[n] fun x => Real.exp (-x ^ 2))
    = deriv^[m] (physHermite p) *
    ((-1 : ℝ) ^ n • physHermite n * (fun x => Real.exp (- x ^ 2))) := by
    funext x
    simp only [Pi.mul_apply, deriv_gaussian_eq_physHermite_mul_gaussian, Algebra.smul_mul_assoc,
      Pi.smul_apply, smul_eq_mul, mul_eq_mul_left_iff]
    ring_nf
    left
    trivial
  rw [h1]
  simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
  refine MeasureTheory.Integrable.smul ((-1) ^ n) ?_
  have h2 : deriv^[m] (physHermite p) * (physHermite n : ℝ → ℝ) =
      fun x => (derivative^[m] (physHermite p) * physHermite n).aeval x := by
    rw [iterated_deriv_physHermite_eq_aeval]
    funext x
    simp
  conv =>
    enter [1, x]
    rw [← mul_assoc, h2]
  have h0 : ((fun x => (aeval x)
      ((⇑derivative)^[m] (physHermite p) * physHermite n)) * fun x => Real.exp (-x ^ 2))
      = fun x => ((⇑derivative)^[m] (physHermite p) * physHermite n).aeval x *
      Real.exp (- (1 : ℝ) * x ^ 2) := by
    funext x
    simp
  exact h0 ▸ guassian_integrable_polynomial Real.zero_lt_one ..

lemma integral_physHermite_mul_physHermite_eq_integral_deriv_exp (n m : ℕ) :
    ∫ x : ℝ, (physHermite n x * physHermite m x) * Real.exp (-x ^ 2) =
    (-1 : ℝ) ^ m * ∫ x : ℝ, (physHermite n x * (deriv^[m] fun x => Real.exp (-x ^ 2)) x) := by
  have h1 (x : ℝ) : (physHermite n x * physHermite m x) * Real.exp (-x ^ 2)
    = (-1 : ℝ) ^ m * (physHermite n x * (deriv^[m] fun x => Real.exp (-x ^ 2)) x) := by
    conv_lhs =>
      enter [1, 2]
      rw [physHermite_eq_deriv_gaussian']
    rw [mul_assoc, mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    ring
  simp only [h1]
  exact MeasureTheory.integral_const_mul ((-1) ^ m) fun a =>
      physHermite n a * deriv^[m] (fun x => Real.exp (-x ^ 2)) a

lemma integral_physHermite_mul_physHermite_eq_integral_deriv_inductive (n m : ℕ) :
    (p : ℕ) → (hpm : p ≤ m) →
    ∫ x : ℝ, (physHermite n x * physHermite m x) * Real.exp (- x ^ 2) =
    (-1 : ℝ) ^ (m - p) * ∫ x : ℝ, (deriv^[p] (physHermite n) x *
    (deriv^[m - p] fun x => Real.exp (-x ^ 2)) x)
  | 0, h => by
    exact integral_physHermite_mul_physHermite_eq_integral_deriv_exp n m
  | p + 1, h => by
    rw [integral_physHermite_mul_physHermite_eq_integral_deriv_inductive n m p (by omega)]
    have h1 : m - p = m - (p + 1) + 1 := by omega
    rw [h1, Function.iterate_succ_apply']
    conv_rhs => rw [Function.iterate_succ_apply']
    have h1 : (-1 : ℝ) ^ (m - (p + 1) + 1) = (-1) ^ (m - (p + 1)) * (-1) := by simp [pow_add]
    rw [h1, mul_assoc]
    congr
    have hl : ∫ (x : ℝ), deriv^[p] (physHermite n) x *
        deriv (deriv^[m - (p + 1)] fun x => Real.exp (-x ^ 2)) x =
        - ∫ (x : ℝ), deriv (deriv^[p] (physHermite n)) x *
        deriv^[m - (p + 1)] (fun x => Real.exp (-x ^ 2)) x := by
      apply MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
      · exact fun _ ↦ DifferentiableAt.hasDerivAt (deriv_physHermite_differentiableAt n p _)
      · intro x
        simp only [hasDerivAt_deriv_iff]
        have h1 : (deriv^[m - (p + 1)] fun x => Real.exp (-x ^ 2)) =
            fun x => (-1 : ℝ) ^ (m - (p + 1)) * physHermite (m - (p + 1)) x *
            Real.exp (- x ^ 2) := by
          funext x
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
  simp [integral_physHermite_mul_physHermite_eq_integral_deriv_inductive n m m (by rfl)]

lemma physHermite_orthogonal_lt {n m : ℕ} (hnm : n < m) :
    ∫ x : ℝ, (physHermite n x * physHermite m x) * Real.exp (- x ^ 2) = 0 := by
  rw [integral_physHermite_mul_physHermite_eq_integral_deriv]
  simp [iterated_deriv_physHermite_eq_aeval, iterate_derivative_physHermite_of_gt hnm]

theorem physHermite_orthogonal {n m : ℕ} (hnm : n ≠ m) :
    ∫ x : ℝ, (physHermite n x * physHermite m x) * Real.exp (- x ^ 2) = 0 := by
  by_cases hnm' : n < m
  · exact physHermite_orthogonal_lt hnm'
  · have hmn : m < n := by omega
    conv_lhs =>
      enter [2, x, 1]
      rw [mul_comm]
    rw [physHermite_orthogonal_lt hmn]

lemma physHermite_orthogonal_cons {n m : ℕ} (hnm : n ≠ m) (c : ℝ) :
    ∫ x : ℝ, (physHermite n (c * x) * physHermite m (c * x)) *
    Real.exp (- c ^ 2 * x ^ 2) = 0 := by
  trans ∫ x : ℝ, (fun x => (physHermite n x * physHermite m x) * Real.exp (- x^2)) (c * x)
  · congr
    funext x
    simp only [neg_mul, mul_eq_mul_left_iff, Real.exp_eq_exp, neg_inj, _root_.mul_eq_zero]
    left
    exact Eq.symm (mul_pow c x 2)
  rw [MeasureTheory.Measure.integral_comp_mul_left
    (fun x => physHermite n x * physHermite m x * Real.exp (-x ^ 2)) c]
  rw [physHermite_orthogonal hnm]
  simp

theorem physHermite_norm (n : ℕ) :
    ∫ x : ℝ, (physHermite n x * physHermite n x) * Real.exp (- x ^ 2) =
    ↑n ! * 2 ^ n * √Real.pi := by
  rw [integral_physHermite_mul_physHermite_eq_integral_deriv, iterated_deriv_physHermite_eq_aeval]
  simp only [iterate_derivative_physHermite_self]
  conv_lhs =>
    enter [2, x]
    rw [aeval_C]
    simp
  rw [MeasureTheory.integral_const_mul]
  have h1 : ∫ (x : ℝ), Real.exp (- x^2) = Real.sqrt (Real.pi) := by
    trans ∫ (x : ℝ), Real.exp (- 1 * x^2)
    · simp
    rw [integral_gaussian]
    simp
  rw [h1]

lemma physHermite_norm_cons (n : ℕ) (c : ℝ) :
    ∫ x : ℝ, (physHermite n (c * x) * physHermite n (c * x)) * Real.exp (- c ^ 2 * x ^ 2) =
    |c⁻¹| • (↑n ! * 2 ^ n * √Real.pi) := by
  trans ∫ x : ℝ, (fun x => (physHermite n x * physHermite n x) * Real.exp (- x^2)) (c * x)
  · congr
    funext x
    simp only [neg_mul, mul_eq_mul_left_iff, Real.exp_eq_exp, neg_inj, _root_.mul_eq_zero, or_self]
    left
    exact Eq.symm (mul_pow c x 2)
  rw [MeasureTheory.Measure.integral_comp_mul_left
    (fun x => physHermite n x * physHermite n x * Real.exp (-x ^ 2)) c]
  rw [physHermite_norm]

lemma polynomial_mem_physHermite_span_induction (P : Polynomial ℤ) : (n : ℕ) →
    (hn : P.natDegree = n) →
    (P : ℝ → ℝ) ∈ Submodule.span ℝ (Set.range (fun n => (physHermite n : ℝ → ℝ)))
  | 0, h => by
    rw [natDegree_eq_zero] at h
    obtain ⟨x, rfl⟩ := h
    refine Finsupp.mem_span_range_iff_exists_finsupp.mpr ?_
    use Finsupp.single 0 x
    funext y
    simp
  | n + 1, h => by
    by_cases hP0 : P = 0
    · subst hP0
      simp only [map_zero]
      change 0 ∈ _
      exact Submodule.zero_mem (Submodule.span ℝ (Set.range (fun n => (physHermite n : ℝ → ℝ))))
    let P' := ((coeff (physHermite (n + 1)) (n + 1)) • P -
        (coeff P (n + 1)) • physHermite (n + 1))
    have hP'mem : (fun x => P'.aeval x) ∈ Submodule.span ℝ
        (Set.range (fun n => (physHermite n : ℝ → ℝ))) := by
      by_cases hP' : P' = 0
      · rw [hP']
        simp only [map_zero]
        change 0 ∈ _
        exact Submodule.zero_mem (Submodule.span ℝ (Set.range (fun n => (physHermite n : ℝ → ℝ))))
      · exact polynomial_mem_physHermite_span_induction P' P'.natDegree (by rfl)
    simp only [P'] at hP'mem
    have hl : (fun x => (aeval x) ((physHermite (n + 1)).coeff (n + 1) • P -
        P.coeff (n + 1) • physHermite (n + 1)))
        = (2 ^ (n + 1) : ℝ) • (fun (x : ℝ) => (aeval x) P) - ↑(P.coeff (n + 1) : ℝ) •
        (fun (x : ℝ)=> (aeval x) (physHermite (n + 1))) := by
      funext x
      simp only [coeff_physHermite_self_succ, zsmul_eq_mul, Int.cast_pow, Int.cast_ofNat, map_sub,
        map_mul, map_pow, map_intCast, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_left_inj,
        mul_eq_mul_right_iff]
      simp [aeval]
    rw [hl] at hP'mem
    rw [Submodule.sub_mem_iff_left] at hP'mem
    · rw [Submodule.smul_mem_iff] at hP'mem
      · exact hP'mem
      · simp
    apply Submodule.smul_mem
    refine Finsupp.mem_span_range_iff_exists_finsupp.mpr ?_
    use Finsupp.single (n + 1) 1
    simp
decreasing_by
  rw [Polynomial.natDegree_lt_iff_degree_lt]
  · apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
    intro m hm'
    simp only [coeff_physHermite_self_succ, coeff_sub]
    change n + 1 ≤ m at hm'
    rw [coeff_smul, coeff_smul]
    by_cases hm : m = n + 1
    · subst hm
      simp only [smul_eq_mul, coeff_physHermite_self_succ]
      ring
    · rw [coeff_eq_zero_of_degree_lt, coeff_eq_zero_of_degree_lt (n := m)]
      · simp only [smul_eq_mul, mul_zero, sub_self]
      · rw [← Polynomial.natDegree_lt_iff_degree_lt]
        · simp only [natDegree_physHermite]
          omega
        · simp
      · rw [← Polynomial.natDegree_lt_iff_degree_lt]
        · omega
        · exact hP0
  · exact hP'

lemma polynomial_mem_physHermite_span (P : Polynomial ℤ) :
    (P : ℝ → ℝ) ∈ Submodule.span ℝ (Set.range (fun n => (physHermite n : ℝ → ℝ))) :=
  polynomial_mem_physHermite_span_induction P P.natDegree rfl

lemma cos_mem_physHermite_span_topologicalClosure (c : ℝ) :
    (fun (x : ℝ) => Real.cos (c * x)) ∈
    (Submodule.span ℝ (Set.range (fun n => (physHermite n : ℝ → ℝ)))).topologicalClosure := by
  change (fun (x : ℝ) => Real.cos (c * x)) ∈
    closure (Submodule.span ℝ (Set.range (fun n => (physHermite n : ℝ → ℝ))))
  have h1 := Real.hasSum_cos
  simp only [HasSum] at h1
  have h1 : Filter.Tendsto
      (fun s => fun y => ∑ x ∈ s, (-1) ^ x * (c * y) ^ (2 * x) / ((2 * x)! : ℝ))
    Filter.atTop (nhds (fun x => Real.cos (c * x))) := by
    exact tendsto_pi_nhds.mpr fun x => h1 (c * x)
  have h2 (z : Finset ℕ) : (fun y => ∑ x ∈ z, (-1) ^ x * (c * y) ^ (2 * x) / ↑(2 * x)!) ∈
      ↑(Submodule.span ℝ (Set.range (fun n => (physHermite n : ℝ → ℝ)))) := by
    have h0 : (fun y => ∑ x ∈ z, (-1) ^ x * (c * y) ^ (2 * x) / ↑(2 * x)!) =
      ∑ x ∈ z, (((-1) ^ x * c ^ (2 * x) / ↑(2 * x)!) • fun (y : ℝ) => (y) ^ (2 * x)) := by
      funext y
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      congr
      funext z
      ring
    rw [h0]
    apply Submodule.sum_mem
    intro l hl
    apply Submodule.smul_mem
    let P : Polynomial ℤ := X ^ (2 * l)
    have hy : (fun y => y ^ (2 * l)) = (fun (y : ℝ) => P.aeval y) := by
      funext y
      simp [P]
    exact hy ▸ polynomial_mem_physHermite_span P
  exact mem_closure_of_tendsto h1 (Filter.Eventually.of_forall h2)

end PhysLean
