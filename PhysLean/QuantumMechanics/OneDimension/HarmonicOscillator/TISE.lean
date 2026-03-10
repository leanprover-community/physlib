/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.QuantumMechanics.OneDimension.HarmonicOscillator.Eigenfunction
/-!

# The time-independent Schrodinger equation

-/

@[expose] public section

namespace QuantumMechanics

namespace OneDimension
namespace HarmonicOscillator

variable (Q : HarmonicOscillator)

open Nat PhysLean HilbertSpace Constants

/-- The `n`th eigenvalues for a Harmonic oscillator is defined as `(n + 1/2) * ℏ * ω`. -/
noncomputable def eigenValue (n : ℕ) : ℝ := (n + 1/2) * ℏ * Q.ω

/-!

## Derivatives of the eigenfunctions

-/

lemma deriv_eigenfunction_zero : deriv (Q.eigenfunction 0) =
    Complex.ofReal (- 1 / Q.ξ ^2) • Complex.ofReal * Q.eigenfunction 0 := by
  rw [eigenfunction_zero]
  simp only [deriv_const_mul_field', Complex.ofReal_div, Complex.ofReal_neg, Algebra.smul_mul_assoc]
  ext x
  have h1 : deriv (fun (x : ℝ) => Complex.exp (- x ^ 2 / (2 * Q.ξ ^ 2))) x =
      - x /Q.ξ^2 * Complex.exp (- x ^ 2 / (2 * Q.ξ ^ 2)) := by
    trans deriv (Complex.exp ∘ (fun (x : ℝ) => - x ^ 2 / (2 * Q.ξ ^ 2))) x
    · rfl
    rw [deriv_comp]
    simp only [Complex.deriv_exp, deriv_div_const, deriv.fun_neg']
    have h1' : deriv (fun x => (Complex.ofReal x) ^ 2) x = 2 * x := by
      trans deriv (fun x => Complex.ofReal x * Complex.ofReal x) x
      · apply congr
        apply congrArg
        funext x
        ring
        rfl
      rw [deriv_fun_mul]
      simp only [Complex.deriv_ofReal, one_mul, mul_one]
      ring
      · exact Complex.differentiableAt_ofReal
      · exact Complex.differentiableAt_ofReal
    rw [h1']
    field_simp
    ring_nf
    exact Complex.differentiableAt_exp
    refine DifferentiableAt.mul_const ?_ _
    refine differentiableAt_neg_iff.mpr ?_
    refine DifferentiableAt.pow ?_ 2
    exact Complex.differentiableAt_ofReal
  simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
  rw [h1]
  simp only [Real.sqrt_nonneg, Real.sqrt_mul, Complex.ofReal_mul, one_div, mul_inv_rev,
    Complex.ofReal_one, Complex.ofReal_pow]
  ring

lemma deriv_eigenfunction_zero' : deriv (Q.eigenfunction 0) =
    (- √2 / (2 * Q.ξ) : ℂ) • Q.eigenfunction 1 := by
  rw [deriv_eigenfunction_zero]
  funext x
  simp only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_pow,
    eigenfunction_eq, pow_zero, factorial_zero, cast_one, mul_one, Real.sqrt_one, ne_eq,
    one_ne_zero, not_false_eq_true, div_self, Real.sqrt_nonneg, Real.sqrt_mul, Complex.ofReal_mul,
    one_div, mul_inv_rev, one_mul, Polynomial.aeval, physHermite_zero, eq_intCast, Int.cast_one,
    Polynomial.eval₂AlgHom'_apply, Polynomial.eval₂_one, Complex.ofReal_exp, Complex.ofReal_ofNat,
    Pi.mul_apply, Pi.smul_apply, smul_eq_mul, pow_one, factorial_one, physHermite_one,
    Polynomial.eval₂_mul, Polynomial.eval₂_ofNat, Polynomial.eval₂_X]
  ring_nf
  simp

lemma deriv_physHermite_characteristic_length (n : ℕ) :
    deriv (fun x => Complex.ofReal (physHermite n (x/Q.ξ))) = fun x =>
    Complex.ofReal (1/Q.ξ) * 2 * n * physHermite (n-1) (x/Q.ξ) := by
  match n with
  | 0 =>
    rw [physHermite_zero]
    simp only [map_one, Complex.ofReal_one, deriv_const', one_div,
      Complex.ofReal_inv, CharP.cast_eq_zero, mul_zero, mul_one]
  | n + 1 =>
    funext x
    trans deriv (Complex.ofReal ∘ physHermite (n + 1) ∘
      fun (x : ℝ) => ((1/Q.ξ) * x)) x
    · congr
      funext x
      simp only [one_div, Function.comp_apply, Complex.ofReal_inj]
      ring_nf
    rw [fderiv_comp_deriv _ (by fun_prop) (by fun_prop)]
    rw [fderiv_comp_deriv _ (by fun_prop) (by fun_prop)]
    simp only [Function.comp_apply, fderiv_eq_smul_deriv, smul_eq_mul, Complex.deriv_ofReal,
      Complex.real_smul, Complex.ofReal_mul, mul_one]
    rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
    simp only [deriv_const', zero_mul, deriv_id'', mul_one, zero_add]
    rw [deriv_physHermite]
    simp only [Pi.natCast_def, Pi.mul_apply, Pi.ofNat_apply, Complex.ofReal_mul,
      Complex.ofReal_ofNat, Complex.ofReal_natCast]
    simp only [cast_add, cast_one, add_tsub_cancel_right]
    ring_nf

lemma deriv_eigenfunction_succ (n : ℕ) :
    deriv (Q.eigenfunction (n + 1)) = fun x =>
    Complex.ofReal (1/√(2 ^ (n + 1) * (n + 1)!) * (1/Q.ξ)) •
    ((2 * (n + 1) * physHermite n (x/Q.ξ)
      - (x/Q.ξ) * physHermite (n + 1) (x/Q.ξ)) * Q.eigenfunction 0 x) := by
  funext x
  rw [eigenfunction_eq_mul_eigenfunction_zero]
  rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
  rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
  simp only [ofNat_nonneg, pow_nonneg, Real.sqrt_mul, one_div, mul_inv_rev, Complex.ofReal_mul,
    Complex.ofReal_inv, deriv_const', zero_mul, zero_add, smul_eq_mul]
  rw [deriv_physHermite_characteristic_length, deriv_eigenfunction_zero]
  simp only [one_div, Complex.ofReal_inv, cast_add, cast_one, add_tsub_cancel_right,
    Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_pow, Pi.mul_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

/-!

## Second derivatives of the eigenfunctions.

-/

lemma deriv_deriv_eigenfunction_zero (x : ℝ) : deriv (deriv (Q.eigenfunction 0)) x =
    (- 1 / Q.ξ^2) * (1 + ((- 1/ Q.ξ^2) * x ^ 2)) * Q.eigenfunction 0 x := by
  simp only [deriv_eigenfunction_zero, Complex.ofReal_div, Complex.ofReal_neg,
    Algebra.smul_mul_assoc]
  trans deriv (fun x => (- (1/Q.ξ^2)) • (Complex.ofReal x * Q.eigenfunction 0 x)) x
  · congr
    funext x
    simp only [Complex.ofReal_one, Complex.ofReal_pow, Pi.smul_apply, Pi.mul_apply, smul_eq_mul,
      one_div, neg_smul, Complex.real_smul, Complex.ofReal_inv]
    ring
  simp only [Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_div, deriv_const_mul_field']
  rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
  simp only [Complex.deriv_ofReal]
  rw [deriv_eigenfunction_zero]
  simp only [Complex.ofReal_div, Complex.ofReal_neg, Pi.mul_apply, Pi.smul_apply, smul_eq_mul,
    neg_mul]
  ring_nf
  simp only [Complex.ofReal_one, Complex.ofReal_pow, one_mul, one_pow, inv_pow]
  ring

lemma deriv_deriv_eigenfunction_succ (n : ℕ) (x : ℝ) :
    deriv (fun x => deriv (Q.eigenfunction (n + 1)) x) x =
    Complex.ofReal (1/√(2 ^ (n + 1) * (n + 1) !) * (1/Q.ξ)) *
      ((2 * (↑n + 1) * deriv (fun x => ↑(physHermite n (x/Q.ξ))) x +
      (-(1/Q.ξ^2)) * (4 * (↑n + 1) * x) *
      (physHermite n (x/Q.ξ)) + (- (1/Q.ξ)) * (1 + (- (1/Q.ξ^2)) * x ^ 2) *
      (physHermite (n + 1) (x/Q.ξ))) * Q.eigenfunction 0 x) := by
  rw [deriv_eigenfunction_succ]
  simp only [ofNat_nonneg, pow_nonneg, Real.sqrt_mul, one_div, mul_inv_rev, Complex.ofReal_mul,
    Complex.ofReal_inv, smul_eq_mul, deriv_const_mul_field', neg_mul, mul_eq_mul_left_iff,
    _root_.mul_eq_zero, inv_eq_zero, Complex.ofReal_eq_zero, cast_nonneg, Real.sqrt_eq_zero,
    cast_eq_zero, ne_eq, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, not_false_eq_true,
    pow_eq_zero_iff, OfNat.ofNat_ne_zero, or_false, ξ_ne_zero]
  left
  rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
  rw [deriv_eigenfunction_zero]
  simp only [Complex.ofReal_div, Complex.ofReal_neg, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, ←
    mul_assoc, ← add_mul, mul_eq_mul_right_iff]
  left
  rw [deriv_fun_sub (by fun_prop) (by fun_prop)]
  rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
  simp only [deriv_const', zero_mul, zero_add]
  rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
  simp only [deriv_div_const, Complex.deriv_ofReal, one_div, Complex.ofReal_one, Complex.ofReal_pow]
  nth_rewrite 2 [deriv_physHermite_characteristic_length]
  simp only [one_div, Complex.ofReal_inv, cast_add, cast_one, add_tsub_cancel_right]
  ring

lemma deriv_deriv_eigenfunction (n : ℕ) (x : ℝ) :
    deriv (fun x => deriv (Q.eigenfunction n) x) x = (- 1 / Q.ξ^2) * ((2 * n + 1)
    + ((- 1/ Q.ξ^2) * x ^ 2)) * Q.eigenfunction n x := by
  match n with
  | 0 => simpa using Q.deriv_deriv_eigenfunction_zero x
  | n + 1 =>
    trans Complex.ofReal (1/Real.sqrt (2 ^ (n + 1) * (n + 1) !)) *
        (((- 1 / Q.ξ ^ 2) * (2 * (n + 1)
        + (1 + (- 1/ Q.ξ ^ 2) * x ^ 2)) *
        (physHermite (n + 1) (x/Q.ξ))) * Q.eigenfunction 0 x)
    · rw [deriv_deriv_eigenfunction_succ]
      rw [Complex.ofReal_mul, mul_assoc]
      congr 1
      rw [← mul_assoc]
      congr 1
      trans ((1 / Q.ξ) * 2 * (n + 1) * ((1 / Q.ξ) *
        2 * n * (physHermite (n - 1) (x/Q.ξ))) +
        (- (1 / Q.ξ^2)) * (1/Q.ξ) * (4 * (n + 1) * x) *
        (physHermite n (x/Q.ξ)) +
        (- (1/Q.ξ^2)) * (1 + (-(1/Q.ξ^2)) * x ^ 2) *
        (physHermite (n + 1) (x/Q.ξ)))
      · rw [deriv_physHermite_characteristic_length]
        simp only [one_div, Complex.ofReal_inv, neg_mul]
        ring
      trans ((1/ Q.ξ^2) * 2 * (n + 1) * (2 * n *
          (physHermite (n - 1) (x/Q.ξ))) +
          (- 1 / Q.ξ^2) * (1/Q.ξ) * (4 * (n + 1) * x) *
          (physHermite n (x/Q.ξ)) +
          (- 1/ Q.ξ^2) * (1 + (- 1 / Q.ξ^2) * x ^ 2) *
          (physHermite (n + 1) ((1/Q.ξ) * x)))
      · ring_nf
      trans (- 1/ Q.ξ^2) * (2 * (n + 1) *
            (2 * ((1 / Q.ξ) * x) * (physHermite n (x/Q.ξ)) -
            2 * n * (physHermite (n - 1) (x/Q.ξ)))
            + (1 + (- 1 / Q.ξ^2) * x ^ 2) * (physHermite (n + 1) (x/Q.ξ)))
      · ring_nf
      trans (- 1 / Q.ξ^2) * (2 * (n + 1) * (physHermite (n + 1) (x/Q.ξ))
            + (1 + (- 1/ Q.ξ^2) * x ^ 2) * (physHermite (n + 1) (x/Q.ξ)))
      · congr
        conv_rhs =>
          rw [physHermite_succ]
        simp only [nsmul_eq_mul, cast_ofNat, derivative_physHermite, map_sub, map_mul,
          Polynomial.aeval_X, map_natCast, Complex.ofReal_sub, Complex.ofReal_mul,
          Complex.ofReal_natCast]
        rw [show (Polynomial.aeval (x / Q.ξ)) 2 = 2 by simp [Polynomial.aeval]]
        simp only [one_div, Complex.ofReal_ofNat, Complex.ofReal_div]
        field_simp
      ring
    · rw [Q.eigenfunction_eq_mul_eigenfunction_zero (n + 1)]
      simp only [ofNat_nonneg, pow_nonneg, Real.sqrt_mul, one_div, mul_inv_rev, Complex.ofReal_mul,
        Complex.ofReal_inv, cast_add, cast_one]
      ring

/-!

## Application of the schrodingerOperator
-/

/-- The `n`th eigenfunction satisfies the time-independent Schrodinger equation with
  respect to the `n`th eigenvalue. That is to say for `Q` a harmonic oscillator,

  `Q.schrodingerOperator (Q.eigenfunction n) x = Q.eigenValue n * Q.eigenfunction n x`.

  The proof of this result is done by explicit calculation of derivatives.
-/
lemma schrodingerOperator_eigenfunction (n : ℕ) (x : ℝ) :
    Q.schrodingerOperator (Q.eigenfunction n) x = Q.eigenValue n * Q.eigenfunction n x := by
  simp only [schrodingerOperator_eq_ξ, one_div]
  rw [Q.deriv_deriv_eigenfunction]
  have hm' := Complex.ofReal_ne_zero.mpr (Ne.symm (_root_.ne_of_lt Q.hm))
  have hℏ' := Complex.ofReal_ne_zero.mpr ℏ_ne_zero
  rw [eigenValue]
  simp only [← Complex.ofReal_pow, ξ_sq]
  simp only [Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_mul, inv_div, one_div,
    Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_inv, Complex.ofReal_ofNat]
  field_simp
  ring

open Filter Finset

open InnerProductSpace

end HarmonicOscillator
end OneDimension
end QuantumMechanics
