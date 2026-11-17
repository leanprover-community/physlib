/-
Copyright (c) 2026 Emil Kubanychbek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emil Kubanychbek
-/
module

public import Physlib.QuantumMechanics.PoschlTeller.Basic
/-!

# Scattering states of the 1d Pöschl-Teller system

The polynomials describing the scattering states of the Pöschl-Teller system.

## i. Overview

At energy `E = ℏ² k² / (2 m)` the scattering states of the Pöschl-Teller system are of the form
`ψₖ(x) = Pₖ(tanh (κ x)) e^{i k x}`, where the polynomial `Pₖ` is obtained by applying the
operators `-∂ₓ + n κ tanh (κ x)`, for `n = 1, …, N`, to the plane wave `e^{i k x}`. The operator
`-∂ₓ + n κ tanh (κ x)` intertwines the Hamiltonians of the Pöschl-Teller systems with family
numbers `n - 1` and `n`, so it maps solutions of the one to solutions of the other at the same
energy.

This file works with the polynomial in `tanh (κ x)` multiplying `e^{i k x}`, as an element of
`ℂ[X]`. The derivative, the raising operators and the Hamiltonian become operators on `ℂ[X]`, and
the intertwining relation becomes an identity of polynomials.

## ii. Key results

- `polyReducedHamiltonian_polyRaise` : the raising operator intertwines the Hamiltonians with family
  numbers `n` and `n + 1`.
- `polyReducedHamiltonian_polyScattering` : the scattering polynomial `Pₖ` is an eigenvector of the
  reduced Hamiltonian with eigenvalue `k²`.
- `polyScattering_eval_one`, `polyScattering_eval_neg_one` : the values `Pₖ(1) = ∏ₙ (n κ - i k)`
  and `Pₖ(-1) = ∏ₙ (-n κ - i k)`.

## iii. Table of contents

- A. Polynomials in `tanh (κ x)`
  - A.1. Derivative, raising operator and Hamiltonian
  - A.2. The intertwining relation
  - A.3. The scattering polynomials
  - A.4. Values at `±1`

## iv. References

* https://arxiv.org/pdf/2411.14941. [ref: arxiv_2411_14941]
-/
@[expose] public section

noncomputable section

namespace QuantumMechanics

namespace PoschlTeller

open Complex Polynomial

variable (Q : PoschlTeller)

/-!
## A. Polynomials in `tanh (κ x)`
-/

/-!
### A.1. Derivative, raising operator and Hamiltonian
-/

/-- The derivative acting on the polynomial of a wave `p(tanh (κ x)) e^{i k x}`,
  `p ↦ κ (1 - X²) p' + i k p`, so that
  `∂ₓ (p(tanh (κ x)) e^{i k x}) = (polyDeriv k p)(tanh (κ x)) e^{i k x}`. -/
def polyDeriv (k : ℝ) (p : ℂ[X]) : ℂ[X] :=
  C (Q.κ : ℂ) * (1 - X ^ 2) * derivative p + C (k * I) * p

/-- The raising operator `-∂ₓ + n κ tanh (κ x)` acting on the polynomial of a wave
  `p(tanh (κ x)) e^{i k x}`. -/
def polyRaise (k : ℝ) (n : ℕ) (p : ℂ[X]) : ℂ[X] := -Q.polyDeriv k p + C (n * Q.κ : ℂ) * X * p

/-- The operator `-∂ₓ² - n (n + 1) κ² / cosh² (κ x)` acting on the polynomial of a wave
  `p(tanh (κ x)) e^{i k x}`. This is `2 m / ℏ²` times the Hamiltonian of the Pöschl-Teller system
  with family number `n`. -/
def polyReducedHamiltonian (k : ℝ) (n : ℕ) (p : ℂ[X]) : ℂ[X] :=
  -Q.polyDeriv k (Q.polyDeriv k p) - C ((Q.κ : ℂ) ^ 2 * n * (n + 1)) * (1 - X ^ 2) * p

/-!
### A.2. The intertwining relation
-/

/-- The raising operator intertwines the Hamiltonians with family numbers `n` and `n + 1`. -/
lemma polyReducedHamiltonian_polyRaise (k : ℝ) (n : ℕ) (p : ℂ[X]) :
    Q.polyReducedHamiltonian k (n + 1) (Q.polyRaise k (n + 1) p) =
      Q.polyRaise k (n + 1) (Q.polyReducedHamiltonian k n p) := by
  simp only [polyReducedHamiltonian, polyRaise, polyDeriv, derivative_mul, derivative_add,
    derivative_sub, derivative_neg, derivative_C, derivative_X, derivative_X_sq, derivative_one,
    derivative_zero]
  simp only [map_mul, map_pow, map_add, map_natCast, map_one, map_ofNat, Nat.cast_add,
    Nat.cast_one]
  ring

/-- The derivative of a constant multiple of the plane wave `c e^{i k x}` is `i k c e^{i k x}`. -/
lemma polyDeriv_C (k : ℝ) (c : ℂ) : Q.polyDeriv k (C c) = C (k * I * c) := by
  simp only [polyDeriv, derivative_C, mul_zero, zero_add, C_mul]

/-- The raising operator is linear with respect to constant multiples. -/
lemma polyRaise_C_mul (k : ℝ) (n : ℕ) (c : ℂ) (p : ℂ[X]) :
    Q.polyRaise k n (C c * p) = C c * Q.polyRaise k n p := by
  simp only [polyRaise, polyDeriv, derivative_mul, derivative_C, zero_mul, zero_add]
  ring

/-!
### A.3. The scattering polynomials
-/

/-- The polynomial `Pₖ` of the scattering state `Pₖ(tanh (κ x)) e^{i k x}` of the Pöschl-Teller
  system with family number `n`, obtained by applying the raising operators with
  `1, …, n` to `1`. -/
def polyScattering (k : ℝ) : ℕ → ℂ[X]
  | 0 => 1
  | n + 1 => Q.polyRaise k (n + 1) (polyScattering k n)

/-- The scattering polynomial with family number `n` is an eigenvector of the reduced Hamiltonian
  with eigenvalue `k²`. -/
lemma polyReducedHamiltonian_polyScattering (k : ℝ) (n : ℕ) :
    Q.polyReducedHamiltonian k n (Q.polyScattering k n) =
      C ((k : ℂ) ^ 2) * Q.polyScattering k n := by
  induction n with
  | zero =>
    rw [polyScattering, polyReducedHamiltonian, ← C_1, Q.polyDeriv_C, Q.polyDeriv_C]
    simp only [Nat.cast_zero, mul_zero, zero_mul, map_zero, sub_zero, ← C_neg, ← C_mul]
    congr 1
    linear_combination (-(k : ℂ) ^ 2) * I_sq
  | succ n ih => rw [polyScattering, polyReducedHamiltonian_polyRaise, ih, polyRaise_C_mul]

/-!
### A.4. Values at `±1`
-/

/-- At `tanh (κ x) = 1` the raising operator acts as multiplication by `n κ - i k`. -/
lemma eval_one_polyRaise (k : ℝ) (n : ℕ) (p : ℂ[X]) :
    (Q.polyRaise k n p).eval 1 = (n * Q.κ - k * I) * p.eval 1 := by
  simp only [polyRaise, polyDeriv, map_mul, neg_add_rev, map_natCast, eval_add, eval_neg, eval_mul,
    eval_C, eval_sub, eval_one, eval_pow, eval_X, one_pow, sub_self, mul_zero, zero_mul, neg_zero,
    add_zero, eval_natCast, mul_one]
  ring

/-- At `tanh (κ x) = -1` the raising operator acts as multiplication by `-n κ - i k`. -/
lemma eval_neg_one_polyRaise (k : ℝ) (n : ℕ) (p : ℂ[X]) :
    (Q.polyRaise k n p).eval (-1) = (-(n * Q.κ) - k * I) * p.eval (-1) := by
  simp only [polyRaise, polyDeriv, map_mul, neg_add_rev, map_natCast, eval_add, eval_neg, eval_mul,
    eval_C, eval_sub, eval_one, eval_pow, eval_X, even_two, Even.neg_pow, one_pow, sub_self,
    mul_zero, zero_mul, neg_zero, add_zero, eval_natCast, mul_neg, mul_one, neg_mul]
  ring

/-- The value at `1` of the scattering polynomial is `∏ₙ (n κ - i k)`. -/
lemma polyScattering_eval_one (k : ℝ) (n : ℕ) :
    (Q.polyScattering k n).eval 1 = ∏ j ∈ Finset.range n, ((j + 1) * Q.κ - k * I) := by
  induction n with
  | zero => simp only [polyScattering, eval_one, Finset.range_zero, Finset.prod_empty]
  | succ n ih =>
    rw [polyScattering, eval_one_polyRaise, ih, Finset.prod_range_succ]
    push_cast
    ring

/-- The value at `-1` of the scattering polynomial is `∏ₙ (-n κ - i k)`. -/
lemma polyScattering_eval_neg_one (k : ℝ) (n : ℕ) :
    (Q.polyScattering k n).eval (-1) = ∏ j ∈ Finset.range n, (-((j + 1) * Q.κ) - k * I) := by
  induction n with
  | zero => simp only [polyScattering, eval_one, Finset.range_zero, Finset.prod_empty]
  | succ n ih =>
    rw [polyScattering, eval_neg_one_polyRaise, ih, Finset.prod_range_succ]
    push_cast
    ring

/-- The value at `1` of the scattering polynomial is non-zero. -/
lemma polyScattering_eval_one_ne_zero (k : ℝ) (n : ℕ) : (Q.polyScattering k n).eval 1 ≠ 0 := by
  rw [polyScattering_eval_one, Finset.prod_ne_zero_iff]
  intro j _ hj
  have hre := congrArg Complex.re hj
  simp only [sub_re, mul_re, add_re, natCast_re, one_re, ofReal_re, ofReal_im, I_re, I_im,
    zero_re] at hre
  have := Q.κ_pos
  nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]

/-- The value at `-1` of the scattering polynomial is non-zero. -/
lemma polyScattering_eval_neg_one_ne_zero (k : ℝ) (n : ℕ) :
    (Q.polyScattering k n).eval (-1) ≠ 0 := by
  rw [polyScattering_eval_neg_one, Finset.prod_ne_zero_iff]
  intro j _ hj
  have hre := congrArg Complex.re hj
  simp only [sub_re, neg_re, mul_re, add_re, natCast_re, one_re, ofReal_re, ofReal_im, I_re,
    I_im, zero_re] at hre
  have := Q.κ_pos
  nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]

end PoschlTeller
end QuantumMechanics
end
