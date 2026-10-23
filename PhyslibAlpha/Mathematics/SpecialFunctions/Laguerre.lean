/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import Mathlib.RingTheory.Binomial
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!

# Generalised Laguerre polynomials

The generalised Laguerre polynomials `L_N^(α)` for natural `N` and `α`, their differential
equation, their moments against `x^q e^(-x)` and the four weighted integrals of `L_N^(α)²` that
give the radial expectation values of the hydrogen atom.

## i. Overview

We define `L_N^(α)(x) = Σ_{i ≤ N} (-1)^i C(N + α, N - i) x^i / i!` as an explicit polynomial and
check the Laguerre equation `x L'' + (α + 1 - x) L' + N L = 0` coefficientwise.

The moments `Σ_i c_i (q + i)!` of the coefficients reduce, by the Chu–Vandermonde identity for
the generalised binomial coefficient `Ring.choose`, to `q! · C(N + α - q - 1, N)`. With Euler's
integral `∫₀^∞ x^q e^(-x) dx = q!` this evaluates

`∫₀^∞ x^e e^(-x) L_N^(α)(x)² dx`

for `e = α + 1, α, α - 1, α - 2`: the terms with large `i` vanish because the upper argument of
the binomial coefficient is a natural number below `N`, and the remaining ones are
`C(-1, N) = (-1)^N` and `C(-2, N) = (-1)^N (N + 1)`.

## ii. Key results

- `laguerre`: the polynomial `L_N^(α)`.
- `laguerre_ode`: the Laguerre differential equation.
- `sum_laguerreCoeff_mul_factorial`: the moment identity.
- `integral_laguerre_sq_alpha`: `∫ x^α e^(-x) L² = (N + α)!/N!`.
- `integral_laguerre_sq_alpha_add_one`: `∫ x^(α+1) e^(-x) L² = (N + α)!/N! · (2N + α + 1)`.
- `integral_laguerre_sq_alpha_sub_one`, `integral_laguerre_sq_alpha_sub_two`: the weights
  `x^(α-1)` and `x^(α-2)`.

## iii. Table of contents

- A. Definition and differential equation
- B. Moments
- C. Integrals

## iv. References

- NIST Digital Library of Mathematical Functions, chapter 18, https://dlmf.nist.gov/18.
- H. A. Bethe and E. E. Salpeter, *Quantum Mechanics of One- and Two-Electron Atoms*, Springer
  (1957).

## A. Definition and differential equation

-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha

open Polynomial MeasureTheory Set

/-- The coefficient `(-1)^i C(N + α, N - i) / i!` of `x^i` in `L_N^(α)`. -/
def laguerreCoeff (N α i : ℕ) : ℝ := (-1) ^ i * ((N + α).choose (N - i) : ℝ) / (i.factorial : ℝ)

/-- The generalised Laguerre polynomial `L_N^(α)(x) = Σ_i (-1)^i C(N + α, N - i) x^i / i!`. -/
def laguerre (N α : ℕ) : ℝ[X] :=
  ∑ i ∈ Finset.range (N + 1), C (laguerreCoeff N α i) * X ^ i

variable {N α : ℕ}

lemma eval_laguerre (x : ℝ) :
    (laguerre N α).eval x = ∑ i ∈ Finset.range (N + 1), laguerreCoeff N α i * x ^ i := by
  simp [laguerre, eval_finsetSum]

lemma eval_laguerre_zero : (laguerre N α).eval 0 = ((N + α).choose N : ℝ) := by
  rw [eval_laguerre, Finset.sum_eq_single 0]
  · simp [laguerreCoeff]
  · intro i _ hi
    rw [zero_pow hi, mul_zero]
  · simp

lemma eval_derivative_laguerre (x : ℝ) :
    (derivative (laguerre N α)).eval x =
      ∑ i ∈ Finset.range (N + 1), laguerreCoeff N α i * ((i : ℝ) * x ^ (i - 1)) := by
  simp only [laguerre, derivative_sum, derivative_C_mul_X_pow, eval_finsetSum, eval_mul, eval_C,
    eval_pow, eval_X]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma eval_derivative_derivative_laguerre (x : ℝ) :
    (derivative (derivative (laguerre N α))).eval x =
      ∑ i ∈ Finset.range (N + 1),
        laguerreCoeff N α i * ((i : ℝ) * ((i - 1 : ℕ) : ℝ) * x ^ (i - 1 - 1)) := by
  simp only [laguerre, derivative_sum, derivative_C_mul_X_pow, eval_finsetSum, eval_mul, eval_C,
    eval_pow, eval_X]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The two-term recursion of the coefficients. -/
lemma laguerreCoeff_succ_mul {i : ℕ} (hi : i < N) :
    laguerreCoeff N α (i + 1) * (((i : ℝ) + 1) * ((i : ℝ) + 1 + α)) =
      -((N : ℝ) - i) * laguerreCoeff N α i := by
  have h := Nat.choose_succ_right_eq (N + α) (N - (i + 1))
  rw [show N - (i + 1) + 1 = N - i by omega, show N + α - (N - (i + 1)) = α + i + 1 by omega] at h
  have hR : ((N + α).choose (N - i) : ℝ) * ((N : ℝ) - i) =
      ((N + α).choose (N - (i + 1)) : ℝ) * ((α : ℝ) + i + 1) := by
    have := congrArg (Nat.cast (R := ℝ)) h
    push_cast [Nat.cast_sub hi.le] at this
    linarith
  have hi1 : ((i : ℝ) + 1) ≠ 0 := by positivity
  have hf : (i.factorial : ℝ) ≠ 0 := by positivity
  simp only [laguerreCoeff, Nat.factorial_succ, Nat.cast_mul, pow_succ]
  push_cast
  have e : ((i : ℝ) + 1) * ((i : ℝ) + 1 + α) / (((i : ℝ) + 1) * (i.factorial : ℝ)) =
      ((i : ℝ) + 1 + α) / i.factorial := by
    field_simp
  calc _ = (-1 : ℝ) ^ i * (-1) * ((N + α).choose (N - (i + 1)) : ℝ) *
        (((i : ℝ) + 1) * ((i : ℝ) + 1 + α) / (((i : ℝ) + 1) * (i.factorial : ℝ))) := by ring
    _ = _ := by
      rw [e]
      linear_combination ((-1 : ℝ) ^ i / (i.factorial : ℝ)) * hR

/-- **Laguerre's differential equation** `x L'' + (α + 1 - x) L' + N L = 0`. -/
lemma laguerre_ode (x : ℝ) :
    x * (derivative (derivative (laguerre N α))).eval x +
      ((α : ℝ) + 1 - x) * (derivative (laguerre N α)).eval x +
        (N : ℝ) * (laguerre N α).eval x = 0 := by
  rw [eval_laguerre, eval_derivative_laguerre, eval_derivative_derivative_laguerre,
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  have h1 : ∀ i : ℕ, x * (laguerreCoeff N α i * ((i : ℝ) * ((i - 1 : ℕ) : ℝ) * x ^ (i - 1 - 1))) +
      ((α : ℝ) + 1 - x) * (laguerreCoeff N α i * ((i : ℝ) * x ^ (i - 1))) +
        (N : ℝ) * (laguerreCoeff N α i * x ^ i) =
      laguerreCoeff N α i * ((i : ℝ) * ((i : ℝ) + α)) * x ^ (i - 1) +
        laguerreCoeff N α i * ((N : ℝ) - i) * x ^ i := fun i => by
    rcases i with _ | _ | i
    · simp
      ring
    · simp
      ring
    · simp only [Nat.add_sub_cancel]
      push_cast
      ring
  rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_add_distrib,
    Finset.sum_range_succ' (fun i => laguerreCoeff N α i * ((i : ℝ) * ((i : ℝ) + α)) * x ^ (i - 1)),
    Finset.sum_range_succ (fun i => laguerreCoeff N α i * ((N : ℝ) - i) * x ^ i)]
  simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, sub_self, Nat.add_sub_cancel]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hrec := laguerreCoeff_succ_mul (α := α) (Finset.mem_range.mp hi)
  push_cast
  linear_combination x ^ i * hrec

/-!

## B. Moments

-/

/-- `Σ_i (-1)^i C(N + α, N - i) C(q + i, i) = C(N + α - q - 1, N)`, the Chu–Vandermonde identity
with a negative upper index. -/
lemma sum_choose_mul_choose_neg (q : ℕ) :
    ∑ i ∈ Finset.range (N + 1), (-1 : ℤ) ^ i * ((N + α).choose (N - i) : ℤ) * ((q + i).choose i) =
      Ring.choose ((N + α : ℤ) - q - 1) N := by
  have h := Ring.add_choose_eq (r := ((N + α : ℕ) : ℤ)) (s := -((q : ℤ) + 1)) N
    (Commute.all _ _)
  rw [show ((N + α : ℕ) : ℤ) + -((q : ℤ) + 1) = (N + α : ℤ) - q - 1 by push_cast; ring] at h
  rw [h, ← Finset.Nat.sum_antidiagonal_swap]
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun i _ => ?_
  dsimp only
  rw [Ring.choose_natCast, Ring.choose_neg, Units.smul_def, Int.coe_negOnePow_natCast, smul_eq_mul,
    show (q : ℤ) + 1 + i - 1 = ((q + i : ℕ) : ℤ) by push_cast; ring, Ring.choose_natCast]
  ring

/-- **Moments.** `Σ_i c_i (q + i)! = q! C(N + α - q - 1, N)`, the integral of `x^q e^(-x) L_N^(α)`
with the integer binomial coefficient `Ring.choose`. -/
lemma sum_laguerreCoeff_mul_factorial (q : ℕ) :
    ∑ i ∈ Finset.range (N + 1), laguerreCoeff N α i * ((q + i).factorial : ℝ) =
      (q.factorial : ℝ) * ((Ring.choose ((N + α : ℤ) - q - 1) N : ℤ) : ℝ) := by
  rw [← sum_choose_mul_choose_neg, Int.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := Nat.choose_mul_factorial_mul_factorial (show i ≤ q + i by omega)
  rw [show q + i - i = q by omega] at h
  have hf : (i.factorial : ℝ) ≠ 0 := by positivity
  have hR : ((q + i).choose i : ℝ) * i.factorial * q.factorial = (q + i).factorial := by
    exact_mod_cast h
  rw [laguerreCoeff, ← hR]
  push_cast
  field_simp

lemma ringChoose_natCast_of_lt {t : ℕ} (h : t < N) : Ring.choose (t : ℤ) N = 0 := by
  rw [Ring.choose_natCast, Nat.choose_eq_zero_of_lt h, Nat.cast_zero]

lemma ringChoose_neg_one : Ring.choose (-1 : ℤ) N = (-1) ^ N := by
  rw [Ring.choose_neg, Units.smul_def, Int.coe_negOnePow_natCast, smul_eq_mul,
    show (1 : ℤ) + N - 1 = (N : ℕ) by ring, Ring.choose_natCast, Nat.choose_self, Nat.cast_one,
    mul_one]

lemma ringChoose_neg_two : Ring.choose (-2 : ℤ) N = (-1) ^ N * (N + 1) := by
  rw [Ring.choose_neg, Units.smul_def, Int.coe_negOnePow_natCast, smul_eq_mul,
    show (2 : ℤ) + N - 1 = ((N + 1 : ℕ) : ℤ) by push_cast; ring, Ring.choose_natCast,
    Nat.choose_succ_self_right]
  push_cast
  ring

/-!

## C. Integrals

-/

lemma integrableOn_pow_mul_exp_neg (q : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ q * Real.exp (-x)) (Ioi 0) := by
  have h := Real.GammaIntegral_convergent (s := (q : ℝ) + 1) (by positivity)
  refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp only [add_sub_cancel_right, Real.rpow_natCast]
  ring

/-- `∫₀^∞ x^q e^(-x) dx = q!`. -/
lemma integral_pow_mul_exp_neg (q : ℕ) :
    ∫ x in Ioi (0 : ℝ), x ^ q * Real.exp (-x) = q.factorial := by
  have h := Real.Gamma_eq_integral (s := (q : ℝ) + 1) (by positivity)
  rw [Real.Gamma_nat_eq_factorial] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  simp only [add_sub_cancel_right, Real.rpow_natCast]
  ring

/-- `∫₀^∞ x^e e^(-x) L(x)² dx = Σ_j c_j Σ_i c_i (e + j + i)!`. -/
lemma integral_pow_mul_exp_neg_mul_laguerre_sq (e : ℕ) :
    ∫ x in Ioi (0 : ℝ), x ^ e * Real.exp (-x) * ((laguerre N α).eval x) ^ 2 =
      ∑ j ∈ Finset.range (N + 1), laguerreCoeff N α j *
        ∑ i ∈ Finset.range (N + 1), laguerreCoeff N α i * ((e + j + i).factorial : ℝ) := by
  have hexp : ∀ x : ℝ, x ^ e * Real.exp (-x) * ((laguerre N α).eval x) ^ 2 =
      ∑ j ∈ Finset.range (N + 1), ∑ i ∈ Finset.range (N + 1),
        laguerreCoeff N α j * laguerreCoeff N α i * (x ^ (e + j + i) * Real.exp (-x)) :=
    fun x => by
      rw [eval_laguerre, sq, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
  simp_rw [hexp]
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun i _ =>
    (integrableOn_pow_mul_exp_neg _).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun i _ => (integrableOn_pow_mul_exp_neg _).const_mul _,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_pow_mul_exp_neg]
  ring

/-- The integrals through the moments. -/
lemma integral_pow_mul_exp_neg_mul_laguerre_sq_eq (e : ℕ) :
    ∫ x in Ioi (0 : ℝ), x ^ e * Real.exp (-x) * ((laguerre N α).eval x) ^ 2 =
      ∑ j ∈ Finset.range (N + 1), laguerreCoeff N α j * (((e + j).factorial : ℝ) *
        ((Ring.choose ((N + α : ℤ) - (e + j : ℕ) - 1) N : ℤ) : ℝ)) := by
  rw [integral_pow_mul_exp_neg_mul_laguerre_sq]
  exact Finset.sum_congr rfl fun j _ => by rw [sum_laguerreCoeff_mul_factorial]

lemma neg_one_pow_mul_self (n : ℕ) : (-1 : ℝ) ^ n * (-1) ^ n = 1 := by
  rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

/-- `∫₀^∞ x^α e^(-x) L_N^(α)(x)² dx = (N + α)!/N!`. -/
lemma integral_laguerre_sq_alpha :
    ∫ x in Ioi (0 : ℝ), x ^ α * Real.exp (-x) * ((laguerre N α).eval x) ^ 2 =
      ((N + α).factorial : ℝ) / N.factorial := by
  rw [integral_pow_mul_exp_neg_mul_laguerre_sq_eq, Finset.sum_range_succ,
    Finset.sum_eq_zero fun j hj => by
      have := Finset.mem_range.mp hj
      rw [show (N + α : ℤ) - ((α + j : ℕ) : ℤ) - 1 = ((N - j - 1 : ℕ) : ℤ) by push_cast; omega,
        ringChoose_natCast_of_lt (by omega), Int.cast_zero, mul_zero, mul_zero],
    zero_add, show (N + α : ℤ) - ((α + N : ℕ) : ℤ) - 1 = -1 by push_cast; ring, ringChoose_neg_one,
    laguerreCoeff, Nat.sub_self, Nat.choose_zero_right, Nat.add_comm α N]
  push_cast
  have h := neg_one_pow_mul_self N
  field_simp
  linear_combination h

/-- `∫₀^∞ x^(α+1) e^(-x) L_N^(α)(x)² dx = (N + α)!/N! · (2N + α + 1)`. -/
lemma integral_laguerre_sq_alpha_add_one :
    ∫ x in Ioi (0 : ℝ), x ^ (α + 1) * Real.exp (-x) * ((laguerre N α).eval x) ^ 2 =
      ((N + α).factorial : ℝ) / N.factorial * (2 * N + α + 1) := by
  rw [integral_pow_mul_exp_neg_mul_laguerre_sq_eq]
  rcases N with _ | N
  · rw [Finset.sum_range_one, Ring.choose_zero_right]
    simp [laguerreCoeff, Nat.factorial_succ]
    ring
  · rw [Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_eq_zero fun j hj => by
        have := Finset.mem_range.mp hj
        rw [show ((N + 1 : ℕ) : ℤ) + α - ((α + 1 + j : ℕ) : ℤ) - 1 = ((N - j - 1 : ℕ) : ℤ) by
          omega, ringChoose_natCast_of_lt (by omega), Int.cast_zero, mul_zero, mul_zero],
      zero_add,
      show ((N + 1 : ℕ) : ℤ) + α - ((α + 1 + N : ℕ) : ℤ) - 1 = -1 by push_cast; ring,
      show ((N + 1 : ℕ) : ℤ) + α - ((α + 1 + (N + 1) : ℕ) : ℤ) - 1 = -2 by push_cast; ring,
      ringChoose_neg_one, ringChoose_neg_two]
    simp only [laguerreCoeff, show N + 1 - N = 1 by omega, Nat.sub_self, Nat.choose_one_right,
      Nat.choose_zero_right]
    rw [show α + 1 + (N + 1) = N + 1 + α + 1 by ring, show α + 1 + N = N + 1 + α by ring,
      Nat.factorial_succ (N + 1 + α), Nat.factorial_succ N]
    push_cast
    rcases Nat.even_or_odd N with hN | hN
    · rw [pow_succ, hN.neg_one_pow]
      field_simp
      ring
    · rw [pow_succ, hN.neg_one_pow]
      field_simp
      ring

/-- `∫₀^∞ x^(α-1) e^(-x) L_N^(α)(x)² dx = (N + α)!/(N! α)`. -/
lemma integral_laguerre_sq_alpha_sub_one (hα : 1 ≤ α) :
    ∫ x in Ioi (0 : ℝ), x ^ (α - 1) * Real.exp (-x) * ((laguerre N α).eval x) ^ 2 =
      ((N + α).factorial : ℝ) / (N.factorial * α) := by
  obtain ⟨a, rfl⟩ : ∃ a, α = a + 1 := ⟨α - 1, by omega⟩
  rw [show a + 1 - 1 = a by omega, integral_pow_mul_exp_neg_mul_laguerre_sq_eq,
    Finset.sum_eq_single 0]
  · rw [show (N : ℤ) + ((a + 1 : ℕ) : ℤ) - ((a + 0 : ℕ) : ℤ) - 1 = ((N : ℕ) : ℤ) by push_cast; ring,
      Ring.choose_natCast, Nat.choose_self]
    simp only [laguerreCoeff, pow_zero, Nat.sub_zero, Nat.factorial_zero, add_zero, Nat.cast_one]
    rw [Nat.cast_choose ℝ (show N ≤ N + (a + 1) by omega), show N + (a + 1) - N = a + 1 by omega,
      Nat.factorial_succ a]
    push_cast
    field_simp
  · intro j hj hj0
    have := Finset.mem_range.mp hj
    rw [show (N : ℤ) + ((a + 1 : ℕ) : ℤ) - ((a + j : ℕ) : ℤ) - 1 = ((N - j : ℕ) : ℤ) by omega,
      ringChoose_natCast_of_lt (by omega), Int.cast_zero, mul_zero, mul_zero]
  · intro h
    simp at h

/-- `∫₀^∞ x^(α-2) e^(-x) L_N^(α)(x)² dx = (N + α)! (2N + α + 1)/(N! (α - 1) α (α + 1))`. -/
lemma integral_laguerre_sq_alpha_sub_two (hα : 2 ≤ α) :
    ∫ x in Ioi (0 : ℝ), x ^ (α - 2) * Real.exp (-x) * ((laguerre N α).eval x) ^ 2 =
      ((N + α).factorial : ℝ) * (2 * N + α + 1) /
        (N.factorial * (((α : ℝ) - 1) * α * (α + 1))) := by
  obtain ⟨a, rfl⟩ : ∃ a, α = a + 2 := ⟨α - 2, by omega⟩
  rw [show a + 2 - 2 = a by omega, integral_pow_mul_exp_neg_mul_laguerre_sq_eq,
    show ((a + 2 : ℕ) : ℝ) - 1 = (a : ℝ) + 1 by push_cast; ring]
  rcases N with _ | N
  · rw [Finset.sum_range_one, Ring.choose_zero_right]
    have h1 : (a : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (a : ℝ) + 2 ≠ 0 := by positivity
    have h3 : (a : ℝ) + 3 ≠ 0 := by positivity
    have h1' : 1 + (a : ℝ) ≠ 0 := by positivity
    simp [laguerreCoeff, Nat.factorial_succ]
    field_simp
    ring
  · rw [Finset.sum_range_succ', Finset.sum_range_succ',
      Finset.sum_eq_zero fun j hj => by
        have := Finset.mem_range.mp hj
        rw [show ((N + 1 : ℕ) : ℤ) + ((a + 2 : ℕ) : ℤ) - ((a + (j + 1 + 1) : ℕ) : ℤ) - 1 =
          ((N - j : ℕ) : ℤ) by omega, ringChoose_natCast_of_lt (by omega), Int.cast_zero,
          mul_zero, mul_zero],
      zero_add,
      show ((N + 1 : ℕ) : ℤ) + ((a + 2 : ℕ) : ℤ) - ((a + (0 + 1) : ℕ) : ℤ) - 1 =
        ((N + 1 : ℕ) : ℤ) by
        push_cast; ring,
      show ((N + 1 : ℕ) : ℤ) + ((a + 2 : ℕ) : ℤ) - ((a + 0 : ℕ) : ℤ) - 1 =
        ((N + 2 : ℕ) : ℤ) by
        push_cast; ring,
      Ring.choose_natCast, Ring.choose_natCast, Nat.choose_self,
      show N + 2 = (N + 1) + 1 by ring, Nat.choose_succ_self_right]
    simp only [laguerreCoeff, pow_zero, pow_one, Nat.sub_zero, Nat.factorial_zero,
      Nat.factorial_one, add_zero, zero_add, show N + 1 - 1 = N by omega]
    rw [Nat.cast_choose ℝ (show N + 1 ≤ N + 1 + (a + 2) by omega),
      Nat.cast_choose ℝ (show N ≤ N + 1 + (a + 2) by omega),
      show N + 1 + (a + 2) - (N + 1) = a + 2 by omega, show N + 1 + (a + 2) - N = a + 3 by omega,
      Nat.factorial_succ (a + 2), Nat.factorial_succ (a + 1), Nat.factorial_succ a,
      Nat.factorial_succ N]
    push_cast
    field_simp
    ring

end PhyslibAlpha
