/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import Mathlib.Basic.Real.Sign
public import PhyslibAlpha.QuantumMechanics.AngularMomentum.Wigner3jRational

/-!

# Rational values of the Wigner 3j symbols with general arguments

The 3j symbols `threeJ` squared, and times their absolute value, as rational numbers, through the
rational values of the 3j symbols of a Regge square in `Wigner3jRational`.

## i. Overview

`threeJ j₁ j₂ j₃ m₁ m₂ m₃` is the 3j symbol `threeJR` of the Regge square
`reggeJ j₁ j₂ j₃ m₁ m₂ m₃` for admissible arguments and `0` otherwise. The rational functions of
`Wigner3jRational` therefore give its square and its product with its absolute value as rational
numbers (`threeJSqQ`, `threeJSgnSqQ`), and the 3j symbol is `sign(q) √|q|` with
`q = threeJSgnSqQ` (`threeJ_eq_sign_mul_sqrt`). The same gives the squares of the Clebsch–Gordan
coefficients (`sq_cgCoefficient`). Section C checks proven identities in the kernel with
`decide +kernel`: the diagonal orthogonality relations and the symmetries of `SixJSymmetry` on a
grid of small spins.

For an admissible symbol the radicand `∏ R_ij! / (J + 1)!` splits into the triangle coefficient
`Δ(j₁j₂j₃)²` and the factorials `(jᵢ - mᵢ)! (jᵢ + mᵢ)!` of the projections (`threeJRRadQ_reggeJ`),
so `threeJ = √(Δ² ∏ᵢ (jᵢ - mᵢ)! (jᵢ + mᵢ)!) · threeJNumQ` (`threeJ_eq_sqrt_mul`). This is the form
in which the four 3j symbols of a 6j symbol combine in `SixJRational`.

## ii. Key results

- `threeJSqQ`, `cast_threeJSqQ`, `threeJSgnSqQ`, `cast_threeJSgnSqQ`: `threeJ ^ 2` and
  `threeJ · |threeJ|` over `ℚ`.
- `threeJ_eq_sign_mul_sqrt`: `threeJ = sign(q) √|q|` with `q = threeJSgnSqQ`.
- `sq_cgCoefficient`: the square of a Clebsch–Gordan coefficient as a rational number.
- `triangleSqQ`, `facPairQ`, `threeJNumQ`: the triangle coefficient, the factorials of the
  projections and the 3j symbol without its square root, over `ℚ`.
- `threeJ_eq_sqrt_mul`: `threeJ = √(Δ² ∏ᵢ (jᵢ - mᵢ)! (jᵢ + mᵢ)!) · threeJNumQ`.

## iii. Table of contents

- A. The 3j symbol with general arguments
- B. The Clebsch–Gordan coefficients
- C. Checks in the kernel
- D. Triangle coefficients and the 3j symbols

## iv. References

- D. A. Varshalovich, A. N. Moskalev, V. K. Khersonskii, *Quantum Theory of Angular Momentum*,
  World Scientific (1988): Sec. 8.1.3, p. 237, Eqs. 8.1(14)–(18) (the Regge symbol); Sec. 8.2,
  p. 237, Eq. 8.2(1) (the Δ symbol); Sec. 8.2.1, p. 238, Eq. 8.2(3) (Racah's sum for the
  Clebsch–Gordan coefficients).
- NIST Digital Library of Mathematical Functions, Sec. 34.2, Eqs. 34.2.4–34.2.5,
  https://dlmf.nist.gov/34.2.

-/

@[expose] public section

namespace PhyslibAlpha.Sl2

/-!

## A. The 3j symbol with general arguments

-/

/-- `threeJ j₁ j₂ j₃ m₁ m₂ m₃ ^ 2` over `ℚ` (doubled units). -/
def threeJSqQ (j₁ j₂ j₃ : ℕ) (m₁ m₂ m₃ : ℤ) : ℚ :=
  if Adm3 j₁ j₂ j₃ m₁ m₂ m₃ then threeJRSqQ (reggeJ j₁ j₂ j₃ m₁ m₂ m₃) else 0

/-- `threeJ j₁ j₂ j₃ m₁ m₂ m₃ · |threeJ j₁ j₂ j₃ m₁ m₂ m₃|` over `ℚ` (doubled units). -/
def threeJSgnSqQ (j₁ j₂ j₃ : ℕ) (m₁ m₂ m₃ : ℤ) : ℚ :=
  if Adm3 j₁ j₂ j₃ m₁ m₂ m₃ then threeJRSgnSqQ (reggeJ j₁ j₂ j₃ m₁ m₂ m₃) else 0

variable (j₁ j₂ j₃ : ℕ) (m₁ m₂ m₃ : ℤ)

/-- `threeJSqQ` is the square of the 3j symbol `threeJ`. -/
lemma cast_threeJSqQ : (threeJSqQ j₁ j₂ j₃ m₁ m₂ m₃ : ℝ) = threeJ j₁ j₂ j₃ m₁ m₂ m₃ ^ 2 := by
  rw [threeJSqQ, threeJ]
  split_ifs
  · exact cast_threeJRSqQ _
  · simp

/-- `threeJSgnSqQ` is the 3j symbol `threeJ` times its absolute value. -/
lemma cast_threeJSgnSqQ :
    (threeJSgnSqQ j₁ j₂ j₃ m₁ m₂ m₃ : ℝ) =
      threeJ j₁ j₂ j₃ m₁ m₂ m₃ * |threeJ j₁ j₂ j₃ m₁ m₂ m₃| := by
  rw [threeJSgnSqQ, threeJ]
  split_ifs
  · exact cast_threeJRSgnSqQ _
  · simp

/-- **The 3j symbol from a rational number.** `threeJ = sign(q) √|q|` with
`q = threeJSgnSqQ`. -/
lemma threeJ_eq_sign_mul_sqrt :
    threeJ j₁ j₂ j₃ m₁ m₂ m₃ =
      Real.sign (threeJSgnSqQ j₁ j₂ j₃ m₁ m₂ m₃ : ℝ) *
        Real.sqrt |(threeJSgnSqQ j₁ j₂ j₃ m₁ m₂ m₃ : ℝ)| := by
  rw [cast_threeJSgnSqQ]
  set t := threeJ j₁ j₂ j₃ m₁ m₂ m₃
  rw [abs_mul, abs_abs, Real.sqrt_mul_self (abs_nonneg t)]
  rcases lt_trichotomy t 0 with h | h | h
  · rw [Real.sign_of_neg (mul_neg_of_neg_of_pos h (abs_pos.mpr h.ne)), abs_of_neg h]
    ring
  · simp [h]
  · rw [Real.sign_of_pos (mul_pos h (abs_pos.mpr h.ne')), abs_of_pos h, one_mul]

/-!

## B. The Clebsch–Gordan coefficients

-/

/-- **Clebsch–Gordan coefficients squared are rational.**
`⟨j₁ m₁ j₂ m₂ | J M⟩² = (2J + 1) (j₁ j₂ J; m₁ m₂ -M)²`, in the parameters of
`ClebschGordanCoefficients`. -/
lemma sq_cgCoefficient {m n : ℕ} (hmn : 0 < m + n) {k l α β : ℕ} (hkm : k ≤ m) (hkn : k ≤ n)
    (hl : l ≤ m + n - 2 * k) (hα : α ≤ m) (hβ : β ≤ n) :
    cgCoefficient m n k l α β ^ 2 = ((m + n - 2 * k + 1 : ℕ) : ℝ) *
      (threeJSqQ m n (m + n - 2 * k) ((m : ℤ) - 2 * α) ((n : ℤ) - 2 * β)
        (-(((m + n - 2 * k : ℕ) : ℤ) - 2 * l)) : ℝ) := by
  have hp : ((-1 : ℝ) ^ (m + k + l)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  rw [cgCoefficient_eq_wigner3j hmn hkm hkn hl hα hβ, wigner3j_eq_threeJ hkm hkn hl hα hβ,
    cast_threeJSqQ, mul_pow, mul_pow, hp, one_mul, Real.sq_sqrt (Nat.cast_nonneg _)]

/-!

## C. Checks in the kernel

Proven identities, evaluated with `decide +kernel` on small spins (doubled units). The
orthogonality relations involving two different 3j symbols are not rational term by term, so only
the diagonal relations are checked.

-/

/-- `Σ_{m₁ m₂} (j₁ j₂ J; m₁ m₂ M)² = 1/(2J + 1)` (`sum_wigner3j_mul_wigner3j`), for
`j₁ = 2`, `j₂ = 3/2` and all `J`, `M`. -/
example : ∀ J ∈ Finset.range 8, ∀ M ∈ Finset.Icc (-(J : ℤ)) J, (J - M) % 2 = 0 →
    ∑ m₁ ∈ Finset.Icc (-4 : ℤ) 4, threeJSqQ 4 3 J m₁ (-m₁ - M) M =
      if 1 ≤ J ∧ J ≤ 7 ∧ J % 2 = 1 then 1 / ((J : ℚ) + 1) else 0 := by
  decide +kernel

/-- `Σ_J (2J + 1) (j₁ j₂ J; m₁ m₂ -M)² = 1` (`sum_wigner3j_mul_wigner3j_JM`), for `j₁ = 2`,
`j₂ = 3/2` and all admissible `m₁`, `m₂`. -/
example : ∀ m₁ ∈ Finset.Icc (-4 : ℤ) 4, ∀ m₂ ∈ Finset.Icc (-3 : ℤ) 3, m₁ % 2 = 0 → m₂ % 2 = 1 →
    ∑ J ∈ Finset.range 8, ((J : ℚ) + 1) * threeJSqQ 4 3 J m₁ m₂ (-m₁ - m₂) = 1 := by
  decide +kernel

/-- `threeJ_swap` for all spins up to `3/2` and all projections. -/
example : ((List.range 4).all fun j₁ => (List.range 4).all fun j₂ => (List.range 4).all fun j₃ =>
    (List.range (j₁ + 1)).all fun a => (List.range (j₂ + 1)).all fun b =>
      threeJSgnSqQ j₂ j₁ j₃ (2 * b - j₂) (2 * a - j₁) (j₁ + j₂ - 2 * a - 2 * b) -
          (-1) ^ ((j₁ + j₂ + j₃) / 2) *
            threeJSgnSqQ j₁ j₂ j₃ (2 * a - j₁) (2 * b - j₂) (j₁ + j₂ - 2 * a - 2 * b) == 0) =
    true := by
  decide +kernel

/-- `threeJ_cycle` for all spins up to `3/2` and all projections. -/
example : ((List.range 4).all fun j₁ => (List.range 4).all fun j₂ => (List.range 4).all fun j₃ =>
    (List.range (j₁ + 1)).all fun a => (List.range (j₂ + 1)).all fun b =>
      threeJSgnSqQ j₂ j₃ j₁ (2 * b - j₂) (j₁ + j₂ - 2 * a - 2 * b) (2 * a - j₁) -
          threeJSgnSqQ j₁ j₂ j₃ (2 * a - j₁) (2 * b - j₂) (j₁ + j₂ - 2 * a - 2 * b) == 0) =
    true := by
  decide +kernel

/-- `threeJ_neg` for all spins up to `3/2` and all projections. -/
example : ((List.range 4).all fun j₁ => (List.range 4).all fun j₂ => (List.range 4).all fun j₃ =>
    (List.range (j₁ + 1)).all fun a => (List.range (j₂ + 1)).all fun b =>
      threeJSgnSqQ j₁ j₂ j₃ (j₁ - 2 * a) (j₂ - 2 * b) (2 * a + 2 * b - j₁ - j₂) -
          (-1) ^ ((j₁ + j₂ + j₃) / 2) *
            threeJSgnSqQ j₁ j₂ j₃ (2 * a - j₁) (2 * b - j₂) (j₁ + j₂ - 2 * a - 2 * b) == 0) =
    true := by
  decide +kernel

/-- `(j j j; 0 0 0) = 0` for odd `3j`, a consequence of `threeJ_neg`, and a non-vanishing
symbol stated as a negation. -/
example : threeJSqQ 2 2 2 0 0 0 = 0 ∧ ¬threeJSqQ 4 4 4 0 0 0 = 0 := by
  decide +kernel

/-!

## D. Triangle coefficients and the 3j symbols

-/

/-- `Δ(j₁ j₂ j₃)² = (j₁+j₂-j₃)! (j₁-j₂+j₃)! (-j₁+j₂+j₃)! / (j₁+j₂+j₃+1)!` in doubled units. -/
def triangleSqQ (j₁ j₂ j₃ : ℕ) : ℚ :=
  ((j₁ + j₂ - j₃) / 2).factorial * ((j₁ + j₃ - j₂) / 2).factorial *
    ((j₂ + j₃ - j₁) / 2).factorial / ((j₁ + j₂ + j₃) / 2 + 1).factorial

/-- `(j - m)! (j + m)!` in doubled units. -/
def facPairQ (j : ℕ) (m : ℤ) : ℚ :=
  ((((j : ℤ) - m) / 2).toNat.factorial : ℚ) * ((((j : ℤ) + m) / 2).toNat.factorial : ℚ)

lemma facPairQ_neg (j : ℕ) (m : ℤ) : facPairQ j (-m) = facPairQ j m := by
  rw [facPairQ, facPairQ, sub_neg_eq_add, ← sub_eq_add_neg, mul_comm]

lemma facPairQ_nonneg (j : ℕ) (m : ℤ) : 0 ≤ facPairQ j m := by
  rw [facPairQ]
  positivity

lemma triangleSqQ_nonneg (j₁ j₂ j₃ : ℕ) : 0 ≤ triangleSqQ j₁ j₂ j₃ := by
  rw [triangleSqQ]
  positivity

/-- The 3j symbol without its square root: `(-1)^(R₂₀ + R₁₁)` times the six-factorial sum. -/
def threeJNumQ (j₁ j₂ j₃ : ℕ) (m₁ m₂ m₃ : ℤ) : ℚ :=
  negOnePowQ (reggeJ j₁ j₂ j₃ m₁ m₂ m₃ 2 0 + reggeJ j₁ j₂ j₃ m₁ m₂ m₃ 1 1) *
    threeJRSumQ (reggeJ j₁ j₂ j₃ m₁ m₂ m₃)

/-- The radicand of the 3j symbol splits into the triangle coefficient and the factorials of the
projections. -/
lemma threeJRRadQ_reggeJ {j₁ j₂ j₃ : ℕ} {m₁ m₂ m₃ : ℤ} (h : Adm3 j₁ j₂ j₃ m₁ m₂ m₃) :
    threeJRRadQ (reggeJ j₁ j₂ j₃ m₁ m₂ m₃) =
      triangleSqQ j₁ j₂ j₃ * facPairQ j₁ m₁ * facPairQ j₂ m₂ * facPairQ j₃ m₃ := by
  rw [threeJRRadQ, reggeJ_row_sum h]
  simp only [reggeJ, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, triangleSqQ, facPairQ]
  ring

/-- `threeJ = √(Δ² (j₁-m₁)!(j₁+m₁)! (j₂-m₂)!(j₂+m₂)! (j₃-m₃)!(j₃+m₃)!) · threeJNumQ`. -/
lemma threeJ_eq_sqrt_mul {j₁ j₂ j₃ : ℕ} {m₁ m₂ m₃ : ℤ} (h : Adm3 j₁ j₂ j₃ m₁ m₂ m₃) :
    threeJ j₁ j₂ j₃ m₁ m₂ m₃ =
      Real.sqrt ((triangleSqQ j₁ j₂ j₃ * facPairQ j₁ m₁ * facPairQ j₂ m₂ * facPairQ j₃ m₃ : ℚ) :
        ℝ) * (threeJNumQ j₁ j₂ j₃ m₁ m₂ m₃ : ℝ) := by
  rw [threeJ, ite_eq_left h, threeJR_eq_rat, ← threeJRRadQ_reggeJ h, threeJNumQ, Rat.cast_mul,
    cast_negOnePowQ, ← Nat.cast_add, zpow_natCast]
  ring

end PhyslibAlpha.Sl2
