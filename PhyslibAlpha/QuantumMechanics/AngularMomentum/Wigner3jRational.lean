/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.QuantumMechanics.AngularMomentum.SixJSymmetry

/-!

# Rational values of the Wigner 3j symbols

Computable rational functions for the square of the 3j symbol of a Regge square and for that
symbol times its absolute value, with proofs that they agree with the real definitions of
`Wigner3j`.

## i. Overview

The 3j symbol `threeJR R = (-1)^(R₂₀ + R₁₁) √(∏ R_ij! / (J + 1)!) · S` of a Regge square `R`
contains a square root and a `finsum`, so it cannot be evaluated. Its square and the product
`threeJR R · |threeJR R|` are rational:

- `threeJR R ^ 2 = ∏ R_ij! / (J + 1)! · S²`,
- `threeJR R · |threeJR R| = (-1)^(R₂₀ + R₁₁) ∏ R_ij! / (J + 1)! · S |S|`,

where the six-factorial sum `S` is a finite sum of rationals over the range in which all
factorials have nonnegative arguments (`sixSumQ`). The second form keeps the sign.

The functions below are defined by finite sums and products over `ℚ`, so concrete values can be
checked in the kernel with `decide +kernel`.

## ii. Key results

- `sixSumQ`, `cast_sixSumQ`: the six-factorial sum over `ℚ`.
- `threeJRSqQ`, `cast_threeJRSqQ`: `threeJR R ^ 2` over `ℚ`.
- `threeJRSgnSqQ`, `cast_threeJRSgnSqQ`: `threeJR R · |threeJR R|` over `ℚ`.

## iii. Table of contents

- A. The six-factorial sum over ℚ
- B. The 3j symbol of a Regge square
- C. Examples

## iv. References

- D. A. Varshalovich, A. N. Moskalev, V. K. Khersonskii, *Quantum Theory of Angular Momentum*,
  World Scientific (1988): Sec. 8.1.3, p. 237, Eqs. 8.1(14)–(18) (the Regge symbol); Sec. 8.2,
  p. 237, Eq. 8.2(1) (the Δ symbol); Sec. 8.2.1, p. 238, Eq. 8.2(3) (Racah's sum for the
  Clebsch–Gordan coefficients).
- NIST Digital Library of Mathematical Functions, Sec. 34.2, Eqs. 34.2.4–34.2.5,
  https://dlmf.nist.gov/34.2.

## A. The six-factorial sum over ℚ

-/

@[expose] public section

namespace PhyslibAlpha.Sl2

/-- `1/u!` in `ℚ` for `u ≥ 0` and `0` for `u < 0`. -/
def invFactQ (u : ℤ) : ℚ := if 0 ≤ u then ((u.toNat.factorial : ℚ))⁻¹ else 0

lemma cast_invFactQ (u : ℤ) : (invFactQ u : ℝ) = invFact u := by
  rw [invFactQ, invFact]
  split_ifs <;> push_cast <;> rfl

/-- `(-1)^z` in `ℚ`, by the parity of `z`. -/
def negOnePowQ (z : ℤ) : ℚ := if z % 2 = 0 then 1 else -1

lemma cast_negOnePowQ (z : ℤ) : (negOnePowQ z : ℝ) = (-1) ^ z := by
  rw [negOnePowQ]
  split_ifs with h
  · rw [neg_one_zpow_congr (q := 0) (by omega)]
    simp
  · rw [neg_one_zpow_congr (q := 1) (by omega)]
    simp

/-- The summand of `sixSumQ`. -/
def sixTermQ (a₁ a₂ a₃ b₁ b₂ b₃ z : ℤ) : ℚ :=
  negOnePowQ z * (invFactQ (z - a₁) * invFactQ (z - a₂) * invFactQ (z - a₃) *
    (invFactQ (b₁ - z) * invFactQ (b₂ - z) * invFactQ (b₃ - z)))

lemma cast_sixTermQ (a₁ a₂ a₃ b₁ b₂ b₃ z : ℤ) :
    (sixTermQ a₁ a₂ a₃ b₁ b₂ b₃ z : ℝ) = sixTerm a₁ a₂ a₃ b₁ b₂ b₃ z := by
  simp only [sixTermQ, sixTerm, Rat.cast_mul, cast_negOnePowQ, cast_invFactQ]

/-- The six-factorial sum over `ℚ`, over the range `max aᵢ ≤ z ≤ min bᵢ` outside of which all
summands vanish. -/
def sixSumQ (a₁ a₂ a₃ b₁ b₂ b₃ : ℤ) : ℚ :=
  ∑ z ∈ Finset.Icc (max a₁ (max a₂ a₃)) (min b₁ (min b₂ b₃)), sixTermQ a₁ a₂ a₃ b₁ b₂ b₃ z

lemma cast_sixSumQ (a₁ a₂ a₃ b₁ b₂ b₃ : ℤ) :
    (sixSumQ a₁ a₂ a₃ b₁ b₂ b₃ : ℝ) = sixSum a₁ a₂ a₃ b₁ b₂ b₃ := by
  rw [sixSum, finsum_eq_sum_of_support_subset (s := Finset.Icc (max a₁ (max a₂ a₃))
    (min b₁ (min b₂ b₃))), sixSumQ, Rat.cast_sum]
  · exact Finset.sum_congr rfl fun z _ => cast_sixTermQ _ _ _ _ _ _ z
  · intro z hz
    rw [Function.mem_support] at hz
    simp only [sixTerm, ne_eq, mul_eq_zero, not_or] at hz
    have h₁ := nonneg_of_invFact_ne_zero hz.2.1.1.1
    have h₂ := nonneg_of_invFact_ne_zero hz.2.1.1.2
    have h₃ := nonneg_of_invFact_ne_zero hz.2.1.2
    have h₄ := nonneg_of_invFact_ne_zero hz.2.2.1.1
    have h₅ := nonneg_of_invFact_ne_zero hz.2.2.1.2
    have h₆ := nonneg_of_invFact_ne_zero hz.2.2.2
    simp only [Finset.coe_Icc, Set.mem_Icc]
    omega

/-!

## B. The 3j symbol of a Regge square

-/

/-- The rational number `∏ R_ij! / (J + 1)!` under the square root of `threeJR`. -/
def threeJRRadQ (R : Fin 3 → Fin 3 → ℕ) : ℚ :=
  (∏ i, ∏ j, ((R i j).factorial : ℚ)) / ((R 0 0 + R 0 1 + R 0 2 + 1).factorial : ℚ)

/-- The six-factorial sum of `threeJR` over `ℚ`. -/
def threeJRSumQ (R : Fin 3 → Fin 3 → ℕ) : ℚ :=
  sixSumQ 0 ((R 1 0 : ℤ) - R 0 1) ((R 2 1 : ℤ) - R 0 0) (R 0 2) (R 1 0) (R 2 1)

/-- `threeJR R ^ 2` over `ℚ`. -/
def threeJRSqQ (R : Fin 3 → Fin 3 → ℕ) : ℚ := threeJRRadQ R * threeJRSumQ R ^ 2

/-- `threeJR R · |threeJR R|` over `ℚ`. -/
def threeJRSgnSqQ (R : Fin 3 → Fin 3 → ℕ) : ℚ :=
  (-1) ^ (R 2 0 + R 1 1) * threeJRRadQ R * (threeJRSumQ R * |threeJRSumQ R|)

lemma cast_threeJRRadQ (R : Fin 3 → Fin 3 → ℕ) : (threeJRRadQ R : ℝ) =
    (∏ i, ∏ j, ((R i j).factorial : ℝ)) / ((R 0 0 + R 0 1 + R 0 2 + 1).factorial : ℝ) := by
  simp only [threeJRRadQ, Rat.cast_div, Rat.cast_prod, Rat.cast_natCast]

lemma threeJRRadQ_nonneg (R : Fin 3 → Fin 3 → ℕ) : 0 ≤ (threeJRRadQ R : ℝ) := by
  rw [cast_threeJRRadQ]
  positivity

lemma cast_threeJRSumQ (R : Fin 3 → Fin 3 → ℕ) : (threeJRSumQ R : ℝ) =
    sixSum 0 ((R 1 0 : ℤ) - R 0 1) ((R 2 1 : ℤ) - R 0 0) (R 0 2) (R 1 0) (R 2 1) :=
  cast_sixSumQ _ _ _ _ _ _

/-- The 3j symbol of a Regge square in terms of the rational radicand `threeJRRadQ` and the
rational six-factorial sum `threeJRSumQ`. -/
lemma threeJR_eq_rat (R : Fin 3 → Fin 3 → ℕ) :
    threeJR R = (-1) ^ (R 2 0 + R 1 1) * Real.sqrt (threeJRRadQ R : ℝ) * (threeJRSumQ R : ℝ) := by
  rw [threeJR, cast_threeJRRadQ, cast_threeJRSumQ]

/-- `threeJRSqQ R` is the square of the 3j symbol of the Regge square `R`. -/
lemma cast_threeJRSqQ (R : Fin 3 → Fin 3 → ℕ) : (threeJRSqQ R : ℝ) = threeJR R ^ 2 := by
  have hs := Real.sq_sqrt (threeJRRadQ_nonneg R)
  have hp : ((-1 : ℝ) ^ (R 2 0 + R 1 1)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  rw [threeJR_eq_rat, threeJRSqQ, Rat.cast_mul, Rat.cast_pow, mul_pow, mul_pow, hp, hs, one_mul]

/-- `threeJRSgnSqQ R` is the 3j symbol of the Regge square `R` times its absolute value. -/
lemma cast_threeJRSgnSqQ (R : Fin 3 → Fin 3 → ℕ) :
    (threeJRSgnSqQ R : ℝ) = threeJR R * |threeJR R| := by
  have hs := Real.mul_self_sqrt (threeJRRadQ_nonneg R)
  rw [threeJR_eq_rat, threeJRSgnSqQ, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  push_cast
  linear_combination -(-1 : ℝ) ^ (R 2 0 + R 1 1) * ((threeJRSumQ R : ℝ) * |(threeJRSumQ R : ℝ)|) *
    hs

/-!

## C. Examples

Two values checked in the kernel. The Regge square of `(j₁ j₂ j₃; m₁ m₂ m₃)` has the rows
`(-j₁ + j₂ + j₃, j₁ - j₂ + j₃, j₁ + j₂ - j₃)`, `(j₁ - m₁, j₂ - m₂, j₃ - m₃)` and
`(j₁ + m₁, j₂ + m₂, j₃ + m₃)`.

-/

/-- `(½ ½ 0; ½ -½ 0) = 1 / √2`, so the symbol times its absolute value is `1 / 2`. -/
example : threeJRSgnSqQ ![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]] = 1 / 2 := by decide +kernel

/-- `(2 2 2; 0 0 0) = -√(2 / 35)`, so the symbol times its absolute value is `-2 / 35`. -/
example : threeJRSgnSqQ ![![2, 2, 2], ![2, 2, 2], ![2, 2, 2]] = -2 / 35 := by decide +kernel

end PhyslibAlpha.Sl2
