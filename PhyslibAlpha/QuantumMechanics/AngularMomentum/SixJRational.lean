/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.QuantumMechanics.AngularMomentum.ThreeJRational

/-!

# Rational values of the 6j symbols

The 6j symbols `sixJSym` of `SixJSymmetry` as a square root times a rational number, and
computable rational functions for their squares.

## i. Overview

In each term of `sixJSym` every spin `jᵢ` enters two of the four 3j symbols, with projections
`±mᵢ`. Written with `threeJ_eq_sqrt_mul` of `ThreeJRational`, the factorials
`(jᵢ - mᵢ)! (jᵢ + mᵢ)!` under the four square roots therefore occur in pairs, and the product of the
four square roots is `√C · ∏ᵢ (jᵢ - mᵢ)! (jᵢ + mᵢ)!` with
`C = Δ(j₁j₂j₃)² Δ(j₁j₅j₆)² Δ(j₄j₂j₆)² Δ(j₄j₅j₃)²` independent of the projections. Hence
`sixJSym = √C · T` with a rational sum `T = sixJSumQ` (`sixJSym_eq_sqrt_mul_sixJSumQ`).

Therefore `sixJSym ^ 2 = C T²` and `sixJSym · |sixJSym| = C T |T|` are rational (`sixJSqQ`,
`sixJSgnSqQ`), and the 6j symbol is `sign(q) √|q|` with `q = sixJSgnSqQ`
(`sixJSym_eq_sign_mul_sqrt`). Section C checks proven identities in the kernel with
`decide +kernel`.

## ii. Key results

- `sixJSym_eq_sqrt_mul_sixJSumQ`: `sixJSym = √C · sixJSumQ`.
- `sixJSqQ`, `cast_sixJSqQ`, `sixJSgnSqQ`, `cast_sixJSgnSqQ`, `sixJSym_eq_sign_mul_sqrt`: the 6j
  symbols squared, and with their sign, as rational numbers.

## iii. Table of contents

- A. The 6j symbol as a square root times a rational number
- B. Rational values of the 6j symbols
- C. Checks in the kernel

## iv. References

- NIST Digital Library of Mathematical Functions, Sec. 34.2, Eqs. 34.2.4–34.2.5, and Sec. 34.4,
  Eq. 34.4.1, https://dlmf.nist.gov/34.

-/

@[expose] public section

namespace PhyslibAlpha.Sl2

/-!

## A. The 6j symbol as a square root times a rational number

-/

/-- The constant `C = Δ(j₁j₂j₃)² Δ(j₁j₅j₆)² Δ(j₄j₂j₆)² Δ(j₄j₅j₃)²`. -/
def sixJRadQ (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) : ℚ :=
  triangleSqQ j₁ j₂ j₃ * triangleSqQ j₁ j₅ j₆ * triangleSqQ j₄ j₂ j₆ * triangleSqQ j₄ j₅ j₃

/-- The summand of `sixJSumQ`: the term of `sixJSym` divided by `√C`. -/
def sixJTermQ (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) (m : Fin 6 → ℤ) : ℚ :=
  if Adm3 j₁ j₂ j₃ (-m 0) (-m 1) (-m 2) ∧ Adm3 j₁ j₅ j₆ (m 0) (-m 4) (m 5) ∧
      Adm3 j₄ j₂ j₆ (m 3) (m 1) (-m 5) ∧ Adm3 j₄ j₅ j₃ (-m 3) (m 4) (m 2) then
    negOnePowQ (((j₁ : ℤ) - m 0 + ((j₂ : ℤ) - m 1) + ((j₃ : ℤ) - m 2) + ((j₄ : ℤ) - m 3) +
        ((j₅ : ℤ) - m 4) + ((j₆ : ℤ) - m 5)) / 2) *
      (threeJNumQ j₁ j₂ j₃ (-m 0) (-m 1) (-m 2) * threeJNumQ j₁ j₅ j₆ (m 0) (-m 4) (m 5) *
        threeJNumQ j₄ j₂ j₆ (m 3) (m 1) (-m 5) * threeJNumQ j₄ j₅ j₃ (-m 3) (m 4) (m 2)) *
      (facPairQ j₁ (m 0) * facPairQ j₂ (m 1) * facPairQ j₃ (m 2) * facPairQ j₄ (m 3) *
        facPairQ j₅ (m 4) * facPairQ j₆ (m 5))
  else 0

/-- The projections of a term of `sixJSym` in terms of the three free ones `m₁`, `m₂`, `m₅`. -/
def sixJVec (a b c : ℤ) : Fin 6 → ℤ := ![a, b, -a - b, c - a - b, c, c - a]

/-- The rational sum `T` with `sixJSym = √C · T`, over the three free projections. -/
def sixJSumQ (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) : ℚ :=
  ∑ a ∈ Finset.Icc (-(j₁ : ℤ)) j₁, ∑ b ∈ Finset.Icc (-(j₂ : ℤ)) j₂, ∑ c ∈ Finset.Icc (-(j₅ : ℤ)) j₅,
    sixJTermQ j₁ j₂ j₃ j₄ j₅ j₆ (sixJVec a b c)

lemma adm_of_sixJTermQ_ne_zero {j₁ j₂ j₃ j₄ j₅ j₆ : ℕ} {m : Fin 6 → ℤ}
    (h : sixJTermQ j₁ j₂ j₃ j₄ j₅ j₆ m ≠ 0) :
    Adm3 j₁ j₂ j₃ (-m 0) (-m 1) (-m 2) ∧ Adm3 j₁ j₅ j₆ (m 0) (-m 4) (m 5) ∧
      Adm3 j₄ j₂ j₆ (m 3) (m 1) (-m 5) ∧ Adm3 j₄ j₅ j₃ (-m 3) (m 4) (m 2) := by
  by_contra h'
  exact h (by rw [sixJTermQ, ite_eq_right h'])

/-- The sum over the three free projections is the sum over all six. -/
lemma sixJSumQ_eq_sum_sixJBox (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    sixJSumQ j₁ j₂ j₃ j₄ j₅ j₆ =
      ∑ m ∈ sixJBox j₁ j₂ j₃ j₄ j₅ j₆, sixJTermQ j₁ j₂ j₃ j₄ j₅ j₆ m := by
  rw [sixJSumQ]
  simp only [← Finset.sum_product']
  refine Finset.sum_bij_ne_zero (fun x _ _ => sixJVec x.1 x.2.1 x.2.2) ?_ ?_ ?_ ?_
  · intro x _ hx
    obtain ⟨h1, h2, -, h4⟩ := adm_of_sixJTermQ_ne_zero hx
    obtain ⟨-, a1, a2, b1, b2, c1, c2, -⟩ := h1
    obtain ⟨-, -, -, -, -, f1, f2, -⟩ := h2
    obtain ⟨-, d1, d2, e1, e2, -⟩ := h4
    rw [mem_sixJBox]
    simp only [sixJVec, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at a1 a2 b1 b2 c1 c2 d1 d2 e1 e2 f1 f2 ⊢
    omega
  · intro x _ _ y _ _ hxy
    have e0 := congrFun hxy 0
    have e1 := congrFun hxy 1
    have e4 := congrFun hxy 4
    simp only [sixJVec, Matrix.cons_val] at e0 e1 e4
    exact Prod.ext e0 (Prod.ext e1 e4)
  · intro m hm hm0
    obtain ⟨h1, h2, h3, _⟩ := adm_of_sixJTermQ_ne_zero hm0
    have e2 : m 2 = -m 0 - m 1 := by linarith [h1.1]
    have e5 : m 5 = m 4 - m 0 := by linarith [h2.1]
    have e3 : m 3 = m 4 - m 0 - m 1 := by linarith [h3.1]
    have hv : sixJVec (m 0) (m 1) (m 4) = m := by
      funext i
      fin_cases i <;> simp [sixJVec, e2, e3, e5]
    rw [mem_sixJBox] at hm
    obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, -, -, ⟨c1, c2⟩, -⟩ := hm
    exact ⟨(m 0, (m 1, m 4)), by simp only [Finset.mem_product, Finset.mem_Icc]; omega,
      by simpa [hv] using hm0, hv⟩
  · intro x _ _
    rfl

/-- A term of `sixJSym` is `√C` times a term of `sixJSumQ`. -/
lemma sixJTerm_eq_sqrt_mul (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) (m : Fin 6 → ℤ) :
    sixJTerm j₁ j₂ j₃ j₄ j₅ j₆ m =
      Real.sqrt (sixJRadQ j₁ j₂ j₃ j₄ j₅ j₆ : ℝ) * (sixJTermQ j₁ j₂ j₃ j₄ j₅ j₆ m : ℝ) := by
  rw [sixJTerm, sixJTermQ]
  split_ifs with h
  · obtain ⟨h1, h2, h3, h4⟩ := h
    rw [threeJ_eq_sqrt_mul h1, threeJ_eq_sqrt_mul h2, threeJ_eq_sqrt_mul h3, threeJ_eq_sqrt_mul h4]
    set P : ℚ := facPairQ j₁ (m 0) * facPairQ j₂ (m 1) * facPairQ j₃ (m 2) * facPairQ j₄ (m 3) *
      facPairQ j₅ (m 4) * facPairQ j₆ (m 5) with hP
    have n := facPairQ_nonneg
    have t := triangleSqQ_nonneg
    have hP0 : (0 : ℝ) ≤ (P : ℝ) := by
      rw [hP]
      exact_mod_cast mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (n _ _) (n _ _))
        (n _ _)) (n _ _)) (n _ _)) (n _ _)
    have r : ∀ a b c d : ℕ, ∀ x y z : ℤ,
        (0 : ℝ) ≤ ((triangleSqQ a b c * facPairQ d x * facPairQ b y * facPairQ c z : ℚ) : ℝ) :=
      fun a b c d x y z => by
        exact_mod_cast mul_nonneg (mul_nonneg (mul_nonneg (t _ _ _) (n _ _)) (n _ _)) (n _ _)
    -- the four radicands multiply to `C P²`
    have hrad : Real.sqrt ((triangleSqQ j₁ j₂ j₃ * facPairQ j₁ (-m 0) * facPairQ j₂ (-m 1) *
          facPairQ j₃ (-m 2) : ℚ) : ℝ) *
        Real.sqrt ((triangleSqQ j₁ j₅ j₆ * facPairQ j₁ (m 0) * facPairQ j₅ (-m 4) *
          facPairQ j₆ (m 5) : ℚ) : ℝ) *
        Real.sqrt ((triangleSqQ j₄ j₂ j₆ * facPairQ j₄ (m 3) * facPairQ j₂ (m 1) *
          facPairQ j₆ (-m 5) : ℚ) : ℝ) *
        Real.sqrt ((triangleSqQ j₄ j₅ j₃ * facPairQ j₄ (-m 3) * facPairQ j₅ (m 4) *
          facPairQ j₃ (m 2) : ℚ) : ℝ) =
        Real.sqrt (sixJRadQ j₁ j₂ j₃ j₄ j₅ j₆ : ℝ) * (P : ℝ) := by
      simp only [facPairQ_neg]
      have hC : (0 : ℝ) ≤ (sixJRadQ j₁ j₂ j₃ j₄ j₅ j₆ : ℝ) := by
        rw [sixJRadQ]
        exact_mod_cast mul_nonneg (mul_nonneg (mul_nonneg (t _ _ _) (t _ _ _)) (t _ _ _)) (t _ _ _)
      rw [← Real.sqrt_mul (r _ _ _ _ _ _ _), ← Real.sqrt_mul (mul_nonneg (r _ _ _ _ _ _ _)
        (r _ _ _ _ _ _ _)), ← Real.sqrt_mul (mul_nonneg (mul_nonneg (r _ _ _ _ _ _ _)
        (r _ _ _ _ _ _ _)) (r _ _ _ _ _ _ _)), ← Real.sqrt_sq hP0, ← Real.sqrt_mul hC]
      congr 1
      rw [hP, sixJRadQ]
      push_cast
      ring
    push_cast at hrad ⊢
    rw [cast_negOnePowQ]
    linear_combination (-1 : ℝ) ^ ((((j₁ : ℤ) - m 0 + ((j₂ : ℤ) - m 1) + ((j₃ : ℤ) - m 2) +
        ((j₄ : ℤ) - m 3) + ((j₅ : ℤ) - m 4) + ((j₆ : ℤ) - m 5)) / 2)) *
      ((threeJNumQ j₁ j₂ j₃ (-m 0) (-m 1) (-m 2) : ℝ) *
        (threeJNumQ j₁ j₅ j₆ (m 0) (-m 4) (m 5) : ℝ) *
        (threeJNumQ j₄ j₂ j₆ (m 3) (m 1) (-m 5) : ℝ) *
        (threeJNumQ j₄ j₅ j₃ (-m 3) (m 4) (m 2) : ℝ)) * hrad
  · have h0 : threeJ j₁ j₂ j₃ (-m 0) (-m 1) (-m 2) * threeJ j₁ j₅ j₆ (m 0) (-m 4) (m 5) *
        threeJ j₄ j₂ j₆ (m 3) (m 1) (-m 5) * threeJ j₄ j₅ j₃ (-m 3) (m 4) (m 2) = 0 := by
      by_cases h1 : Adm3 j₁ j₂ j₃ (-m 0) (-m 1) (-m 2)
      · by_cases h2 : Adm3 j₁ j₅ j₆ (m 0) (-m 4) (m 5)
        · by_cases h3 : Adm3 j₄ j₂ j₆ (m 3) (m 1) (-m 5)
          · rw [threeJ_of_not (fun h4 => h ⟨h1, h2, h3, h4⟩), mul_zero]
          · rw [threeJ_of_not h3]; ring
        · rw [threeJ_of_not h2]; ring
      · rw [threeJ_of_not h1]; ring
    rw [h0, mul_zero, Rat.cast_zero, mul_zero]

/-- **The 6j symbol as a square root times a rational number.** -/
lemma sixJSym_eq_sqrt_mul_sixJSumQ (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    sixJSym j₁ j₂ j₃ j₄ j₅ j₆ =
      Real.sqrt (sixJRadQ j₁ j₂ j₃ j₄ j₅ j₆ : ℝ) * (sixJSumQ j₁ j₂ j₃ j₄ j₅ j₆ : ℝ) := by
  rw [sixJSym, sixJSumQ_eq_sum_sixJBox, Rat.cast_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => sixJTerm_eq_sqrt_mul _ _ _ _ _ _ m

/-!

## B. Rational values of the 6j symbols

-/

lemma sixJRadQ_nonneg (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) : 0 ≤ sixJRadQ j₁ j₂ j₃ j₄ j₅ j₆ := by
  have t := triangleSqQ_nonneg
  exact mul_nonneg (mul_nonneg (mul_nonneg (t _ _ _) (t _ _ _)) (t _ _ _)) (t _ _ _)

/-- `sixJSym ^ 2` over `ℚ` (doubled units). -/
def sixJSqQ (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) : ℚ :=
  sixJRadQ j₁ j₂ j₃ j₄ j₅ j₆ * sixJSumQ j₁ j₂ j₃ j₄ j₅ j₆ ^ 2

/-- `sixJSym · |sixJSym|` over `ℚ` (doubled units). -/
def sixJSgnSqQ (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) : ℚ :=
  sixJRadQ j₁ j₂ j₃ j₄ j₅ j₆ * (sixJSumQ j₁ j₂ j₃ j₄ j₅ j₆ * |sixJSumQ j₁ j₂ j₃ j₄ j₅ j₆|)

section Rational

variable (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ)

lemma cast_sixJSqQ : (sixJSqQ j₁ j₂ j₃ j₄ j₅ j₆ : ℝ) = sixJSym j₁ j₂ j₃ j₄ j₅ j₆ ^ 2 := by
  have hC : (0 : ℝ) ≤ (sixJRadQ j₁ j₂ j₃ j₄ j₅ j₆ : ℝ) := by
    exact_mod_cast sixJRadQ_nonneg j₁ j₂ j₃ j₄ j₅ j₆
  rw [sixJSym_eq_sqrt_mul_sixJSumQ, mul_pow, Real.sq_sqrt hC, sixJSqQ, Rat.cast_mul, Rat.cast_pow]

lemma cast_sixJSgnSqQ :
    (sixJSgnSqQ j₁ j₂ j₃ j₄ j₅ j₆ : ℝ) =
      sixJSym j₁ j₂ j₃ j₄ j₅ j₆ * |sixJSym j₁ j₂ j₃ j₄ j₅ j₆| := by
  have hC : (0 : ℝ) ≤ (sixJRadQ j₁ j₂ j₃ j₄ j₅ j₆ : ℝ) := by
    exact_mod_cast sixJRadQ_nonneg j₁ j₂ j₃ j₄ j₅ j₆
  have hs := Real.mul_self_sqrt hC
  rw [sixJSym_eq_sqrt_mul_sixJSumQ, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), sixJSgnSqQ]
  push_cast
  linear_combination -((sixJSumQ j₁ j₂ j₃ j₄ j₅ j₆ : ℝ) * |(sixJSumQ j₁ j₂ j₃ j₄ j₅ j₆ : ℝ)|) * hs

/-- **The 6j symbol from a rational number.** `sixJSym = sign(q) √|q|` with `q = sixJSgnSqQ`. -/
lemma sixJSym_eq_sign_mul_sqrt :
    sixJSym j₁ j₂ j₃ j₄ j₅ j₆ =
      Real.sign (sixJSgnSqQ j₁ j₂ j₃ j₄ j₅ j₆ : ℝ) *
        Real.sqrt |(sixJSgnSqQ j₁ j₂ j₃ j₄ j₅ j₆ : ℝ)| := by
  rw [cast_sixJSgnSqQ]
  set t := sixJSym j₁ j₂ j₃ j₄ j₅ j₆
  rw [abs_mul, abs_abs, Real.sqrt_mul_self (abs_nonneg t)]
  rcases lt_trichotomy t 0 with h | h | h
  · rw [Real.sign_of_neg (mul_neg_of_neg_of_pos h (abs_pos.mpr h.ne)), abs_of_neg h]
    ring
  · simp [h]
  · rw [Real.sign_of_pos (mul_pos h (abs_pos.mpr h.ne')), abs_of_pos h, one_mul]

end Rational

/-!

## C. Checks in the kernel

Proven identities, evaluated with `decide +kernel` on small spins (doubled units). A 6j symbol
costs a triple sum over projections, so only a few values are checked here. Two computed values
are compared through their difference.

-/

/-- `Σ_{j₁₂} (2j₁₂ + 1)(2j₂₃ + 1) {j₁ j₂ j₁₂; j₃ J j₂₃}² = 1` (`sum_sixJ_mul_sixJ`, diagonal), for
`j₁ = j₂ = j₃ = J = 1` and all `j₂₃`. -/
example : ∀ f ∈ ([0, 2, 4] : List ℕ),
    ∑ e ∈ Finset.range 5, ((e : ℚ) + 1) * ((f : ℚ) + 1) * sixJSqQ 2 2 e 2 2 f = 1 := by
  decide +kernel

/-- `sixJSym_swap₁₂` on two sextets. -/
example : sixJSgnSqQ 2 1 3 1 2 2 - sixJSgnSqQ 1 2 3 2 1 2 = 0 ∧
    sixJSgnSqQ 1 2 1 1 0 1 - sixJSgnSqQ 2 1 1 0 1 1 = 0 := by
  decide +kernel

/-- `sixJSym_swap₂₃` on two sextets. -/
example : sixJSgnSqQ 1 3 2 2 2 1 - sixJSgnSqQ 1 2 3 2 1 2 = 0 ∧
    sixJSgnSqQ 2 1 3 1 2 2 - sixJSgnSqQ 2 3 1 1 2 2 = 0 := by
  decide +kernel

/-- `sixJSym_flip₁₂` on two sextets. -/
example : sixJSgnSqQ 1 2 1 2 3 2 - sixJSgnSqQ 2 3 1 1 2 2 = 0 ∧
    sixJSgnSqQ 0 1 1 2 1 1 - sixJSgnSqQ 2 1 1 0 1 1 = 0 := by
  decide +kernel

/-- An inadmissible 6j symbol vanishes, and an admissible one stated as a negation. -/
example : sixJSqQ 1 1 1 1 1 1 = 0 ∧ ¬sixJSqQ 2 2 2 2 2 2 = 0 := by
  decide +kernel

end PhyslibAlpha.Sl2
