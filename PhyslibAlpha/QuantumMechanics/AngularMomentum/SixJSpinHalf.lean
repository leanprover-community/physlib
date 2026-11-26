/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.QuantumMechanics.AngularMomentum.SixJRational

/-!

# The 6j symbols of three spins ½

The four 6j symbols of three spins `½` and the recoupling matrix for total spin `½`.

## i. Overview

Three spins `½` couple to `J = 3/2` once and to `J = ½` twice: in the scheme `((1 2) 3)` the two
copies of `J = ½` have `j₁₂ = 1` (triplet) and `j₁₂ = 0` (singlet), in the scheme `(1 (2 3))` they
have `j₂₃ = 1` and `j₂₃ = 0`. In doubled units `sixJSym 1 1 j₁₂ 1 1 j₂₃` is
`{½ ½ j₁₂; ½ ½ j₂₃}`, with `j₁₂, j₂₃ ∈ {2, 0}`.

The rational values of `SixJRational` give the four values `{½ ½ 1; ½ ½ 1} = 1/6`,
`{½ ½ 1; ½ ½ 0} = {½ ½ 0; ½ ½ 1} = 1/2` and `{½ ½ 0; ½ ½ 0} = -1/2`. With `recoupling_eq_sixJ` and
`sixJ_eq_sixJSym` they give the recoupling coefficients
`⟨(½ ½) j₁₂, ½; ½ M | ½, (½ ½) j₂₃; ½ M⟩` for `J = ½`, independent of `M`: with rows `j₁₂ = 1, 0`
and columns `j₂₃ = 1, 0` they form the matrix `!![1/2, √3/2; √3/2, -1/2]`
(`recoupling_spinHalf`). The phase `(-1)^(j₁ + j₂ + j₃ + J)` of `sixJ` is `+1` here, and the phase
conventions are those of `ClebschGordanCoefficients` and `SixJ` (Condon–Shortley).

## ii. Key results

- `sixJSym_spinHalf_triplet_triplet`, `sixJSym_spinHalf_triplet_singlet`,
  `sixJSym_spinHalf_singlet_triplet`, `sixJSym_spinHalf_singlet_singlet`: the 6j symbols of three
  spins `½`.
- `recoupling_spinHalf`: the recoupling matrix of three spins `½` for `J = ½`.

## iii. Table of contents

- A. The 6j symbols of three spins ½
- B. The recoupling matrix

## iv. References

- D. A. Varshalovich, A. N. Moskalev, V. K. Khersonskii, *Quantum Theory of Angular Momentum*,
  World Scientific (1988): Sec. 9.1.1, p. 291, Eq. 9.1(5) (recoupling coefficients and 6j
  symbols) and Table 9.1, p. 311 (6j symbols with an argument ½).

-/

@[expose] public section

namespace PhyslibAlpha.Sl2

/-!

## A. The 6j symbols of three spins ½

-/

/-- `{½ ½ 1; ½ ½ 1} = 1/6`. -/
lemma sixJSym_spinHalf_triplet_triplet : sixJSym 1 1 2 1 1 2 = 1 / 6 := by
  rw [sixJSym_eq_sign_mul_sqrt, show sixJSgnSqQ 1 1 2 1 1 2 = 1 / 36 by decide +kernel,
    show ((1 / 36 : ℚ) : ℝ) = (1 / 6) ^ 2 by norm_num, abs_of_nonneg (by positivity),
    Real.sqrt_sq (by norm_num), Real.sign_of_pos (by norm_num), one_mul]

/-- `{½ ½ 1; ½ ½ 0} = 1/2`. -/
lemma sixJSym_spinHalf_triplet_singlet : sixJSym 1 1 2 1 1 0 = 1 / 2 := by
  rw [sixJSym_eq_sign_mul_sqrt, show sixJSgnSqQ 1 1 2 1 1 0 = 1 / 4 by decide +kernel,
    show ((1 / 4 : ℚ) : ℝ) = (1 / 2) ^ 2 by norm_num, abs_of_nonneg (by positivity),
    Real.sqrt_sq (by norm_num), Real.sign_of_pos (by norm_num), one_mul]

/-- `{½ ½ 0; ½ ½ 1} = 1/2`. -/
lemma sixJSym_spinHalf_singlet_triplet : sixJSym 1 1 0 1 1 2 = 1 / 2 := by
  rw [sixJSym_eq_sign_mul_sqrt, show sixJSgnSqQ 1 1 0 1 1 2 = 1 / 4 by decide +kernel,
    show ((1 / 4 : ℚ) : ℝ) = (1 / 2) ^ 2 by norm_num, abs_of_nonneg (by positivity),
    Real.sqrt_sq (by norm_num), Real.sign_of_pos (by norm_num), one_mul]

/-- `{½ ½ 0; ½ ½ 0} = -1/2`. -/
lemma sixJSym_spinHalf_singlet_singlet : sixJSym 1 1 0 1 1 0 = -1 / 2 := by
  rw [sixJSym_eq_sign_mul_sqrt, show sixJSgnSqQ 1 1 0 1 1 0 = -1 / 4 by decide +kernel,
    show ((-1 / 4 : ℚ) : ℝ) = -(1 / 2) ^ 2 by norm_num, abs_neg, abs_of_nonneg (by positivity),
    Real.sqrt_sq (by norm_num), Real.sign_of_neg (by norm_num)]
  norm_num

/-!

## B. The recoupling matrix

-/

/-- The recoupling coefficients `⟨(½ ½) j₁₂, ½; ½ M | ½, (½ ½) j₂₃; ½ M⟩` of three spins `½` for
`J = ½`, with `j₁₂ = 1 - k₁` and `j₂₃ = 1 - k₃`, for both `M = ½ - l`. -/
lemma recoupling_spinHalf (k₁ k₃ : Fin (min 1 1 + 1)) {l : ℕ} (hl : l ≤ 1) :
    recoupling (a := 1) (b := 1) (c := 1) (by norm_num) (by norm_num) 1 l k₁ k₃ =
      !![1 / 2, Real.sqrt 3 / 2; Real.sqrt 3 / 2, -1 / 2] k₁ k₃ := by
  have hA : ∀ k : Fin (min 1 1 + 1), ValidA 1 1 1 1 k := by intro k; fin_cases k <;> decide
  have hB : ∀ k : Fin (min 1 1 + 1), ValidB 1 1 1 1 k := by intro k; fin_cases k <;> decide
  rw [recoupling_eq_sixJ _ _ (by norm_num) (hA k₁) (hB k₃) (by omega),
    sixJ_eq_sixJSym _ _ (by norm_num) (by norm_num) (hA k₁) (hB k₃)]
  fin_cases k₁ <;> fin_cases k₃ <;>
    simp [sixJSym_spinHalf_triplet_triplet, sixJSym_spinHalf_triplet_singlet,
      sixJSym_spinHalf_singlet_triplet, sixJSym_spinHalf_singlet_singlet] <;> ring

end PhyslibAlpha.Sl2
