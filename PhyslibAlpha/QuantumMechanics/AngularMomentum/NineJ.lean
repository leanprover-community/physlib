/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.QuantumMechanics.AngularMomentum.SixJSymmetry

/-!

# The 9j symbols

The 9j symbols as sums over products of three 6j symbols, and their invariance under
transposition.

## i. Overview

In doubled units, the 9j symbol
`{j₁₁ j₁₂ j₁₃; j₂₁ j₂₂ j₂₃; j₃₁ j₃₂ j₃₃}` is
`Σ_J (-1)^J (J + 1) {j₁₁ j₂₁ j₃₁; j₃₂ j₃₃ J} {j₁₂ j₂₂ j₃₂; j₂₁ J j₂₃} {j₁₃ j₂₃ j₃₃; J j₁₁ j₁₂}`
(`nineJSym`), with the 6j symbols `sixJSym` of `SixJSymmetry`. The first 6j symbol contains the
triad `(j₁₁ j₃₃ J)`, so it vanishes for `J > j₁₁ + j₃₃` (`sixJSym_eq_zero_of_lt`) and the sum is
over `J ≤ j₁₁ + j₃₃`. Extending the range does not change it (`nineJSym_eq_sum`).

Transposition of the 3 × 3 array fixes `j₁₁` and `j₃₃`, and hence the range of summation. It
exchanges the first and third 6j symbols and maps the second to itself, up to the tetrahedral
symmetries `sixJSym_swap₁₂`, `sixJSym_swap₂₃`, `sixJSym_flip₁₂`. So the 9j symbol is invariant
under transposition summand by summand (`nineJSym_transpose`).

## ii. Key results

- `nineJSym`: the 9j symbol as a sum over products of three 6j symbols.
- `nineJSym_eq_sum`: the sum may be taken over any larger range.
- `nineJSym_transpose`: invariance under transposition.

## iii. Table of contents

- A. The 9j symbol
- B. Invariance under transposition

## iv. References

- NIST Digital Library of Mathematical Functions, §34.6, https://dlmf.nist.gov/34.6, equation
  34.6.2, and §34.7, https://dlmf.nist.gov/34.7.
- D. A. Varshalovich, A. N. Moskalev, V. K. Khersonskii, *Quantum Theory of Angular Momentum*,
  World Scientific (1988), chapter 10.

## A. The 9j symbol

-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Sl2

/-- A 6j symbol whose triad `(j₁ j₅ j₆)` violates the triangle inequality `j₆ ≤ j₁ + j₅`
vanishes. -/
lemma sixJSym_eq_zero_of_lt {j₁ j₂ j₃ j₄ j₅ j₆ : ℕ} (h : j₁ + j₅ < j₆) :
    sixJSym j₁ j₂ j₃ j₄ j₅ j₆ = 0 := by
  refine Finset.sum_eq_zero fun m _ => ?_
  have h0 : threeJ j₁ j₅ j₆ (m 0) (-m 4) (m 5) = 0 :=
    threeJ_of_not fun h' => by
      obtain ⟨-, -, -, -, -, -, -, -, -, -, t, -, -, -⟩ := h'
      omega
  simp [sixJTerm, h0]

/-- The **9j symbol** `{j₁₁ j₁₂ j₁₃; j₂₁ j₂₂ j₂₃; j₃₁ j₃₂ j₃₃}` (doubled units) as a sum over
products of three 6j symbols. -/
def nineJSym (j₁₁ j₁₂ j₁₃ j₂₁ j₂₂ j₂₃ j₃₁ j₃₂ j₃₃ : ℕ) : ℝ :=
  ∑ J ∈ Finset.range (j₁₁ + j₃₃ + 1), (-1 : ℝ) ^ J * (J + 1) *
    (sixJSym j₁₁ j₂₁ j₃₁ j₃₂ j₃₃ J * sixJSym j₁₂ j₂₂ j₃₂ j₂₁ J j₂₃ *
      sixJSym j₁₃ j₂₃ j₃₃ J j₁₁ j₁₂)

/-- The sum defining `nineJSym` may be taken over any range containing `J ≤ j₁₁ + j₃₃`. -/
lemma nineJSym_eq_sum {j₁₁ j₁₂ j₁₃ j₂₁ j₂₂ j₂₃ j₃₁ j₃₂ j₃₃ N : ℕ} (hN : j₁₁ + j₃₃ < N) :
    nineJSym j₁₁ j₁₂ j₁₃ j₂₁ j₂₂ j₂₃ j₃₁ j₃₂ j₃₃ =
      ∑ J ∈ Finset.range N, (-1 : ℝ) ^ J * (J + 1) *
        (sixJSym j₁₁ j₂₁ j₃₁ j₃₂ j₃₃ J * sixJSym j₁₂ j₂₂ j₃₂ j₂₁ J j₂₃ *
          sixJSym j₁₃ j₂₃ j₃₃ J j₁₁ j₁₂) := by
  refine Finset.sum_subset (Finset.range_subset_range.2 hN) fun J _ hJ => ?_
  rw [Finset.mem_range, not_lt] at hJ
  rw [sixJSym_eq_zero_of_lt (by omega)]
  ring

/-!

## B. Invariance under transposition

-/

/-- **Transposition symmetry.** The 9j symbol is invariant under exchange of rows and columns. -/
lemma nineJSym_transpose (j₁₁ j₁₂ j₁₃ j₂₁ j₂₂ j₂₃ j₃₁ j₃₂ j₃₃ : ℕ) :
    nineJSym j₁₁ j₂₁ j₃₁ j₁₂ j₂₂ j₃₂ j₁₃ j₂₃ j₃₃ =
      nineJSym j₁₁ j₁₂ j₁₃ j₂₁ j₂₂ j₂₃ j₃₁ j₃₂ j₃₃ := by
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [sixJSym_flip₁₂ j₂₃ j₃₃ j₁₃ j₁₁ j₁₂ J, sixJSym_swap₂₃ j₂₃ j₁₃ j₃₃ j₁₁ J j₁₂,
    sixJSym_swap₁₂ j₁₃ j₂₃ j₃₃ J j₁₁ j₁₂, ← sixJSym_swap₂₃ j₂₁ j₂₂ j₂₃ j₁₂ J j₃₂,
    sixJSym_flip₁₂ j₁₂ j₃₂ j₂₂ j₂₁ j₂₃ J, sixJSym_swap₂₃ j₁₂ j₂₂ j₃₂ j₂₁ J j₂₃,
    sixJSym_flip₁₂ j₃₂ j₃₃ j₃₁ j₁₁ j₂₁ J, sixJSym_swap₂₃ j₃₂ j₃₁ j₃₃ j₁₁ J j₂₁,
    sixJSym_swap₁₂ j₃₁ j₃₂ j₃₃ J j₁₁ j₂₁]
  ring

end PhyslibAlpha.Sl2
