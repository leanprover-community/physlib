/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.QuantumMechanics.AngularMomentum.SixJ
public import PhyslibAlpha.QuantumMechanics.AngularMomentum.Wigner3j

/-!

# The tetrahedral symmetry of the 6j symbols

The 3j symbols with general arguments, the 6j symbols as sums over four 3j symbols, their
agreement with the 6j symbols of `SixJ`, and the 24 symmetries of the tetrahedron.

## i. Overview

`threeJ j₁ j₂ j₃ m₁ m₂ m₃` is the 3j symbol with spins and projections in doubled units, defined
through the Regge square of `Wigner3j` and set to zero for inadmissible arguments. It changes by
`(-1)^(j₁ + j₂ + j₃)` under an odd permutation of the columns and under `m ↦ -m`, and is invariant
under cyclic permutations (`threeJ_swap`, `threeJ_cycle`, `threeJ_neg`).

The 6j symbol

`{j₁ j₂ j₃; j₄ j₅ j₆} = Σ_m (-1)^(Σ (jᵢ - mᵢ)) (j₁ j₂ j₃; -m₁ -m₂ -m₃) (j₁ j₅ j₆; m₁ -m₅ m₆)
(j₄ j₂ j₆; m₄ m₂ -m₆) (j₄ j₅ j₃; -m₄ m₅ m₃)`

(`sixJSym`) is attached to a tetrahedron whose four faces are the four triads. Each generator of
its symmetry group is a change of summation variables, a permutation and sign change of the six
projections, under which the four 3j symbols are permuted and transformed by the 3j symmetries;
the signs cancel on the support. This gives

- `sixJSym_swap₁₂`, `sixJSym_swap₂₃`: invariance under permutations of the columns;
- `sixJSym_flip₁₂`: invariance under exchange of upper and lower arguments in two columns.

Indexing the six arguments by the edges of the tetrahedron whose vertices `0, 1, 2, 3` are the
triads `(j₁ j₂ j₃)`, `(j₁ j₅ j₆)`, `(j₄ j₂ j₆)`, `(j₄ j₅ j₃)` (`sixJSymEdge`), the three generators
become the vertex permutations `(1 2)`, `(2 3)` and `(0 3)(1 2)`. These generate the symmetric
group on the four vertices, so `sixJSymEdge_comp_map` gives invariance under every permutation of
the triads. The action on the edges is faithful (`sym2_map_perm_injective`), so these are 24
distinct symmetries.

The connection to the recoupling coefficients of `SixJ` is `sixJ_eq_sixJSym`. Expanding both
coupled states in the product basis writes `⟨(j₁ j₂) j₁₂, j₃; J M | j₁, (j₂ j₃) j₂₃; J M⟩` as a sum
over four Clebsch–Gordan coefficients (`recoupling_eq_sum`). Summing over `M`, which by
`recoupling_eq_recoupling_zero` multiplies by `2J + 1`, and converting the coefficients into 3j
symbols turns every summand into a summand of `sixJSym` (`cg_four_eq`, `sum_sixJTerm_eq`).

## ii. Key results

- `threeJ`, `threeJ_swap`, `threeJ_cycle`, `threeJ_neg`: the 3j symbol and its symmetries.
- `sixJSym`: the 6j symbol as a sum over four 3j symbols.
- `sixJSymEdge_comp_map`: invariance under all 24 symmetries of the tetrahedron, with the
  generators `sixJSym_swap₁₂`, `sixJSym_swap₂₃`, `sixJSym_flip₁₂` as special cases.
- `recoupling_eq_sum`: the recoupling coefficient through four Clebsch–Gordan coefficients.
- `sixJ_eq_sixJSym`: the 6j symbols of `SixJ` are the symmetric sums.

## iii. Table of contents

- A. The 3j symbol with general arguments
- B. The 6j symbol as a sum over four 3j symbols
- C. The tetrahedral symmetry
- D. The 6j symbols of `SixJ` as sums over four 3j symbols

## iv. References

- G. Racah, *Theory of complex spectra. II*, Phys. Rev. 62, 438 (1942).
- A. R. Edmonds, *Angular Momentum in Quantum Mechanics*, Princeton University Press (1957),
  chapter 6.

## A. The 3j symbol with general arguments

-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Sl2

/-- Admissibility of `(j₁ j₂ j₃; m₁ m₂ m₃)` in doubled units: the projections add up to zero,
`|mᵢ| ≤ jᵢ`, `jᵢ - mᵢ` is even and the triangle condition holds with even perimeter. -/
abbrev Adm3 (j₁ j₂ j₃ : ℕ) (m₁ m₂ m₃ : ℤ) : Prop :=
  m₁ + m₂ + m₃ = 0 ∧ -(j₁ : ℤ) ≤ m₁ ∧ m₁ ≤ j₁ ∧ -(j₂ : ℤ) ≤ m₂ ∧ m₂ ≤ j₂ ∧
    -(j₃ : ℤ) ≤ m₃ ∧ m₃ ≤ j₃ ∧ ((j₁ : ℤ) - m₁) % 2 = 0 ∧ ((j₂ : ℤ) - m₂) % 2 = 0 ∧
      ((j₃ : ℤ) - m₃) % 2 = 0 ∧ j₃ ≤ j₁ + j₂ ∧ j₁ ≤ j₂ + j₃ ∧ j₂ ≤ j₁ + j₃ ∧
        (j₁ + j₂ + j₃) % 2 = 0

/-- The Regge square of `(j₁ j₂ j₃; m₁ m₂ m₃)` in doubled units. -/
def reggeJ (j₁ j₂ j₃ : ℕ) (m₁ m₂ m₃ : ℤ) : Fin 3 → Fin 3 → ℕ :=
  ![![(j₂ + j₃ - j₁) / 2, (j₁ + j₃ - j₂) / 2, (j₁ + j₂ - j₃) / 2],
    ![(((j₁ : ℤ) - m₁) / 2).toNat, (((j₂ : ℤ) - m₂) / 2).toNat, (((j₃ : ℤ) - m₃) / 2).toNat],
    ![(((j₁ : ℤ) + m₁) / 2).toNat, (((j₂ : ℤ) + m₂) / 2).toNat, (((j₃ : ℤ) + m₃) / 2).toNat]]

/-- The **3j symbol** `(j₁ j₂ j₃; m₁ m₂ m₃)` with `jᵢ` and `mᵢ` given in doubled units, zero for
inadmissible arguments. -/
def threeJ (j₁ j₂ j₃ : ℕ) (m₁ m₂ m₃ : ℤ) : ℝ :=
  if Adm3 j₁ j₂ j₃ m₁ m₂ m₃ then threeJR (reggeJ j₁ j₂ j₃ m₁ m₂ m₃) else 0

variable {j₁ j₂ j₃ : ℕ} {m₁ m₂ m₃ : ℤ}

lemma threeJ_of_not (h : ¬Adm3 j₁ j₂ j₃ m₁ m₂ m₃) : threeJ j₁ j₂ j₃ m₁ m₂ m₃ = 0 := by
  rw [threeJ, ite_eq_right h]

lemma adm3_of_threeJ_ne_zero (h : threeJ j₁ j₂ j₃ m₁ m₂ m₃ ≠ 0) : Adm3 j₁ j₂ j₃ m₁ m₂ m₃ := by
  by_contra h'
  exact h (threeJ_of_not h')

lemma isMagic_reggeJ (h : Adm3 j₁ j₂ j₃ m₁ m₂ m₃) : IsMagic (reggeJ j₁ j₂ j₃ m₁ m₂ m₃) := by
  obtain ⟨hs, h1, h2, h3, h4, h5, h6, hp1, hp2, hp3, ht1, ht2, ht3, hpar⟩ := h
  have e1 : ((((j₁ : ℤ) - m₁) / 2).toNat : ℤ) * 2 = (j₁ : ℤ) - m₁ := by omega
  have e2 : ((((j₂ : ℤ) - m₂) / 2).toNat : ℤ) * 2 = (j₂ : ℤ) - m₂ := by omega
  have e3 : ((((j₃ : ℤ) - m₃) / 2).toNat : ℤ) * 2 = (j₃ : ℤ) - m₃ := by omega
  have f1 : ((((j₁ : ℤ) + m₁) / 2).toNat : ℤ) * 2 = (j₁ : ℤ) + m₁ := by omega
  have f2 : ((((j₂ : ℤ) + m₂) / 2).toNat : ℤ) * 2 = (j₂ : ℤ) + m₂ := by omega
  have f3 : ((((j₃ : ℤ) + m₃) / 2).toNat : ℤ) * 2 = (j₃ : ℤ) + m₃ := by omega
  simp only [IsMagic, reggeJ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  generalize (((j₁ : ℤ) - m₁) / 2).toNat = p₁ at *
  generalize (((j₂ : ℤ) - m₂) / 2).toNat = p₂ at *
  generalize (((j₃ : ℤ) - m₃) / 2).toNat = p₃ at *
  generalize (((j₁ : ℤ) + m₁) / 2).toNat = q₁ at *
  generalize (((j₂ : ℤ) + m₂) / 2).toNat = q₂ at *
  generalize (((j₃ : ℤ) + m₃) / 2).toNat = q₃ at *
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega

lemma reggeJ_row_sum (h : Adm3 j₁ j₂ j₃ m₁ m₂ m₃) :
    reggeJ j₁ j₂ j₃ m₁ m₂ m₃ 0 0 + reggeJ j₁ j₂ j₃ m₁ m₂ m₃ 0 1 +
      reggeJ j₁ j₂ j₃ m₁ m₂ m₃ 0 2 = (j₁ + j₂ + j₃) / 2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, ht1, ht2, ht3, hpar⟩ := h
  simp [reggeJ]
  omega

/-- Exchange of the first two columns:
`(j₂ j₁ j₃; m₂ m₁ m₃) = (-1)^(j₁+j₂+j₃) (j₁ j₂ j₃; m₁ m₂ m₃)`. -/
lemma threeJ_swap (j₁ j₂ j₃ : ℕ) (m₁ m₂ m₃ : ℤ) :
    threeJ j₂ j₁ j₃ m₂ m₁ m₃ = (-1) ^ ((j₁ + j₂ + j₃) / 2) * threeJ j₁ j₂ j₃ m₁ m₂ m₃ := by
  by_cases h : Adm3 j₁ j₂ j₃ m₁ m₂ m₃
  · have h' : Adm3 j₂ j₁ j₃ m₂ m₁ m₃ := by omega
    rw [threeJ, ite_eq_left h', threeJ, ite_eq_left h]
    have hR := threeJR_swap_columns (isMagic_reggeJ h)
    have hE : reggeJ j₂ j₁ j₃ m₂ m₁ m₃ = fun i => ![reggeJ j₁ j₂ j₃ m₁ m₂ m₃ i 1,
        reggeJ j₁ j₂ j₃ m₁ m₂ m₃ i 0, reggeJ j₁ j₂ j₃ m₁ m₂ m₃ i 2] := by
      obtain ⟨hs, h1, h2, h3, h4, h5, h6, hp1, hp2, hp3, ht1, ht2, ht3, hpar⟩ := h
      funext i k
      fin_cases i <;> fin_cases k <;> simp [reggeJ]
      omega
    rw [hE, hR, reggeJ_row_sum h]
  · have h' : ¬Adm3 j₂ j₁ j₃ m₂ m₁ m₃ := by omega
    rw [threeJ_of_not h, threeJ_of_not h', mul_zero]

/-- Cyclic permutation of the columns: `(j₂ j₃ j₁; m₂ m₃ m₁) = (j₁ j₂ j₃; m₁ m₂ m₃)`. -/
lemma threeJ_cycle (j₁ j₂ j₃ : ℕ) (m₁ m₂ m₃ : ℤ) :
    threeJ j₂ j₃ j₁ m₂ m₃ m₁ = threeJ j₁ j₂ j₃ m₁ m₂ m₃ := by
  by_cases h : Adm3 j₁ j₂ j₃ m₁ m₂ m₃
  · have h' : Adm3 j₂ j₃ j₁ m₂ m₃ m₁ := by omega
    rw [threeJ, ite_eq_left h', threeJ, ite_eq_left h]
    have hR := threeJR_cycle_columns (isMagic_reggeJ h)
    have hE : reggeJ j₂ j₃ j₁ m₂ m₃ m₁ = fun i => ![reggeJ j₁ j₂ j₃ m₁ m₂ m₃ i 1,
        reggeJ j₁ j₂ j₃ m₁ m₂ m₃ i 2, reggeJ j₁ j₂ j₃ m₁ m₂ m₃ i 0] := by
      obtain ⟨hs, h1, h2, h3, h4, h5, h6, hp1, hp2, hp3, ht1, ht2, ht3, hpar⟩ := h
      funext i k
      fin_cases i <;> fin_cases k <;> simp [reggeJ] <;> omega
    rw [hE, hR]
  · have h' : ¬Adm3 j₂ j₃ j₁ m₂ m₃ m₁ := by omega
    rw [threeJ_of_not h, threeJ_of_not h']

/-- Reversal of the projections:
`(j₁ j₂ j₃; -m₁ -m₂ -m₃) = (-1)^(j₁+j₂+j₃) (j₁ j₂ j₃; m₁ m₂ m₃)`. -/
lemma threeJ_neg (j₁ j₂ j₃ : ℕ) (m₁ m₂ m₃ : ℤ) :
    threeJ j₁ j₂ j₃ (-m₁) (-m₂) (-m₃) = (-1) ^ ((j₁ + j₂ + j₃) / 2) * threeJ j₁ j₂ j₃ m₁ m₂ m₃ := by
  by_cases h : Adm3 j₁ j₂ j₃ m₁ m₂ m₃
  · have h' : Adm3 j₁ j₂ j₃ (-m₁) (-m₂) (-m₃) := by omega
    rw [threeJ, ite_eq_left h', threeJ, ite_eq_left h]
    have hR := threeJR_swap_rows (isMagic_reggeJ h)
    have hE : reggeJ j₁ j₂ j₃ (-m₁) (-m₂) (-m₃) = ![reggeJ j₁ j₂ j₃ m₁ m₂ m₃ 0,
        reggeJ j₁ j₂ j₃ m₁ m₂ m₃ 2, reggeJ j₁ j₂ j₃ m₁ m₂ m₃ 1] := by
      obtain ⟨hs, h1, h2, h3, h4, h5, h6, hp1, hp2, hp3, ht1, ht2, ht3, hpar⟩ := h
      funext i k
      fin_cases i <;> fin_cases k <;> simp [reggeJ] <;> omega
    rw [hE, hR, reggeJ_row_sum h]
  · have h' : ¬Adm3 j₁ j₂ j₃ (-m₁) (-m₂) (-m₃) := by omega
    rw [threeJ_of_not h, threeJ_of_not h', mul_zero]

/-- The 3j symbols of `Wigner3j` in terms of `threeJ`. -/
lemma wigner3j_eq_threeJ {m n k l α β : ℕ} (hkm : k ≤ m) (hkn : k ≤ n)
    (hl : l ≤ m + n - 2 * k) (hα : α ≤ m) (hβ : β ≤ n) :
    wigner3j m n k l α β = threeJ m n (m + n - 2 * k) ((m : ℤ) - 2 * α) ((n : ℤ) - 2 * β)
      (-(((m + n - 2 * k : ℕ) : ℤ) - 2 * l)) := by
  by_cases h : α + β = k + l
  · have hA : Adm3 m n (m + n - 2 * k) ((m : ℤ) - 2 * α) ((n : ℤ) - 2 * β)
        (-(((m + n - 2 * k : ℕ) : ℤ) - 2 * l)) := by omega
    rw [wigner3j, ite_eq_left h, threeJ, ite_eq_left hA]
    congr 1
    funext i j
    fin_cases i <;> fin_cases j <;> simp [regge, reggeJ] <;> omega
  · have hA : ¬Adm3 m n (m + n - 2 * k) ((m : ℤ) - 2 * α) ((n : ℤ) - 2 * β)
        (-(((m + n - 2 * k : ℕ) : ℤ) - 2 * l)) := by omega
    rw [wigner3j, ite_eq_right h, threeJ_of_not hA]

/-!

## B. The 6j symbol as a sum over four 3j symbols

-/

/-- The summand of `sixJSym`:
`(-1)^(Σ (jᵢ - mᵢ)) (j₁ j₂ j₃; -m₁ -m₂ -m₃) (j₁ j₅ j₆; m₁ -m₅ m₆) (j₄ j₂ j₆; m₄ m₂ -m₆)
(j₄ j₅ j₃; -m₄ m₅ m₃)`. -/
def sixJTerm (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) (m : Fin 6 → ℤ) : ℝ :=
  (-1 : ℝ) ^ (((j₁ : ℤ) - m 0 + ((j₂ : ℤ) - m 1) + ((j₃ : ℤ) - m 2) + ((j₄ : ℤ) - m 3) +
      ((j₅ : ℤ) - m 4) + ((j₆ : ℤ) - m 5)) / 2) *
    (threeJ j₁ j₂ j₃ (-m 0) (-m 1) (-m 2) * threeJ j₁ j₅ j₆ (m 0) (-m 4) (m 5) *
      threeJ j₄ j₂ j₆ (m 3) (m 1) (-m 5) * threeJ j₄ j₅ j₃ (-m 3) (m 4) (m 2))

/-- The projections `|mᵢ| ≤ jᵢ`. -/
def sixJBox (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) : Finset (Fin 6 → ℤ) :=
  Fintype.piFinset ![Finset.Icc (-(j₁ : ℤ)) j₁, Finset.Icc (-(j₂ : ℤ)) j₂,
    Finset.Icc (-(j₃ : ℤ)) j₃, Finset.Icc (-(j₄ : ℤ)) j₄, Finset.Icc (-(j₅ : ℤ)) j₅,
    Finset.Icc (-(j₆ : ℤ)) j₆]

lemma mem_sixJBox {j₁ j₂ j₃ j₄ j₅ j₆ : ℕ} {m : Fin 6 → ℤ} :
    m ∈ sixJBox j₁ j₂ j₃ j₄ j₅ j₆ ↔ (-(j₁ : ℤ) ≤ m 0 ∧ m 0 ≤ j₁) ∧
      (-(j₂ : ℤ) ≤ m 1 ∧ m 1 ≤ j₂) ∧ (-(j₃ : ℤ) ≤ m 2 ∧ m 2 ≤ j₃) ∧
        (-(j₄ : ℤ) ≤ m 3 ∧ m 3 ≤ j₄) ∧ (-(j₅ : ℤ) ≤ m 4 ∧ m 4 ≤ j₅) ∧
          (-(j₆ : ℤ) ≤ m 5 ∧ m 5 ≤ j₆) := by
  simp [sixJBox, Fintype.mem_piFinset, Fin.forall_fin_succ]

/-- The **6j symbol** `{j₁ j₂ j₃; j₄ j₅ j₆}` (doubled units) as a sum over the projections of
four 3j symbols. -/
def sixJSym (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) : ℝ :=
  ∑ m ∈ sixJBox j₁ j₂ j₃ j₄ j₅ j₆, sixJTerm j₁ j₂ j₃ j₄ j₅ j₆ m

/-!

## C. The tetrahedral symmetry

-/

lemma neg_one_zpow_mul_pow_four {S S' : ℤ} {p q r s : ℕ}
    (h : (S' + p + q + r + s) % 2 = S % 2) :
    (-1 : ℝ) ^ S' * ((-1) ^ p * (-1) ^ q * (-1) ^ r * (-1) ^ s) = (-1) ^ S := by
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (by norm_num),
    ← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num),
    show S' + (p + q + r + s : ℤ) = S' + p + q + r + s by ring]
  exact neg_one_zpow_congr h

lemma prod_four_eq_zero_or {F₁ F₂ F₃ F₄ : ℝ} {P : Prop}
    (h : F₁ ≠ 0 → F₂ ≠ 0 → F₃ ≠ 0 → F₄ ≠ 0 → P) : F₁ * F₂ * F₃ * F₄ = 0 ∨ P := by
  by_cases h₁ : F₁ = 0
  · simp [h₁]
  by_cases h₂ : F₂ = 0
  · simp [h₂]
  by_cases h₃ : F₃ = 0
  · simp [h₃]
  by_cases h₄ : F₄ = 0
  · simp [h₄]
  exact Or.inr (h h₁ h₂ h₃ h₄)

lemma term_congr_1324 {S S' : ℤ} {p q r s : ℕ} {F₁ F₂ F₃ F₄ : ℝ}
    (h : F₁ ≠ 0 → F₂ ≠ 0 → F₃ ≠ 0 → F₄ ≠ 0 → (S' + p + q + r + s) % 2 = S % 2) :
    (-1 : ℝ) ^ S * (F₁ * F₂ * F₃ * F₄) =
      (-1) ^ S' * ((-1) ^ p * F₁ * ((-1) ^ q * F₃) * ((-1) ^ r * F₂) * ((-1) ^ s * F₄)) := by
  rcases prod_four_eq_zero_or h with h0 | h0
  · rw [show (-1 : ℝ) ^ S' * ((-1) ^ p * F₁ * ((-1) ^ q * F₃) * ((-1) ^ r * F₂) *
      ((-1) ^ s * F₄)) = (-1) ^ S' * ((-1) ^ p * (-1) ^ q * (-1) ^ r * (-1) ^ s) *
        (F₁ * F₂ * F₃ * F₄) by ring, h0]
    simp
  · rw [← neg_one_zpow_mul_pow_four h0]
    ring

lemma term_congr_1243 {S S' : ℤ} {p q r s : ℕ} {F₁ F₂ F₃ F₄ : ℝ}
    (h : F₁ ≠ 0 → F₂ ≠ 0 → F₃ ≠ 0 → F₄ ≠ 0 → (S' + p + q + r + s) % 2 = S % 2) :
    (-1 : ℝ) ^ S * (F₁ * F₂ * F₃ * F₄) =
      (-1) ^ S' * ((-1) ^ p * F₁ * ((-1) ^ q * F₂) * ((-1) ^ r * F₄) * ((-1) ^ s * F₃)) := by
  rcases prod_four_eq_zero_or h with h0 | h0
  · rw [show (-1 : ℝ) ^ S' * ((-1) ^ p * F₁ * ((-1) ^ q * F₂) * ((-1) ^ r * F₄) *
      ((-1) ^ s * F₃)) = (-1) ^ S' * ((-1) ^ p * (-1) ^ q * (-1) ^ r * (-1) ^ s) *
        (F₁ * F₂ * F₃ * F₄) by ring, h0]
    simp
  · rw [← neg_one_zpow_mul_pow_four h0]
    ring

lemma term_congr_4321 {S S' : ℤ} {F₁ F₂ F₃ F₄ : ℝ}
    (h : F₁ ≠ 0 → F₂ ≠ 0 → F₃ ≠ 0 → F₄ ≠ 0 → S' % 2 = S % 2) :
    (-1 : ℝ) ^ S * (F₁ * F₂ * F₃ * F₄) = (-1) ^ S' * (F₄ * F₃ * F₂ * F₁) := by
  rcases prod_four_eq_zero_or h with h0 | h0
  · rw [show F₄ * F₃ * F₂ * F₁ = F₁ * F₂ * F₃ * F₄ by ring, h0]
    simp
  · rw [neg_one_zpow_congr h0]
    ring

/-- Exchange of the last two columns:
`(j₁ j₃ j₂; m₁ m₃ m₂) = (-1)^(j₁+j₂+j₃) (j₁ j₂ j₃; m₁ m₂ m₃)`. -/
lemma threeJ_swap₂₃ (j₁ j₂ j₃ : ℕ) (m₁ m₂ m₃ : ℤ) :
    threeJ j₁ j₃ j₂ m₁ m₃ m₂ = (-1) ^ ((j₁ + j₂ + j₃) / 2) * threeJ j₁ j₂ j₃ m₁ m₂ m₃ := by
  rw [threeJ_cycle j₂ j₁ j₃ m₂ m₁ m₃, threeJ_swap]

/-- `(j₂ j₃ j₁; -m₂ m₃ -m₁) = (-1)^(j₁+j₂+j₃) (j₁ j₂ j₃; m₁ m₂ -m₃)`. -/
lemma threeJ_negCycle (j₁ j₂ j₃ : ℕ) (x y z : ℤ) :
    threeJ j₂ j₃ j₁ (-y) z (-x) = (-1) ^ ((j₁ + j₂ + j₃) / 2) * threeJ j₁ j₂ j₃ x y (-z) := by
  have h := threeJ_neg j₂ j₃ j₁ y (-z) x
  rw [neg_neg, threeJ_cycle j₁ j₂ j₃ x y (-z)] at h
  rw [h, show (j₂ + j₃ + j₁) / 2 = (j₁ + j₂ + j₃) / 2 by ring_nf]

variable (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ)

/-- Exchange of the first two columns: `{j₂ j₁ j₃; j₅ j₄ j₆} = {j₁ j₂ j₃; j₄ j₅ j₆}`. -/
lemma sixJSym_swap₁₂ : sixJSym j₂ j₁ j₃ j₅ j₄ j₆ = sixJSym j₁ j₂ j₃ j₄ j₅ j₆ := by
  symm
  refine Finset.sum_nbij' (fun m => ![m 1, m 0, m 2, -m 4, -m 3, -m 5])
    (fun m => ![m 1, m 0, m 2, -m 4, -m 3, -m 5]) (fun m hm => ?_) (fun m hm => ?_)
    (fun m _ => ?_) (fun m _ => ?_) (fun m _ => ?_)
  · rw [mem_sixJBox] at hm ⊢
    simp only [Matrix.cons_val]
    omega
  · rw [mem_sixJBox] at hm ⊢
    simp only [Matrix.cons_val]
    omega
  · funext i
    fin_cases i <;> simp
  · funext i
    fin_cases i <;> simp
  · simp only [sixJTerm, Matrix.cons_val, neg_neg]
    rw [threeJ_swap j₁ j₂ j₃, threeJ_swap j₄ j₂ j₆, threeJ_swap j₁ j₅ j₆, threeJ_swap j₄ j₅ j₃]
    refine term_congr_1324 fun h₁ h₂ h₃ h₄ => ?_
    obtain ⟨s₁, -, -, -, -, -, -, p₁, p₂, p₃, -, -, -, t₁⟩ := adm3_of_threeJ_ne_zero h₁
    obtain ⟨s₂, -, -, -, -, -, -, -, p₅, p₆, -, -, -, t₂⟩ := adm3_of_threeJ_ne_zero h₂
    obtain ⟨s₃, -, -, -, -, -, -, p₄, -, -, -, -, -, t₃⟩ := adm3_of_threeJ_ne_zero h₃
    obtain ⟨s₄, -, -, -, -, -, -, -, -, -, -, -, -, t₄⟩ := adm3_of_threeJ_ne_zero h₄
    omega

/-- Exchange of the last two columns: `{j₁ j₃ j₂; j₄ j₆ j₅} = {j₁ j₂ j₃; j₄ j₅ j₆}`. -/
lemma sixJSym_swap₂₃ : sixJSym j₁ j₃ j₂ j₄ j₆ j₅ = sixJSym j₁ j₂ j₃ j₄ j₅ j₆ := by
  symm
  refine Finset.sum_nbij' (fun m => ![m 0, m 2, m 1, -m 3, -m 5, -m 4])
    (fun m => ![m 0, m 2, m 1, -m 3, -m 5, -m 4]) (fun m hm => ?_) (fun m hm => ?_)
    (fun m _ => ?_) (fun m _ => ?_) (fun m _ => ?_)
  · rw [mem_sixJBox] at hm ⊢
    simp only [Matrix.cons_val]
    omega
  · rw [mem_sixJBox] at hm ⊢
    simp only [Matrix.cons_val]
    omega
  · funext i
    fin_cases i <;> simp
  · funext i
    fin_cases i <;> simp
  · simp only [sixJTerm, Matrix.cons_val, neg_neg]
    rw [threeJ_swap₂₃ j₁ j₂ j₃, threeJ_swap₂₃ j₁ j₅ j₆, threeJ_swap₂₃ j₄ j₅ j₃,
      threeJ_swap₂₃ j₄ j₂ j₆]
    refine term_congr_1243 fun h₁ h₂ h₃ h₄ => ?_
    obtain ⟨s₁, -, -, -, -, -, -, p₁, p₂, p₃, -, -, -, t₁⟩ := adm3_of_threeJ_ne_zero h₁
    obtain ⟨s₂, -, -, -, -, -, -, -, p₅, p₆, -, -, -, t₂⟩ := adm3_of_threeJ_ne_zero h₂
    obtain ⟨s₃, -, -, -, -, -, -, p₄, -, -, -, -, -, t₃⟩ := adm3_of_threeJ_ne_zero h₃
    obtain ⟨s₄, -, -, -, -, -, -, -, -, -, -, -, -, t₄⟩ := adm3_of_threeJ_ne_zero h₄
    omega

/-- Exchange of upper and lower arguments in the first two columns:
`{j₄ j₅ j₃; j₁ j₂ j₆} = {j₁ j₂ j₃; j₄ j₅ j₆}`. -/
lemma sixJSym_flip₁₂ : sixJSym j₄ j₅ j₃ j₁ j₂ j₆ = sixJSym j₁ j₂ j₃ j₄ j₅ j₆ := by
  symm
  refine Finset.sum_nbij' (fun m => ![m 3, -m 4, -m 2, m 0, -m 1, -m 5])
    (fun m => ![m 3, -m 4, -m 2, m 0, -m 1, -m 5]) (fun m hm => ?_) (fun m hm => ?_)
    (fun m _ => ?_) (fun m _ => ?_) (fun m _ => ?_)
  · rw [mem_sixJBox] at hm ⊢
    simp only [Matrix.cons_val]
    omega
  · rw [mem_sixJBox] at hm ⊢
    simp only [Matrix.cons_val]
    omega
  · funext i
    fin_cases i <;> simp
  · funext i
    fin_cases i <;> simp
  · simp only [sixJTerm, Matrix.cons_val, neg_neg]
    refine term_congr_4321 fun h₁ h₂ h₃ h₄ => ?_
    obtain ⟨s₁, -, -, -, -, -, -, p₁, p₂, p₃, -, -, -, t₁⟩ := adm3_of_threeJ_ne_zero h₁
    obtain ⟨s₂, -, -, -, -, -, -, -, p₅, p₆, -, -, -, t₂⟩ := adm3_of_threeJ_ne_zero h₂
    obtain ⟨s₃, -, -, -, -, -, -, p₄, -, -, -, -, -, t₃⟩ := adm3_of_threeJ_ne_zero h₃
    obtain ⟨s₄, -, -, -, -, -, -, -, -, -, -, -, -, t₄⟩ := adm3_of_threeJ_ne_zero h₄
    omega

/-- The 6j symbol as a function of the edge labels of the tetrahedron whose vertices are the four
triads `0 = (j₁ j₂ j₃)`, `1 = (j₁ j₅ j₆)`, `2 = (j₄ j₂ j₆)`, `3 = (j₄ j₅ j₃)`. -/
def sixJSymEdge (j : Sym2 (Fin 4) → ℕ) : ℝ :=
  sixJSym (j s(0, 1)) (j s(0, 2)) (j s(0, 3)) (j s(2, 3)) (j s(1, 3)) (j s(1, 2))

lemma sixJSymEdge_comp_map_swap₁₂ (j : Sym2 (Fin 4) → ℕ) :
    sixJSymEdge (j ∘ Sym2.map (Equiv.swap 1 2)) = sixJSymEdge j := by
  simp only [sixJSymEdge, Function.comp_apply]
  rw [show Sym2.map (Equiv.swap (1 : Fin 4) 2) s(0, 1) = s(0, 2) by decide,
    show Sym2.map (Equiv.swap (1 : Fin 4) 2) s(0, 2) = s(0, 1) by decide,
    show Sym2.map (Equiv.swap (1 : Fin 4) 2) s(0, 3) = s(0, 3) by decide,
    show Sym2.map (Equiv.swap (1 : Fin 4) 2) s(2, 3) = s(1, 3) by decide,
    show Sym2.map (Equiv.swap (1 : Fin 4) 2) s(1, 3) = s(2, 3) by decide,
    show Sym2.map (Equiv.swap (1 : Fin 4) 2) s(1, 2) = s(1, 2) by decide]
  exact sixJSym_swap₁₂ ..

lemma sixJSymEdge_comp_map_swap₂₃ (j : Sym2 (Fin 4) → ℕ) :
    sixJSymEdge (j ∘ Sym2.map (Equiv.swap 2 3)) = sixJSymEdge j := by
  simp only [sixJSymEdge, Function.comp_apply]
  rw [show Sym2.map (Equiv.swap (2 : Fin 4) 3) s(0, 1) = s(0, 1) by decide,
    show Sym2.map (Equiv.swap (2 : Fin 4) 3) s(0, 2) = s(0, 3) by decide,
    show Sym2.map (Equiv.swap (2 : Fin 4) 3) s(0, 3) = s(0, 2) by decide,
    show Sym2.map (Equiv.swap (2 : Fin 4) 3) s(2, 3) = s(2, 3) by decide,
    show Sym2.map (Equiv.swap (2 : Fin 4) 3) s(1, 3) = s(1, 2) by decide,
    show Sym2.map (Equiv.swap (2 : Fin 4) 3) s(1, 2) = s(1, 3) by decide]
  exact sixJSym_swap₂₃ ..

lemma sixJSymEdge_comp_map_flip (j : Sym2 (Fin 4) → ℕ) :
    sixJSymEdge (j ∘ Sym2.map (Equiv.swap 0 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4))) =
      sixJSymEdge j := by
  simp only [sixJSymEdge, Function.comp_apply]
  rw [show Sym2.map (Equiv.swap 0 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4)) s(0, 1) = s(2, 3) by
      decide,
    show Sym2.map (Equiv.swap 0 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4)) s(0, 2) = s(1, 3) by
      decide,
    show Sym2.map (Equiv.swap 0 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4)) s(0, 3) = s(0, 3) by
      decide,
    show Sym2.map (Equiv.swap 0 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4)) s(2, 3) = s(0, 1) by
      decide,
    show Sym2.map (Equiv.swap 0 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4)) s(1, 3) = s(0, 2) by
      decide,
    show Sym2.map (Equiv.swap 0 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4)) s(1, 2) = s(1, 2) by
      decide]
  exact sixJSym_flip₁₂ ..

lemma sixJSymEdge_comp_map_mul {σ τ : Equiv.Perm (Fin 4)}
    (hσ : ∀ j, sixJSymEdge (j ∘ Sym2.map σ) = sixJSymEdge j)
    (hτ : ∀ j, sixJSymEdge (j ∘ Sym2.map τ) = sixJSymEdge j) (j : Sym2 (Fin 4) → ℕ) :
    sixJSymEdge (j ∘ Sym2.map (σ * τ : Equiv.Perm (Fin 4))) = sixJSymEdge j := by
  rw [Equiv.Perm.coe_mul, Sym2.map_comp, ← Function.comp_assoc, hτ, hσ]

/-- **Tetrahedral symmetry.** The 6j symbol is invariant under every permutation of the four
triads. -/
lemma sixJSymEdge_comp_map (σ : Equiv.Perm (Fin 4)) (j : Sym2 (Fin 4) → ℕ) :
    sixJSymEdge (j ∘ Sym2.map σ) = sixJSymEdge j := by
  have h12 := sixJSymEdge_comp_map_swap₁₂
  have h23 := sixJSymEdge_comp_map_swap₂₃
  have h03 : ∀ j, sixJSymEdge (j ∘ Sym2.map (Equiv.swap (0 : Fin 4) 3)) = sixJSymEdge j := by
    rw [show Equiv.swap (0 : Fin 4) 3 = Equiv.swap 0 3 * Equiv.swap 1 2 * Equiv.swap 1 2 by decide]
    exact sixJSymEdge_comp_map_mul sixJSymEdge_comp_map_flip h12
  have h13 : ∀ j, sixJSymEdge (j ∘ Sym2.map (Equiv.swap (1 : Fin 4) 3)) = sixJSymEdge j := by
    rw [show Equiv.swap (1 : Fin 4) 3 = Equiv.swap 2 3 * Equiv.swap 1 2 * Equiv.swap 2 3 by decide]
    exact sixJSymEdge_comp_map_mul (sixJSymEdge_comp_map_mul h23 h12) h23
  have h02 : ∀ j, sixJSymEdge (j ∘ Sym2.map (Equiv.swap (0 : Fin 4) 2)) = sixJSymEdge j := by
    rw [show Equiv.swap (0 : Fin 4) 2 = Equiv.swap 2 3 * Equiv.swap 0 3 * Equiv.swap 2 3 by decide]
    exact sixJSymEdge_comp_map_mul (sixJSymEdge_comp_map_mul h23 h03) h23
  have h01 : ∀ j, sixJSymEdge (j ∘ Sym2.map (Equiv.swap (0 : Fin 4) 1)) = sixJSymEdge j := by
    rw [show Equiv.swap (0 : Fin 4) 1 = Equiv.swap 1 2 * Equiv.swap 0 2 * Equiv.swap 1 2 by decide]
    exact sixJSymEdge_comp_map_mul (sixJSymEdge_comp_map_mul h12 h02) h12
  have hswap : ∀ x y : Fin 4, x ≠ y →
      ∀ j, sixJSymEdge (j ∘ Sym2.map (Equiv.swap x y)) = sixJSymEdge j := by
    intro x y hxy
    have : Equiv.swap x y = Equiv.swap 0 1 ∨ Equiv.swap x y = Equiv.swap 0 2 ∨
        Equiv.swap x y = Equiv.swap 0 3 ∨ Equiv.swap x y = Equiv.swap 1 2 ∨
        Equiv.swap x y = Equiv.swap 1 3 ∨ Equiv.swap x y = Equiv.swap 2 3 := by
      revert x y; decide
    rcases this with h | h | h | h | h | h
    · rw [h]; exact h01
    · rw [h]; exact h02
    · rw [h]; exact h03
    · rw [h]; exact h12
    · rw [h]; exact h13
    · rw [h]; exact h23
  induction σ using Equiv.Perm.swap_induction_on generalizing j with
  | one => rw [Equiv.Perm.coe_one, Sym2.map_id]; rfl
  | swap_mul f x y hxy ih => exact sixJSymEdge_comp_map_mul (hswap x y hxy) ih j

/-- The permutations of the triads act faithfully on the edges, so the symmetries of
`sixJSymEdge_comp_map` are 24 distinct permutations of the arguments. -/
lemma sym2_map_perm_injective :
    Function.Injective (fun σ : Equiv.Perm (Fin 4) => Sym2.map σ) := by
  refine fun σ τ h => Equiv.ext fun x => ?_
  have h₁ := congrFun h s(x, x + 1)
  have h₂ := congrFun h s(x, x + 2)
  simp only [Sym2.map_mk, Sym2.eq_iff] at h₁ h₂
  rcases h₁ with ⟨e, -⟩ | ⟨e₁, -⟩
  · exact e
  rcases h₂ with ⟨e, -⟩ | ⟨e₂, -⟩
  · exact e
  exact absurd (τ.injective (e₁.symm.trans e₂)) (by simp)

/-!

## D. The 6j symbols of `SixJ` as sums over four 3j symbols

-/

lemma link_congr {S : ℤ} {p₁ p₂ p₃ p₄ q₁ q₂ q₃ q₄ r : ℕ} {A B C T₁ T₂ T₃ T₄ : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : T₁ ≠ 0 → T₂ ≠ 0 → T₃ ≠ 0 → T₄ ≠ 0 →
      (S + p₁ + p₂ + p₃ + p₄ + q₁ + q₂ + q₃ + q₄ + r) % 2 = 0) :
    (-1) ^ p₂ * Real.sqrt B * T₂ * ((-1) ^ p₁ * Real.sqrt A * T₁ *
        ((-1) ^ p₄ * Real.sqrt B * T₄ * ((-1) ^ p₃ * Real.sqrt C * T₃))) =
      Real.sqrt (A * C) * B * (-1) ^ r * ((-1) ^ S *
        ((-1) ^ q₁ * T₁ * ((-1) ^ q₄ * T₄) * ((-1) ^ q₃ * T₃) * ((-1) ^ q₂ * T₂))) := by
  rcases prod_four_eq_zero_or h with h0 | h0
  · linear_combination ((-1) ^ p₂ * Real.sqrt B * (-1) ^ p₁ * Real.sqrt A * (-1) ^ p₄ *
      Real.sqrt B * (-1) ^ p₃ * Real.sqrt C - Real.sqrt (A * C) * B * (-1) ^ r * (-1) ^ S *
        ((-1) ^ q₁ * (-1) ^ q₄ * (-1) ^ q₃ * (-1) ^ q₂)) * h0
  · have key : (-1 : ℝ) ^ ((p₁ + p₂ + p₃ + p₄ : ℕ) : ℤ) =
        (-1) ^ (S + ((q₁ + q₂ + q₃ + q₄ + r : ℕ) : ℤ)) := neg_one_zpow_congr (by push_cast; omega)
    rw [zpow_add₀ (by norm_num), zpow_natCast, zpow_natCast] at key
    simp only [pow_add] at key
    have hB2 := Real.mul_self_sqrt hB
    rw [Real.sqrt_mul hA]
    calc _ = ((-1) ^ p₁ * (-1) ^ p₂ * (-1) ^ p₃ * (-1) ^ p₄) * (Real.sqrt B * Real.sqrt B) *
          Real.sqrt A * Real.sqrt C * (T₁ * T₂ * T₃ * T₄) := by ring
      _ = _ := by rw [key, hB2]; ring

section Link

variable {a b c : ℕ}

open scoped TensorProduct

lemma tripleForm_normVec_stateB (hbc : 0 < b + c) (k₃ : Fin (min b c + 1)) (k₄ l : ℕ)
    {α : ℕ} (hα : α ≤ a) (β γ : ℕ) :
    tripleForm a b c ((normVec a α ⊗ₜ normVec b β) ⊗ₜ normVec c γ) (stateB hbc k₃ k₄ l) =
      ∑ ν ∈ Finset.range (b + c - 2 * (k₃ : ℕ) + 1),
        cgCoefficient a (b + c - 2 * (k₃ : ℕ)) k₄ l α ν * cgCoefficient b c k₃ ν β γ := by
  have hterm : ∀ α' ∈ Finset.range (a + 1), ∀ ν : ℕ,
      tripleForm a b c ((normVec a α ⊗ₜ normVec b β) ⊗ₜ normVec c γ)
        (assocEmbed hbc k₃ (normVec a α' ⊗ₜ normVec _ ν)) =
          if α = α' then cgCoefficient b c k₃ ν β γ else 0 := fun α' hα' ν => by
    rw [assocEmbed, LinearMap.comp_apply, LinearMap.lTensor_tmul, embed_normVec,
      LinearEquiv.coe_coe, ← TensorProduct.assoc_symm_tmul, tripleForm_assoc_symm,
      invForm_normVec hα (Nat.lt_succ_iff.mp (Finset.mem_range.mp hα')), cgCoefficient]
    split_ifs <;> simp
  rw [stateB, coupledVec_eq_sum, map_sum, map_sum, Finset.sum_eq_single α]
  · rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [map_smul, map_smul, hterm α (Finset.mem_range.mpr (by omega)), ite_eq_left rfl,
      smul_eq_mul]
  · intro α' hα' hne
    rw [map_sum, map_sum]
    refine Finset.sum_eq_zero fun ν _ => ?_
    rw [map_smul, map_smul, hterm α' hα', ite_eq_right (Ne.symm hne), smul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

/-- The recoupling coefficient as a sum over products of four Clebsch–Gordan coefficients. -/
lemma recoupling_eq_sum (hab : 0 < a + b) (hbc : 0 < b + c) (K l : ℕ) (k₁ : Fin (min a b + 1))
    (k₃ : Fin (min b c + 1)) :
    recoupling hab hbc K l k₁ k₃ =
      ∑ μ ∈ Finset.range (a + b - 2 * (k₁ : ℕ) + 1), ∑ γ ∈ Finset.range (c + 1),
        cgCoefficient (a + b - 2 * (k₁ : ℕ)) c (K - k₁) l μ γ *
          ∑ α ∈ Finset.range (a + 1), ∑ β ∈ Finset.range (b + 1),
            cgCoefficient a b k₁ μ α β *
              ∑ ν ∈ Finset.range (b + c - 2 * (k₃ : ℕ) + 1),
                cgCoefficient a (b + c - 2 * (k₃ : ℕ)) (K - k₃) l α ν *
                  cgCoefficient b c k₃ ν β γ := by
  rw [recoupling, stateA, coupledVec_eq_sum, map_sum, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_sum, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [map_smul, LinearMap.rTensor_tmul, embed_normVec, coupledVec_eq_sum, map_smul,
    LinearMap.smul_apply, smul_eq_mul, TensorProduct.sum_tmul, map_sum, LinearMap.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [TensorProduct.sum_tmul, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [← TensorProduct.smul_tmul', map_smul, LinearMap.smul_apply, smul_eq_mul,
    tripleForm_normVec_stateB hbc k₃ _ l (Nat.lt_succ_iff.mp (Finset.mem_range.mp hα))]

/-- One summand of `recoupling_eq_sum` is a summand of `sixJSym`. -/
lemma cg_four_eq {a b c e f g k₁ k₂ k₃ k₄ l μ γ α β ν : ℕ}
    (hab : 0 < a + b) (hbc : 0 < b + c) (hec : 0 < e + c) (haf : 0 < a + f)
    (he : e = a + b - 2 * k₁) (hf : f = b + c - 2 * k₃) (hg₂ : g = e + c - 2 * k₂)
    (hg₄ : g = a + f - 2 * k₄) (h₁a : k₁ ≤ a) (h₁b : k₁ ≤ b) (h₂e : k₂ ≤ e) (h₂c : k₂ ≤ c)
    (h₃b : k₃ ≤ b) (h₃c : k₃ ≤ c) (h₄a : k₄ ≤ a) (h₄f : k₄ ≤ f) (hl : l ≤ g) (hμ : μ ≤ e)
    (hγ : γ ≤ c) (hα : α ≤ a) (hβ : β ≤ b) (hν : ν ≤ f) :
    cgCoefficient e c k₂ l μ γ * (cgCoefficient a b k₁ μ α β *
        (cgCoefficient a f k₄ l α ν * cgCoefficient b c k₃ ν β γ)) =
      Real.sqrt (((e + 1 : ℕ) : ℝ) * ((f + 1 : ℕ) : ℝ)) * ((g + 1 : ℕ) : ℝ) *
        (-1) ^ (a + b + c - (k₁ + k₂)) *
          sixJTerm a b e c g f ![(a : ℤ) - 2 * α, (b : ℤ) - 2 * β, -((e : ℤ) - 2 * μ),
            (c : ℤ) - 2 * γ, (g : ℤ) - 2 * l, (f : ℤ) - 2 * ν] := by
  rw [cgCoefficient_eq_wigner3j hec h₂e h₂c (by omega) hμ hγ,
    cgCoefficient_eq_wigner3j hab h₁a h₁b (by omega) hα hβ,
    cgCoefficient_eq_wigner3j haf h₄a h₄f (by omega) hα hν,
    cgCoefficient_eq_wigner3j hbc h₃b h₃c (by omega) hβ hγ,
    wigner3j_eq_threeJ h₂e h₂c (by omega) hμ hγ, wigner3j_eq_threeJ h₁a h₁b (by omega) hα hβ,
    wigner3j_eq_threeJ h₄a h₄f (by omega) hα hν, wigner3j_eq_threeJ h₃b h₃c (by omega) hβ hγ,
    ← he, ← hf, ← hg₂, ← hg₄]
  simp only [sixJTerm, Matrix.cons_val]
  rw [threeJ_neg a b e, threeJ_swap₂₃ a f g, threeJ_swap b c f, threeJ_negCycle e c g]
  refine link_congr (by positivity) (by positivity) fun h₁ h₂ h₃ h₄ => ?_
  obtain ⟨s₁, -, -, -, -, -, -, -, -, -, -, -, -, t₁⟩ := adm3_of_threeJ_ne_zero h₁
  obtain ⟨s₂, -, -, -, -, -, -, -, -, -, -, -, -, t₂⟩ := adm3_of_threeJ_ne_zero h₂
  obtain ⟨s₃, -, -, -, -, -, -, -, -, -, -, -, -, t₃⟩ := adm3_of_threeJ_ne_zero h₃
  obtain ⟨s₄, -, -, -, -, -, -, -, -, -, -, -, -, t₄⟩ := adm3_of_threeJ_ne_zero h₄
  omega

/-- The sum of `sixJTerm` over the six projections, written through `jᵢ - 2·index`. -/
lemma sum_sixJTerm_eq (a b c e f g : ℕ) :
    ∑ x ∈ Finset.range (g + 1) ×ˢ (Finset.range (e + 1) ×ˢ (Finset.range (c + 1) ×ˢ
        (Finset.range (a + 1) ×ˢ (Finset.range (b + 1) ×ˢ Finset.range (f + 1))))),
      sixJTerm a b e c g f ![(a : ℤ) - 2 * x.2.2.2.1, (b : ℤ) - 2 * x.2.2.2.2.1,
        -((e : ℤ) - 2 * x.2.1), (c : ℤ) - 2 * x.2.2.1, (g : ℤ) - 2 * x.1,
        (f : ℤ) - 2 * x.2.2.2.2.2] = sixJSym a b e c g f := by
  refine Finset.sum_bij_ne_zero (fun x _ _ => ![(a : ℤ) - 2 * x.2.2.2.1,
        (b : ℤ) - 2 * x.2.2.2.2.1, -((e : ℤ) - 2 * x.2.1), (c : ℤ) - 2 * x.2.2.1, (g : ℤ) - 2 * x.1,
        (f : ℤ) - 2 * x.2.2.2.2.2]) (fun x hx _ => ?_) (fun x hx _ y hy _ hxy => ?_)
    (fun m hm hne => ?_) (fun x _ _ => rfl)
  · simp only [Finset.mem_product, Finset.mem_range] at hx
    rw [mem_sixJBox]
    simp only [Matrix.cons_val]
    omega
  · simp only [Finset.mem_product, Finset.mem_range] at hx hy
    have h0 := congrFun hxy 0
    have h1 := congrFun hxy 1
    have h2 := congrFun hxy 2
    have h3 := congrFun hxy 3
    have h4 := congrFun hxy 4
    have h5 := congrFun hxy 5
    simp only [Matrix.cons_val] at h0 h1 h2 h3 h4 h5
    ext <;> omega
  · rw [mem_sixJBox] at hm
    have hne' := hne
    simp only [sixJTerm, ne_eq, mul_eq_zero, not_or] at hne'
    obtain ⟨-, ⟨⟨h₁, h₂⟩, -⟩, h₄⟩ := hne'
    obtain ⟨-, -, -, -, -, -, -, p₁, p₂, p₃, -, -, -, -⟩ := adm3_of_threeJ_ne_zero h₁
    obtain ⟨-, -, -, -, -, -, -, -, -, p₆, -, -, -, -⟩ := adm3_of_threeJ_ne_zero h₂
    obtain ⟨-, -, -, -, -, -, -, p₄, p₅, -, -, -, -, -⟩ := adm3_of_threeJ_ne_zero h₄
    have heq : ![(a : ℤ) - 2 * (((a : ℤ) - m 0) / 2).toNat,
        (b : ℤ) - 2 * (((b : ℤ) - m 1) / 2).toNat, -((e : ℤ) - 2 * (((e : ℤ) + m 2) / 2).toNat),
        (c : ℤ) - 2 * (((c : ℤ) - m 3) / 2).toNat, (g : ℤ) - 2 * (((g : ℤ) - m 4) / 2).toNat,
        (f : ℤ) - 2 * (((f : ℤ) - m 5) / 2).toNat] = m := by
      funext i
      fin_cases i <;> simp <;> omega
    refine ⟨((((g : ℤ) - m 4) / 2).toNat, ((((e : ℤ) + m 2) / 2).toNat,
      ((((c : ℤ) - m 3) / 2).toNat, ((((a : ℤ) - m 0) / 2).toNat, ((((b : ℤ) - m 1) / 2).toNat,
        (((f : ℤ) - m 5) / 2).toNat))))), ?_, ?_, heq⟩
    · simp only [Finset.mem_product, Finset.mem_range]
      omega
    · rw [heq]
      exact hne

/-- **The 6j symbols of `SixJ` are the symmetric sums over four 3j symbols.** With
`j₁₂ = (a + b)/2 - k₁`, `j₂₃ = (b + c)/2 - k₃` and `J = (a + b + c)/2 - K`,
`{j₁ j₂ j₁₂; j₃ J j₂₃}` of `sixJ` equals `sixJSym`. -/
lemma sixJ_eq_sixJSym (hab : 0 < a + b) (hbc : 0 < b + c) (ha : 0 < a) (hc : 0 < c) {K : ℕ}
    {k₁ : Fin (min a b + 1)} {k₃ : Fin (min b c + 1)} (hA : ValidA a b c K k₁)
    (hB : ValidB a b c K k₃) :
    sixJ hab hbc K k₁ k₃ =
      sixJSym a b (a + b - 2 * (k₁ : ℕ)) c (a + b + c - 2 * K) (b + c - 2 * (k₃ : ℕ)) := by
  have hk₁ := k₁.isLt
  have hk₃ := k₃.isLt
  obtain ⟨hA1, hA2, hA3⟩ := hA
  obtain ⟨hB1, hB2, hB3⟩ := hB
  set e := a + b - 2 * (k₁ : ℕ) with he
  set f := b + c - 2 * (k₃ : ℕ) with hf
  set g := a + b + c - 2 * K with hg
  have hsum : ∑ l ∈ Finset.range (g + 1), recoupling hab hbc K l k₁ k₃ =
      ((g + 1 : ℕ) : ℝ) * recoupling hab hbc K 0 k₁ k₃ := by
    rw [Finset.sum_congr rfl fun l hl => recoupling_eq_recoupling_zero hab hbc ha
      ⟨hA1, hA2, hA3⟩ ⟨hB1, hB2, hB3⟩ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hexp : ∑ l ∈ Finset.range (g + 1), recoupling hab hbc K l k₁ k₃ =
      Real.sqrt (((e + 1 : ℕ) : ℝ) * ((f + 1 : ℕ) : ℝ)) * ((g + 1 : ℕ) : ℝ) *
        (-1) ^ (a + b + c - K) * sixJSym a b e c g f := by
    rw [← sum_sixJTerm_eq, Finset.mul_sum]
    simp only [recoupling_eq_sum, Finset.mul_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun l hl => Finset.sum_congr rfl fun μ hμ =>
      Finset.sum_congr rfl fun γ hγ => Finset.sum_congr rfl fun α hα =>
        Finset.sum_congr rfl fun β hβ => Finset.sum_congr rfl fun ν hν => ?_
    simp only [Finset.mem_range] at hl hμ hγ hα hβ hν
    rw [cg_four_eq (e := e) (f := f) (g := g) (k₁ := k₁) (k₂ := K - k₁) (k₃ := k₃)
      (k₄ := K - k₃) (l := l) (μ := μ) (γ := γ) (α := α) (β := β) (ν := ν)
      hab hbc (by omega) (by omega) rfl rfl (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega),
      show (k₁ : ℕ) + (K - k₁) = K by omega]
  have hP : 0 < Real.sqrt (((e + 1 : ℕ) : ℝ) * ((f + 1 : ℕ) : ℝ)) :=
    Real.sqrt_pos.mpr (by positivity)
  have hG : ((g + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hR : recoupling hab hbc K 0 k₁ k₃ = Real.sqrt (((e + 1 : ℕ) : ℝ) * ((f + 1 : ℕ) : ℝ)) *
      (-1) ^ (a + b + c - K) * sixJSym a b e c g f := by
    have h := hsum.symm.trans hexp
    apply mul_left_cancel₀ hG
    linear_combination h
  have hs : ((-1 : ℝ) ^ (a + b + c - K)) * (-1) ^ (a + b + c - K) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  rw [sixJ, ite_eq_left ⟨⟨hA1, hA2, hA3⟩, ⟨hB1, hB2, hB3⟩⟩, hR]
  calc _ = ((-1 : ℝ) ^ (a + b + c - K) * (-1) ^ (a + b + c - K)) * sixJSym a b e c g f *
        (Real.sqrt (((e + 1 : ℕ) : ℝ) * ((f + 1 : ℕ) : ℝ)) /
          Real.sqrt (((e + 1 : ℕ) : ℝ) * ((f + 1 : ℕ) : ℝ))) := by ring
    _ = _ := by rw [hs, div_self hP.ne', one_mul, mul_one]

end Link

end PhyslibAlpha.Sl2
