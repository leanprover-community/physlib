/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.QuantumMechanics.AngularMomentum.Wigner3j

/-!

# A sum rule for multipole transitions

`Σ_{μ M_f} ⟨J_i M_i λ μ | J_f M_f⟩² = (2J_f + 1) / (2J_i + 1)`, independent of `M_i`.

## i. Overview

A multipole operator `T^λ_μ` of rank `λ` connects an initial level `J_i` with a final level
`J_f`. By the Wigner–Eckart theorem its matrix elements are
`⟨J_f M_f | T^λ_μ | J_i M_i⟩ = ⟨J_i M_i λ μ | J_f M_f⟩ · ⟨J_f ‖ T^λ ‖ J_i⟩ / √(2J_f + 1)`,
so the total transition rate out of the substate `|J_i M_i⟩`, summed over all final substates and
all components `μ`, is proportional to

`Σ_{μ M_f} ⟨J_i M_i λ μ | J_f M_f⟩² = (2J_f + 1) / (2J_i + 1)`.

The right-hand side does not depend on `M_i`: an unpolarised and a fully polarised initial state
decay at the same total rate, and `|⟨J_f ‖ T^λ ‖ J_i⟩|² / (2J_i + 1)` is the rate of every
substate.

The sum runs over the first and the third column of the Clebsch–Gordan coefficient, which the
orthogonality relations of `ClebschGordanCoefficients` do not cover. It follows from the cyclic
symmetry of the 3j symbols (`threeJR_cycle_columns`), which moves `J_i` into the third column,
and the orthogonality of the 3j symbols.

## ii. Key results

- `wigner3j_cycle`: the cyclic symmetry in the parameters of `ClebschGordanCoefficients`.
- `sum_sq_cgCoefficient_initial`: the sum rule.

## iii. Table of contents

- A. The cyclic symmetry
- B. The sum rule

## iv. References

- A. Bohr and B. R. Mottelson, *Nuclear Structure*, Vol. I, Benjamin (1969), appendix 1A.
- A. R. Edmonds, *Angular Momentum in Quantum Mechanics*, Princeton University Press (1957),
  section 5.4.

## A. The cyclic symmetry

-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Sl2

variable {m n : ℕ}

/-- `(j₁ j₂ J; m₁ m₂ -M) = (j₂ J j₁; m₂ -M m₁)` in the parameters of
`ClebschGordanCoefficients`: the new triple is `(n, m + n - 2k)` with `k' = n - k`, `l' = m - α`,
`α' = β` and `β' = m + n - 2k - l`. -/
lemma wigner3j_cycle {k l α β : ℕ} (hkm : k ≤ m) (hkn : k ≤ n) (hl : l ≤ m + n - 2 * k)
    (hα : α ≤ m) (hβ : β ≤ n) :
    wigner3j m n k l α β =
      wigner3j n (m + n - 2 * k) (n - k) (m - α) β (m + n - 2 * k - l) := by
  by_cases h : α + β = k + l
  · rw [wigner3j, wigner3j, ite_eq_left h,
      ite_eq_left (show β + (m + n - 2 * k - l) = n - k + (m - α) by omega),
      ← threeJR_cycle_columns (isMagic_regge hkm hkn hl hα hβ h)]
    congr 1
    funext i j
    fin_cases i <;> fin_cases j <;> simp [regge] <;> omega
  · rw [wigner3j, wigner3j, ite_eq_right h,
      ite_eq_right (show ¬(β + (m + n - 2 * k - l) = n - k + (m - α)) by omega)]

/-!

## B. The sum rule

-/

/-- **Sum rule for multipole transitions.** With `j₁ = m/2 = J_i`, `j₂ = n/2 = λ`,
`J = (m + n)/2 - k = J_f` and `m₁ = j₁ - α = M_i`,
`Σ_{μ M_f} ⟨J_i M_i λ μ | J_f M_f⟩² = (2J_f + 1) / (2J_i + 1)`. -/
lemma sum_sq_cgCoefficient_initial (hmn : 0 < m + n) {k α : ℕ} (hkm : k ≤ m) (hkn : k ≤ n)
    (hα : α ≤ m) :
    ∑ b ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + n - 2 * k + 1),
      cgCoefficient m n k l α b ^ 2 = ((m + n - 2 * k + 1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) := by
  have hterm : ∀ b ∈ Finset.range (n + 1), ∀ l ∈ Finset.range (m + n - 2 * k + 1),
      cgCoefficient m n k l α b ^ 2 = ((m + n - 2 * k + 1 : ℕ) : ℝ) *
        (wigner3j n (m + n - 2 * k) (n - k) (m - α) b (m + n - 2 * k - l) *
          wigner3j n (m + n - 2 * k) (n - k) (m - α) b (m + n - 2 * k - l)) := by
    intro b hb l hl
    have hb' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    have hl' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    rw [cgCoefficient_eq_wigner3j hmn hkm hkn hl' hα hb', wigner3j_cycle hkm hkn hl' hα hb']
    have hs := Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) (m + n - 2 * k + 1))
    have hsq : ((-1 : ℝ) ^ (m + k + l)) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    linear_combination (((-1 : ℝ) ^ (m + k + l)) ^ 2 *
      (wigner3j n (m + n - 2 * k) (n - k) (m - α) b (m + n - 2 * k - l)) ^ 2) * hs +
      (((m + n - 2 * k + 1 : ℕ) : ℝ) *
        (wigner3j n (m + n - 2 * k) (n - k) (m - α) b (m + n - 2 * k - l)) ^ 2) * hsq
  have hrefl : ∀ b, ∑ l ∈ Finset.range (m + n - 2 * k + 1),
      wigner3j n (m + n - 2 * k) (n - k) (m - α) b (m + n - 2 * k - l) *
        wigner3j n (m + n - 2 * k) (n - k) (m - α) b (m + n - 2 * k - l) =
      ∑ l ∈ Finset.range (m + n - 2 * k + 1),
        wigner3j n (m + n - 2 * k) (n - k) (m - α) b l *
          wigner3j n (m + n - 2 * k) (n - k) (m - α) b l := fun b => by
    refine Eq.trans ?_ (Finset.sum_range_reflect (fun l => wigner3j n (m + n - 2 * k) (n - k)
      (m - α) b l * wigner3j n (m + n - 2 * k) (n - k) (m - α) b l) (m + n - 2 * k + 1))
    exact Finset.sum_congr rfl fun l _ => by
      rw [show m + n - 2 * k + 1 - 1 - l = m + n - 2 * k - l by omega]
  have horth := sum_wigner3j_mul_wigner3j (m := n) (n := m + n - 2 * k) (k := n - k)
    (k' := n - k) (l := m - α) (l' := m - α) (by omega) (Nat.sub_le n k) (by omega)
    (Nat.sub_le n k) (by omega) (by omega) (by omega)
  rw [ite_eq_left ⟨rfl, rfl⟩, show n + (m + n - 2 * k) - 2 * (n - k) + 1 = m + 1 by omega]
    at horth
  rw [Finset.sum_congr rfl fun b hb => Finset.sum_congr rfl (hterm b hb)]
  simp only [← Finset.mul_sum, hrefl]
  rw [horth]
  ring

end PhyslibAlpha.Sl2
