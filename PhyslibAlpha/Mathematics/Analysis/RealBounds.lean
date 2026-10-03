/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Group
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Elementary real bounds

Elementary real estimates: suprema of sums, bounds up to `1 / (n + 1)`, and weighted averages.

## i. Overview

Three elementary estimates for real numbers: suprema of sums over a codirected family, inequalities
up to `1 / (n + 1)` for every `n`, and averages that put almost all weight on one term.

## ii. Key results

- `Real.ciSup_add` : suprema add along a family in which any two indices are dominated by a third.
- `Real.le_of_forall_nat_le_add` : `a ≤ b` if `a ≤ b + 1 / (n + 1)` for every `n`.
- `Real.abs_sum_mul_sub_le` : an average with weight at least `1 - θ` on one term is within
  `2 * A * θ` of it, for terms bounded by `A`.

## iii. Table of contents

- A. Suprema
- B. Averages

## iv. References

* None.

-/

@[expose] public section

namespace Real

/-! ## A. Suprema -/

/-- Suprema of two bounded families add when any two indices are dominated by a common one. -/
lemma ciSup_add {ι : Type*} [Nonempty ι] {f g : ι → ℝ} (hf : BddAbove (Set.range f))
    (hg : BddAbove (Set.range g)) (h : ∀ i j, ∃ k, f i ≤ f k ∧ g j ≤ g k) :
    ⨆ i, (f i + g i) = (⨆ i, f i) + ⨆ i, g i := by
  refine le_antisymm (ciSup_le fun i => add_le_add (le_ciSup hf i) (le_ciSup hg i)) ?_
  refine ciSup_add_ciSup_le fun i j => ?_
  obtain ⟨k, hik, hjk⟩ := h i j
  obtain ⟨Bf, hBf⟩ := hf
  obtain ⟨Bg, hBg⟩ := hg
  exact (add_le_add hik hjk).trans (le_ciSup ⟨Bf + Bg, by
    rintro _ ⟨l, rfl⟩; exact add_le_add (hBf ⟨l, rfl⟩) (hBg ⟨l, rfl⟩)⟩ k)

/-- A real number that is at most `b + 1 / (n + 1)` for every `n` is at most `b`. -/
lemma le_of_forall_nat_le_add {a b : ℝ} (h : ∀ n : ℕ, a ≤ b + 1 / (n + 1)) : a ≤ b :=
  le_of_forall_pos_le_add fun ε hε => by
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    exact (h n).trans (by linarith)

/-! ## B. Averages -/

/-- An average of numbers bounded by `A`, with weight at least `1 - θ` on the `i`-th number, is
within `2 * A * θ` of it. -/
lemma abs_sum_mul_sub_le {ι : Type*} [Fintype ι] [DecidableEq ι] {q c : ι → ℝ}
    (hq0 : ∀ l, 0 ≤ q l) (hq1 : ∑ l, q l = 1) (i : ι) {θ A : ℝ} (hqi : 1 - θ ≤ q i)
    (hc : ∀ l, |c l| ≤ A) : |∑ l, c l * q l - c i| ≤ 2 * A * θ := by
  have hrest : ∑ l ∈ Finset.univ.erase i, q l = 1 - q i := by
    rw [← hq1, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]; ring
  have e : ∑ l, c l * q l - c i = ∑ l ∈ Finset.univ.erase i, (c l - c i) * q l := by
    have e₁ : ∑ l, c l * q l - c i = ∑ l, (c l - c i) * q l := by
      simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hq1, mul_one]
    rw [e₁, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), sub_self, zero_mul, zero_add]
  rw [e]
  calc |∑ l ∈ Finset.univ.erase i, (c l - c i) * q l|
      ≤ ∑ l ∈ Finset.univ.erase i, 2 * A * q l := (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun l _ => by
          rw [abs_mul, abs_of_nonneg (hq0 l)]
          exact mul_le_mul_of_nonneg_right ((abs_sub _ _).trans (by linarith [hc l, hc i]))
            (hq0 l))
    _ = 2 * A * (1 - q i) := by rw [← Finset.mul_sum, hrest]
    _ ≤ 2 * A * θ := by
      have : 0 ≤ A := (abs_nonneg _).trans (hc i)
      nlinarith

end Real
