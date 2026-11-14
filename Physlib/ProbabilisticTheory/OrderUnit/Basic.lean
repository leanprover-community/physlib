/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.Basic

/-!

# Ordered vector spaces and order units

## i. Overview

Order-unit spaces capture the basic structure needed for a probabilistic theory: observables,
positivity, effects, states and probabilities. They do this without assuming that the system is
classical or quantum, or that observables have any particular algebraic structure.

In quantum mechanics, the standard example is the real vector space of self-adjoint matrices,
ordered by positive semidefiniteness, with the identity matrix as 1. Keeping only the vector
space, its order, and this distinguished unit gives the abstract order-unit setting.

## ii. Key results

- `ProbabilisticTheory.exists_two_sided_bound` : every observable sits between `-(n • 1)` and
  `n • 1`, for some `n`.
- `ProbabilisticTheory.exists_eq_sub_nonneg` : every observable is a difference of two positive
  observables.
- `ProbabilisticTheory.exists_real_shift_nonneg` : enough copies of the order unit shift any element
  into the positive cone.
- `ProbabilisticTheory.nonneg_add_eq_zero` : the positive cone meets its negation only at `0`.

## iii. Table of contents

- A. Ordered vector spaces and order units
- B. Consequences of being an order unit

## iv. References

-/

@[expose] public section

namespace ProbabilisticTheory

/-!

## A. Ordered vector spaces and order-unit elements

-/

variable {P : ProbabilisticTheory}

/-- The certain outcome is nonnegative. -/
lemma one_nonneg : 0 ≤ (1 : P.Observables) := P.one_nonneg'

/-- Every observable is bounded above by a natural multiple of the certain outcome. -/
lemma exists_nsmul_one_le (B : P.Observables) : ∃ n : ℕ, B ≤ n • (1 : P.Observables) :=
  P.exists_nsmul_one_le' B

/-!

## B. Consequences of being an order unit

-/

/-- Every element is bounded on both sides by a natural multiple of the order unit. -/
lemma exists_two_sided_bound (A : P.Observables) :
    ∃ n : ℕ, -(n • (1 : P.Observables)) ≤ A ∧ A ≤ n • (1 : P.Observables) := by
  obtain ⟨n, hn⟩ := exists_nsmul_one_le A
  obtain ⟨m, hm⟩ := exists_nsmul_one_le (-A)
  refine ⟨max n m, ?_, hn.trans (nsmul_le_nsmul_left one_nonneg (le_max_left n m))⟩
  exact neg_le_of_neg_le <| hm.trans (nsmul_le_nsmul_left one_nonneg (le_max_right n m))

/-- Every element is a difference of two positive elements. -/
lemma exists_eq_sub_nonneg (A : P.Observables) :
    ∃ Ap An : P.Observables, 0 ≤ Ap ∧ 0 ≤ An ∧ A = Ap - An := by
  obtain ⟨n, hn⟩ := exists_nsmul_one_le (-A)
  refine ⟨A + n • (1 : P.Observables), n • (1 : P.Observables), ?_, nsmul_nonneg one_nonneg n, ?_⟩
  · exact neg_le_iff_add_nonneg'.mp hn
  · exact (add_sub_cancel_right A (n • (1 : P.Observables))).symm

/-- Every element becomes nonnegative after adding enough copies of the order unit: the positive
cone reaches everywhere, once you're allowed to shift by the unit. -/
lemma exists_real_shift_nonneg (A : P.Observables) : ∃ r : ℝ, 0 ≤ r • (1 : P.Observables) + A := by
  obtain ⟨n, hn⟩ := exists_nsmul_one_le (-A)
  use n
  rw [← sub_neg_eq_add, sub_nonneg]
  exact_mod_cast hn

/-- A nonnegative vector that adds with another nonnegative vector to `0` is itself `0`: the
positive cone meets its negation only at `0`. -/
lemma nonneg_add_eq_zero {A B : P.Observables} (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : A + B = 0) :
    A = 0 :=
  le_antisymm (hAB ▸ le_add_of_nonneg_right hB) hA

end ProbabilisticTheory
