/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Physlib.Mathematics.ForMathlib.Fin
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Module.Defs
/-!
# Peeling the first slot off a sum over tuples

Sums over tuples of indices, split into the first slot and the remaining ones.

## i. Overview

A monomial in several slots contributes one factor per slot, and summing such monomials over
all tuples of indices is the basic operation of a component expansion.
`sum_pi_succ_prod_smul` peels the first slot off such a sum, weighted by one scalar per slot,
turning a sum over `Fin (n + 1) → ι` into a double sum over `ι` and `Fin n → ι` along
`Fin.consEquiv`. It is the induction step of the component expansions of tensors.

For two slots the splitting is complete, and `sum_fin_two_arrow` writes a sum over pairs of indices
as a double sum, the form in which two-index invariant tensors are contracted.

## ii. Key results

- `Physlib.Fin.sum_pi_succ_prod_smul` : a sum over tuples, weighted by one scalar factor per
  slot, split into the first slot and the rest.
- `Physlib.Fin.sum_fin_two_arrow` : a sum over pairs of indices, as a double sum.

## iii. Table of contents

- A. Splitting off the first slot

## iv. References

The `Fin.consEquiv` along which the splitting is done is Mathlib's.

-/

@[expose] public section
namespace Physlib.Fin

/-!

## A. Splitting off the first slot

-/

/-- A sum over tuples of indices, weighted by one scalar factor per slot, split into the
  first slot and the remaining ones. -/
lemma sum_pi_succ_prod_smul {R M ι : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    [Fintype ι] {n : ℕ} (c : Fin (n + 1) → ι → R) (X : (Fin (n + 1) → ι) → M) :
    ∑ q : Fin (n + 1) → ι, (∏ i, c i (q i)) • X q =
      ∑ b : ι, ∑ p : Fin n → ι, (c 0 b * ∏ i, c i.succ (p i)) • X (Fin.cons b p) := by
  rw [← (Fin.consEquiv fun _ : Fin (n + 1) => ι).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun p _ => ?_
  show (∏ i, c i ((Fin.cons b p : Fin (n + 1) → ι) i)) • X (Fin.cons b p) = _
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- A sum over functions from `Fin 2` is a double sum. -/
lemma sum_fin_two_arrow {α M : Type*} [Fintype α] [AddCommMonoid M] (F : (Fin 2 → α) → M) :
    ∑ ψ : Fin 2 → α, F ψ = ∑ x, ∑ y, F ![x, y] := by
  rw [← (finTwoArrowEquiv _).symm.sum_comp, Fintype.sum_prod_type]
  rfl

end Physlib.Fin
