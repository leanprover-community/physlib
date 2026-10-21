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
all tuples of indices is the basic operation of a component expansion. Both lemmas here peel
the first slot off such a sum, turning a sum over `Fin (n + 1) → ι` into a double sum over `ι`
and `Fin n → ι` along `Fin.consEquiv`. `sum_pi_succ_prod_smul` does this for a sum weighted by
one scalar per slot, and `sum_filter_weight_succ` for a sum restricted to the tuples of a
prescribed total weight, where the first slot takes its own weight and the rest make up the
remainder. They are the induction steps of the component expansions which the weight
decompositions run on.

## ii. Key results

- `Physlib.Fin.sum_pi_succ_prod_smul` : a sum over tuples, weighted by one scalar factor per
  slot, split into the first slot and the rest.
- `Physlib.Fin.sum_filter_weight_succ` : the same split for a sum over the tuples of a
  prescribed total weight.

## iii. Table of contents

- A. Splitting off the first slot

## iv. References

The `Fin.consEquiv` along which the splitting is done is Mathlib's.

-/

@[expose] public section
namespace Physlib.Fin

open _root_.Physlib.Fin

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

/-- Peeling the first slot off a sum over the tuples of a prescribed total weight: the first
  slot takes its own weight `w b` and the remaining slots make up the rest. Each slot draws its
  letter from the same alphabet `ι`, `w` gives a letter its weight and the weights of the slots
  add; `f s` is the factor contributed by slot `s`. -/
lemma sum_filter_weight_succ {R ι : Type*} [CommSemiring R] [Fintype ι] {n : ℕ} (w : ι → ℤ)
    (f : Fin (n + 1) → ι → R) (m : ℤ) :
    ∑ q ∈ Finset.univ.filter (fun q : Fin (n + 1) → ι => (∑ s, w (q s)) = m), ∏ s, f s (q s)
      = ∑ b : ι, f 0 b
          * ∑ q ∈ Finset.univ.filter (fun q : Fin n → ι => (∑ s, w (q s)) = m - w b),
              ∏ s, f s.succ (q s) := by
  rw [Finset.sum_filter, ← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (n + 1) => ι),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [Fin.consEquiv_apply, Fin.sum_univ_succ, Fin.prod_univ_succ, Fin.cons_zero,
    Fin.cons_succ, mul_ite, mul_zero]
  exact if_congr (by omega) rfl rfl

end Physlib.Fin
