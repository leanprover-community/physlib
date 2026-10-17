/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.OrderUnit.PositiveDual

/-!

# Monotone-complete ordered spaces

Monotone-complete orders and chosen suprema of bounded directed sets and increasing sequences.

## i. Overview

An ordered space is monotone complete when every nonempty directed set that is bounded above has a
least upper bound.

## ii. Key results

- `MonotoneCompleteOrder` : monotone-complete ordered spaces.
- `MonotoneCompleteOrder.directedSup` : the supremum of a bounded directed set.
- `MonotoneCompleteOrder.rangeSup` : the supremum of a bounded increasing sequence.

## iii. Table of contents

- A. Monotone-complete orders
- B. Chosen suprema

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory

/-! ## A. Monotone-complete orders -/

/-- An order is monotone complete when every nonempty upward-directed bounded set has a supremum.
No lattice operations are bundled: ordered vector spaces need not be lattices. -/
class MonotoneCompleteOrder (E : Type*) [Preorder E] : Prop where
  /-- Existence of the directed supremum. -/
  exists_isLUB (D : Set E) : D.Nonempty → DirectedOn (· ≤ ·) D → BddAbove D →
    ∃ x : E, IsLUB D x

/-! ## B. Chosen suprema -/

namespace MonotoneCompleteOrder

variable {E : Type*} [Preorder E] [MonotoneCompleteOrder E]

/-- A chosen supremum of a nonempty directed set that is bounded above. -/
noncomputable def directedSup (D : Set E) (hD : D.Nonempty)
    (hdir : DirectedOn (· ≤ ·) D) (hbdd : BddAbove D) : E :=
  Classical.choose (exists_isLUB D hD hdir hbdd)

lemma isLUB_directedSup (D : Set E) (hD : D.Nonempty)
    (hdir : DirectedOn (· ≤ ·) D) (hbdd : BddAbove D) :
    IsLUB D (directedSup D hD hdir hbdd) :=
  Classical.choose_spec (exists_isLUB D hD hdir hbdd)

/-- A monotone sequence with a common upper bound has a least upper bound. -/
lemma exists_isLUB_range (x : ℕ → E) (hx : Monotone x) (hbounded : BddAbove (Set.range x)) :
    ∃ a : E, IsLUB (Set.range x) a := by
  apply exists_isLUB
  · exact ⟨x 0, Set.mem_range_self 0⟩
  · exact hx.directed_le.directedOn_range
  · exact hbounded

/-- The chosen supremum of a bounded increasing sequence. -/
noncomputable def rangeSup (x : ℕ → E) (hx : Monotone x)
    (hbounded : BddAbove (Set.range x)) : E :=
  directedSup (Set.range x) ⟨x 0, Set.mem_range_self 0⟩
    hx.directed_le.directedOn_range hbounded

lemma isLUB_rangeSup (x : ℕ → E) (hx : Monotone x)
    (hbounded : BddAbove (Set.range x)) :
    IsLUB (Set.range x) (rangeSup x hx hbounded) :=
  isLUB_directedSup (Set.range x) ⟨x 0, Set.mem_range_self 0⟩
    hx.directed_le.directedOn_range hbounded

end MonotoneCompleteOrder

end ProbabilisticTheory
