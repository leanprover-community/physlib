/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.OrderUnit.Basic

/-!

# Monotone-complete ordered spaces

Monotone completeness is order-theoretic: every nonempty upward-directed set which is bounded
above has a least upper bound.  It therefore belongs below the Jordan and JBW layers.  Those
layers consume this class; they do not redefine directed suprema.

-/

@[expose] public section

/-- An order is monotone complete when every nonempty upward-directed bounded set has a supremum.
No lattice operations are bundled: ordered vector spaces need not be lattices. -/
class MonotoneCompleteOrder (E : Type*) [Preorder E] : Prop where
  /-- Existence of the directed supremum. -/
  exists_isLUB (D : Set E) : D.Nonempty → DirectedOn (· ≤ ·) D → BddAbove D →
    ∃ x : E, IsLUB D x

namespace MonotoneCompleteOrder

variable {E : Type*} [Preorder E] [MonotoneCompleteOrder E]

/-- A chosen supremum for a nonempty upward-directed bounded set.  The choice is deliberately
confined to this order-theoretic layer; algebraic and JBW layers use its `isLUB_directedSup`
specification rather than introducing competing supremum operations. -/
noncomputable def directedSup (D : Set E) (hD : D.Nonempty)
    (hdir : DirectedOn (· ≤ ·) D) (hbdd : BddAbove D) : E :=
  Classical.choose (exists_isLUB D hD hdir hbdd)

theorem isLUB_directedSup (D : Set E) (hD : D.Nonempty)
    (hdir : DirectedOn (· ≤ ·) D) (hbdd : BddAbove D) :
    IsLUB D (directedSup D hD hdir hbdd) :=
  Classical.choose_spec (exists_isLUB D hD hdir hbdd)

/-- A monotone sequence with a common upper bound has a least upper bound. -/
theorem exists_isLUB_range (x : ℕ → E) (hx : Monotone x) (hbounded : BddAbove (Set.range x)) :
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

theorem isLUB_rangeSup (x : ℕ → E) (hx : Monotone x)
    (hbounded : BddAbove (Set.range x)) :
    IsLUB (Set.range x) (rangeSup x hx hbounded) :=
  isLUB_directedSup (Set.range x) ⟨x 0, Set.mem_range_self 0⟩
    hx.directed_le.directedOn_range hbounded

end MonotoneCompleteOrder
