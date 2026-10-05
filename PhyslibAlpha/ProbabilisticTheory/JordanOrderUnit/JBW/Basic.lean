/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.JordanOrderUnit.JB.Basic
public import PhyslibAlpha.ProbabilisticTheory.Channel.Normal
public import PhyslibAlpha.ProbabilisticTheory.OrderUnit.MonotoneComplete
public import PhyslibAlpha.ProbabilisticTheory.State.NormalEquivalence

/-!

# JBW-algebras

JBW-algebras: monotone-complete JB-algebras whose normal states separate points.

## i. Overview

A JBW-algebra is a monotone-complete JB-algebra whose normal states separate points.

## ii. Key results

- `JBWAlgebra` : JBW-algebras.
- `JBWAlgebra.eq_of_forall_normal_state_eq` : normal states separate points.

## iii. Table of contents

- A. JBW-algebras
- B. Separation and monotone convergence

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory

/-! ## A. JBW-algebras -/

/-- A JBW-algebra, presented as a monotone-complete JB-algebra with enough normal states.
The ordinary JB, order-unit, and scalar-order data stay in their existing canonical classes. -/
class JBWAlgebra (E : Type*) [IsJBOrderUnit E] : Prop
    extends MonotoneCompleteOrder E where
  /-- Normal states separate a nonzero observable from zero. -/
  exists_normal_state_ne_zero : ∀ {x : E}, x ≠ 0 →
    ∃ ω : 𝓢[ℝ, E], ω.IsNormal ∧ ω x ≠ 0

namespace JBWAlgebra

variable {E : Type*} [IsJBOrderUnit E] [JBWAlgebra E]

/-! ## B. Separation and monotone convergence -/

/-- Equality of observables is detected by all normal states. -/
lemma eq_of_forall_normal_state_eq {x y : E}
    (h : ∀ ω : 𝓢[ℝ, E], ω.IsNormal → ω x = ω y) : x = y := by
  by_contra hxy
  obtain ⟨ω, hωnormal, hωne⟩ := exists_normal_state_ne_zero (sub_ne_zero.mpr hxy)
  apply hωne
  rw [map_sub, h ω hωnormal, sub_self]

/-- A bounded increasing sequence has a supremum, and a normal state maps it to the supremum of the
values. -/
lemma exists_isLUB_range_and_normal_state_image (ω : 𝓢[ℝ, E]) (hω : ω.IsNormal)
    (x : ℕ → E) (hx : Monotone x) (hbounded : BddAbove (Set.range x)) :
    ∃ a : E, IsLUB (Set.range x) a ∧
      IsLUB (Set.range fun n => ω (x n)) (ω a) := by
  obtain ⟨a, ha⟩ := MonotoneCompleteOrder.exists_isLUB_range x hx hbounded
  refine ⟨a, ha, ?_⟩
  exact hω x a hx ha

/-- The same monotone-convergence statement using the canonical chosen sequence supremum from
`MonotoneCompleteOrder`. -/
lemma isLUB_rangeSup_normal_state_image (ω : 𝓢[ℝ, E]) (hω : ω.IsNormal)
    (x : ℕ → E) (hx : Monotone x) (hbounded : BddAbove (Set.range x)) :
    IsLUB (Set.range fun n => ω (x n))
      (ω (MonotoneCompleteOrder.rangeSup x hx hbounded)) := by
  exact hω x (MonotoneCompleteOrder.rangeSup x hx hbounded) hx
    (MonotoneCompleteOrder.isLUB_rangeSup x hx hbounded)

/-- A nonzero positive observable is detected by a normal finite weight.  This is the canonical
state-to-weight direction: normal-state separation supplies the state, and the established
state/weight conversion transports its normality to the positive cone. -/
lemma exists_normal_finite_weight_ne_zero {x : E} (hx : 0 ≤ x) (hxne : x ≠ 0) :
    ∃ w : Weight E, w.IsNormal ∧ w.IsFinite ∧ w ⟨x, hx⟩ ≠ 0 := by
  obtain ⟨ω, hωnormal, hωx⟩ := exists_normal_state_ne_zero hxne
  refine ⟨ω.toWeight, hωnormal.toWeight_isNormal, (ω.toWeight_isState).finite, ?_⟩
  rw [UnitalPositiveLinearMap.toWeight_apply]
  exact ne_of_gt <| ENNReal.ofReal_pos.mpr
    (lt_of_le_of_ne (ω.map_nonneg hx) hωx.symm)

end JBWAlgebra

end ProbabilisticTheory
