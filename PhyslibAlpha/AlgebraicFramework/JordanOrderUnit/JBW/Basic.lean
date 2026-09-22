/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.JordanOrderUnit.JB.Basic
public import PhyslibAlpha.AlgebraicFramework.OrderUnit.Channel.Normal
public import PhyslibAlpha.AlgebraicFramework.OrderUnit.MonotoneComplete
public import PhyslibAlpha.AlgebraicFramework.OrderUnit.State.NormalEquivalence

/-!

# JBW-algebras

This file fixes the boundary between continuous JB theory and monotone-complete JBW theory.  We
use the order-theoretic characterization: a JBW-algebra is a monotone-complete JB-algebra whose
normal states separate points.  Normality itself remains the canonical
`UnitalPositiveLinearMap.IsNormal`; it is not copied into this layer.

Projection-valued spectral measures and Borel functional calculus belong downstream of this
interface.  The continuous single-generator spectrum remains in the JB layer.

-/

@[expose] public section

/-- A JBW-algebra, presented as a monotone-complete JB-algebra with enough normal states.
The ordinary JB, order-unit, and scalar-order data stay in their existing canonical classes. -/
class JBWAlgebra (E : Type*) [NormedJordanAlgebra E] [PartialOrder E]
    [IsOrderedAddMonoid E] [IsArchimedeanOrderUnit E] [PosSMulMono ℝ E] [JBAlgebra E]
    [IsJBOrderUnit E] : Prop
    extends MonotoneCompleteOrder E where
  /-- Normal states separate a nonzero observable from zero. -/
  exists_normal_state_ne_zero : ∀ {x : E}, x ≠ 0 →
    ∃ ω : 𝓢[ℝ, E], ω.IsNormal ∧ ω x ≠ 0

namespace JBWAlgebra

variable {E : Type*} [NormedJordanAlgebra E] [PartialOrder E] [IsOrderedAddMonoid E]
  [IsArchimedeanOrderUnit E] [PosSMulMono ℝ E] [JBAlgebra E] [IsJBOrderUnit E] [JBWAlgebra E]

/-- Equality of observables is detected by all normal states. -/
theorem eq_of_forall_normal_state_eq {x y : E}
    (h : ∀ ω : 𝓢[ℝ, E], ω.IsNormal → ω x = ω y) : x = y := by
  by_contra hxy
  obtain ⟨ω, hωnormal, hωne⟩ := exists_normal_state_ne_zero (sub_ne_zero.mpr hxy)
  apply hωne
  rw [map_sub, h ω hωnormal, sub_self]

/-- A normal state preserves the canonical supremum of every nonempty bounded directed family.
This is the directed-set form of JBW monotone convergence; the sequence statements below are its
special case after passing to the range of a monotone sequence. -/
theorem isLUB_directedSup_normal_state_image (ω : 𝓢[ℝ, E]) (hω : ω.IsNormal)
    (D : Set E) (hD : D.Nonempty) (hdir : DirectedOn (· ≤ ·) D) (hbounded : BddAbove D) :
    IsLUB (ω '' D) (ω (MonotoneCompleteOrder.directedSup D hD hdir hbounded)) := by
  exact hω D (MonotoneCompleteOrder.directedSup D hD hdir hbounded) hD hdir
    (MonotoneCompleteOrder.isLUB_directedSup D hD hdir hbounded)

/-- Monotone completeness and normality give the expected monotone-convergence statement for a
normal state: a bounded increasing sequence has a supremum in the JBW-algebra, and evaluating it
is the least upper bound of the scalar sequence.  This is stated with `IsLUB`, rather than an
unconditional `iSup`, because `ℝ` is conditionally complete. -/
theorem exists_isLUB_range_and_normal_state_image (ω : 𝓢[ℝ, E]) (hω : ω.IsNormal)
    (x : ℕ → E) (hx : Monotone x) (hbounded : BddAbove (Set.range x)) :
    ∃ a : E, IsLUB (Set.range x) a ∧
      IsLUB (Set.range fun n => ω (x n)) (ω a) := by
  obtain ⟨a, ha⟩ := MonotoneCompleteOrder.exists_isLUB_range x hx hbounded
  refine ⟨a, ha, ?_⟩
  have himage := hω (Set.range x) a ⟨x 0, Set.mem_range_self 0⟩
    hx.directed_le.directedOn_range ha
  have heq : ω '' Set.range x = Set.range fun n => ω (x n) := by
    ext r
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨x n, ⟨n, rfl⟩, rfl⟩
  change IsLUB (ω '' Set.range x) (ω a) at himage
  rwa [heq] at himage

/-- The same monotone-convergence statement using the canonical chosen sequence supremum from
`MonotoneCompleteOrder`. -/
theorem isLUB_rangeSup_normal_state_image (ω : 𝓢[ℝ, E]) (hω : ω.IsNormal)
    (x : ℕ → E) (hx : Monotone x) (hbounded : BddAbove (Set.range x)) :
    IsLUB (Set.range fun n => ω (x n))
      (ω (MonotoneCompleteOrder.rangeSup x hx hbounded)) := by
  have himage := isLUB_directedSup_normal_state_image ω hω (Set.range x)
    ⟨x 0, Set.mem_range_self 0⟩ hx.directed_le.directedOn_range hbounded
  have heq : ω '' Set.range x = Set.range fun n => ω (x n) := by
    ext r
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨x n, ⟨n, rfl⟩, rfl⟩
  simpa only [MonotoneCompleteOrder.rangeSup, heq] using himage

/-- A nonzero positive observable is detected by a normal finite weight.  This is the canonical
state-to-weight direction: normal-state separation supplies the state, and the established
state/weight conversion transports its normality to the positive cone. -/
theorem exists_normal_finite_weight_ne_zero {x : E} (hx : 0 ≤ x) (hxne : x ≠ 0) :
    ∃ w : Weight E, w.IsNormal ∧ w.IsFinite ∧ w ⟨x, hx⟩ ≠ 0 := by
  obtain ⟨ω, hωnormal, hωx⟩ := exists_normal_state_ne_zero hxne
  refine ⟨ω.toWeight, hωnormal.toWeight_isNormal, (ω.toWeight_isState).finite, ?_⟩
  rw [UnitalPositiveLinearMap.toWeight_apply]
  exact ne_of_gt <| ENNReal.ofReal_pos.mpr
    (lt_of_le_of_ne (ω.map_nonneg hx) hωx.symm)

end JBWAlgebra
