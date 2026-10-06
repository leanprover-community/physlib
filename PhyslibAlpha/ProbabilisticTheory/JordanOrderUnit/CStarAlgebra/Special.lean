/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.JordanOrderUnit.CStarAlgebra.Basic
public import PhyslibAlpha.ProbabilisticTheory.JordanOrderUnit.JB.Order

/-!

# Special JB-algebras

Special JB-algebras: those embedding as closed Jordan subalgebras of a C⋆-algebra.

## i. Overview

A JB-algebra is special when it embeds as a closed Jordan subalgebra of the self-adjoint part of a
C⋆-algebra, by a linear, isometric, unital map preserving the Jordan product. The self-adjoint part
of a C⋆-algebra is special.

## ii. Key results

- `JBAlgebra.IsSpecialWitness` : an embedding into the self-adjoint part of a C⋆-algebra.
- `JBAlgebra.IsSpecial` : a special JB-algebra.
- `JB.isSpecial_selfAdjoint` : the self-adjoint part of a C⋆-algebra is special.
- `JBAlgebra.IsSpecialWitness.map_nonneg`, `JBAlgebra.IsSpecialWitness.monotone` : such an
  embedding preserves positivity and order.

## iii. Table of contents

- A. Special JB-algebras
- B. Order properties of special embeddings
- C. The self-adjoint part of a C⋆-algebra

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory

open scoped JB selfAdjoint

/-!

## A. Special JB-algebras

-/

/-- A witness that `E` is special: an isometric unital Jordan embedding into the self-adjoint part
of a Cstar algebra whose range is norm closed. -/
structure JBAlgebra.IsSpecialWitness (E : Type*) [NormedJordanAlgebra E]
    [JBAlgebra E] (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] where
  /-- The underlying injective isometric real-linear map. -/
  toLinearIsometry : E →ₗᵢ[ℝ] selfAdjoint A
  /-- The order unit is preserved. -/
  map_one : toLinearIsometry 1 = 1
  /-- The Jordan product is preserved. -/
  map_mul : ∀ x y : E, toLinearIsometry (x * y) = toLinearIsometry x * toLinearIsometry y
  /-- The represented Jordan subalgebra is norm closed. -/
  isClosed_range : IsClosed (Set.range toLinearIsometry)

/-- `E` is special when it embeds as a closed Jordan subalgebra of the self-adjoint part of a
Cstar algebra in the same universe. -/
def JBAlgebra.IsSpecial (E : Type u) [NormedJordanAlgebra E]
    [JBAlgebra E] : Prop :=
  ∃ (A : Type u) (_ : CStarAlgebra A) (_ : PartialOrder A) (_ : StarOrderedRing A),
    Nonempty (JBAlgebra.IsSpecialWitness E A)

/-!

## B. Order properties of special embeddings

-/

namespace JBAlgebra.IsSpecialWitness

variable {E A : Type*} [IsJBOrderUnit E] [Nontrivial E] [CStarAlgebra A] [PartialOrder A]
  [StarOrderedRing A]

/-- A special-JB embedding preserves positivity. Exact-cone reconstruction supplies a square
witness in the source; multiplicativity carries that witness to a square in the represented
self-adjoint algebra. -/
lemma map_nonneg (j : JBAlgebra.IsSpecialWitness E A) {x : E} (hx : 0 ≤ x) :
    0 ≤ (j.toLinearIsometry x : selfAdjoint A) := by
  obtain ⟨y, hy⟩ := JBAlgebra.nonneg_iff_exists_mul_self x |>.mp hx
  rw [← hy, j.map_mul]
  exact IsJordanOrderUnit.mul_self_nonneg _

/-- A special-JB embedding is order preserving. This is derived from exact cone reconstruction,
not assumed in the definition of specialness. -/
lemma monotone (j : JBAlgebra.IsSpecialWitness E A) : Monotone j.toLinearIsometry := by
  intro x y hxy
  rw [← sub_nonneg]
  rw [← map_sub]
  exact j.map_nonneg (sub_nonneg.mpr hxy)

end JBAlgebra.IsSpecialWitness

/-!

## C. The self-adjoint part of a C⋆-algebra

-/

namespace JB

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The identity equivalence witnesses that `selfAdjoint A` is special in `A` itself. -/
noncomputable def isSpecialWitnessRefl : JBAlgebra.IsSpecialWitness (selfAdjoint A) A where
  toLinearIsometry := LinearIsometry.id
  map_one := rfl
  map_mul _ _ := rfl
  isClosed_range := by simp

/-- `selfAdjoint A` is special, for any unital C⋆-algebra `A`. -/
lemma isSpecial_selfAdjoint : JBAlgebra.IsSpecial (selfAdjoint A) :=
  ⟨A, ‹_›, ‹_›, ‹_›, ⟨isSpecialWitnessRefl⟩⟩

end JB

end ProbabilisticTheory
