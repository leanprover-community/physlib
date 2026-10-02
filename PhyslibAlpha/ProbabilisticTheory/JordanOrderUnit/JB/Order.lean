/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.JordanOrderUnit.JB.GeneratedByOne.PosInvertibility

/-!

# The positive cone of a JB-algebra

## i. Overview

In an ordered JB-algebra the nonnegative observables are exactly the squares: every nonnegative
observable is a square in its closed one-generator subalgebra.

## ii. Key results

- `JBAlgebra.nonneg_iff_exists_mul_self` : the nonnegative observables are the squares.

-/

@[expose] public section

namespace ProbabilisticTheory

namespace JBAlgebra

variable {E : Type*} [IsJBOrderUnit E] [Nontrivial E]

/-- **The nonnegative observables of an ordered JB-algebra are the squares.** -/
lemma nonneg_iff_exists_mul_self (a : E) :
    0 ≤ a ↔ ∃ b : E, b * b = a := by
  constructor
  · intro ha
    let x : NormedJordanAlgebra.ClosedGeneratedByOne a :=
      ⟨a, NormedJordanAlgebra.self_mem_closedGeneratedByOne a⟩
    have hx : 0 ≤ x := ha
    obtain ⟨b, hb⟩ := ClosedGeneratedByOne.exists_mul_self_of_nonneg a x hx
    refine ⟨(b : E), ?_⟩
    exact congrArg Subtype.val hb
  · rintro ⟨b, rfl⟩
    exact IsJordanOrderUnit.mul_self_nonneg b

end JBAlgebra

end ProbabilisticTheory
