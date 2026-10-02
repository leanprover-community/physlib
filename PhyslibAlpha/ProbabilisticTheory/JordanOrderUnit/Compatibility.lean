/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.JordanOrderUnit.Operator

/-!

# Compatible observables

## i. Overview

Two observables of a Jordan algebra are compatible when their multiplication operators commute, `L_a
L_b = L_b L_a`. This needs no commutator, which the Jordan structure does not have. Commuting
observables of a C⋆-algebra are compatible.

## ii. Key results

- `JordanAlgebra.IsJordanCompatible` : compatible observables.
- `JordanAlgebra.isJordanCompatible_comm` : compatibility is symmetric.
- `JordanAlgebra.isJordanCompatible_one_left` : the unit is compatible with everything.

## iii. Table of contents

- A. The compatibility predicate

-/

@[expose] public section

namespace ProbabilisticTheory

namespace JordanAlgebra

variable {E : Type*} [NonAssocCommRing E] [Module ℝ E] [SMulCommClass ℝ E E]

open scoped JordanAlgebra

/-! ## A. The compatibility predicate -/

/-- `a` and `b` are Jordan-compatible: their multiplication operators commute,
`L_a \circ L_b = L_b \circ L_a`. The Jordan-intrinsic substitute for "`a` and `b` commute", not
needing an associative product to state. -/
def IsJordanCompatible (a b : E) : Prop := Commute (L a) (L b)

lemma isJordanCompatible_self (a : E) : IsJordanCompatible a a := Commute.refl _

lemma isJordanCompatible_comm {a b : E} (h : IsJordanCompatible a b) :
    IsJordanCompatible b a := h.symm

/-- `L_1` is the identity. -/
lemma mulLeft_one_eq_id : (L (1 : E) : E →ₗ[ℝ] E) = LinearMap.id :=
  LinearMap.ext mulLeft_one_apply

/-- The order unit is Jordan-compatible with everything: `L_1 = id` commutes with any operator. -/
lemma isJordanCompatible_one_left (a : E) : IsJordanCompatible 1 a := by
  unfold IsJordanCompatible
  rw [mulLeft_one_eq_id]
  exact Commute.one_left _

lemma isJordanCompatible_one_right (a : E) : IsJordanCompatible a 1 :=
  (isJordanCompatible_one_left a).symm

end JordanAlgebra

end ProbabilisticTheory
