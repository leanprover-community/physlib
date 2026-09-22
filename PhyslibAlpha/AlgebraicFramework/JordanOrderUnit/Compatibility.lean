/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.JordanOrderUnit.Operator

/-!

# Jordan-intrinsic compatibility of observables

## i. Overview

The physical notion of two observables being "compatible" (jointly measurable, simultaneously
sharp) should not need the C⋆-commutator to state — that commutator does not exist at the bare
Jordan level, and defining compatibility via it would put the cart before the horse (compatibility
is exactly the *classical*, commuting fragment of the theory, the fragment that should not need the
full C⋆ apparatus to talk about). The standard Jordan-algebraic substitute is **operator
commutativity**: `a` and `b` are Jordan-compatible when their multiplication operators commute,
`L_a ∘ L_b = L_b ∘ L_a`.

`CStarAlgebra/JordanCompatibility.lean` shows this is no idle abstraction: for `a`, `b` self-adjoint
elements of a C⋆-algebra that already commute in the ordinary associative sense (`ab = ba`), `L_a`
and `L_b` commute as Jordan operators too — so every associatively-compatible pair of observables
is automatically Jordan-compatible, recovering the expected physics. The converse (Jordan
compatibility implies associative commutativity) is *not* claimed here; it is a separate, harder
question left open.

A genuinely stronger notion — that `a` and `b` *jointly generate an associative Jordan
subalgebra*, giving a two-observable joint functional calculus — needs a two-generator analogue of
`Power/GeneratedByOne.lean` and, in turn, a two-variable strengthening of
`Power/Associative.lean`'s open power-associativity theorem. `FreeJordanTwo.lean`/
`FreeSpecialTwo.lean` lay the groundwork (the abstract and concrete special free Jordan algebras
on two generators), but the two hard theorems connecting them — Shirshov (the abstract algebra
embeds specially) and Cohn (every quotient of a special algebra stays special) — are real,
disconnected future work, not attempted here.

## ii. Key definitions and results

- `IsJordanOrderUnit.IsJordanCompatible`
- `IsJordanOrderUnit.isJordanCompatible_comm`, `.isJordanCompatible_one_left/right`

## iii. Table of contents

- A. The compatibility predicate

-/

@[expose] public section

namespace JordanAlgebra

variable {E : Type*} [NonAssocCommRing E] [Module ℝ E] [SMulCommClass ℝ E E]

open scoped JordanAlgebra

/-! ## A. The compatibility predicate -/

/-- `a` and `b` are Jordan-compatible: their multiplication operators commute,
`L_a \circ L_b = L_b \circ L_a`. The Jordan-intrinsic substitute for "`a` and `b` commute", not
needing an associative product to state. -/
def IsJordanCompatible (a b : E) : Prop := Commute (L a) (L b)

theorem isJordanCompatible_self (a : E) : IsJordanCompatible a a := Commute.refl _

theorem isJordanCompatible_comm {a b : E} (h : IsJordanCompatible a b) :
    IsJordanCompatible b a := h.symm

/-- `L 1` is the identity operator (`mulLeft_one_apply` upgraded from pointwise to a genuine
operator equality). -/
theorem mulLeft_one_eq_id : (L (1 : E) : E →ₗ[ℝ] E) = LinearMap.id :=
  LinearMap.ext mulLeft_one_apply

/-- The order unit is Jordan-compatible with everything: `L_1 = id` commutes with any operator. -/
theorem isJordanCompatible_one_left (a : E) : IsJordanCompatible 1 a := by
  unfold IsJordanCompatible
  rw [mulLeft_one_eq_id]
  exact Commute.one_left _

theorem isJordanCompatible_one_right (a : E) : IsJordanCompatible a 1 :=
  (isJordanCompatible_one_left a).symm

end JordanAlgebra
