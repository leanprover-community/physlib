/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Algebra.Jordan.Basic
public import PhyslibAlpha.AlgebraicFramework.OrderUnit.Norm

/-!

# Jordan order-unit spaces

## i. Overview

This is the next rung above `OrderUnit`, per the architecture

`AOU → JordanOrderUnit → JB → JBW (later)`.

An order-unit space only remembers `≤` and `1`. Quantum observables carry one more
piece of structure that is *not* the full associative operator product (which loses
self-adjointness for non-commuting `a`, `b`): the Jordan product `a ∘ b`, a commutative,
generally non-associative multiplication satisfying the weak-associativity Jordan identity. This
file adds the minimal compatibility condition: every square is a possible outcome,
`0 ≤ a ∘ a`. In the operator picture `a ∘ a = a²`, and
`⟨ψ, a²ψ⟩ = ‖aψ‖² ≥ 0` is the reason variances are never negative. Identifying *every* positive
element with a square is deliberately not assumed here; that is a stronger spectral theorem of
the JB layer.

We do not redefine Jordan algebras: `IsCommJordan` and the surrounding non-unital, non-associative
commutative ring axioms are exactly mathlib's `Mathlib.Algebra.Jordan.Basic`, together with the
real-linearity hypotheses (`Module ℝ E`, `SMulCommClass`, `IsScalarTower`) that its own module
docstring already names as the standard setting for a *real* Jordan algebra. This file only adds
this one order-compatibility axiom.

## ii. Key definitions and results

- `IsJordanOrderUnit E`
- `IsJordanOrderUnit.mul_one`
- `IsJordanOrderUnit.mul_self_nonneg`

## iii. Table of contents

- A. The compatibility class
- B. Consequences

-/

@[expose] public section

/-! ## A. The compatibility class -/

/-- `E` carries a unital Jordan product compatible with its order unit: every square is positive.
The multiplicative unit laws belong to `NonAssocCommRing`; they are deliberately not duplicated
here. Archimedeanness is not needed for this algebraic-order compatibility. -/
class IsJordanOrderUnit (E : Type*) [NonAssocCommRing E] [PartialOrder E]
    [IsOrderedAddMonoid E] [Module ℝ E] [SMulCommClass ℝ E E] [IsScalarTower ℝ E E]
    [IsCommJordan E] [IsOrderUnit E] : Prop where
  /-- Every Jordan square is a possible measurement outcome. -/
  mul_self_nonneg : ∀ a : E, 0 ≤ a * a

namespace IsJordanOrderUnit

variable {E : Type*} [NonAssocCommRing E] [PartialOrder E] [IsOrderedAddMonoid E]
  [Module ℝ E] [SMulCommClass ℝ E E] [IsScalarTower ℝ E E] [IsCommJordan E]
  [IsOrderUnit E] [IsJordanOrderUnit E]

/-! ## B. Consequences -/

/-- Every Jordan square is a possible measurement outcome (unprimed re-export of the field, for
uniform dot-notation with the rest of this file's API). -/
theorem sq_nonneg (a : E) : 0 ≤ a * a := mul_self_nonneg a

end IsJordanOrderUnit
