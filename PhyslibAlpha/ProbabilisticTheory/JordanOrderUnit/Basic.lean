/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Algebra.Jordan.Basic
public import Physlib.ProbabilisticTheory.OrderUnit.Archimedean

/-!

# Jordan order-unit spaces

## i. Overview

Quantum observables carry, besides their order and unit, the Jordan product `a ∘ b`, a commutative
product satisfying the Jordan identity. A Jordan order-unit space is an order-unit space that is a
real Jordan algebra, using Mathlib's `IsCommJordan`, whose squares are nonnegative: `0 ≤ a ∘ a`. In
the operator picture `⟪ψ, a² ψ⟫ = ‖a ψ‖² ≥ 0`.

## ii. Key results

- `IsJordanOrderUnit` : a Jordan order-unit space.
- `IsJordanOrderUnit.sq_nonneg` : squares are nonnegative.

## iii. Table of contents

- A. The compatibility class
- B. Consequences

-/

@[expose] public section

namespace ProbabilisticTheory

/-! ## A. The compatibility class -/

/-- A coherent unital Jordan algebra with an order unit and positive squares. Bundling the
data-bearing algebra and order-unit parents together prevents incompatible additions, scalar
actions, orders, or units from being selected downstream. -/
class IsJordanOrderUnit (E : Type*) extends NonAssocCommRing E, OrderUnitSpace E,
    SMulCommClass ℝ E E, IsScalarTower ℝ E E, IsCommJordan E where
  /-- Every Jordan square is a possible measurement outcome. -/
  mul_self_nonneg : ∀ a : E, 0 ≤ a * a
  /-- The algebra product and the distinguished order unit satisfy the complement-square
  expansion. This records the compatibility between the two data-bearing parent structures. -/
  one_sub_mul_one_sub : ∀ a : E, (1 - a) * (1 - a) = 1 - a - a + a * a
  /-- Multiplication by an order-unit complement has the expected algebraic expansion. -/
  mul_one_sub : ∀ a : E, a * (1 - a) = a - a * a

namespace IsJordanOrderUnit

variable {E : Type*} [IsJordanOrderUnit E]

/-! ## B. Consequences -/

/-- Squares are nonnegative. -/
lemma sq_nonneg (a : E) : 0 ≤ a * a := mul_self_nonneg a

end IsJordanOrderUnit

end ProbabilisticTheory
