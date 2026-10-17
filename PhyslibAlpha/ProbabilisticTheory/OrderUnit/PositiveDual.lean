/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.OrderUnit.Basic
public import PhyslibAlpha.Mathematics.Order.PositiveDual.Basic

/-!

# The unit of an order-unit space as an order unit

The unit of an order-unit space is an order unit, so weight-zero positive functionals vanish.

## i. Overview

The unit of an order-unit space is an order unit of the underlying ordered vector space, so the
general order theory of positive functionals applies to observables. In particular a positive
functional that vanishes on the unit vanishes everywhere.

## ii. Key results

- `OrderUnitSpace.isOrderUnit_one` : the unit is an order unit.
- `PositiveLinearMap.eq_zero_of_map_one_eq_zero` : a positive functional of total weight zero
  vanishes.

## iii. Table of contents

- A. The unit as an order unit
- B. Positive functionals

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory

namespace OrderUnitSpace

variable {E : Type*} [OrderUnitSpace E]

/-! ## A. The unit as an order unit -/

/-- The unit is an order unit: nonnegative, and every observable lies below a multiple of it. -/
lemma isOrderUnit_one : IsOrderUnit (1 : E) := ⟨one_nonneg, exists_nsmul_one_le⟩

/-- Any two observables lie below a common one. -/
instance : IsDirectedOrder E := isOrderUnit_one.isDirectedOrder

end OrderUnitSpace

/-! ## B. Positive functionals -/

/-- A positive functional with total weight zero vanishes. -/
lemma _root_.PositiveLinearMap.eq_zero_of_map_one_eq_zero {E : Type*} [OrderUnitSpace E]
    {ψ : E →ₚ[ℝ] ℝ} (h : ψ 1 = 0) : ψ = 0 :=
  PositiveLinearMap.eq_zero_of_map_eq_zero OrderUnitSpace.isOrderUnit_one h

end ProbabilisticTheory
