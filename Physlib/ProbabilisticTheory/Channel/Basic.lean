/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Algebra.Order.Module.PositiveLinearMap

/-!
# Positive unital maps

## i. Overview

In the order-unit-space model used here, a channel is a positive unital transformation: it sends
observables to observables without turning a possible outcome negative, and it leaves the certain
outcome certain. This covers time evolution, noise, and measurements whose outcomes are discarded
at the level of a general probabilistic theory. For quantum systems with a specified composite
structure, physical channels normally require the stronger condition of complete positivity,
which is not expressible using the order-unit structure alone.

## ii. Key results

- `UnitalPositiveLinearMap` : a positive linear map preserving `1`, notated `E →ₚ₁[R] F`.
- `UnitalPositiveLinearMap.ofLinearMap` : bundle a linear map after checking positivity and
  unitality.

## iii. Table of contents

- A. Unital positive linear maps
- B. Constructing unital positive linear maps

-/

@[expose] public section

/-!

## A. Unital positive linear maps

-/

/-- A positive linear map preserving `1`. -/
structure UnitalPositiveLinearMap (R E F : Type*) [Semiring R]
    [AddCommMonoid E] [PartialOrder E] [AddCommMonoid F] [PartialOrder F]
    [Module R E] [Module R F] [One E] [One F] extends E →ₚ[R] F where
  /-- A unital positive linear map preserves the order unit. -/
  map_one' : toPositiveLinearMap 1 = 1

/-- Notation for positive unital linear maps. -/
notation:25 E " →ₚ₁[" R:25 "] " F:0 => UnitalPositiveLinearMap R E F

namespace UnitalPositiveLinearMap

variable {R E F : Type*} [Semiring R]
  [AddCommMonoid E] [PartialOrder E] [AddCommMonoid F] [PartialOrder F]
  [Module R E] [Module R F] [One E] [One F]

instance : FunLike (E →ₚ₁[R] F) E F where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    exact DFunLike.coe_injective h

instance : LinearMapClass (E →ₚ₁[R] F) R E F where
  map_add f := map_add f.toLinearMap
  map_smulₛₗ f := f.toLinearMap.map_smul'

instance : OrderHomClass (E →ₚ₁[R] F) E F where
  map_rel f {_ _} h := f.monotone' h

instance : OneHomClass (E →ₚ₁[R] F) E F where
  map_one f := f.map_one'

@[ext]
lemma ext {f g : E →ₚ₁[R] F} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

/-- Unital positive linear maps are determined by their underlying linear map. -/
lemma toLinearMap_injective : Function.Injective (fun f : E →ₚ₁[R] F => f.toLinearMap) :=
  fun _ _ h => ext (LinearMap.congr_fun h)

end UnitalPositiveLinearMap

namespace UnitalPositiveLinearMap

variable {R E F : Type*} [Semiring R]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]
  [AddCommGroup F] [PartialOrder F] [IsOrderedAddMonoid F]
  [Module R E] [Module R F] [One E] [One F]

/-!

## B. Constructing unital positive linear maps

-/

/-- Bundle a linear map after proving only positivity and preservation of `1`. -/
def ofLinearMap (f : E →ₗ[R] F) (hpos : ∀ x, 0 ≤ x → 0 ≤ f x) (hone : f 1 = 1) : E →ₚ₁[R] F where
  toPositiveLinearMap := PositiveLinearMap.mk₀ f hpos
  map_one' := hone

end UnitalPositiveLinearMap
