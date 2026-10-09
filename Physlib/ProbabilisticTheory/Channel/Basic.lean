/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import Mathlib.Basic.NNReal.Defs

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
- `PositiveLinearMap` scalar action : positive linear maps can be scaled by nonnegative reals.
- `UnitalPositiveLinearMap.ofLinearMap` : bundle a linear map after checking positivity and
  unitality.
- `UnitalPositiveLinearMap.ofPositiveLinearMap` : bundle a positive linear map after checking
  unitality.

## iii. Table of contents

- A. Unital positive linear maps
- B. Constructing unital positive linear maps
- C. Scaling positive linear maps

## iv. References

-/

@[expose] public section

/-!

## A. Unital positive linear maps

-/

/-- A positive linear map preserving `1`. -/
@[ext]
structure UnitalPositiveLinearMap (R E F : Type*) [Semiring R]
    [AddCommMonoid E] [PartialOrder E] [AddCommMonoid F] [PartialOrder F]
    [Module R E] [Module R F] [One E] [One F] extends E →ₚ[R] F, OneHom E F

attribute [nolint docBlame] UnitalPositiveLinearMap.toOneHom

/-- Notation for positive unital linear maps. -/
notation:25 E " →ₚ₁[" R:25 "] " F:0 => UnitalPositiveLinearMap R E F

namespace UnitalPositiveLinearMap

variable {R E F : Type*} [Semiring R]
  [AddCommMonoid E] [PartialOrder E] [AddCommMonoid F] [PartialOrder F]
  [Module R E] [Module R F] [One E] [One F]

instance : FunLike (E →ₚ₁[R] F) E F where
  coe f := f.toFun
  coe_injective _ _ h := UnitalPositiveLinearMap.ext h

instance : LinearMapClass (E →ₚ₁[R] F) R E F where
  map_add f := map_add f.toLinearMap
  map_smulₛₗ f := map_smul f.toLinearMap

instance : OrderHomClass (E →ₚ₁[R] F) E F where
  map_rel f {_ _} h := f.monotone' h

instance : OneHomClass (E →ₚ₁[R] F) E F where
  map_one f := f.map_one'

instance : Coe (E →ₚ₁[R] F) (E →ₚ[R] F) := ⟨toPositiveLinearMap⟩

@[simp]
lemma toPositiveLinearMap_apply (f : E →ₚ₁[R] F) (x : E) : f.toPositiveLinearMap x = f x := rfl

/-- Unital positive linear maps are determined by their underlying positive linear map. -/
lemma toPositiveLinearMap_injective :
    Function.Injective (toPositiveLinearMap (R := R) (E := E) (F := F)) :=
  fun _ _ h ↦ by ext x; congrm($h x)

/-- Unital positive linear maps are determined by their underlying linear map. -/
lemma toLinearMap_injective : Function.Injective (fun f : E →ₚ₁[R] F => f.toLinearMap) :=
  fun _ _ h ↦ toPositiveLinearMap_injective
    (PositiveLinearMap.toLinearMap_injective h)

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

/-- Bundle a positive linear map after proving only that it preserves `1`. -/
def ofPositiveLinearMap (f : E →ₚ[R] F) (hone : f 1 = 1) : E →ₚ₁[R] F where
  toPositiveLinearMap := f
  map_one' := hone

omit [IsOrderedAddMonoid E] [IsOrderedAddMonoid F] in
@[simp]
lemma ofPositiveLinearMap_apply (f : E →ₚ[R] F) (hone : f 1 = 1) (x : E) :
    ofPositiveLinearMap f hone x = f x := rfl

end UnitalPositiveLinearMap

/-!

## C. Scaling positive linear maps

Positive linear maps are closed under addition and under scaling by nonnegative reals, but
unital ones are not closed under scaling.

-/

namespace PositiveLinearMap

variable {R E F : Type*} [Semiring R]
  [AddCommMonoid E] [PartialOrder E] [AddCommMonoid F] [PartialOrder F]
  [Module R E] [Module R F] [Module NNReal F] [SMulCommClass R NNReal F] [PosSMulMono NNReal F]

instance : SMul NNReal (E →ₚ[R] F) where
  smul c f := .mk (c • f.toLinearMap) fun _ _ h ↦ by
    simpa using smul_le_smul_of_nonneg_left (OrderHomClass.mono f h) zero_le

@[simp]
lemma nnreal_smul_apply (c : NNReal) (f : E →ₚ[R] F) (x : E) : (c • f) x = c • f x := rfl

end PositiveLinearMap
