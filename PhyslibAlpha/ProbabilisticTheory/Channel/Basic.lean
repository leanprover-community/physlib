/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import PhyslibAlpha.ProbabilisticTheory.OrderUnit.PositiveDual

/-!
# Channels

Channels as unital positive linear maps between order-unit spaces, and their composition.

## i. Overview

A channel is a transformation of a system, described by what it does to observables: it sends
observables of the output system to observables of the input system, keeps nonnegative
observables nonnegative, and keeps the certain outcome certain. This covers time evolution, noise,
and measurements. Quantum channels additionally stay positive on composite systems; they are
`QuantumChannel`.

## ii. Key results

- `UnitalPositiveLinearMap` : a positive linear map preserving `1`, notated `E →ₚ₁[R] F`.
- `Channel E F` : a channel between order-unit spaces, a unital positive map `E →ₚ₁[ℝ] F`.
- `UnitalPositiveLinearMap.ofLinearMap` : bundle a linear map after checking positivity and
  unitality.

## iii. Table of contents

- A. Unital positive linear maps
- B. Constructing unital positive linear maps
- C. Composing channels
- D. Channels

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory

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

namespace UnitalPositiveLinearMap

variable {R E F G : Type*} [Semiring R]
  [AddCommMonoid E] [PartialOrder E] [AddCommMonoid F] [PartialOrder F]
  [AddCommMonoid G] [PartialOrder G] [Module R E] [Module R F] [Module R G]
  [One E] [One F] [One G]

/-!

## C. Composing channels

-/

variable (R E) in
/-- The identity channel. -/
protected def id : E →ₚ₁[R] E where
  toPositiveLinearMap := .id R E
  map_one' := rfl

@[simp]
lemma id_apply (x : E) : UnitalPositiveLinearMap.id R E x = x := rfl

/-- The composite of two channels. -/
def comp (g : F →ₚ₁[R] G) (f : E →ₚ₁[R] F) : E →ₚ₁[R] G where
  toPositiveLinearMap := g.toPositiveLinearMap.comp f.toPositiveLinearMap
  map_one' := (congrArg g f.map_one').trans g.map_one'

@[simp]
lemma comp_apply (g : F →ₚ₁[R] G) (f : E →ₚ₁[R] F) (x : E) : g.comp f x = g (f x) := rfl

@[simp]
lemma comp_id (f : E →ₚ₁[R] F) : f.comp (.id R E) = f :=
  ext fun _ => rfl

@[simp]
lemma id_comp (f : E →ₚ₁[R] F) : (UnitalPositiveLinearMap.id R F).comp f = f :=
  ext fun _ => rfl

lemma comp_assoc {H : Type*} [AddCommMonoid H] [PartialOrder H] [Module R H] [One H]
    (h : G →ₚ₁[R] H) (g : F →ₚ₁[R] G) (f : E →ₚ₁[R] F) :
    h.comp (g.comp f) = (h.comp g).comp f :=
  ext fun _ => rfl

/-- Positive unital endomorphisms form a monoid under composition. -/
instance instMonoid : Monoid (E →ₚ₁[R] E) where
  one := .id R E
  mul := comp
  mul_assoc f g h := (comp_assoc f g h).symm
  one_mul := id_comp
  mul_one := comp_id

end UnitalPositiveLinearMap

/-!

## D. Channels

-/

/-- A channel between two systems: a unital positive map between their order-unit spaces. -/
abbrev Channel (E F : Type*) [OrderUnitSpace E] [OrderUnitSpace F] := E →ₚ₁[ℝ] F

end ProbabilisticTheory
