/-
Copyright (c) 2026 David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross
-/
module

public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import Mathlib.Analysis.Complex.Basic

/-!

# Channels

## i. Overview

A channel from system `A` to system `B` is, in the Schrödinger picture, an affine map on states.
Dualizing gives a unital positive linear map on effects in the other direction (the Heisenberg
picture): `UnitalPositiveLinearMap` is exactly that dual, and `E₁ →ₚ₁[R] E₂` reads as "the
adjoint of a channel `A → B`" whenever `E₁`, `E₂` are the effect algebras of `A`, `B`.

## ii. Key definitions and results

- `UnitalPositiveLinearMap` is the type of positive linear maps that preserve `1`.
- `E₁ →ₚ₁[R] E₂` is notation for it.
- Endomorphisms `E →ₚ₁[R] E` form a monoid under composition.

## iii. Table of contents

- A. Unital positive linear maps
- B. Constructors
- C. Coercions and extensionality
- D. Identity and composition

## Implementation details

We follow the implementation of `PositiveLinearMap` closely.

-/

@[expose] public section

section UnitalPositiveLinearMap

/-! ## A. Unital positive linear maps -/

/-- A positive linear map that preserves `1`. -/
structure UnitalPositiveLinearMap (R E₁ E₂ : Type*) [Semiring R]
    [AddCommMonoid E₁] [PartialOrder E₁] [AddCommMonoid E₂] [PartialOrder E₂]
    [Module R E₁] [Module R E₂] [One E₁] [One E₂] extends E₁ →ₚ[R] E₂, OneHom E₁ E₂

-- The inherited `OneHom` projection has no separately attachable docstring.
attribute [nolint docBlame] UnitalPositiveLinearMap.toOneHom

/-- Notation for unital positive linear maps. -/
notation:25 E " →ₚ₁[" R:25 "] " F:0 => UnitalPositiveLinearMap R E F

section UnitalPositiveLinearMapClass

/-! ## B. Constructors -/

variable {F R E₁ E₂ : Type*} [Semiring R]
  [AddCommMonoid E₁] [PartialOrder E₁] [AddCommMonoid E₂] [PartialOrder E₂]
  [Module R E₁] [Module R E₂] [FunLike F E₁ E₂] [LinearMapClass F R E₁ E₂]
  [OrderHomClass F E₁ E₂] [One E₁] [One E₂] [OneHomClass F E₁ E₂]

/-- Bundle a positive, unital linear map satisfying the relevant typeclass assumptions. -/
def UnitalPositiveLinearMap.ofClass (f : F) : E₁ →ₚ₁[R] E₂ :=
  { (f : E₁ →ₗ[R] E₂), (f : E₁ →o E₂), (f : OneHom E₁ E₂) with }

end UnitalPositiveLinearMapClass

namespace UnitalPositiveLinearMap

variable {R E₁ E₂ : Type*} [Semiring R]
  [AddCommGroup E₁] [PartialOrder E₁] [IsOrderedAddMonoid E₁]
  [AddCommGroup E₂] [PartialOrder E₂] [IsOrderedAddMonoid E₂]
  [Module R E₁] [Module R E₂] [One E₁] [One E₂]

/-- Bundle a linear map after proving only positivity and preservation of `1`. -/
def ofLinearMap (f : E₁ →ₗ[R] E₂) (hpos : ∀ x, 0 ≤ x → 0 ≤ f x)
    (hone : f 1 = 1) : E₁ →ₚ₁[R] E₂ where
  toPositiveLinearMap := PositiveLinearMap.mk₀ f hpos
  map_one' := hone

end UnitalPositiveLinearMap

namespace UnitalPositiveLinearMap

/-! ## C. Coercions and extensionality -/

variable {R E₁ E₂ E₃ E₄ : Type*} [Semiring R]
    [AddCommMonoid E₁] [PartialOrder E₁]
    [AddCommMonoid E₂] [PartialOrder E₂]
    [AddCommMonoid E₃] [PartialOrder E₃]
    [AddCommMonoid E₄] [PartialOrder E₄]
    [Module R E₁] [Module R E₂] [Module R E₃] [Module R E₄]
    [One E₁] [One E₂] [One E₃] [One E₄]

instance : FunLike (E₁ →ₚ₁[R] E₂) E₁ E₂ where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective
    exact h

instance : LinearMapClass (E₁ →ₚ₁[R] E₂) R E₁ E₂ where
  map_add f := map_add f.toLinearMap
  map_smulₛₗ f := f.toLinearMap.map_smul'

instance : OrderHomClass (E₁ →ₚ₁[R] E₂) E₁ E₂ where
  map_rel f {_ _} hab := f.monotone' hab

instance : OneHomClass (E₁ →ₚ₁[R] E₂) E₁ E₂ where
  map_one f := f.map_one'

example (f : E₁ →ₚ₁[R] E₂) : f 1 = 1 := by simp

@[simp]
lemma coe_toPositiveLinearMap (f : E₁ →ₚ₁[R] E₂) : (f.toPositiveLinearMap : E₁ → E₂) = f :=
  rfl

example (f : E₁ →ₚ₁[R] E₂) : f.toLinearMap 1 = 1 := by
  simp

initialize_simps_projections UnitalPositiveLinearMap (toFun → apply, as_prefix toLinearMap)

@[ext]
lemma ext {f g : E₁ →ₚ₁[R] E₂} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

variable (R E₁) in
/-- The identity as a positive linear one-preserving map. -/
@[simps! apply toLinearMap] protected def id : E₁ →ₚ₁[R] E₁ where
  __ := LinearMap.id
  __ := OrderHom.id
  __ := OneHom.id E₁

@[simp] lemma toOrderHom_id : (UnitalPositiveLinearMap.id R E₁).toOrderHom = .id := rfl
@[simp] lemma toOneHom_id : (UnitalPositiveLinearMap.id R E₁).toOneHom = .id E₁ := rfl

/-! ## D. Identity and composition -/

/-- Composition of positive linear one-preserving maps. -/
@[simps! apply]
def comp (g : E₂ →ₚ₁[R] E₃) (f : E₁ →ₚ₁[R] E₂) : E₁ →ₚ₁[R] E₃ where
  toLinearMap := g.toPositiveLinearMap.comp f.toPositiveLinearMap
  monotone' := g.monotone'.comp f.monotone'
  map_one' := by simp

/-- Composition of unital positive linear maps is associative. -/
lemma comp_assoc (h : E₃ →ₚ₁[R] E₄) (g : E₂ →ₚ₁[R] E₃) (f : E₁ →ₚ₁[R] E₂) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  ext x
  simp

@[simp] lemma toPositiveLinearMap_comp (g : E₂ →ₚ₁[R] E₃) (f : E₁ →ₚ₁[R] E₂) :
    (g.comp f).toPositiveLinearMap = g.toPositiveLinearMap.comp f.toPositiveLinearMap :=
  rfl

@[simp] lemma toOrderHom_comp (g : E₂ →ₚ₁[R] E₃) (f : E₁ →ₚ₁[R] E₂) :
    (g.comp f).toOrderHom = g.toOrderHom.comp f.toOrderHom :=
  rfl

@[simp] lemma comp_id (f : E₁ →ₚ₁[R] E₂) : f.comp (.id R E₁) = f := rfl
@[simp] lemma id_comp (f : E₁ →ₚ₁[R] E₂) : (UnitalPositiveLinearMap.id R E₂).comp f = f := rfl

/-- Unital positive endomorphisms form a monoid under composition. -/
instance instMonoid : Monoid (E₁ →ₚ₁[R] E₁) where
  one := .id R E₁
  mul := comp
  one_mul := id_comp
  mul_one := comp_id
  mul_assoc := comp_assoc

@[simp] lemma one_apply (x : E₁) : (1 : E₁ →ₚ₁[R] E₁) x = x := rfl

@[simp] lemma mul_apply (f g : E₁ →ₚ₁[R] E₁) (x : E₁) : (f * g) x = f (g x) := rfl

@[simp]
lemma map_smul_of_tower {S : Type*} [SMul S E₁] [SMul S E₂]
    [LinearMap.CompatibleSMul E₁ E₂ S R] (f : E₁ →ₚ₁[R] E₂) (c : S) (x : E₁) :
    f (c • x) = c • f x := LinearMapClass.map_smul_of_tower f _ _

@[aesop safe apply (rule_sets := [CStarAlgebra])]
protected lemma map_nonneg (f : E₁ →ₚ₁[R] E₂) {x : E₁} (hx : 0 ≤ x) : 0 ≤ f x :=
  map_nonneg f hx

lemma toPositiveLinearMap_injective :
    Function.Injective (toPositiveLinearMap : (E₁ →ₚ₁[R] E₂) → (E₁ →ₚ[R] E₂)) :=
  fun _ _ h ↦ by ext x; congrm($h x)

/-- Unital positive linear maps are determined by their underlying linear maps. -/
lemma toLinearMap_injective :
    Function.Injective
      (fun f : E₁ →ₚ₁[R] E₂ => f.toLinearMap) := by
  intro f g h
  ext x
  exact congrArg (fun k : E₁ →ₗ[R] E₂ => k x) h

@[simp]
lemma toPositiveLinearMap_inj {f g : E₁ →ₚ₁[R] E₂} :
    f.toPositiveLinearMap = g.toPositiveLinearMap ↔ f = g :=
  toPositiveLinearMap_injective.eq_iff
