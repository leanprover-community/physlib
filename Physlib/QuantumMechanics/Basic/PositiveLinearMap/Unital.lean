/-
Copyright (c) 2026 David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross
-/
module

public import Mathlib
public import Mathlib.Algebra.Order.Module.PositiveLinearMap

/-!

# UnitalPositiveLinearMap

## Main definitions

- `UnitalPositiveLinearMap` is the type of positive linear maps that preserve `1`

## Implementation details

We follow the implementation of `PositiveLinearMap` closely.

## TODO

- Define affine linear combinations of `UnitalPositiveLinearMaps`

-/

@[expose] public section

section UnitalPositiveLinearMap

/-- A positive linear map that preserves `1`. -/
structure UnitalPositiveLinearMap (R E₁ E₂ : Type*) [Semiring R]
    [AddCommMonoid E₁] [PartialOrder E₁] [AddCommMonoid E₂] [PartialOrder E₂]
    [Module R E₁] [Module R E₂] [One E₁] [One E₂] extends E₁ →ₚ[R] E₂, OneHom E₁ E₂

notation:25 E " →ₚ₁[" R:25 "] " F:0 => UnitalPositiveLinearMap R E F

section UnitalPositiveLinearMapClass

variable {F R E₁ E₂ : Type*} [Semiring R]
  [AddCommMonoid E₁] [PartialOrder E₁] [AddCommMonoid E₂] [PartialOrder E₂]
  [Module R E₁] [Module R E₂] [FunLike F E₁ E₂] [LinearMapClass F R E₁ E₂]
  [OrderHomClass F E₁ E₂] [One E₁] [One E₂] [OneHomClass F E₁ E₂]

def UnitalPositiveLinearMap.ofClass (f : F) : E₁ →ₚ₁[R] E₂ :=
  { (f : E₁ →ₗ[R] E₂), (f : E₁ →o E₂), (f : OneHom E₁ E₂) with }

end UnitalPositiveLinearMapClass

namespace UnitalPositiveLinearMap

variable {R E₁ E₂ E₃ : Type*} [Semiring R]
    [AddCommMonoid E₁] [PartialOrder E₁]
    [AddCommMonoid E₂] [PartialOrder E₂]
    [AddCommMonoid E₃] [PartialOrder E₃]
    [Module R E₁] [Module R E₂] [Module R E₃]
    [One E₁] [One E₂] [One E₃]

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
theorem coe_toPositiveLinearMap (f : E₁ →ₚ₁[R] E₂) : (f.toPositiveLinearMap : E₁ → E₂) = f :=
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

/-- The composition of positive linear 1-preseving maps is a positive linear 1-preserving map. -/
@[simps! apply toLinearMap]
def comp (g : E₂ →ₚ₁[R] E₃) (f : E₁ →ₚ₁[R] E₂) : E₁ →ₚ₁[R] E₃ where
  toLinearMap := g.toPositiveLinearMap.comp f.toPositiveLinearMap
  monotone' := g.monotone'.comp f.monotone'
  map_one' := by simp

@[simp] lemma toPositiveLinearMap_comp (g : E₂ →ₚ₁[R] E₃) (f : E₁ →ₚ₁[R] E₂) :
    (g.comp f).toPositiveLinearMap = g.toPositiveLinearMap.comp f.toPositiveLinearMap :=
  rfl

@[simp] lemma toOrderHom_comp (g : E₂ →ₚ₁[R] E₃) (f : E₁ →ₚ₁[R] E₂) :
    (g.comp f).toOrderHom = g.toOrderHom.comp f.toOrderHom :=
  rfl

@[simp] lemma comp_id (f : E₁ →ₚ₁[R] E₂) : f.comp (.id R E₁) = f := rfl
@[simp] lemma id_comp (f : E₁ →ₚ₁[R] E₂) : (UnitalPositiveLinearMap.id R E₂).comp f = f := rfl

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

@[simp]
lemma toPositiveLinearMap_inj {f g : E₁ →ₚ₁[R] E₂} :
    f.toPositiveLinearMap = g.toPositiveLinearMap ↔ f = g :=
  toPositiveLinearMap_injective.eq_iff
