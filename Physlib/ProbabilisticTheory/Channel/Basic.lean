/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import Physlib.ProbabilisticTheory.Basic

/-!
# Channels between observable spaces

Channels preserve positivity and the certain outcome between observable spaces.

## i. Overview

In the order-unit-space model used here, a channel is a positive unital transformation: it sends
observables to observables without turning a possible outcome negative, and it leaves the certain
outcome certain. This covers time evolution, noise, and measurements whose outcomes are discarded
using only ordered real observables and a certain outcome. For quantum systems with a specified
composite structure, physical channels normally require the stronger condition of complete
positivity, which is not expressible using the order-unit structure alone.

A channel `Φ : Channel P Q` is a unital positive linear map from
`P.Observables` to `Q.Observables`.

## ii. Key results

- `Channel` : channels between observable spaces.
- `Channel.id`, `Channel.comp` : the identity and composition of channels.
- `Channel.ofLinearMap` : bundle a linear map after checking positivity and unitality.

## iii. Table of contents

- A. Channels between observable spaces

## iv. References

-/

@[expose] public section

/-! ## A. Channels between observable spaces -/

/-- A channel preserves positivity and the certain outcome between observable spaces. -/
structure Channel (P Q : ProbabilisticTheory) extends P.Observables →ₚ[ℝ] Q.Observables where
  /-- The certain outcome is sent to the certain outcome. -/
  map_one' : toFun 1 = 1

namespace Channel

variable {P Q R : ProbabilisticTheory}

instance : FunLike (Channel P Q) P.Observables Q.Observables where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr 1
    exact DFunLike.coe_injective h

@[ext]
lemma ext {f g : Channel P Q} (h : ∀ x, f x = g x) : f = g := DFunLike.ext _ _ h

instance : AddMonoidHomClass (Channel P Q) P.Observables Q.Observables where
  map_zero f := map_zero f.toLinearMap
  map_add f := map_add f.toLinearMap

instance : LinearMapClass (Channel P Q) ℝ P.Observables Q.Observables where
  map_add f := map_add f.toLinearMap
  map_smulₛₗ f := map_smul f.toLinearMap

instance : OrderHomClass (Channel P Q) P.Observables Q.Observables where
  map_rel f {_ _} h := f.monotone' h

instance : OneHomClass (Channel P Q) P.Observables Q.Observables where
  map_one f := f.map_one'

instance : Coe (Channel P Q) (P.Observables →ₚ[ℝ] Q.Observables) := ⟨toPositiveLinearMap⟩

@[simp]
lemma toPositiveLinearMap_apply (f : Channel P Q) (x : P.Observables) :
    f.toPositiveLinearMap x = f x := rfl

/-- Channels are determined by their underlying positive linear map. -/
lemma toPositiveLinearMap_injective :
    Function.Injective (toPositiveLinearMap (P := P) (Q := Q)) :=
  fun _ _ h ↦ by ext x; congrm($h x)

/-- Channels are determined by their underlying linear map. -/
lemma toLinearMap_injective : Function.Injective (fun f : Channel P Q => f.toLinearMap) :=
  fun _ _ h ↦ toPositiveLinearMap_injective (PositiveLinearMap.toLinearMap_injective h)

/-- The identity as a channel. -/
def id (P : ProbabilisticTheory) : Channel P P where
  toPositiveLinearMap := PositiveLinearMap.id ℝ P.Observables
  map_one' := rfl

/-- The composition of channels. -/
def comp (g : Channel Q R) (f : Channel P Q) : Channel P R where
  toPositiveLinearMap := g.toPositiveLinearMap.comp f.toPositiveLinearMap
  map_one' := by simp

@[simp] lemma id_apply (x : P.Observables) : Channel.id P x = x := rfl

@[simp] lemma comp_apply (g : Channel Q R) (f : Channel P Q) (x : P.Observables) :
    g.comp f x = g (f x) := rfl

@[simp] lemma comp_id (f : Channel P Q) : f.comp (.id P) = f := rfl

@[simp] lemma id_comp (f : Channel P Q) : (Channel.id Q).comp f = f := rfl

/-- Channels on an observable space form a monoid under composition. -/
instance : Monoid (Channel P P) where
  mul f g := f.comp g
  one := .id P
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl

/-- Bundle a linear map after proving only positivity and preservation of `1`. -/
def ofLinearMap (f : P.Observables →ₗ[ℝ] Q.Observables) (hpos : ∀ x, 0 ≤ x → 0 ≤ f x)
    (hone : f 1 = 1) : Channel P Q where
  toPositiveLinearMap := PositiveLinearMap.mk₀ f hpos
  map_one' := hone

/-- Bundle a positive linear map after proving only that it preserves `1`. -/
def ofPositiveLinearMap (f : P.Observables →ₚ[ℝ] Q.Observables) (hone : f 1 = 1) : Channel P Q where
  toPositiveLinearMap := f
  map_one' := hone

end Channel
