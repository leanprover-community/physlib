/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.Prod
/-!
# The componentwise representation of a product group

## i. Overview

Representations `ρ₁` of `G₁` on `V₁` and `ρ₂` of `G₂` on `V₂` give a representation of
`G₁ × G₂` on `V₁ × V₂`, acting componentwise. Mathlib's `Representation.prod` is the
diagonal action of a single group; this is the external product.

## ii. Key results

- `Representation.prodMap` : the componentwise representation.

## iii. Table of contents

- A. The componentwise representation

-/

@[expose] public section

/-!

## A. The componentwise representation

-/

/-- The componentwise representation of a product group on a product space. -/
noncomputable def Representation.prodMap {k G₁ G₂ V₁ V₂ : Type*} [CommSemiring k]
    [Monoid G₁] [Monoid G₂] [AddCommMonoid V₁] [Module k V₁] [AddCommMonoid V₂] [Module k V₂]
    (ρ₁ : Representation k G₁ V₁) (ρ₂ : Representation k G₂ V₂) :
    Representation k (G₁ × G₂) (V₁ × V₂) where
  toFun p := (ρ₁ p.1).prodMap (ρ₂ p.2)
  map_one' := by
    refine LinearMap.ext fun v => ?_
    simp
  map_mul' p q := by
    refine LinearMap.ext fun v => ?_
    simp [Module.End.mul_apply]

@[simp]
lemma Representation.prodMap_apply {k G₁ G₂ V₁ V₂ : Type*} [CommSemiring k]
    [Monoid G₁] [Monoid G₂] [AddCommMonoid V₁] [Module k V₁] [AddCommMonoid V₂] [Module k V₂]
    (ρ₁ : Representation k G₁ V₁) (ρ₂ : Representation k G₂ V₂) (p : G₁ × G₂) (v : V₁ × V₂) :
    Representation.prodMap ρ₁ ρ₂ p v = (ρ₁ p.1 v.1, ρ₂ p.2 v.2) := rfl
