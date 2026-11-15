/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.State.Basic
public import Mathlib.Algebra.Module.Equiv.Defs

/-!
# Reversible transformations of observables

Reversible transformations of observable spaces, their group structure, their action on states and
the transport of group actions.

## i. Overview

Time evolution, spatial symmetries and changes of reference frame all have something in common:
they transform observables in a way that can be undone.

This motivates reversible transformations, defined as unital linear order isomorphisms of
observable spaces. They form a group and naturally act on states. A group representation by
reversible transformations describes symmetries or reversible dynamics. For example, time evolution
is represented by the additive group of real numbers. A reversible transformation also transports a
group action from one observable space to another by conjugation.

## ii. Key results

- `Reversible`: Reversible transformations, i.e. unital linear order isomorphisms of
  observable spaces.
- `Reversible.toChannelHom`: Reversible transformations embed in the monoid of channels.
- `Reversible.instMulActionState`: The induced action on states.
- `Reversible.transport`: Transport of a group action along a reversible transformation.
- `IsInvariant`: A state fixed by every transformation of a group action.

## iii. Table of contents

- A. Reversible transformations
  - A.1. Definition
  - A.2. Group structure
  - A.3. As channels
- B. Action on states
- C. Transport of group actions
  - C.1. Conjugation
  - C.2. Transported actions
- D. Invariant states

## iv. References

-/

@[expose] public section

namespace ProbabilisticTheory

/-! ## A. Reversible transformations -/

/-! ### A.1. Definition -/

/-- A reversible transformation between observable spaces: a linear bijection that preserves and
reflects the order and preserves the order unit. Both it and its inverse are channels. -/
structure Reversible (P Q : ProbabilisticTheory)
    extends P.Observables ≃ₗ[ℝ] Q.Observables where
  /-- The equivalence preserves and reflects the order. -/
  map_le_map_iff' : ∀ {x y : P.Observables}, toLinearEquiv x ≤ toLinearEquiv y ↔ x ≤ y
  /-- The order unit is preserved. -/
  map_one' : toLinearEquiv 1 = 1

namespace Reversible

variable {G : Type*} [Group G] {P Q R : ProbabilisticTheory}

instance : FunLike (Reversible P Q) P.Observables Q.Observables where
  coe e := e.toLinearEquiv
  coe_injective e f h := by
    obtain ⟨e, _, _⟩ := e
    obtain ⟨f, _, _⟩ := f
    obtain rfl : e = f := DFunLike.coe_injective h
    rfl

@[ext]
lemma ext {e f : Reversible P Q} (h : ∀ x, e x = f x) : e = f := DFunLike.ext _ _ h

/-! ### A.2. Group structure -/

/-- The identity reversible transformation. -/
def refl (P : ProbabilisticTheory) : Reversible P P where
  toLinearEquiv := .refl ℝ P.Observables
  map_le_map_iff' := Iff.rfl
  map_one' := rfl

/-- The inverse of a reversible transformation. -/
def symm (e : Reversible P Q) : Reversible Q P where
  toLinearEquiv := e.toLinearEquiv.symm
  map_le_map_iff' {x y} := by
    simpa using (e.map_le_map_iff' (x := e.toLinearEquiv.symm x) (y := e.toLinearEquiv.symm y)).symm
  map_one' := e.toLinearEquiv.symm_apply_eq.2 e.map_one'.symm

/-- Composition of reversible transformations, applying `e₁` before `e₂`. -/
def trans (e₁ : Reversible P Q) (e₂ : Reversible Q R) : Reversible P R where
  toLinearEquiv := e₁.toLinearEquiv.trans e₂.toLinearEquiv
  map_le_map_iff' {x y} :=
    (e₂.map_le_map_iff' (x := e₁ x) (y := e₁ y)).trans e₁.map_le_map_iff'
  map_one' := by
    change e₂ (e₁ 1) = 1
    rw [show e₁ 1 = 1 from e₁.map_one', show e₂ 1 = 1 from e₂.map_one']

@[simp] lemma refl_apply (x : P.Observables) : refl P x = x := rfl

@[simp] lemma symm_apply_apply (e : Reversible P Q) (x : P.Observables) : e.symm (e x) = x :=
  e.toLinearEquiv.symm_apply_apply x

@[simp] lemma apply_symm_apply (e : Reversible P Q) (y : Q.Observables) : e (e.symm y) = y :=
  e.toLinearEquiv.apply_symm_apply y

@[simp] lemma trans_apply (e₁ : Reversible P Q) (e₂ : Reversible Q R) (x : P.Observables) :
    e₁.trans e₂ x = e₂ (e₁ x) := rfl

/-- Reversible transformations of a single space form a group under composition. -/
instance automorphismGroup : Group (Reversible P P) where
  mul f g := g.trans f
  one := refl P
  inv := symm
  mul_assoc _ _ _ := by ext; rfl
  one_mul _ := by ext; rfl
  mul_one _ := by ext; rfl
  inv_mul_cancel f := by ext x; exact f.symm_apply_apply x

@[simp] lemma mul_apply (f g : Reversible P P) (x : P.Observables) : (f * g) x = f (g x) := rfl

@[simp] lemma one_apply (x : P.Observables) : (1 : Reversible P P) x = x := rfl

@[simp] lemma inv_apply (f : Reversible P P) (x : P.Observables) : f⁻¹ x = f.symm x := rfl

/-! ### A.3. As channels -/

/-- A reversible transformation regarded as a channel. -/
def toChannel (e : Reversible P Q) : Channel P Q :=
  .ofLinearMap e.toLinearEquiv.toLinearMap
    (by intro x hx; simpa using (e.map_le_map_iff' (x := 0) (y := x)).2 hx) e.map_one'

@[simp] lemma toChannel_apply (e : Reversible P Q) (x : P.Observables) : e.toChannel x = e x := rfl

/-- Regarding reversible transformations as channels is a homomorphism of monoids. -/
def toChannelHom : Reversible P P →* Channel P P where
  toFun := toChannel
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] lemma toChannelHom_apply (e : Reversible P P) (x : P.Observables) :
    toChannelHom e x = e x := rfl

/-! ## B. Action on states -/

/-- The action on states induced by the inverse of a reversible transformation. -/
instance instMulActionState : MulAction (Reversible P P) (𝓢[ℝ, P.Observables]) where
  smul φ ω := Channel.comap (toChannelHom φ⁻¹) ω
  one_smul _ := by ext; rfl
  mul_smul _ _ _ := by ext; rfl

lemma smul_state_apply (φ : Reversible P P) (ω : 𝓢[ℝ, P.Observables]) (x : P.Observables) :
    (φ • ω) x = ω (φ.symm x) := rfl

/-! ## C. Transport of group actions -/

/-! ### C.1. Conjugation -/

/-- Conjugation transports reversible dynamics between observable spaces. -/
def conj (e : Reversible P Q) : Reversible P P →* Reversible Q Q where
  toFun φ := e.symm.trans (φ.trans e)
  map_one' := by ext y; exact e.apply_symm_apply y
  map_mul' φ ψ := by ext y; simp

/-! ### C.2. Transported actions -/

/-- Transport a group action between observable spaces along a reversible transformation. -/
def transport (ρ : G →* Reversible P P) (e : Reversible P Q) :
    G →* Reversible Q Q := e.conj.comp ρ

end Reversible

/-! ## D. Invariant states -/

/-- A state is invariant if it is fixed by every transformation of the group action. -/
def IsInvariant {G : Type*} [Group G] {P : ProbabilisticTheory} (ρ : G →* Reversible P P)
    (ω : 𝓢[ℝ, P.Observables]) : Prop := ∀ g, ρ g • ω = ω

end ProbabilisticTheory
