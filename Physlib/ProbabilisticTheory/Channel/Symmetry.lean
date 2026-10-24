/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Physlib.ProbabilisticTheory.State.Basic

/-!
# Reversible dynamics and covariant channels

Reversible transformations of observables, their action on states, and covariance under
group actions.

## i. Overview

Reversible transformations are unital order isomorphisms of observable spaces. They form
a group under composition and act on states through the inverse transformation.

A group representation by reversible transformations describes symmetries or reversible
dynamics. For example, time evolution is represented by the additive group of real numbers.

A channel is covariant if it intertwines the group actions on its domain and codomain.
Covariance preserves invariant states under pullback. An order isomorphism also transports
a group action between observable spaces, giving the unique action for which the
isomorphism is covariant.

## ii. Key results

- `OrderUnitEquiv`: Unital linear order isomorphisms between observable spaces.
- `OrderUnitEquiv.instMulActionState`: The induced action on states.
- `IsIntertwining`: Covariance of a channel under two group actions.
- `IsIntertwining.comap_isInvariant`: Pullback of invariant states along covariant channels.
- `OrderUnitEquiv.transport`: Transport of a group action along an order isomorphism.
- `OrderUnitEquiv.isIntertwining_iff_eq_transport`: Characterization of the transported action.

## iii. Table of contents

- A. Order-unit equivalences
- B. Action on states
- C. Covariant channels
- D. Transport of group actions

## iv. References

-/

@[expose] public section

namespace ProbabilisticTheory

/-! ## A. Order-unit equivalences -/

/-- A unital linear order isomorphism between order-unit spaces. -/
structure OrderUnitEquiv (E F : Type*) [OrderUnitSpace E] [OrderUnitSpace F]
    extends E ≃ₗ[ℝ] F where
  /-- The equivalence preserves and reflects the order. -/
  map_le_map_iff' : ∀ {x y : E}, toLinearEquiv x ≤ toLinearEquiv y ↔ x ≤ y
  /-- The order unit is preserved. -/
  map_one' : toLinearEquiv 1 = 1

namespace OrderUnitEquiv

variable {E F G : Type*} [OrderUnitSpace E] [OrderUnitSpace F] [OrderUnitSpace G]

instance : FunLike (OrderUnitEquiv E F) E F where
  coe e := e.toLinearEquiv
  coe_injective e f h := by
    obtain ⟨e, _, _⟩ := e
    obtain ⟨f, _, _⟩ := f
    obtain rfl : e = f := DFunLike.coe_injective h
    rfl

@[ext]
lemma ext {e f : OrderUnitEquiv E F} (h : ∀ x, e x = f x) : e = f := DFunLike.ext _ _ h

/-- The identity order-unit equivalence. -/
def refl (E : Type*) [OrderUnitSpace E] : OrderUnitEquiv E E where
  toLinearEquiv := .refl ℝ E
  map_le_map_iff' := Iff.rfl
  map_one' := rfl

/-- The inverse of an order-unit equivalence. -/
def symm (e : OrderUnitEquiv E F) : OrderUnitEquiv F E where
  toLinearEquiv := e.toLinearEquiv.symm
  map_le_map_iff' {x y} := by
    simpa using (e.map_le_map_iff' (x := e.toLinearEquiv.symm x) (y := e.toLinearEquiv.symm y)).symm
  map_one' := e.toLinearEquiv.symm_apply_eq.2 e.map_one'.symm

/-- Composition of order-unit equivalences, applying `e₁` before `e₂`. -/
def trans (e₁ : OrderUnitEquiv E F) (e₂ : OrderUnitEquiv F G) : OrderUnitEquiv E G where
  toLinearEquiv := e₁.toLinearEquiv.trans e₂.toLinearEquiv
  map_le_map_iff' {x y} :=
    (e₂.map_le_map_iff' (x := e₁ x) (y := e₁ y)).trans e₁.map_le_map_iff'
  map_one' := by
    change e₂ (e₁ 1) = 1
    rw [show e₁ 1 = 1 from e₁.map_one', show e₂ 1 = 1 from e₂.map_one']

@[simp] lemma refl_apply (x : E) : refl E x = x := rfl

@[simp] lemma symm_apply_apply (e : OrderUnitEquiv E F) (x : E) : e.symm (e x) = x :=
  e.toLinearEquiv.symm_apply_apply x

@[simp] lemma apply_symm_apply (e : OrderUnitEquiv E F) (y : F) : e (e.symm y) = y :=
  e.toLinearEquiv.apply_symm_apply y

@[simp] lemma trans_apply (e₁ : OrderUnitEquiv E F) (e₂ : OrderUnitEquiv F G) (x : E) :
    e₁.trans e₂ x = e₂ (e₁ x) := rfl

/-- Order-unit automorphisms form a group under composition. -/
instance : Group (OrderUnitEquiv E E) where
  mul f g := g.trans f
  one := refl E
  inv := symm
  mul_assoc _ _ _ := by ext; rfl
  one_mul _ := by ext; rfl
  mul_one _ := by ext; rfl
  inv_mul_cancel f := by ext x; exact f.symm_apply_apply x

@[simp] lemma mul_apply (f g : OrderUnitEquiv E E) (x : E) : (f * g) x = f (g x) := rfl

@[simp] lemma one_apply (x : E) : (1 : OrderUnitEquiv E E) x = x := rfl

@[simp] lemma inv_apply (f : OrderUnitEquiv E E) (x : E) : f⁻¹ x = f.symm x := rfl

/-- An order-unit equivalence regarded as a unital positive linear map. -/
def toChannel (e : OrderUnitEquiv E F) : E →ₚ₁[ℝ] F :=
  .ofLinearMap e.toLinearEquiv.toLinearMap
    (by intro x hx; simpa using (e.map_le_map_iff' (x := 0) (y := x)).2 hx) e.map_one'

@[simp] lemma toChannel_apply (e : OrderUnitEquiv E F) (x : E) : e.toChannel x = e x := rfl

/-! ## B. Action on states -/

/-- The action on states induced by the inverse of an order-unit automorphism. -/
instance instMulActionState : MulAction (OrderUnitEquiv E E) (𝓢[ℝ, E]) where
  smul φ ω := UnitalPositiveLinearMap.comap φ⁻¹.toChannel ω
  one_smul _ := by ext; rfl
  mul_smul _ _ _ := by ext; rfl

lemma smul_state_apply (φ : OrderUnitEquiv E E) (ω : 𝓢[ℝ, E]) (x : E) :
    (φ • ω) x = ω (φ.symm x) := rfl

end OrderUnitEquiv

/-! ## C. Covariant channels -/

section Intertwining

variable {G E F : Type*} [Group G] [OrderUnitSpace E] [OrderUnitSpace F]
  (ρ : G →* OrderUnitEquiv E E) (σ : G →* OrderUnitEquiv F F)

/-- A channel intertwines two group actions if it commutes with their transformations. -/
def IsIntertwining (Φ : E →ₚ₁[ℝ] F) : Prop := ∀ g x, Φ (ρ g x) = σ g (Φ x)

/-- A state is invariant if it is fixed by every transformation of the group action. -/
def IsInvariant (ω : 𝓢[ℝ, E]) : Prop := ∀ g, ρ g • ω = ω

variable {ρ σ}

/-- The identity channel intertwines a group action with itself. -/
lemma isIntertwining_id : IsIntertwining ρ ρ (.id ℝ E) := by
  intro _ _
  rfl

/-- The composition of intertwining channels also intertwines the group actions. -/
lemma IsIntertwining.comp {H : Type*} [OrderUnitSpace H] {τ : G →* OrderUnitEquiv H H}
    {Φ : E →ₚ₁[ℝ] F} {Ψ : F →ₚ₁[ℝ] H} (hΦ : IsIntertwining ρ σ Φ)
    (hΨ : IsIntertwining σ τ Ψ) : IsIntertwining ρ τ (Ψ.comp Φ) := by
  intro g x
  simp [hΦ g x, hΨ g (Φ x)]

/-- Pulling back an invariant state along an intertwining channel preserves invariance. -/
lemma IsIntertwining.comap_isInvariant {Φ : E →ₚ₁[ℝ] F} (h : IsIntertwining ρ σ Φ)
    {ω : 𝓢[ℝ, F]} (hω : IsInvariant σ ω) :
    IsInvariant ρ (UnitalPositiveLinearMap.comap Φ ω) := by
  intro g
  ext x
  have h1 := h g⁻¹ x
  have h2 := DFunLike.congr_fun (hω g) (Φ x)
  simp only [map_inv, OrderUnitEquiv.inv_apply] at h1
  change ω (Φ ((ρ g).symm x)) = ω (Φ x)
  rw [h1]
  exact h2

end Intertwining

/-! ## D. Transport of group actions -/

namespace OrderUnitEquiv

variable {G E F : Type*} [Group G] [OrderUnitSpace E] [OrderUnitSpace F]

/-- Conjugation by an order-unit equivalence transports automorphisms from `E` to `F`. -/
def conj (e : OrderUnitEquiv E F) : OrderUnitEquiv E E →* OrderUnitEquiv F F where
  toFun φ := e.symm.trans (φ.trans e)
  map_one' := by ext y; exact e.apply_symm_apply y
  map_mul' φ ψ := by ext y; simp

/-- Transport a group action from `E` to `F` along an order-unit equivalence. -/
def transport (e : OrderUnitEquiv E F) (ρ : G →* OrderUnitEquiv E E) :
    G →* OrderUnitEquiv F F := e.conj.comp ρ

/-- An order-unit equivalence intertwines an action with its transport. -/
lemma isIntertwining_transport (e : OrderUnitEquiv E F) (ρ : G →* OrderUnitEquiv E E) :
    IsIntertwining ρ (e.transport ρ) e.toChannel := by
  intro g x
  simp [transport, conj]

/-- An order-unit equivalence intertwines two actions exactly when the target action
is the transport of the source action. -/
lemma isIntertwining_iff_eq_transport (e : OrderUnitEquiv E F) (ρ : G →* OrderUnitEquiv E E)
    (σ : G →* OrderUnitEquiv F F) :
    IsIntertwining ρ σ e.toChannel ↔ σ = e.transport ρ := by
  constructor
  · intro h
    ext g y
    have := h g (e.symm y)
    simp only [toChannel_apply, apply_symm_apply] at this
    simp [transport, conj, this]
  · rintro rfl
    exact e.isIntertwining_transport ρ

end OrderUnitEquiv

end ProbabilisticTheory
