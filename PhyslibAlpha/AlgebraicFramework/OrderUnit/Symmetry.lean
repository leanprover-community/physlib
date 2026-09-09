/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.OrderUnit.State.Basic
public import Mathlib.Algebra.Group.Action.Hom

/-!

# Symmetry: order-automorphisms and their action on states

## i. Overview

Physically, a symmetry of a system is a *reversible* transformation: a change of description that
loses no information and can always be undone. In the order-unit picture (`Channel/Basic.lean`) a
transformation between effect algebras is a channel, a unital positive linear map; a symmetry is
exactly a channel `φ : E →ₚ₁[ℝ] E` that is invertible with an inverse `φ⁻¹` that is *also* a
channel. Both directions have to be physical: undoing a symmetry must again be positive and send
the certain event to the certain event, not just be some linear inverse.

A group `G` acting on `E` "by symmetries" is then a homomorphism `ρ : G →* Symmetry E` into the
group of such automorphisms. Every symmetry, via `UnitalPositiveLinearMap.comp`, transports a
state: precomposing a state `ω : E →ₚ₁[ℝ] ℝ` with `φ⁻¹` gives the state that assigns to an
observable `x` whatever `ω` assigned to the pulled-back observable `φ⁻¹ x`. This needs no new
proof of positivity or normalization — `ω.comp φ⁻¹` is already a unital positive linear map
because `.comp` always is; all that is new
here is checking this assignment is a genuine group action, `(g*h) • ω = g • (h • ω)` and
`1 • ω = ω`, which reduces to associativity and identity laws for `.comp` already on hand.

This is the state-level pushforward along a channel, specialized to a channel that happens to be
invertible (`Channel/Basic.lean`'s `Weight.comp` is the same idea one level down, on weights on
the positive cone; working with the state directly as a `UnitalPositiveLinearMap` avoids the extra
order-unit hypotheses `Weight.comp` needs and is the cleaner route here).

## ii. Key definitions and results

- `IsOrderAutomorphism φ`: `φ` is a channel with a two-sided inverse that is also a channel.
- `Symmetry E`: the bundled group of order-automorphisms of `E`, with `Group` instance
  `mul := comp`.
- The `MulAction (Symmetry E) (𝓢[ℝ, E])` instance: pushing a state forward along the inverse
  automorphism.
- `stateSMul`: the action of a general `G` on `𝓢[ℝ, E]` induced by a homomorphism
  `ρ : G →* Symmetry E`, together with the group action laws it satisfies.
- `OneParameterAutomorphismGroup E`: a one-parameter (reversible dynamics) family
  `α : ℝ → (E →ₚ₁[ℝ] E)` with `α 0 = id` and `α (s + t) = α s ∘ α t`, each `α t` an automorphism.

## iii. Table of contents

- A. Order automorphisms
- B. The symmetry group
- C. The induced action on states
- D. One-parameter automorphism groups

-/

@[expose] public section

variable {E : Type*} [AddCommGroup E] [PartialOrder E] [Module ℝ E] [One E]

/-! ## A. Order automorphisms -/

/-- `φ` is an order-automorphism of `E`: a channel with a two-sided inverse that is itself a
channel. Equivalently, `φ` is bijective and both `φ` and `φ⁻¹` are positive and unital
(`IsOrderAutomorphism.bijective` records the "bijective" half of that equivalence). -/
def IsOrderAutomorphism (φ : E →ₚ₁[ℝ] E) : Prop :=
  ∃ ψ : E →ₚ₁[ℝ] E, ψ.comp φ = .id ℝ E ∧ φ.comp ψ = .id ℝ E

/-- The identity is trivially an order-automorphism. -/
lemma isOrderAutomorphism_id : IsOrderAutomorphism (.id ℝ E : E →ₚ₁[ℝ] E) :=
  ⟨.id ℝ E, UnitalPositiveLinearMap.id_comp _, UnitalPositiveLinearMap.id_comp _⟩

namespace IsOrderAutomorphism

variable {φ ψ : E →ₚ₁[ℝ] E}

/-- A chosen inverse channel witnessing `φ` is an order-automorphism. -/
noncomputable def inverse (h : IsOrderAutomorphism φ) : E →ₚ₁[ℝ] E := h.choose

lemma inverse_comp (h : IsOrderAutomorphism φ) : h.inverse.comp φ = .id ℝ E := h.choose_spec.1

lemma comp_inverse (h : IsOrderAutomorphism φ) : φ.comp h.inverse = .id ℝ E := h.choose_spec.2

/-- Pointwise form of `inverse_comp`: applying `φ` then its chosen inverse is the identity. -/
lemma inverse_apply_apply (h : IsOrderAutomorphism φ) (x : E) : h.inverse (φ x) = x := by
  simpa using DFunLike.congr_fun h.inverse_comp x

/-- Pointwise form of `comp_inverse`: applying the chosen inverse then `φ` is the identity. -/
lemma apply_inverse_apply (h : IsOrderAutomorphism φ) (x : E) : φ (h.inverse x) = x := by
  simpa using DFunLike.congr_fun h.comp_inverse x

/-- The inverse of an order-automorphism is again an order-automorphism, witnessed by `φ` itself.
-/
lemma inverse_isOrderAutomorphism (h : IsOrderAutomorphism φ) :
    IsOrderAutomorphism h.inverse :=
  ⟨φ, h.comp_inverse, h.inverse_comp⟩

/-- The composite of two order-automorphisms is again one, witnessed by the composite of their
inverses in the opposite order. -/
lemma comp (hφ : IsOrderAutomorphism φ) (hψ : IsOrderAutomorphism ψ) :
    IsOrderAutomorphism (φ.comp ψ) := by
  refine ⟨hψ.inverse.comp hφ.inverse, ?_, ?_⟩
  · ext x
    simp [hφ.inverse_apply_apply, hψ.inverse_apply_apply]
  · ext x
    simp [hφ.apply_inverse_apply, hψ.apply_inverse_apply]

/-- An order-automorphism is, in particular, a bijection of `E` — the "equivalently" half of the
definition's docstring. -/
lemma bijective (h : IsOrderAutomorphism φ) : Function.Bijective φ :=
  Function.bijective_iff_has_inverse.mpr ⟨h.inverse, h.inverse_apply_apply, h.apply_inverse_apply⟩

end IsOrderAutomorphism

/-! ## B. The symmetry group -/

/-- A symmetry of `E`: an order-automorphism, bundled with its defining property. Composition
makes these into a group, `Symmetry.instGroup` below. Reducible, so the underlying channel
coercion (`Subtype.val`) unifies transparently wherever a `E →ₚ₁[ℝ] E` is expected. -/
abbrev Symmetry (E : Type*) [AddCommGroup E] [PartialOrder E] [Module ℝ E] [One E] :=
  {φ : E →ₚ₁[ℝ] E // IsOrderAutomorphism φ}

namespace Symmetry

@[ext]
lemma ext {φ ψ : Symmetry E} (h : ∀ x, (φ : E →ₚ₁[ℝ] E) x = (ψ : E →ₚ₁[ℝ] E) x) : φ = ψ :=
  Subtype.ext (UnitalPositiveLinearMap.ext h)

instance instOne : One (Symmetry E) := ⟨⟨.id ℝ E, isOrderAutomorphism_id⟩⟩

instance instMul : Mul (Symmetry E) := ⟨fun φ ψ => ⟨φ.1.comp ψ.1, φ.2.comp ψ.2⟩⟩

noncomputable instance instInv : Inv (Symmetry E) :=
  ⟨fun φ => ⟨φ.2.inverse, φ.2.inverse_isOrderAutomorphism⟩⟩

@[simp] lemma val_one : (1 : Symmetry E).1 = .id ℝ E := rfl

@[simp] lemma val_mul (φ ψ : Symmetry E) : (φ * ψ).1 = φ.1.comp ψ.1 := rfl

@[simp] lemma val_inv (φ : Symmetry E) : (φ⁻¹ : Symmetry E).1 = φ.2.inverse := rfl

/-- Order-automorphisms of `E` form a group under composition, with `1` the identity channel and
`φ⁻¹` the (chosen) inverse channel. -/
noncomputable instance instGroup : Group (Symmetry E) where
  mul_assoc φ ψ χ := Subtype.ext (UnitalPositiveLinearMap.comp_assoc φ.1 ψ.1 χ.1)
  one_mul φ := Subtype.ext (UnitalPositiveLinearMap.id_comp φ.1)
  mul_one φ := Subtype.ext (UnitalPositiveLinearMap.comp_id φ.1)
  inv_mul_cancel φ := Subtype.ext φ.2.inverse_comp

/-- The symmetry group is canonically equivalent to the group of units of the monoid of unital
positive endomorphisms. This identifies the explicit order-automorphism presentation with
Mathlib's general algebraic notion of an invertible element. -/
noncomputable def unitsEquiv : Symmetry E ≃* (E →ₚ₁[ℝ] E)ˣ where
  toFun φ :=
    { val := φ.1
      inv := φ.2.inverse
      val_inv := φ.2.comp_inverse
      inv_val := φ.2.inverse_comp }
  invFun φ := ⟨φ.val, ⟨φ.inv, φ.inv_val, φ.val_inv⟩⟩
  left_inv _ := Symmetry.ext fun _ => rfl
  right_inv _ := Units.ext rfl
  map_mul' _ _ := Units.ext rfl

/-! ## C. The induced action on states -/

/-- The canonical action of `Symmetry E` on the state space `𝓢[ℝ, E]`: a symmetry `φ` transports a
state `ω` by pulling it back along the inverse automorphism, `φ • ω = ω ∘ φ⁻¹`. This is exactly
the Schrödinger-picture pushforward of a state along the channel `φ⁻¹` (`Channel/Basic.lean`), so
it costs nothing beyond `UnitalPositiveLinearMap.comp` — positivity and normalization of `φ • ω`
are already built into `.comp`. -/
noncomputable instance instMulActionState : MulAction (Symmetry E) (𝓢[ℝ, E]) where
  smul φ ω := ω.comp φ⁻¹.1
  one_smul ω := by
    show ω.comp (1 : Symmetry E)⁻¹.1 = ω
    rw [inv_one, val_one, UnitalPositiveLinearMap.comp_id]
  mul_smul φ ψ ω := by
    show ω.comp (φ * ψ)⁻¹.1 = (ω.comp ψ⁻¹.1).comp φ⁻¹.1
    rw [mul_inv_rev, val_mul, ← UnitalPositiveLinearMap.comp_assoc]

lemma smul_state_def (φ : Symmetry E) (ω : 𝓢[ℝ, E]) : φ • ω = ω.comp φ⁻¹.1 := rfl

/-- A group `G` acting on `E` by order-automorphisms — a homomorphism `ρ : G →* Symmetry E` — acts
on the state space `𝓢[ℝ, E]` by transporting each state along `ρ g`. This is the induced action of
`instMulActionState` along `ρ`, so the group action laws below are inherited for free rather than
reproved: they are literally `mul_smul`/`one_smul` for `instMulActionState`, precomposed with the
homomorphism `ρ`. -/
noncomputable def stateSMul {G : Type*} [Group G] (ρ : G →* Symmetry E) (g : G) (ω : 𝓢[ℝ, E]) :
    𝓢[ℝ, E] :=
  ρ g • ω

@[simp] lemma stateSMul_one {G : Type*} [Group G] (ρ : G →* Symmetry E) (ω : 𝓢[ℝ, E]) :
    stateSMul ρ 1 ω = ω := by
  simp [stateSMul]

lemma stateSMul_mul {G : Type*} [Group G] (ρ : G →* Symmetry E) (g h : G) (ω : 𝓢[ℝ, E]) :
    stateSMul ρ (g * h) ω = stateSMul ρ g (stateSMul ρ h ω) := by
  simp [stateSMul, map_mul, mul_smul]

end Symmetry

/-! ## D. One-parameter automorphism groups: reversible dynamics -/

/-- A one-parameter group of order-automorphisms of `E`, indexed by time: `α t` is the
automorphism of "let `t` units of time pass". This is exactly the "reversible dynamics" idea named
in `OVERVIEW.md` (§8's channels, §13's outlook) — the definition and group law only; generators
and Stone's theorem are future work. -/
structure OneParameterAutomorphismGroup (E : Type*) [AddCommGroup E] [PartialOrder E]
    [Module ℝ E] [One E] where
  /-- The automorphism of `E` after time `t` has passed. -/
  toFun : ℝ → E →ₚ₁[ℝ] E
  /-- Letting no time pass does nothing. -/
  map_zero' : toFun 0 = .id ℝ E
  /-- Letting `s + t` units of time pass is the same as letting `t` pass, then `s`. -/
  map_add' : ∀ s t, toFun (s + t) = (toFun s).comp (toFun t)

namespace OneParameterAutomorphismGroup

instance : CoeFun (OneParameterAutomorphismGroup E) (fun _ => ℝ → E →ₚ₁[ℝ] E) := ⟨toFun⟩

@[simp] lemma coe_map_zero (α : OneParameterAutomorphismGroup E) : α 0 = .id ℝ E := α.map_zero'

lemma coe_map_add (α : OneParameterAutomorphismGroup E) (s t : ℝ) :
    α (s + t) = (α s).comp (α t) := α.map_add' s t

/-- Every automorphism in a one-parameter group is genuinely an order-automorphism, with `α (-t)`
its inverse: running time backwards undoes running it forwards. -/
lemma isOrderAutomorphism (α : OneParameterAutomorphismGroup E) (t : ℝ) :
    IsOrderAutomorphism (α t) := by
  refine ⟨α (-t), ?_, ?_⟩
  · rw [← α.coe_map_add, neg_add_cancel, α.coe_map_zero]
  · rw [← α.coe_map_add, add_neg_cancel, α.coe_map_zero]

/-- A one-parameter automorphism group organizes into a homomorphism from `Multiplicative ℝ` into
the automorphism group `Symmetry E` — reconnecting to the general group action of
`Symmetry.stateSMul` above, with `G = Multiplicative ℝ`. -/
noncomputable def toSymmetryHom (α : OneParameterAutomorphismGroup E) :
    Multiplicative ℝ →* Symmetry E where
  toFun t := ⟨α (Multiplicative.toAdd t), α.isOrderAutomorphism _⟩
  map_one' := Symmetry.ext fun x => by simp
  map_mul' s t := Symmetry.ext fun x => by
    simp [Symmetry.val_mul, α.coe_map_add, UnitalPositiveLinearMap.comp_apply]

/-- The state evolution induced by a one-parameter automorphism group: `α.stateEvolution t` moves
a state forward by time `t`, and composes correctly in `t` (`Symmetry.stateSMul_mul` specialized
along `toSymmetryHom`). -/
noncomputable def stateEvolution (α : OneParameterAutomorphismGroup E) (t : ℝ) (ω : 𝓢[ℝ, E]) :
    𝓢[ℝ, E] :=
  Symmetry.stateSMul α.toSymmetryHom (Multiplicative.ofAdd t) ω

@[simp] lemma stateEvolution_zero (α : OneParameterAutomorphismGroup E) (ω : 𝓢[ℝ, E]) :
    α.stateEvolution 0 ω = ω := by
  simp [stateEvolution, ofAdd_zero]

lemma stateEvolution_add (α : OneParameterAutomorphismGroup E) (s t : ℝ) (ω : 𝓢[ℝ, E]) :
    α.stateEvolution (s + t) ω = α.stateEvolution s (α.stateEvolution t ω) := by
  simp only [stateEvolution, ofAdd_add]
  exact Symmetry.stateSMul_mul α.toSymmetryHom (Multiplicative.ofAdd s) (Multiplicative.ofAdd t) ω

end OneParameterAutomorphismGroup
