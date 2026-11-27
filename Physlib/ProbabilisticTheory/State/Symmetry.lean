/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.State.Convex
public import Physlib.ProbabilisticTheory.Channel.Covariant

/-!
# States under symmetries

Reversible changes of observables act on states by inverse pullback.

## i. Overview

A state is invariant under a group action when every transformation leaves it fixed.
Pullback along an intertwining channel preserves this invariance.

## ii. Key results

- `ProbabilisticTheory.State.reversible_smul_apply` : evaluation after a reversible action.
- `ProbabilisticTheory.State.IsInvariant` : states fixed by a group action.
- `ProbabilisticTheory.State.IsInvariant.comap` : pullback preserves invariant states.
- `ProbabilisticTheory.State.IsPure.comap` : reversible transformations preserve pure states.

## iii. Table of contents

- A. Reversible action
- B. Invariant states
- C. Pure states

## iv. References

-/

@[expose] public section

open ProbabilisticTheory

namespace ProbabilisticTheory.State

variable {G : Type*} [Group G] {P Q : ProbabilisticTheory}

/-! ## A. Reversible action -/

/-- The action on states induced by the inverse of a reversible transformation. -/
instance instMulActionReversible : MulAction (Reversible P P) P.State where
  smul φ ω := ω.comap (Reversible.toChannelHom φ⁻¹)
  one_smul _ := by ext; rfl
  mul_smul _ _ _ := by ext; rfl

lemma reversible_smul_apply (φ : Reversible P P) (ω : P.State) (x : P.Observables) :
    (φ • ω) x = ω (φ.symm x) := rfl

/-! ## B. Invariant states -/

/-- A state is invariant when every transformation of the group action fixes it. -/
def IsInvariant (ω : P.State) (ρ : G →* Reversible P P) : Prop := ∀ g, ρ g • ω = ω

/-- Pulling back an invariant state along an intertwining channel preserves invariance. -/
lemma IsInvariant.comap {ρ : G →* Reversible P P} {σ : G →* Reversible Q Q}
    {Φ : Channel P Q} {ω : Q.State} (hω : ω.IsInvariant σ)
    (h : Φ.IsIntertwining ρ σ) : (ω.comap Φ).IsInvariant ρ := by
  intro g
  ext x
  have h1 := h g⁻¹ x
  simp only [map_inv, Reversible.inv_apply] at h1
  change ω (Φ ((ρ g).symm x)) = ω (Φ x)
  rw [h1]
  exact DFunLike.congr_fun (hω g) (Φ x)

/-! ## C. Pure states -/

/-- Pullback along a reversible transformation maps pure states to pure states. -/
lemma IsPure.comap {ω : Q.State} (h : ω.IsPure) (e : Reversible P Q) :
    (ω.comap e.toChannel).IsPure := by
  refine isPure_iff_forall_mix_eq.mpr fun φ ψ t ht0 ht1 hmix ↦ ?_
  have hω : mix (φ.comap e.symm.toChannel) (ψ.comap e.symm.toChannel) t = ω :=
    Channel.ext fun y ↦ by simpa using DFunLike.congr_fun hmix (e.symm y)
  obtain ⟨hφ, hψ⟩ := isPure_iff_forall_mix_eq.mp h _ _ t ht0 ht1 hω
  exact ⟨Channel.ext fun x ↦ by simpa using DFunLike.congr_fun hφ (e x),
    Channel.ext fun x ↦ by simpa using DFunLike.congr_fun hψ (e x)⟩

end ProbabilisticTheory.State
