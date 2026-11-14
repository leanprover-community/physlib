/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.State.Basic
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

## iii. Table of contents

- A. Reversible action
- B. Invariant states

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
  have h2 := DFunLike.congr_fun (hω g) (Φ x)
  simp only [map_inv, Reversible.inv_apply] at h1
  change ω (Φ ((ρ g).symm x)) = ω (Φ x)
  rw [h1]
  exact h2

end ProbabilisticTheory.State
