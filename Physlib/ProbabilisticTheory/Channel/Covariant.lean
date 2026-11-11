/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.Channel.Reversible

/-!
# Covariant channels

Channels that commute with two group actions by reversible transformations.

## i. Overview

More general channels may lose information but can still respect the symmetries of a system. This
is captured by covariance: a channel `Φ` between two spaces carrying group actions `ρ` and `σ` by
reversible transformations is covariant, or intertwining, if

`Φ ∘ ρ g = σ g ∘ Φ` for every group element `g`.

Covariance preserves invariant states under pullback. A reversible transformation is covariant
exactly when the target action is the transport of the source action. Together with the reversible
transformations, this gives a common framework for symmetries and dynamics in general probabilistic
theories.

## ii. Key results

- `IsIntertwining`: Covariance of a channel under two group actions.
- `IsIntertwining.comap_isInvariant`: Pullback of invariant states along covariant channels.
- `Reversible.isIntertwining_iff_eq_transport`: Characterization of the transported action.

## iii. Table of contents

- A. Covariant channels
  - A.1. Definition and closure properties
  - A.2. Invariant states
- B. Covariance of transport

## iv. References

-/

@[expose] public section

namespace ProbabilisticTheory

variable {G E F : Type*} [Group G] [OrderUnitSpace E] [OrderUnitSpace F]
  (ρ : G →* Reversible E E) (σ : G →* Reversible F F)

/-! ## A. Covariant channels -/

/-! ### A.1. Definition and closure properties -/

/-- A channel intertwines two group actions if it commutes with their transformations. -/
def IsIntertwining (Φ : E →ₚ₁[ℝ] F) : Prop := ∀ g x, Φ (ρ g x) = σ g (Φ x)

variable {ρ σ}

/-- The identity channel intertwines a group action with itself. -/
lemma isIntertwining_id : IsIntertwining ρ ρ (.id ℝ E) := by
  intro _ _
  rfl

namespace IsIntertwining

/-- The composition of intertwining channels also intertwines the group actions. -/
lemma comp {H : Type*} [OrderUnitSpace H] {τ : G →* Reversible H H}
    {Φ : E →ₚ₁[ℝ] F} {Ψ : F →ₚ₁[ℝ] H} (hΦ : IsIntertwining ρ σ Φ)
    (hΨ : IsIntertwining σ τ Ψ) : IsIntertwining ρ τ (Ψ.comp Φ) := by
  intro g x
  simp [hΦ g x, hΨ g (Φ x)]

/-! ### A.2. Invariant states -/

/-- Pulling back an invariant state along an intertwining channel preserves invariance. -/
lemma comap_isInvariant {Φ : E →ₚ₁[ℝ] F} (h : IsIntertwining ρ σ Φ)
    {ω : 𝓢[ℝ, F]} (hω : IsInvariant σ ω) :
    IsInvariant ρ (UnitalPositiveLinearMap.comap Φ ω) := by
  intro g
  ext x
  have h1 := h g⁻¹ x
  have h2 := DFunLike.congr_fun (hω g) (Φ x)
  simp only [map_inv, Reversible.inv_apply] at h1
  change ω (Φ ((ρ g).symm x)) = ω (Φ x)
  rw [h1]
  exact h2

end IsIntertwining

/-! ## B. Covariance of transport -/

namespace Reversible

variable (ρ σ) (e : Reversible E F)

/-- A reversible transformation intertwines an action with its transport. -/
lemma isIntertwining_transport :
    IsIntertwining ρ (e.transport ρ) e.toChannel := by
  intro g x
  simp [transport, conj]

/-- A reversible transformation intertwines two actions exactly when the target action
is the transport of the source action. -/
lemma isIntertwining_iff_eq_transport :
    IsIntertwining ρ σ e.toChannel ↔ σ = e.transport ρ := by
  constructor
  · intro h
    ext g y
    have := h g (e.symm y)
    simp only [toChannel_apply, apply_symm_apply] at this
    simp [transport, conj, this]
  · rintro rfl
    exact e.isIntertwining_transport ρ

end Reversible

end ProbabilisticTheory
