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

A reversible transformation is covariant
exactly when the target action is the transport of the source action. Together with the reversible
transformations, this gives a common framework for symmetries and dynamics of observable spaces.

## ii. Key results

- `Channel.IsIntertwining`: Covariance of a channel under two group actions.
- `Channel.isIntertwining_iff_eq_transport`: Characterization of the transported action.

## iii. Table of contents

- A. Covariant channels
  - A.1. Definition and closure properties
- B. Covariance of transport

## iv. References

-/

@[expose] public section

open ProbabilisticTheory ProbabilisticTheory.Reversible

namespace Channel

variable {G : Type*} [Group G] {P Q : ProbabilisticTheory}
  {ρ : G →* Reversible P P} {σ : G →* Reversible Q Q}

/-! ## A. Covariant channels -/

/-! ### A.1. Definition and closure properties -/

/-- A channel intertwines two group actions if it commutes with their transformations. -/
def IsIntertwining (Φ : Channel P Q) (ρ : G →* Reversible P P)
    (σ : G →* Reversible Q Q) : Prop := ∀ g x, Φ (ρ g x) = σ g (Φ x)

/-- The identity channel intertwines a group action with itself. -/
lemma isIntertwining_id (ρ : G →* Reversible P P) : (Channel.id P).IsIntertwining ρ ρ := by
  intro _ _
  rfl

/-- The composition of intertwining channels also intertwines the group actions. -/
lemma IsIntertwining.comp {R : ProbabilisticTheory} {τ : G →* Reversible R R}
    {Φ : Channel P Q} {Ψ : Channel Q R} (hΦ : Φ.IsIntertwining ρ σ)
    (hΨ : Ψ.IsIntertwining σ τ) : (Ψ.comp Φ).IsIntertwining ρ τ := by
  intro g x
  simp [hΦ g x, hΨ g (Φ x)]

/-! ## B. Covariance of transport -/

/-- A reversible transformation intertwines an action with its transport. -/
lemma isIntertwining_transport (ρ : G →* Reversible P P) (e : Reversible P Q) :
    e.toChannel.IsIntertwining ρ (e.transport ρ) := by
  intro g x
  simp [transport, conj]

/-- A reversible transformation intertwines two actions exactly when the target action
is the transport of the source action. -/
lemma isIntertwining_iff_eq_transport (ρ : G →* Reversible P P)
    (σ : G →* Reversible Q Q) (e : Reversible P Q) :
    e.toChannel.IsIntertwining ρ σ ↔ σ = e.transport ρ := by
  constructor
  · intro h
    ext g y
    have := h g (e.symm y)
    simp only [toChannel_apply, apply_symm_apply] at this
    simp [transport, conj, this]
  · rintro rfl
    exact isIntertwining_transport ρ e

end Channel
