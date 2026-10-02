/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Channel.Symmetry
public import PhyslibAlpha.ProbabilisticTheory.Measurement.EffectValuedMeasure
public import PhyslibAlpha.ProbabilisticTheory.Measurement.Pushforward
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Basic

/-!

# Covariant measurements and channels

## i. Overview

A measurement is covariant under a symmetry group when transforming the outcome transforms the
effect: `μ (g • S) = ρ g • μ S`. A symmetry acts on effects, a group acts on outcomes by measurable
bijections, and a channel is covariant when it intertwines two symmetry actions.

## ii. Key results

- `Symmetry.instSMulEffect` : symmetries act on effects.
- `MeasurableAction` : a group acting on outcomes by measurable bijections.
- `EffectValuedMeasure.IsCovariant` : covariant effect-valued measures.
- `UnitalPositiveLinearMap.IsCovariant` : covariant channels.

## iii. Table of contents

- A. Covariant channels: the general intertwiner picture

-/

@[expose] public section

namespace ProbabilisticTheory

open scoped Pointwise

section EffectAction

variable {E : Type*} [OrderUnitSpace E]

/-- A symmetry acts on effects the way it acts on `E` itself, via the underlying channel — the
dual of `Symmetry`'s existing action on states. -/
instance Symmetry.instSMulEffect : SMul (Symmetry E) (Effect E) := ⟨fun φ e => φ.1.mapEffect e⟩

@[simp]
lemma Symmetry.coe_smul_effect (φ : Symmetry E) (e : Effect E) :
    ((φ • e : Effect E) : E) = φ.1 (e : E) := rfl

instance Symmetry.instMulActionEffect : MulAction (Symmetry E) (Effect E) where
  one_smul e := Subtype.ext (by simp)
  mul_smul φ ψ e := Subtype.ext (by simp [UnitalPositiveLinearMap.comp_apply])

end EffectAction

section MeasurableAction

/-- `G` acts on the measurable space `Ω`, and every group element moves points measurably. Since
this holds for `g` and `g⁻¹` both, the action is by measurable *bijections*: `MeasurableSet.smul`
below shows it moves measurable sets to measurable sets, not merely points. -/
class MeasurableAction (G Ω : Type*) [Group G] [MeasurableSpace Ω] [MulAction G Ω] : Prop where
  /-- Every group element acts as a measurable map. -/
  measurable_smul : ∀ g : G, Measurable (fun x : Ω => g • x)

variable {G Ω : Type*} [Group G] [MeasurableSpace Ω] [MulAction G Ω] [MeasurableAction G Ω]

/-- The image of a measurable set under the action of a group element is again measurable:
`g • S` is the preimage of `S` under the (measurable) action of `g⁻¹`. -/
lemma measurableSet_smul {S : Set Ω} (hS : MeasurableSet S) (g : G) : MeasurableSet (g • S) := by
  have heq : g • S = (fun x => g⁻¹ • x) ⁻¹' S := by
    ext x
    simp only [Set.mem_smul_set, Set.mem_preimage]
    constructor
    · rintro ⟨s, hs, rfl⟩
      rwa [inv_smul_smul]
    · intro hx
      exact ⟨g⁻¹ • x, hx, by rw [smul_inv_smul]⟩
  rw [heq]
  exact MeasurableSet.preimage hS (MeasurableAction.measurable_smul g⁻¹)

end MeasurableAction

section Covariant

variable {G Ω E : Type*} [Group G] [MeasurableSpace Ω] [MulAction G Ω] [MeasurableAction G Ω]
  [OrderUnitSpace E]

/-- A measurement (POVM) `μ` is **covariant** under an action of `G` on the outcome space,
transported to the physical system via `ρ : G →* Symmetry E`, when transforming the outcome set
and transforming the assigned effect agree: `μ(g • S) = ρ(g) • μ(S)`. This is the abstract form of
`E(gS) = α_g(E(S))` — a rotated detector pointed at a rotated direction reads out what a rotation
of the original detector would have. -/
def EffectValuedMeasure.IsCovariant (ρ : G →* Symmetry E) (μ : EffectValuedMeasure Ω E) : Prop :=
  ∀ (g : G) (S : Set Ω) (hS : MeasurableSet S), μ (g • S) (measurableSet_smul hS g) = ρ g • μ S hS

end Covariant

/-! ## A. Covariant channels: the general intertwiner picture

A channel between two systems is covariant when transporting the input and transporting the
output agree: the channel intertwines the two actions. -/

section CovariantChannel

variable {G E₁ E₂ E₃ : Type*} [Group G] [OrderUnitSpace E₁] [OrderUnitSpace E₂]
  [OrderUnitSpace E₃]

/-- A channel `φ : Channel E₁ E₂` is **covariant** under symmetry actions `ρ₁`, `ρ₂` of `G` on the
two systems when transporting the input along `ρ₁ g` then applying `φ`, or applying `φ` then
transporting the output along `ρ₂ g`, agree — the channel intertwines the two actions. -/
def UnitalPositiveLinearMap.IsCovariant (ρ₁ : G →* Symmetry E₁) (ρ₂ : G →* Symmetry E₂)
    (φ : Channel E₁ E₂) : Prop :=
  ∀ g : G, φ.comp (ρ₁ g).1 = (ρ₂ g).1.comp φ

/-- The identity channel is covariant under any action of `G`, against itself: it trivially
intertwines an action with itself. -/
lemma UnitalPositiveLinearMap.isCovariant_id (ρ : G →* Symmetry E₁) :
    (UnitalPositiveLinearMap.id ℝ E₁).IsCovariant ρ ρ := fun g => by
  rw [UnitalPositiveLinearMap.id_comp, UnitalPositiveLinearMap.comp_id]

/-- Covariance is preserved by composition: a covariant channel followed by a covariant channel is
covariant for the actions at the two ends, with the middle system's action cancelling out. -/
lemma UnitalPositiveLinearMap.IsCovariant.comp {ρ₁ : G →* Symmetry E₁} {ρ₂ : G →* Symmetry E₂}
    {ρ₃ : G →* Symmetry E₃} {ψ : Channel E₂ E₃} {φ : Channel E₁ E₂}
    (hψ : ψ.IsCovariant ρ₂ ρ₃) (hφ : φ.IsCovariant ρ₁ ρ₂) :
    (ψ.comp φ).IsCovariant ρ₁ ρ₃ := fun g => by
  apply UnitalPositiveLinearMap.ext
  intro x
  have hφx := DFunLike.congr_fun (hφ g) x
  have hψx := DFunLike.congr_fun (hψ g) (φ x)
  simpa only [UnitalPositiveLinearMap.comp_apply] using (congrArg ψ hφx).trans hψx

end CovariantChannel

end ProbabilisticTheory
