/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Representation.Covariance.Basic
public import PhyslibAlpha.ProbabilisticTheory.Measurement.Postprocessing
public import Mathlib.Algebra.Group.Action.Prod

/-!

# Covariance of measurements under an action on the outcomes

Covariance of measurements under a group action on outcomes, and its preservation.

## i. Overview

A group `G` acting measurably on an outcome space `Ω` acts on the classical system of `Ω` by
relabeling: `σ` sends an observable `f` to `x ↦ f (σ⁻¹ • x)`. The inverse makes this a left
action. A measurement is a channel out of the classical system, so its covariance, matched to a
symmetry action `ρ` on the physical system, is just covariance of that channel.

Post-processing a measurement is composing its channel with a classical channel, so covariance is
preserved by covariant post-processing. In particular the marginals of a covariant joint
measurement, for the diagonal action on a product of outcome spaces, are covariant.

## ii. Key results

- `BoundedMeasurable.inducedAction` : the action of `G` on the classical system of `Ω`.
- `Measurement.IsCovariant` : covariance of a measurement.
- `Measurement.IsCovariant.comp` : covariant post-processing preserves covariance.
- `Measurement.IsCovariant.marginal` : marginals of a covariant joint measurement are covariant.

## iii. Table of contents

- A. The induced action on the classical system
- B. Covariant measurements

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory

/-! ## A. The induced action on the classical system -/

end ProbabilisticTheory

namespace BoundedMeasurable
open ProbabilisticTheory

variable {G Ω : Type*} [Group G] [MeasurableSpace Ω] [MulAction G Ω] [MeasurableAction G Ω]

/-- The channel on the classical system that relabels outcomes by `σ`:
`f ↦ (x ↦ f (σ⁻¹ • x))`. -/
def inducedChannel (σ : G) : Channel (BoundedMeasurable Ω) (BoundedMeasurable Ω) :=
  comap (σ⁻¹ • ·) (MeasurableAction.measurable_smul σ⁻¹)

@[simp]
lemma inducedChannel_apply (σ : G) (f : BoundedMeasurable Ω) (x : Ω) :
    inducedChannel σ f x = f (σ⁻¹ • x) := rfl

/-- Relabeling by `σ⁻¹` undoes relabeling by `σ`, so each relabeling channel is an
order-automorphism. -/
lemma isOrderAutomorphism_inducedChannel (σ : G) :
    IsOrderAutomorphism (inducedChannel (Ω := Ω) σ) :=
  ⟨inducedChannel σ⁻¹, UnitalPositiveLinearMap.ext fun f => BoundedMeasurable.ext fun x => by
      simp [UnitalPositiveLinearMap.comp_apply],
    UnitalPositiveLinearMap.ext fun f => BoundedMeasurable.ext fun x => by
      simp [UnitalPositiveLinearMap.comp_apply]⟩

/-- The action of `G` on the classical system of `Ω` induced by its action on the outcomes. -/
noncomputable def inducedAction : G →* Symmetry (BoundedMeasurable Ω) where
  toFun σ := ⟨inducedChannel σ, isOrderAutomorphism_inducedChannel σ⟩
  map_one' := Symmetry.ext fun f => BoundedMeasurable.ext fun x => by simp
  map_mul' σ τ := Symmetry.ext fun f => BoundedMeasurable.ext fun x => by
    simp [UnitalPositiveLinearMap.comp_apply, mul_smul]

@[simp]
lemma inducedAction_val (σ : G) :
    (inducedAction σ : Symmetry (BoundedMeasurable Ω)).1 = inducedChannel σ := rfl

variable {Ω' : Type*} [MeasurableSpace Ω'] [MulAction G Ω'] [MeasurableAction G Ω']

/-- The diagonal action on a product of outcome spaces is measurable. -/
instance : MeasurableAction G (Ω × Ω') :=
  ⟨fun σ => ((MeasurableAction.measurable_smul σ).comp measurable_fst).prodMk
    ((MeasurableAction.measurable_smul σ).comp measurable_snd)⟩

/-- Relabeling along an equivariant measurable map is a covariant classical channel. -/
lemma comap_isCovariant (g : Ω' → Ω) (hg : Measurable g)
    (hequiv : ∀ (σ : G) x, g (σ • x) = σ • g x) :
    (comap g hg).IsCovariant (inducedAction (G := G)) (inducedAction (G := G)) := fun σ =>
  UnitalPositiveLinearMap.ext fun f => BoundedMeasurable.ext fun x => by
    simp [UnitalPositiveLinearMap.comp_apply, hequiv]

end BoundedMeasurable

namespace ProbabilisticTheory


/-! ## B. Covariant measurements -/

namespace Measurement

open BoundedMeasurable

variable {G Ω Ω' E : Type*} [Group G] [MeasurableSpace Ω] [MulAction G Ω] [MeasurableAction G Ω]
  [MeasurableSpace Ω'] [MulAction G Ω'] [MeasurableAction G Ω'] [OrderUnitSpace E]

/-- A measurement is covariant for an action on its outcomes, matched to the symmetry action `ρ`
on the system, when its channel intertwines the two actions. -/
def IsCovariant (ρ : G →* Symmetry E) (M : Measurement Ω E) : Prop :=
  M.toChannel.IsCovariant inducedAction ρ

/-- Post-processing a covariant measurement by a covariant classical channel gives a covariant
channel. -/
lemma IsCovariant.comp {ρ : G →* Symmetry E} {M : Measurement Ω E}
    {K : Channel (BoundedMeasurable Ω') (BoundedMeasurable Ω)} (hM : M.IsCovariant ρ)
    (hK : K.IsCovariant (inducedAction (G := G)) inducedAction) :
    (M.toChannel.comp K).IsCovariant inducedAction ρ :=
  UnitalPositiveLinearMap.IsCovariant.comp hM hK

/-- Relabeling the outcomes of a covariant measurement along an equivariant map gives a
covariant measurement. -/
lemma IsCovariant.mapOutcome {ρ : G →* Symmetry E} {N : Measurement Ω' E} (hN : N.IsCovariant ρ)
    (g : Ω' → Ω) (hg : Measurable g) (hequiv : ∀ (σ : G) x, g (σ • x) = σ • g x) :
    (N.mapOutcome g hg).IsCovariant ρ :=
  hN.comp (comap_isCovariant g hg hequiv)

/-- The first marginal of a covariant joint measurement, for the diagonal action on the product
of outcome spaces, is covariant. -/
lemma IsCovariant.marginal {ρ : G →* Symmetry E} {J : Measurement (Ω × Ω') E}
    (hJ : J.IsCovariant ρ) :
    (J.mapOutcome Prod.fst measurable_fst).IsCovariant ρ :=
  hJ.mapOutcome _ _ fun _ _ => rfl

end Measurement

end ProbabilisticTheory
