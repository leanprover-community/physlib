/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Measurement.EffectValuedMeasure
public import PhyslibAlpha.ProbabilisticTheory.CStarAlgebra.SharpEffect

/-!

# POVMs and PVMs

## i. Overview

For the self-adjoint part of an operator algebra, an effect-valued measure is a POVM. A PVM is a
POVM whose values are sharp effects. A POVM whose values are projections is a PVM.

## ii. Key results

- `POVM` : positive-operator-valued measures.
- `POVM.IsPVM`, `PVM` : projection-valued measures.
- `POVM.isPVM_of_forall_isIdempotentElem` : a POVM of projections is a PVM.

-/

@[expose] public section

namespace ProbabilisticTheory

/-- A positive-operator-valued measure: the physics name for `EffectValuedMeasure`. -/
abbrev POVM (Ω E : Type*) [MeasurableSpace Ω] [OrderUnitSpace E] := EffectValuedMeasure Ω E

variable {Ω E : Type*} [MeasurableSpace Ω] [OrderUnitSpace E]

namespace POVM

/-- A POVM is a PVM (projection-valued measure) when every effect it assigns is sharp. -/
def IsPVM (μ : POVM Ω E) : Prop := ∀ s hs, Effect.IsSharp (μ s hs)

/-- The impossible event is always sharp, in any POVM: it is assigned the effect `0`. -/
lemma isSharp_apply_empty (μ : POVM Ω E) : Effect.IsSharp (μ ∅ MeasurableSet.empty) :=
  μ.map_empty ▸ Effect.isSharp_zero

/-- The certain event is always sharp, in any POVM: it is assigned the effect `1`. -/
lemma isSharp_apply_univ (μ : POVM Ω E) : Effect.IsSharp (μ Set.univ MeasurableSet.univ) :=
  μ.map_univ ▸ Effect.isSharp_one

end POVM

section CStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A POVM whose values are projections is a PVM. -/
lemma POVM.isPVM_of_forall_isIdempotentElem {Ω : Type*} [MeasurableSpace Ω]
    {μ : POVM Ω (selfAdjoint A)}
    (h : ∀ s hs, IsIdempotentElem (((μ s hs : Effect (selfAdjoint A)) : selfAdjoint A) : A)) :
    μ.IsPVM :=
  fun s hs => (h s hs).isSharp

end CStarAlgebra

/-- Projection-valued measures: POVMs whose values are sharp effects. -/
def PVM (Ω E : Type*) [MeasurableSpace Ω] [OrderUnitSpace E] :=
  {μ : POVM Ω E // μ.IsPVM}

namespace PVM

/-- A PVM, viewed as a POVM, forgetting the sharpness of its effects. -/
instance : CoeOut (PVM Ω E) (POVM Ω E) := ⟨Subtype.val⟩

@[ext]
lemma ext {π ρ : PVM Ω E} (h : ∀ s hs, (π : POVM Ω E) s hs = (ρ : POVM Ω E) s hs) : π = ρ :=
  Subtype.ext (EffectValuedMeasure.ext h)

/-- Every effect of a PVM is sharp: unfolding what it means to be one. -/
lemma isSharp_apply (π : PVM Ω E) (s : Set Ω) (hs : MeasurableSet s) :
    Effect.IsSharp ((π : POVM Ω E) s hs) :=
  π.2 s hs

end PVM

end ProbabilisticTheory
