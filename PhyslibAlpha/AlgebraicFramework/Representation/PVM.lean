/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.OrderUnit.Effect.EffectValuedMeasure
public import PhyslibAlpha.AlgebraicFramework.CStarAlgebra.SharpEffect

/-!

# POVMs and PVMs

`EffectValuedMeasure Ω E` already *is* a positive-operator-valued measure, once `E` is the
self-adjoint part of an operator algebra: `POVM` is just the physics-literature name for it, kept
here for discoverability.

A projection-valued measure is a POVM every one of whose effects is sharp (`Effect.IsSharp`):
the general (order-unit) notion of a projection. Both endpoints `∅` and the whole space are
automatically sharp for *every* POVM, since the impossible and certain effects `0` and `1` are
always sharp (`Effect.isSharp_zero`, `Effect.isSharp_one`) — `IsPVM` only has bite on the
measurable sets strictly between them.

A genuine operator-algebraic projection-valued measure — every assigned effect an idempotent
self-adjoint operator — is a `PVM` in this abstract sense (`POVM.isPVM_of_forall_isIdempotentElem`),
via `IsIdempotentElem.isSharp`: this is the payoff of building the general framework on top of the
self-adjoint part of a C⋆-algebra (`StarAlgebra/OrderUnit.lean`).

## Main definitions

- `POVM`
- `POVM.IsPVM`
- `PVM`
- `POVM.isPVM_of_forall_isIdempotentElem`

-/

@[expose] public section

/-- A positive-operator-valued measure: the physics name for `EffectValuedMeasure`. -/
abbrev POVM (Ω E : Type*) [MeasurableSpace Ω] [AddCommGroup E] [PartialOrder E]
    [IsOrderedAddMonoid E] [One E] [IsOrderUnit E] := EffectValuedMeasure Ω E

variable {Ω E : Type*} [MeasurableSpace Ω] [AddCommGroup E] [PartialOrder E]
  [IsOrderedAddMonoid E] [Module ℝ E] [PosSMulMono ℝ E] [One E] [IsOrderUnit E]

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

/-- A POVM valued in the self-adjoint part of a C⋆-algebra, all of whose effects are genuine
(idempotent) projections, is a PVM: `IsIdempotentElem.isSharp` upgrades an operator-theoretic
projection to the abstract, order-unit-level notion of sharpness. -/
theorem POVM.isPVM_of_forall_isIdempotentElem {Ω : Type*} [MeasurableSpace Ω]
    {μ : POVM Ω (selfAdjoint A)}
    (h : ∀ s hs, IsIdempotentElem (((μ s hs : Effect (selfAdjoint A)) : selfAdjoint A) : A)) :
    μ.IsPVM :=
  fun s hs => (h s hs).isSharp

end CStarAlgebra

/-- A projection-valued measure: a POVM every one of whose effects is a genuine projection
(sharp effect). -/
def PVM (Ω E : Type*) [MeasurableSpace Ω] [AddCommGroup E] [PartialOrder E]
    [IsOrderedAddMonoid E] [Module ℝ E] [One E] [IsOrderUnit E] :=
  {μ : POVM Ω E // μ.IsPVM}

namespace PVM

/-- A PVM, viewed as a POVM, forgetting the sharpness of its effects. -/
instance : CoeOut (PVM Ω E) (POVM Ω E) := ⟨Subtype.val⟩

omit [PosSMulMono ℝ E] in
@[ext]
lemma ext {π ρ : PVM Ω E} (h : ∀ s hs, (π : POVM Ω E) s hs = (ρ : POVM Ω E) s hs) : π = ρ :=
  Subtype.ext (EffectValuedMeasure.ext h)

omit [PosSMulMono ℝ E] in
/-- Every effect of a PVM is sharp: unfolding what it means to be one. -/
lemma isSharp_apply (π : PVM Ω E) (s : Set Ω) (hs : MeasurableSet s) :
    Effect.IsSharp ((π : POVM Ω E) s hs) :=
  π.2 s hs

end PVM
