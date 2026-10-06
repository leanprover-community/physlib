/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.State.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.Normed.Module.WeakDual

/-!

# W⋆-algebras and normal states

W⋆-algebras with a chosen predual, their weak-⋆ topology, and normal states.

## i. Overview

A W⋆-algebra is a C⋆-algebra that is the dual of a Banach space, its predual. Mathlib's
`WStarAlgebra` only asserts that a predual exists. The weak-⋆ topology depends on the predual, so
`WStarAlgebraStructure` fixes one together with the isometric identification of `A` with its dual.
The weak-⋆ topology is coarser than the norm topology. A normal state is a state that is continuous
for the weak-⋆ topology.

## ii. Key results

- `WStarAlgebraStructure` : a C⋆-algebra with a chosen predual.
- `WStarAlgebraStructure.weakStarTopology` : the weak-⋆ topology.
- `WStarAlgebraStructure.norm_le_weakStarTopology` : the weak-⋆ topology is coarser than the norm
  topology.
- `NormalState` : a weak-⋆ continuous state.

## iii. Table of contents

- A. W⋆-algebras
- B. The predual pairing
- C. Normal states

## iv. References

* None.

-/

@[expose] public section

noncomputable section

namespace ProbabilisticTheory

open scoped ComplexOrder Topology
open TopologicalSpace
open Filter

/-! ## A. W⋆-algebras -/

/-- **A W⋆-algebra**: a C⋆-algebra with a chosen predual and an isometric identification of the
algebra with the dual of its predual. -/
class WStarAlgebraStructure (A : Type*) extends CStarAlgebra A, PartialOrder A, StarOrderedRing A
    where
  /-- The predual: a Banach space `E` with `A ≃ₗᵢ[ℂ] StrongDual ℂ E` isometrically. -/
  Predual : Type*
  predualNormedAddCommGroup : NormedAddCommGroup Predual
  predualNormedSpace : NormedSpace ℂ Predual
  predualCompleteSpace : CompleteSpace Predual
  /-- The defining isometric identification `A ≃ₗᵢ[ℂ] StrongDual ℂ (Predual A)`, `a ↦ (ξ ↦
  ⟨a, ξ⟩)` for the duality pairing `A` inherits from being `Predual A`'s dual. -/
  toDual : A ≃ₗᵢ[ℂ] StrongDual ℂ Predual

attribute [instance_reducible] WStarAlgebraStructure.predualNormedAddCommGroup
  WStarAlgebraStructure.predualNormedSpace

attribute [instance] WStarAlgebraStructure.predualNormedAddCommGroup
  WStarAlgebraStructure.predualNormedSpace WStarAlgebraStructure.predualCompleteSpace

namespace WStarAlgebraStructure

variable (A : Type*) [WStarAlgebraStructure A]

/-- **The weak-⋆ topology**, induced from the dual of the predual. States converge in it when their
values on each predual element converge. It is not an instance, since `A` already carries its norm
topology. -/
@[instance_reducible]
def weakStarTopology : TopologicalSpace A :=
  TopologicalSpace.induced (fun a => StrongDual.toWeakDual (toDual a)) inferInstance

/-- **The weak-⋆ topology is coarser than the norm topology.** -/
lemma norm_le_weakStarTopology :
    (inferInstance : TopologicalSpace A) ≤ weakStarTopology A :=
  continuous_iff_le_induced.mp
    (NormedSpace.Dual.toWeakDual_continuous.comp (toDual (A := A)).continuous)

end WStarAlgebraStructure

/-! ## B. The predual pairing -/

namespace WStarAlgebraStructure

variable {A : Type*} [WStarAlgebraStructure A]

/-- The continuous functional on `A` given by a predual element. -/
def predualPairing (ξ : WStarAlgebraStructure.Predual A) : A →L[ℂ] ℂ :=
  (ContinuousLinearMap.apply ℂ ℂ ξ).comp
    ((toDual (A := A)).toLinearIsometry.toContinuousLinearMap)

@[simp]
lemma predualPairing_apply (ξ : WStarAlgebraStructure.Predual A) (a : A) :
    predualPairing ξ a = toDual a ξ := rfl

lemma norm_predualPairing_apply (ξ : WStarAlgebraStructure.Predual A) (a : A) :
    ‖predualPairing ξ a‖ ≤ ‖a‖ * ‖ξ‖ := by
  have h := ContinuousLinearMap.le_opNorm (toDual a) ξ
  simpa [predualPairing] using h

/-- The functional of a predual element is weak-⋆ continuous. -/
lemma predualPairing_weakStar_continuous (ξ : WStarAlgebraStructure.Predual A) :
    Continuous[WStarAlgebraStructure.weakStarTopology A, inferInstance]
      (predualPairing ξ) := by
  change Continuous[TopologicalSpace.induced
      (fun a => StrongDual.toWeakDual (toDual a)) inferInstance, inferInstance]
      (fun a => (StrongDual.toWeakDual (toDual a)) ξ)
  have hmap : Continuous[TopologicalSpace.induced
      (fun a => StrongDual.toWeakDual (toDual a)) inferInstance, inferInstance]
      (fun a => StrongDual.toWeakDual (toDual a)) :=
    (continuous_induced_dom (f := fun a : A =>
      StrongDual.toWeakDual (toDual a)))
  have heval : Continuous[
      (inferInstance : TopologicalSpace (WeakDual ℂ (WStarAlgebraStructure.Predual A))),
        inferInstance]
      (fun z : WeakDual ℂ (WStarAlgebraStructure.Predual A) => z ξ) :=
    WeakBilin.eval_continuous _ _
  exact @Continuous.comp A (WeakDual ℂ (WStarAlgebraStructure.Predual A)) ℂ
    (TopologicalSpace.induced (fun a => StrongDual.toWeakDual (toDual a)) inferInstance)
    inferInstance inferInstance _ _ heval hmap

/-- Predual elements separate the points of a W⋆-algebra. -/
lemma ext_of_forall_predualPairing_eq {a b : A}
    (h : ∀ ξ : WStarAlgebraStructure.Predual A, predualPairing ξ a = predualPairing ξ b) :
    a = b := by
  apply (toDual (A := A)).injective
  ext ξ
  exact h ξ

/-! Weak-⋆ convergence is convergence of all predual pairings, for filters. -/

lemma tendsto_weakStar_iff_forall_predualPairing_tendsto
    {α : Type*} {l : Filter α} {f : α → A} {a : A} :
    Tendsto f l (@nhds A (WStarAlgebraStructure.weakStarTopology A) a) ↔
      ∀ ξ : WStarAlgebraStructure.Predual A,
        Tendsto (fun i => predualPairing ξ (f i)) l
          (𝓝 (predualPairing ξ a)) := by
  change Tendsto f l (@nhds A
      (TopologicalSpace.induced
        (fun b => StrongDual.toWeakDual (toDual b)) inferInstance) a) ↔ _
  rw [nhds_induced, Filter.tendsto_comap_iff]
  change Tendsto (fun i => StrongDual.toWeakDual (toDual (f i))) l
      (𝓝 (StrongDual.toWeakDual (toDual a))) ↔
    ∀ ξ : WStarAlgebraStructure.Predual A,
      Tendsto (fun i => (toDual (f i)) ξ) l (𝓝 ((toDual a) ξ))
  exact tendsto_iff_forall_eval_tendsto_topDualPairing
    (𝕜 := ℂ) (E := WStarAlgebraStructure.Predual A) (l := l)
    (f := fun i => StrongDual.toWeakDual (toDual (f i)))
    (x := StrongDual.toWeakDual (toDual a))

end WStarAlgebraStructure

/-! ## C. Normal states -/

/-- A state that is continuous for the weak-* topology of the chosen predual. -/
structure NormalState (A : Type*) [WStarAlgebraStructure A] where
  /-- The underlying state. -/
  toState : 𝓢[ℂ, A]
  /-- The state is continuous for the chosen weak-* topology. -/
  weakStar_continuous :
    Continuous[WStarAlgebraStructure.weakStarTopology A, inferInstance] (⇑toState : A → ℂ)

namespace NormalState

variable {A : Type*} [WStarAlgebraStructure A]

noncomputable instance : CoeFun (NormalState A) (fun _ => A → ℂ) where
  coe ω := ω.toState

@[simp, nolint synTaut]
lemma toState_apply (ω : NormalState A) (a : A) : ω.toState a = ω a := rfl

/-- Weak-* continuity implies ordinary norm continuity because the weak-* topology is coarser. -/
lemma continuous (ω : NormalState A) : Continuous (ω : A → ℂ) :=
  continuous_le_dom (WStarAlgebraStructure.norm_le_weakStarTopology A) ω.weakStar_continuous

end NormalState

end ProbabilisticTheory
