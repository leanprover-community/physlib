/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.State.Separation
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# The state space

## i. Overview

A state is a normalized positive functional: it gives the certain outcome `1` the value `1` and
every positive observable a nonnegative value. So the states form a subset `stateSpace E` of the
dual of `E`. This file studies it with the weak-star topology, the topology of `WeakDual ℝ E`.

Two states are close in the weak-star topology when they predict nearly the same expectation value
for every observable, one observable at a time. In this topology the state space is compact, by
the Banach–Alaoglu theorem, and metrizable when `E` is separable.

On `𝓢[ℝ, E]` itself the states carry the finer state metric.

## ii. Key results

- `stateSpace E` is the set of states in the weak dual of `E`.
- `StateSpace.toState` and `StateSpace.ofState` pass between points of `stateSpace E` and states.
- `StateSpace.tendsto_iff_forall_apply_tendsto` proves that weak-star convergence is convergence of
  every expectation value.
- `isCompact_stateSpace` proves that the state space is weak-star compact.
- `convex_stateSpace` proves that the state space is convex.
- `StateSpace.isPure_iff_mem_extremePoints` proves that the pure states are its extreme points.

## iii. Table of contents

- A. States as continuous functionals
- B. The state space in the weak dual
- C. Pointwise convergence
- D. Compactness
- E. Convexity and pure states

-/

@[expose] public section

namespace ProbabilisticTheory

open ArchimedeanOrderUnitSpace MeasureTheory Filter Topology

variable {E : Type*} [ArchimedeanOrderUnitSpace E]

/-!

## A. States as continuous functionals

-/

namespace UnitalPositiveLinearMap

/-- A state as a continuous linear functional for the order-unit norm. -/
noncomputable def toStrongDual (ω : 𝓢[ℝ, E]) : StrongDual ℝ E :=
  ω.toLinearMap.mkContinuous 1 fun A => by
    rw [one_mul]
    exact ω.abs_apply_le_orderUnitNorm A

@[simp]
lemma toStrongDual_apply (ω : 𝓢[ℝ, E]) (A : E) : ω.toStrongDual A = ω A := rfl

lemma toStrongDual_injective : Function.Injective (toStrongDual : 𝓢[ℝ, E] → StrongDual ℝ E) :=
  fun _ _ h => ext fun A => DFunLike.congr_fun h A

lemma norm_toStrongDual_le (ω : 𝓢[ℝ, E]) : ‖ω.toStrongDual‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Every state has norm `1`. -/
@[simp]
lemma norm_toStrongDual [Nontrivial E] (ω : 𝓢[ℝ, E]) : ‖ω.toStrongDual‖ = 1 := by
  refine le_antisymm (norm_toStrongDual_le ω) ?_
  have h := ω.toStrongDual.le_opNorm 1
  rwa [toStrongDual_apply, map_one, norm_one, show ‖(1 : E)‖ = 1 from orderUnitNorm_one,
    mul_one] at h

lemma toStrongDual_mix (ω φ : 𝓢[ℝ, E]) (t : unitInterval) :
    (mix ω φ t).toStrongDual = (t : ℝ) • ω.toStrongDual + (1 - (t : ℝ)) • φ.toStrongDual := by
  ext A
  simp

end UnitalPositiveLinearMap

/-!

## B. The state space in the weak dual

-/

variable (E) in
/-- The state space: the functionals in the weak dual sending `1` to `1` and positive observables
to nonnegative numbers. -/
def stateSpace : Set (WeakDual ℝ E) := {f | f 1 = 1 ∧ ∀ A : E, 0 ≤ A → 0 ≤ f A}

namespace StateSpace

/-- The state given by a point of the state space. -/
noncomputable def toState (ω : stateSpace E) : 𝓢[ℝ, E] :=
  .ofLinearMap (WeakDual.toStrongDual ω.1).toLinearMap ω.2.2 ω.2.1

/-- A state, as a point of the state space. -/
noncomputable def ofState (ω : 𝓢[ℝ, E]) : stateSpace E :=
  ⟨StrongDual.toWeakDual ω.toStrongDual, by simp, fun _ hA => map_nonneg ω hA⟩

@[simp] lemma coe_apply (ω : stateSpace E) (A : E) : (ω : WeakDual ℝ E) A = toState ω A := rfl

@[simp] lemma toState_ofState (ω : 𝓢[ℝ, E]) : toState (ofState ω) = ω := rfl

@[simp] lemma ofState_toState (ω : stateSpace E) : ofState (toState ω) = ω := rfl

/-- Points of the state space are states. -/
noncomputable def equivState : stateSpace E ≃ 𝓢[ℝ, E] :=
  ⟨toState, ofState, ofState_toState, toState_ofState⟩

lemma toState_injective : Function.Injective (toState (E := E)) := equivState.injective

/-- The Borel sets of the weak-star topology. -/
noncomputable instance : MeasurableSpace (stateSpace E) := borel _

instance : BorelSpace (stateSpace E) := ⟨rfl⟩

/-!

## C. Pointwise convergence

-/

/-- Each expectation value depends continuously on the state. -/
@[fun_prop]
lemma continuous_apply (A : E) : Continuous fun ω : stateSpace E => toState ω A :=
  (WeakDual.eval_continuous A).comp continuous_subtype_val

/-- States converge weak-star exactly when every expectation value converges. -/
lemma tendsto_iff_forall_apply_tendsto {ι : Type*} {f : ι → stateSpace E} {l : Filter ι}
    {ω : stateSpace E} :
    Tendsto f l (𝓝 ω) ↔ ∀ A : E, Tendsto (fun i => toState (f i) A) l (𝓝 (toState ω A)) := by
  rw [Topology.IsEmbedding.subtypeVal.tendsto_nhds_iff,
    tendsto_iff_forall_eval_tendsto_topDualPairing]
  rfl

end StateSpace

/-!

## D. Compactness

-/

lemma isClosed_stateSpace : IsClosed (stateSpace E) := by
  have h : stateSpace E = {f | f 1 = 1} ∩ ⋂ A : E, ⋂ _ : 0 ≤ A, {f | 0 ≤ f A} := by
    ext; simp [stateSpace]
  rw [h]
  exact (isClosed_eq (WeakDual.eval_continuous _) continuous_const).inter <|
    isClosed_iInter fun A => isClosed_iInter fun _ =>
      isClosed_le continuous_const (WeakDual.eval_continuous _)

lemma stateSpace_subset_closedBall :
    stateSpace E ⊆ WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 1 := fun f hf =>
  mem_closedBall_zero_iff.2 (StateSpace.toState ⟨f, hf⟩).norm_toStrongDual_le

/-- **Banach–Alaoglu** for states: the state space is weak-star compact. -/
lemma isCompact_stateSpace : IsCompact (stateSpace E) :=
  (WeakDual.isCompact_closedBall 0 1).of_isClosed_subset isClosed_stateSpace
    stateSpace_subset_closedBall

instance : CompactSpace (stateSpace E) := isCompact_iff_compactSpace.1 isCompact_stateSpace

/-- For separable `E`, the state space is metrizable. -/
instance [TopologicalSpace.SeparableSpace E] : TopologicalSpace.MetrizableSpace (stateSpace E) :=
  WeakDual.metrizable_of_isCompact ℝ E _ isCompact_stateSpace

/-!

## E. Convexity and pure states

-/

/-- A mixture of states is a state. -/
lemma convex_stateSpace : Convex ℝ (stateSpace E) := fun f hf g hg a b ha hb hab =>
  ⟨show a * f 1 + b * g 1 = 1 by rw [hf.1, hg.1, mul_one, mul_one, hab],
    fun A hA => show 0 ≤ a * f A + b * g A from
      add_nonneg (mul_nonneg ha (hf.2 A hA)) (mul_nonneg hb (hg.2 A hA))⟩

namespace StateSpace

lemma range_ofState : Set.range (fun ω : 𝓢[ℝ, E] => (ofState ω : WeakDual ℝ E)) = stateSpace E :=
  Set.ext fun f => ⟨by rintro ⟨ω, rfl⟩; exact (ofState ω).2, fun hf => ⟨toState ⟨f, hf⟩, rfl⟩⟩

/-- A state is pure exactly when it is an extreme point of the state space. -/
lemma isPure_iff_mem_extremePoints (ω : stateSpace E) :
    (toState ω).IsPure ↔ (ω : WeakDual ℝ E) ∈ (stateSpace E).extremePoints ℝ := by
  have := UnitalPositiveLinearMap.isPure_iff_mem_extremePoints
    (F := fun ω : 𝓢[ℝ, E] => (ofState ω : WeakDual ℝ E))
    (fun φ ψ h => (toState_ofState φ).symm.trans ((congrArg toState (Subtype.ext h)).trans
      (toState_ofState ψ))) (fun _ _ _ => DFunLike.ext _ _ fun _ => by simp; rfl) (toState ω)
  rwa [range_ofState] at this

end StateSpace

end ProbabilisticTheory
