/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Mathematics.Convex.Choquet.ExtremePointDecomposition
public import PhyslibAlpha.ProbabilisticTheory.Classical.UniqueDecomposition
public import PhyslibAlpha.ProbabilisticTheory.State.Barycenter

/-!
# Classical systems with separable observables

Choquet–Meyer: with separable observables, classical exactly when ensembles refine.

## i. Overview

Most systems in physics can be described by countably many observables: the observables are
separable. For such systems every state is a mixture of pure states. This is Choquet's theorem.

The idea is simple. The states form a compact convex set. Its corners are the pure states.
A state that is not pure is the midpoint of two other states, so its weight can be pushed
outwards to them. Pushing weight outwards as far as possible leaves a probability measure that
lives on the pure states. Countably many observables are needed to make this limit exist.

Combined with the uniqueness theorem, this gives a clean criterion. A system with separable
observables is classical exactly when its ensembles refine.

## ii. Key results

- `UnitalPositiveLinearMap.exists_pure_representingMeasure` proves that every state is the
  barycenter of a probability measure living on the pure states.
- `PureState.hasPureDecomposition_of_separable` proves that every state has a pure
  decomposition.
- `isSimplexStateSpace_iff_ensemblesRefine` proves that the system is classical exactly when
  ensembles refine. This is the **Choquet–Meyer theorem**.

## iii. Table of contents

- A. A dense sequence of observables separates states
- B. Every state is a mixture of pure states
- C. Pure decompositions
- D. Classical systems are those whose ensembles refine

## iv. References

- G. Choquet and P.-A. Meyer, *Existence et unicité des représentations intégrales dans les
  convexes compacts quelconques*, Ann. Inst. Fourier 13 (1963), 139–154.

-/

@[expose] public section

namespace ProbabilisticTheory

open MeasureTheory ArchimedeanOrderUnitSpace Set StateSpace

variable {E : Type*} [ArchimedeanOrderUnitSpace E]

/-!

## A. A dense sequence of observables separates states

-/

variable [TopologicalSpace.SeparableSpace E]

namespace StateSpace

/-- The expectation value of the `n`-th observable of a dense sequence, as a continuous linear
functional on the weak dual. -/
noncomputable def denseEval (n : ℕ) : WeakDual ℝ E →L[ℝ] ℝ :=
  WeakBilin.eval _ (TopologicalSpace.denseSeq E n)

/-- The expectation values of a dense sequence of observables separate states. -/
lemma denseEval_injective (x y : stateSpace E)
    (h : ∀ n, denseEval n (x : WeakDual ℝ E) = denseEval n (y : WeakDual ℝ E)) :
    x = y :=
  Subtype.ext <| DFunLike.coe_injective <| (TopologicalSpace.denseRange_denseSeq E).equalizer
    (WeakDual.toStrongDual x.1).continuous (WeakDual.toStrongDual y.1).continuous (funext h)

end StateSpace

/-!

## B. Every state is a mixture of pure states

-/

namespace UnitalPositiveLinearMap

/-- **Choquet representation of states.** Every state is the barycenter of a probability measure
living on the pure states. -/
lemma exists_pure_representingMeasure (ω : 𝓢[ℝ, E]) :
    ∃ μ : ProbabilityMeasure (stateSpace E),
      barycenter μ = ω ∧ ∀ᵐ φ : stateSpace E ∂(μ : Measure _), (toState φ).IsPure := by
  obtain ⟨μ, hrep, hext⟩ := Choquet.exists_extreme_representingMeasure convex_stateSpace denseEval
    denseEval_injective (ofState ω)
  exact ⟨μ, ext fun A => (hrep (WeakBilin.eval _ A)).symm,
    hext.mono fun φ hφ => (StateSpace.isPure_iff_mem_extremePoints φ).2 hφ⟩

end UnitalPositiveLinearMap

/-!

## C. Pure decompositions

-/

namespace PureState

lemma measurableSet_setOf_isPure : MeasurableSet {ω : stateSpace E | (toState ω).IsPure} := by
  simpa only [StateSpace.isPure_iff_mem_extremePoints] using
    Choquet.measurableSet_extremePoints (convex_stateSpace (E := E))

lemma measurableEmbedding_val : MeasurableEmbedding (Subtype.val : PureState E → stateSpace E) :=
  MeasurableEmbedding.subtype_coe measurableSet_setOf_isPure

/-- A probability measure on the state space living on the pure states, restricted to them. -/
lemma map_comap_val_eq {μ : Measure (stateSpace E)}
    (hμ : ∀ᵐ φ ∂μ, (toState φ).IsPure) :
    (μ.comap (Subtype.val : PureState E → stateSpace E)).map Subtype.val = μ := by
  rw [measurableEmbedding_val.map_comap, Subtype.range_coe_subtype]
  exact Measure.restrict_eq_self_of_ae_mem hμ

lemma isProbabilityMeasure_comap_val {μ : Measure (stateSpace E)} [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ φ ∂μ, (toState φ).IsPure) :
    IsProbabilityMeasure (μ.comap (Subtype.val : PureState E → stateSpace E)) := by
  have := congrArg (fun ν : Measure (stateSpace E) => ν univ) (map_comap_val_eq hμ)
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ, preimage_univ] at this
  exact ⟨this.trans measure_univ⟩

/-- With separable observables, every state decomposes into pure states. -/
lemma hasPureDecomposition_of_separable (ω : 𝓢[ℝ, E]) : ω.HasPureDecomposition := by
  obtain ⟨μ, hbar, hpure⟩ := UnitalPositiveLinearMap.exists_pure_representingMeasure ω
  have hprob := isProbabilityMeasure_comap_val hpure
  have hinner : ((μ : Measure (stateSpace E)).comap
      (Subtype.val : PureState E → stateSpace E)).InnerRegular :=
    Measure.InnerRegular.comap_subtype measurableSet_setOf_isPure
  refine ⟨_, Measure.Regular.of_innerRegular, hprob, fun f => ?_⟩
  refine (measurableEmbedding_val.integral_map fun φ : stateSpace E => toState φ f).symm.trans ?_
  rw [map_comap_val_eq hpure, ← hbar]
  rfl

end PureState

/-!

## D. Classical systems are those whose ensembles refine

-/

/-- **Choquet–Meyer**: for separable observables, the state space is a simplex exactly when
ensembles refine. -/
lemma isSimplexStateSpace_iff_ensemblesRefine : IsSimplexStateSpace E ↔ EnsemblesRefine E :=
  ⟨IsSimplexStateSpace.ensemblesRefine, fun hE ω =>
    hE.hasUniquePureDecomposition (PureState.hasPureDecomposition_of_separable ω)⟩

end ProbabilisticTheory
