/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Classical.UniqueDecomposition
public import PhyslibAlpha.Mathematics.MeasureTheory.PositiveFunctionalIntegral

/-!
# Bauer simplices

## i. Overview

A Bauer simplex is a classical state space whose pure states form a closed set. The pure states
are then a compact phase space, and observables become continuous functions on it.

Closed pure states already give every state a pure decomposition. A state is a positive
functional on the observables. The M. Riesz extension theorem extends it to a positive functional
on all continuous functions on the pure states, and the Riesz–Markov–Kakutani theorem turns that
into a probability measure. Together with the uniqueness of pure decompositions, the state space
is a Bauer simplex exactly when ensembles refine and the pure states are closed.

## ii. Key results

- `PureState.hasPureDecomposition` proves that, with compact pure states, every state has a pure
  decomposition.
- `isSimplexStateSpace_iff_ensemblesRefine_of_isClosed` proves that, with closed pure states, the
  system is classical exactly when ensembles refine.
- `isBauerSimplexStateSpace_iff` proves that the state space is a Bauer simplex exactly when
  ensembles refine and the pure states are closed.

## iii. Table of contents

- A. Pure decompositions
- B. Bauer simplices

## iv. References

- E. M. Alfsen, *Compact Convex Sets and Boundary Integrals*, Springer, 1971, ch. II.4.

-/

@[expose] public section

namespace ProbabilisticTheory

open StateSpace

open MeasureTheory PureState Set

variable {E : Type*} [ArchimedeanOrderUnitSpace E]

/-!

## A. Pure decompositions

-/

/-- With closed pure states, every state decomposes into pure states. -/
lemma PureState.hasPureDecomposition [CompactSpace (PureState E)] (ω : 𝓢[ℝ, E]) :
    ω.HasPureDecomposition :=
  exists_regular_probabilityMeasure_integral_eq evalPure ω.toLinearMap
    (fun a ha => map_nonneg ω (evalPure_le_iff.1 (by rwa [map_zero]))) evalPure_one (map_one ω)

/-!

## B. Bauer simplices

-/

/-- With closed pure states, the state space is a simplex exactly when ensembles refine. -/
lemma isSimplexStateSpace_iff_ensemblesRefine_of_isClosed
    (hP : IsClosed {ω : stateSpace E | (toState ω).IsPure}) :
    IsSimplexStateSpace E ↔ EnsemblesRefine E :=
  have : CompactSpace (PureState E) := isCompact_iff_compactSpace.1 hP.isCompact
  ⟨IsSimplexStateSpace.ensemblesRefine, fun hE ω =>
    hE.hasUniquePureDecomposition (hasPureDecomposition ω)⟩

/-- **Bauer simplices**: the state space is a Bauer simplex exactly when ensembles refine and the
pure states are closed. -/
lemma isBauerSimplexStateSpace_iff : IsBauerSimplexStateSpace E ↔
    EnsemblesRefine E ∧ IsClosed {ω : stateSpace E | (toState ω).IsPure} :=
  ⟨fun h => ⟨h.1.ensemblesRefine, h.2⟩,
    fun ⟨hE, hP⟩ => ⟨(isSimplexStateSpace_iff_ensemblesRefine_of_isClosed hP).2 hE, hP⟩⟩

end ProbabilisticTheory
