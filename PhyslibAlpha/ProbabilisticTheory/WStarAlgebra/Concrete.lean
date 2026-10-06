/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.WStarAlgebra.Basic
public import PhyslibAlpha.ProbabilisticTheory.WStarAlgebra.RankOnePairing

/-!

# The bounded operators as a W⋆-algebra

The bounded operators on a Hilbert space form a W⋆-algebra with the trace class as predual.

## i. Overview

The trace pairing `A ↦ (ρ ↦ Tr (A ρ))` is an isometric isomorphism from the bounded operators on a
Hilbert space onto the dual of the trace-class operators. So the bounded operators form a W⋆-algebra
with predual the trace-class operators.

## ii. Key results

- `tracePairingEquiv` : the trace pairing as an isometric isomorphism onto the dual.
- `instWStarAlgebraStructureContinuousLinearMap` : the bounded operators with the trace-class
  operators as predual.

## iii. Table of contents

- A. The `WStarAlgebraStructure (H →L[ℂ] H)` instance

## iv. References

* None.

-/

@[expose] public section

noncomputable section

namespace ProbabilisticTheory

open scoped ComplexOrder InnerProductSpace

namespace TraceClass

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The concrete trace pairing is surjective onto the strong dual of the trace class. -/
lemma tracePairing_surjective :
    Function.Surjective (⇑(tracePairingLinearIsometry (H := H))) :=
  tracePairing_surjective_concrete

/-- The isometric identification of `H →L[ℂ] H` with the strong dual of its trace class. -/
def tracePairingEquiv : (H →L[ℂ] H) ≃ₗᵢ[ℂ] StrongDual ℂ (TraceClass H) :=
  LinearIsometryEquiv.ofSurjective tracePairingLinearIsometry tracePairing_surjective

@[simp] lemma tracePairingEquiv_apply (A : H →L[ℂ] H) :
    tracePairingEquiv A = tracePairing A := rfl

end TraceClass

/-! ## A. The `WStarAlgebraStructure (H →L[ℂ] H)` instance -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The bounded operators form a W⋆-algebra**, with predual the trace-class operators and the
trace pairing `a ↦ (ρ ↦ Tr (a ρ))`. -/
noncomputable instance instWStarAlgebraStructureContinuousLinearMap :
    WStarAlgebraStructure (H →L[ℂ] H) where
  Predual := TraceClass H
  predualNormedAddCommGroup := TraceClass.instNormedAddCommGroup
  predualNormedSpace := TraceClass.instNormedSpace
  predualCompleteSpace := TraceClass.instCompleteSpace
  toDual := TraceClass.tracePairingEquiv

end ProbabilisticTheory
