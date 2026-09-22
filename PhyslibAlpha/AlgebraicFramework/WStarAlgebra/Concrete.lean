/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.WStarAlgebra.Basic
public import PhyslibAlpha.AlgebraicFramework.WStarAlgebra.RankOnePairing

/-!
# The concrete `WStarAlgebraStructure (H →L[ℂ] H)` instance

Ported from `unbounded-alpha-public`'s `WStarAlgebra/InfiniteDim.lean`. This module is the
integration point for the concrete predual construction of `Basic.lean`'s module docstring: the
trace-class operators `𝒮₁(H)` (`HilbertSpace/TraceClass/Banach.lean`) form a complete normed space,
the trace pairing `A ↦ (ρ ↦ Tr(Aρ))` is a linear isometry
(`WStarAlgebra/TracePairingNorm.lean`), and Hilbert–Schmidt truncation proves that the pairing is
onto (`WStarAlgebra/TracePairingSurjectivity.lean`). This file only packages that proved equivalence
as the `WStarAlgebraStructure` instance. No capability class or unproved surjectivity certificate
is used here, and the construction applies uniformly whether `H` is finite- or
infinite-dimensional.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace TraceClass

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The concrete trace pairing is surjective onto the strong dual of the trace class. -/
theorem tracePairing_surjective :
    Function.Surjective (⇑(tracePairingLinearIsometry (H := H))) :=
  tracePairing_surjective_concrete

/-- The isometric identification of `H →L[ℂ] H` with the strong dual of its trace class. -/
def tracePairingEquiv : (H →L[ℂ] H) ≃ₗᵢ[ℂ] StrongDual ℂ (TraceClass H) :=
  LinearIsometryEquiv.ofSurjective tracePairingLinearIsometry tracePairing_surjective

@[simp] theorem tracePairingEquiv_apply (A : H →L[ℂ] H) :
    tracePairingEquiv A = tracePairing A := rfl

end TraceClass

/-! ## The `WStarAlgebraStructure (H →L[ℂ] H)` instance -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **`H →L[ℂ] H` with its trace class as predual.** The genuinely concrete realization promised by
`WStarAlgebra/Basic.lean`'s module docstring: `A := H →L[ℂ] H`, `Predual A := TraceClass H`, and
`toDual` the trace pairing `a ↦ (ρ ↦ Tr(aρ))`. -/
noncomputable instance instWStarAlgebraStructureContinuousLinearMap :
    WStarAlgebraStructure (H →L[ℂ] H) where
  Predual := TraceClass H
  predualNormedAddCommGroup := TraceClass.instNormedAddCommGroup
  predualNormedSpace := TraceClass.instNormedSpace
  predualCompleteSpace := TraceClass.instCompleteSpace
  toDual := TraceClass.tracePairingEquiv
