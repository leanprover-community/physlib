/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.StarHomSpec.SpectralMeasure
public import Mathlib.Analysis.CStarAlgebra.Unitary.Span
public import Mathlib.Topology.Algebra.Group.Basic

/-!

# The commutant of a representation of continuous functions

Every bounded operator commuting with the range of `Φ` commutes with its spectral measure.

## i. Overview

The spectral measure of `Φ` commutes with every unitary operator commuting with the range of `Φ`.
A bounded operator commuting with the range of `Φ` lies in the commutant of the range, a closed
⋆-subalgebra of `B(H)` and hence a C⋆-algebra, which is spanned by its unitary elements. So the
spectral measure commutes with every operator commuting with the range of `Φ`.

## ii. Key results

- `starHomSpectralMeasure_commute_of_commute` : the spectral measure of `Φ` commutes with every
  bounded operator commuting with the range of `Φ`.

## iii. Table of contents

- A. Arbitrary operators in the commutant

## iv. References

* None.

-/

@[expose] public section

noncomputable section

namespace ProbabilisticTheory

open MeasureTheory Set Topology
open scoped ComplexOrder CStarAlgebra InnerProductSpace

namespace QuantumMechanics

section StarHomCommutan

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] [CompactSpace X] (Φ : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))

/-- The commutant of the range of `Φ`, a ⋆-subalgebra of the bounded operators. -/
def starHomCommutant : StarSubalgebra ℂ (H →L[ℂ] H) :=
  StarSubalgebra.centralizer ℂ (Set.range Φ)

omit [T2Space X] [BorelSpace X] [CompactSpace X] [MeasurableSpace X] in
lemma mem_starHomCommutant_iff {T : H →L[ℂ] H} :
    T ∈ starHomCommutant Φ ↔ ∀ f : C(X, ℂ), Commute (Φ f) T := by
  rw [starHomCommutant, StarSubalgebra.mem_centralizer_iff]
  constructor
  · rintro h f
    exact (h (Φ f) ⟨f, rfl⟩).1
  · rintro h _ ⟨f, rfl⟩
    refine ⟨h f, ?_⟩
    rw [← map_star]
    exact h (star f)

instance starHomCommutant_isClosed : IsClosed (starHomCommutant Φ : Set (H →L[ℂ] H)) := by
  rw [starHomCommutant, StarSubalgebra.coe_centralizer]
  exact Set.isClosed_centralizer _

/-! ## A. Arbitrary operators in the commutant -/

/-- **The spectral operators commute with the commutant**: every bounded operator commuting with
the range of `Φ` commutes with each spectral operator of `Φ`. A bounded operator commuting with the
range is a combination of four unitary operators in the C⋆-algebra of such operators, and the
spectral operators commute with unitaries commuting with the range. -/
lemma starHomSpectralOperator_commute_of_commute {T : H →L[ℂ] H}
    (hT : ∀ f : C(X, ℂ), Commute (Φ f) T) (S : Set X) :
    starHomSpectralOperator Φ S * T = T * starHomSpectralOperator Φ S := by
  obtain ⟨u, c, hc, -⟩ := CStarAlgebra.exists_sum_four_unitary
    (⟨T, (mem_starHomCommutant_iff Φ).2 hT⟩ : starHomCommutant Φ)
  have hTsum : T = ∑ i, c i • ((u i : starHomCommutant Φ) : H →L[ℂ] H) := by
    simpa using congrArg (fun z : starHomCommutant Φ => (z : H →L[ℂ] H)) hc
  have hu : ∀ i, ((u i : starHomCommutant Φ) : H →L[ℂ] H) ∈ unitary (H →L[ℂ] H) := fun i => by
    refine ⟨?_, ?_⟩
    · exact congrArg (fun z : starHomCommutant Φ => (z : H →L[ℂ] H))
        (Unitary.star_mul_self_of_mem (u i).2)
    · exact congrArg (fun z : starHomCommutant Φ => (z : H →L[ℂ] H))
        (Unitary.mul_star_self_of_mem (u i).2)
  have hcomm : ∀ i, ∀ f : C(X, ℂ), Commute (Φ f) ((u i : starHomCommutant Φ) : H →L[ℂ] H) :=
    fun i => (mem_starHomCommutant_iff Φ).1 (u i).1.2
  have hi := fun i =>
    starHomSpectralOperator_commute_of_commute_unitary Φ (hcomm i) (hu i) S
  rw [hTsum, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by rw [mul_smul_comm, smul_mul_assoc, hi i]

/-- **The spectral measure commutes with the commutant**: every bounded operator commuting with
the range of `Φ` commutes with each spectral projection of `Φ`. -/
lemma starHomSpectralMeasure_commute_of_commute {T : H →L[ℂ] H}
    (hT : ∀ f : C(X, ℂ), Commute (Φ f) T) (S : Set X) :
    starHomSpectralMeasure Φ S * ContinuousLinearMapWOT.ofCLM T =
      ContinuousLinearMapWOT.ofCLM T * starHomSpectralMeasure Φ S := by
  rw [starHomSpectralMeasure_apply]
  show ContinuousLinearMapWOT.ofCLM (starHomSpectralOperator Φ S) *
      ContinuousLinearMapWOT.ofCLM T =
    ContinuousLinearMapWOT.ofCLM T * ContinuousLinearMapWOT.ofCLM (starHomSpectralOperator Φ S)
  rw [← ContinuousLinearMapWOT.ofCLM_mul, ← ContinuousLinearMapWOT.ofCLM_mul]
  exact congrArg ContinuousLinearMapWOT.ofCLM
    (starHomSpectralOperator_commute_of_commute Φ hT S)

end StarHomCommutan

end QuantumMechanics

end ProbabilisticTheory

end
