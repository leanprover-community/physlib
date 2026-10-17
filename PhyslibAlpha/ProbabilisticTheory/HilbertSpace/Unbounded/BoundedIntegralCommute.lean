/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.SpectralIntegral.Construction
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.BoundedIntegralAlgebra

/-!

# Operators commuting with a spectral measure

An operator commuting with every spectral projection commutes with every bounded spectral integral.

## i. Overview

The matrix-coefficient measures of a spectral measure have finite variation on every spectral
variable space, not only on the real line. If `T` commutes with every spectral projection, the
matrix-coefficient measure of `(T x, y)` agrees with that of `(x, T⋆ y)`. Integrating a bounded
measurable function against these measures shows that `T` commutes with the integral.

## ii. Key results

- `WOTSpectralMeasure.scalarMeasure_isFiniteVariation'` : matrix-coefficient measures have finite
  variation.
- `WOTSpectralMeasure.boundedIntegral_commute` : an operator commuting with the spectral
  projections commutes with every bounded integral.

## iii. Table of contents

- A. Finite variation of the matrix-coefficient measures
- B. Commutation with the bounded integrals

## iv. References

* None.

-/

@[expose] public section

noncomputable section

namespace ProbabilisticTheory

open MeasureTheory Set Topology
open scoped ComplexOrder InnerProductSpace

namespace QuantumMechanics

namespace WOTSpectralMeasure

variable {α : Type*} [MeasurableSpace α]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (μS : WOTSpectralMeasure α H)

/-! ## A. Finite variation of the matrix-coefficient measures -/

lemma scalarMeasure_inner_projection' (x y : H) (S : Set α) :
    ⟪y, μS S x⟫_ℂ = ⟪μS S y, μS S x⟫_ℂ := by
  let p : H →L[ℂ] H := ContinuousLinearMapWOT.toCLM (μS S)
  have hmul : p * p = p :=
    congrArg ContinuousLinearMapWOT.toCLM (μS.isStarProjection S).isIdempotentElem
  have hstar : ContinuousLinearMap.adjoint p = p := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact congrArg ContinuousLinearMapWOT.toCLM (μS.isStarProjection S).isSelfAdjoint
  change ⟪y, p x⟫_ℂ = ⟪p y, p x⟫_ℂ
  calc
    ⟪y, p x⟫_ℂ = ⟪ContinuousLinearMap.adjoint p y, x⟫_ℂ :=
      (ContinuousLinearMap.adjoint_inner_left p x y).symm
    _ = ⟪p y, x⟫_ℂ := by rw [hstar]
    _ = ⟪p y, p x⟫_ℂ := by
      have h := ContinuousLinearMap.adjoint_inner_right p (p y) x
      rw [hstar] at h
      have hpy : p (p y) = p y := congrArg (fun q : H →L[ℂ] H => q y) hmul
      rw [hpy] at h
      exact h.symm

lemma scalarMeasure_variation_le_diagonal_add' (x y : H) :
    (μS.scalarMeasure x y).variation ≤ μS.diagonalMeasure x + μS.diagonalMeasure y := by
  apply MeasureTheory.VectorMeasure.variation_le_of_forall_enorm_le
  intro S hS
  rw [μS.scalarMeasure_apply x y S]
  rw [← ofReal_norm]
  rw [MeasureTheory.Measure.add_apply _ _ S, μS.diagonalMeasure_apply_eq_norm_sq x S hS,
    μS.diagonalMeasure_apply_eq_norm_sq y S hS]
  rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hinner := norm_inner_le_norm (𝕜 := ℂ) (μS S y) (μS S x)
  have hproj := scalarMeasure_inner_projection' μS x y S
  rw [hproj]
  nlinarith [sq_nonneg ‖μS S y‖, sq_nonneg ‖μS S x‖]

/-- The matrix-coefficient measures of a weak spectral measure have finite variation. -/
lemma scalarMeasure_isFiniteVariation' (x y : H) :
    IsFiniteMeasure (μS.scalarMeasure x y).variation :=
  MeasureTheory.isFiniteMeasure_of_le (μS.diagonalMeasure x + μS.diagonalMeasure y)
    (scalarMeasure_variation_le_diagonal_add' μS x y)

/-! ## B. Commutation with the bounded integrals -/

/-- An operator commuting with every spectral projection commutes with every bounded integral
against the spectral measure. -/
lemma boundedIntegral_commute [Nonempty α] {T : H →L[ℂ] H}
    (hT : ∀ S, μS S * ContinuousLinearMapWOT.ofCLM T = ContinuousLinearMapWOT.ofCLM T * μS S)
    {f : α → ℂ} (hf : Measurable f) (hbf : ∃ C, ∀ z, ‖f z‖ ≤ C) :
    ContinuousLinearMapWOT.toCLM (boundedIntegral μS f hf hbf) * T =
      T * ContinuousLinearMapWOT.toCLM (boundedIntegral μS f hf hbf) := by
  ext x
  apply ext_inner_left ℂ
  intro y
  have hmeas :
      (μS.scalarMeasure (T x) y) = (μS.scalarMeasure x (ContinuousLinearMap.adjoint T y)) := by
    apply VectorMeasure.ext
    intro S _
    rw [scalarMeasure_apply, scalarMeasure_apply]
    have h := congrArg (fun A : H →WOT[ℂ] H => ContinuousLinearMapWOT.toCLM A x) (hT S)
    have h' : ContinuousLinearMapWOT.toCLM (μS S) (T x) =
        T (ContinuousLinearMapWOT.toCLM (μS S) x) := by
      simpa using h
    change ⟪y, ContinuousLinearMapWOT.toCLM (μS S) (T x)⟫_ℂ = _
    rw [h']
    exact (ContinuousLinearMap.adjoint_inner_left T _ y).symm
  have h1 := boundedIntegral_inner μS hf hbf (T x) y (scalarMeasure_isFiniteVariation' μS _ _)
  have h2 := boundedIntegral_inner μS hf hbf x (ContinuousLinearMap.adjoint T y)
    (scalarMeasure_isFiniteVariation' μS _ _)
  change ⟪y, ContinuousLinearMapWOT.toCLM (boundedIntegral μS f hf hbf) (T x)⟫_ℂ =
    ⟪y, T (ContinuousLinearMapWOT.toCLM (boundedIntegral μS f hf hbf) x)⟫_ℂ
  rw [← ContinuousLinearMap.adjoint_inner_left T _ y]
  rw [show ContinuousLinearMapWOT.toCLM (boundedIntegral μS f hf hbf) (T x) =
    boundedIntegral μS f hf hbf (T x) from rfl, h1, hmeas, ← h2]
  rfl

end WOTSpectralMeasure

end QuantumMechanics

end ProbabilisticTheory

end
