/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.ScalarMeasure

/-!

# Transporting a weak spectral measure through a Hilbert-space unitary

A Hilbert-space isometric isomorphism `u : H ≃ₗᵢ[ℂ] H'` conjugates bounded operators on `H` to
bounded operators on `H'` (`A ↦ u A u⁻¹`), and this conjugation is a `*`-algebra isomorphism
between the two weak-operator-topology spaces. Composing a `WOTSpectralMeasure α H` with it
therefore gives a `WOTSpectralMeasure α H'` — the spectral measure "carried across" the unitary.
This is the tool that lets a spectral measure constructed on one concrete representation be
transported to any unitarily equivalent one, and it also transports the associated scalar and
diagonal measures from `ScalarMeasure.lean` (`unitaryConjSpectralMeasure_scalarMeasure`,
`unitaryConjSpectralMeasure_diagonalMeasure`).

## Main definitions

- `unitaryConj` : conjugation of a single bounded WOT operator by `u`.
- `unitaryConjSpectralMeasure` : conjugation of a whole `WOTSpectralMeasure` by `u`.
- `unitaryConjSpectralMeasure_scalarMeasure`, `_diagonalMeasure` : the transported measure's
  scalar/diagonal measures, in terms of the original.

-/

@[expose] public section

noncomputable section

open scoped Topology InnerProductSpace Function
open ContinuousLinearMap ContinuousLinearMapWOT MeasureTheory Set

namespace QuantumMechanics

namespace WOTSpectralMeasure

variable {α : Type*} [MeasurableSpace α]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## A. Conjugation of a single operator -/

/-- Conjugation of a bounded operator by a Hilbert-space unitary, viewed in the WOT type. -/
@[nolint unusedArguments]
def unitaryConj {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    [CompleteSpace H'] (u : H ≃ₗᵢ[ℂ] H') (A : H →WOT[ℂ] H) : H' →WOT[ℂ] H' :=
  ContinuousLinearMapWOT.ofCLM
    (u.toLinearIsometry.toContinuousLinearMap.comp
      ((ContinuousLinearMapWOT.toCLM A).comp u.symm.toLinearIsometry.toContinuousLinearMap))

/-- Unitary conjugation is additive on WOT operators. -/
def unitaryConjAddHom {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    [CompleteSpace H'] (u : H ≃ₗᵢ[ℂ] H') :
    (H →WOT[ℂ] H) →+ (H' →WOT[ℂ] H') where
  toFun := unitaryConj u
  map_zero' := by
    apply ContinuousLinearMapWOT.toCLM_injective
    simp [unitaryConj]
  map_add' A B := by
    apply ContinuousLinearMapWOT.toCLM_injective
    simp [unitaryConj]

lemma continuous_unitaryConjAddHom {H' : Type*} [NormedAddCommGroup H']
    [InnerProductSpace ℂ H'] [CompleteSpace H'] (u : H ≃ₗᵢ[ℂ] H') :
    Continuous (unitaryConjAddHom u) := by
  rw [ContinuousLinearMapWOT.continuous_iff]
  intro x y
  change Continuous (fun A : H →WOT[ℂ] H ↦ ⟪y, (unitaryConj u A) x⟫_ℂ)
  dsimp [unitaryConj]
  change Continuous (fun A : H →WOT[ℂ] H ↦
    ⟪y, u ((ContinuousLinearMapWOT.toCLM A) (u.symm x))⟫_ℂ)
  have heq : (fun A : H →WOT[ℂ] H ↦
      ⟪y, u ((ContinuousLinearMapWOT.toCLM A) (u.symm x))⟫_ℂ) =
      fun A ↦ ⟪u.symm y, A (u.symm x)⟫_ℂ := by
    funext A
    exact (u.symm.inner_map_eq_flip y
      ((ContinuousLinearMapWOT.toCLM A) (u.symm x))).symm
  rw [heq]
  fun_prop

omit [CompleteSpace H] in
@[nolint unusedArguments]
lemma unitaryConj_mul {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    [CompleteSpace H'] (u : H ≃ₗᵢ[ℂ] H') (A B : H →WOT[ℂ] H) :
    unitaryConj u (A * B) = unitaryConj u A * unitaryConj u B := by
  apply ContinuousLinearMapWOT.toCLM_injective
  ext x
  simp [unitaryConj, ContinuousLinearMap.comp_apply]

lemma unitaryConj_star {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    [CompleteSpace H'] (u : H ≃ₗᵢ[ℂ] H') (A : H →WOT[ℂ] H) :
    unitaryConj u (star A) = star (unitaryConj u A) := by
  apply ContinuousLinearMapWOT.ext_inner
  intro x y
  change ⟪y, u ((star (ContinuousLinearMapWOT.toCLM A)) (u.symm x))⟫_ℂ =
    ⟪y, (star (ContinuousLinearMapWOT.toCLM (unitaryConj u A))) x⟫_ℂ
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  change ⟪y, u ((ContinuousLinearMap.adjoint
      (ContinuousLinearMapWOT.toCLM A)) (u.symm x))⟫_ℂ =
    ⟪u ((ContinuousLinearMapWOT.toCLM A) (u.symm y)), x⟫_ℂ
  calc
    _ = ⟪u.symm y, (ContinuousLinearMap.adjoint
        (ContinuousLinearMapWOT.toCLM A)) (u.symm x)⟫_ℂ :=
      (u.symm.inner_map_eq_flip y _).symm
    _ = ⟪(ContinuousLinearMapWOT.toCLM A) (u.symm y), u.symm x⟫_ℂ :=
      ContinuousLinearMap.adjoint_inner_right _ _ _
    _ = ⟪u ((ContinuousLinearMapWOT.toCLM A) (u.symm y)), x⟫_ℂ :=
      (u.inner_map_eq_flip _ _).symm

omit [CompleteSpace H] in
@[nolint unusedArguments]
lemma unitaryConj_one {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    [CompleteSpace H'] (u : H ≃ₗᵢ[ℂ] H') :
    unitaryConj u (1 : H →WOT[ℂ] H) = 1 := by
  apply ContinuousLinearMapWOT.toCLM_injective
  ext x
  simp [unitaryConj]

/-! ## B. Conjugation of a spectral measure -/

/-- Transport a WOT spectral measure through a Hilbert-space unitary. -/
def unitaryConjSpectralMeasure {H' : Type*} [NormedAddCommGroup H']
    [InnerProductSpace ℂ H'] [CompleteSpace H'] (u : H ≃ₗᵢ[ℂ] H') :
    WOTSpectralMeasure α H → WOTSpectralMeasure α H' := fun μS ↦ {
  toVectorMeasure := μS.toVectorMeasure.mapRange (unitaryConjAddHom u)
    (continuous_unitaryConjAddHom u)
  isStarProjection' S := by
    change IsStarProjection (unitaryConj u (μS S))
    refine { isIdempotentElem := ?_, isSelfAdjoint := ?_ }
    · change unitaryConj u (μS S) * unitaryConj u (μS S) = unitaryConj u (μS S)
      rw [← unitaryConj_mul]
      exact congrArg (unitaryConj u) (μS.comp_self S)
    · change star (unitaryConj u (μS S)) = unitaryConj u (μS S)
      rw [← unitaryConj_star]
      exact congrArg (unitaryConj u) (μS.isStarProjection S).isSelfAdjoint
  univ' := by
    change unitaryConj u (μS Set.univ) = 1
    rw [μS.univ, unitaryConj_one] }

@[simp]
lemma unitaryConjSpectralMeasure_apply {H' : Type*} [NormedAddCommGroup H']
    [InnerProductSpace ℂ H'] [CompleteSpace H'] (u : H ≃ₗᵢ[ℂ] H')
    (μS : WOTSpectralMeasure α H) (S : Set α) :
    unitaryConjSpectralMeasure u μS S = unitaryConj u (μS S) := by
  rfl

/-! ## C. Interaction with the scalar and diagonal measures -/

lemma unitaryConjSpectralMeasure_scalarMeasure_apply
    {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    (u : H ≃ₗᵢ[ℂ] H') (μS : WOTSpectralMeasure α H) (x y : H') (S : Set α) :
    (unitaryConjSpectralMeasure u μS).scalarMeasure x y S =
      μS.scalarMeasure (u.symm x) (u.symm y) S := by
  rw [scalarMeasure_apply, scalarMeasure_apply]
  change ⟪y, u ((ContinuousLinearMapWOT.toCLM (μS S)) (u.symm x))⟫_ℂ = _
  exact (u.symm.inner_map_eq_flip _ _).symm

lemma unitaryConjSpectralMeasure_scalarMeasure
    {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    (u : H ≃ₗᵢ[ℂ] H') (μS : WOTSpectralMeasure α H) (x y : H') :
    (unitaryConjSpectralMeasure u μS).scalarMeasure x y =
      μS.scalarMeasure (u.symm x) (u.symm y) := by
  apply MeasureTheory.VectorMeasure.ext
  intro S hS
  exact unitaryConjSpectralMeasure_scalarMeasure_apply u μS x y S

lemma unitaryConjSpectralMeasure_diagonalMeasure
    {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    (u : H ≃ₗᵢ[ℂ] H') (μS : WOTSpectralMeasure α H) (x : H') :
    (unitaryConjSpectralMeasure u μS).diagonalMeasure x =
      μS.diagonalMeasure (u.symm x) := by
  apply Measure.ext
  intro S hS
  rw [(unitaryConjSpectralMeasure u μS).diagonalMeasure_apply_eq_norm_sq x S hS,
    μS.diagonalMeasure_apply_eq_norm_sq (u.symm x) S hS,
    unitaryConjSpectralMeasure_apply]
  change ENNReal.ofReal
      (‖u ((ContinuousLinearMapWOT.toCLM (μS S)) (u.symm x))‖ ^ 2) = _
  rw [u.norm_map]
  rfl

end WOTSpectralMeasure

end QuantumMechanics

end
