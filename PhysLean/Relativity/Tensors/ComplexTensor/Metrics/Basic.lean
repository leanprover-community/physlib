/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.ComplexTensor.OfRat
/-!

## Metrics as complex Lorentz tensors

-/
open IndexNotation
open CategoryTheory
open MonoidalCategory
open Matrix
open MatrixGroups
open Complex
open TensorProduct
open IndexNotation
open CategoryTheory
open OverColor.Discrete
noncomputable section

namespace complexLorentzTensor
open Fermion

/-!

## Definitions.

-/

/-- The metric `ηᵢᵢ` as a complex Lorentz tensor. -/
abbrev coMetric : ℂT[.down, .down] := complexLorentzTensor.metricTensor Color.down

/-- The metric `ηⁱⁱ` as a complex Lorentz tensor. -/
abbrev contrMetric : ℂT[.up, .up] := complexLorentzTensor.metricTensor Color.up

/-- The metric `εᵃᵃ` as a complex Lorentz tensor. -/
abbrev leftMetric : ℂT[.upL, .upL] := complexLorentzTensor.metricTensor Color.upL

/-- The metric `ε^{dot a}^{dot a}` as a complex Lorentz tensor. -/
abbrev rightMetric : ℂT[.upR, .upR] := complexLorentzTensor.metricTensor Color.upR

/-- The metric `εₐₐ` as a complex Lorentz tensor. -/
abbrev altLeftMetric : ℂT[.downL, .downL] := complexLorentzTensor.metricTensor Color.downL

/-- The metric `ε_{dot a}_{dot a}` as a complex Lorentz tensor. -/
abbrev altRightMetric : ℂT[.downR, .downR] := complexLorentzTensor.metricTensor Color.downR

/-!

## Notation

-/

/-- The metric `ηᵢᵢ` as a complex Lorentz tensors. -/
scoped[complexLorentzTensor] notation "η'" => coMetric

/-- The metric `ηⁱⁱ` as a complex Lorentz tensors. -/
scoped[complexLorentzTensor] notation "η" => contrMetric

/-- The metric `εᵃᵃ` as a complex Lorentz tensors. -/
scoped[complexLorentzTensor] notation "εL" => leftMetric

/-- The metric `ε^{dot a}^{dot a}` as a complex Lorentz tensors. -/
scoped[complexLorentzTensor] notation "εR" => rightMetric

/-- The metric `εₐₐ` as a complex Lorentz tensors. -/
scoped[complexLorentzTensor] notation "εL'" => altLeftMetric

/-- The metric `ε_{dot a}_{dot a}` as a complex Lorentz tensors. -/
scoped[complexLorentzTensor] notation "εR'" => altRightMetric

/-!

## Other forms

-/
open TensorSpecies
open Tensor
/-!

### fromConstPair

-/

lemma coMetric_eq_fromConstPair : η' = fromConstPair Lorentz.coMetric := by
  rw [Lorentz.coMetric]
  rfl

lemma contrMetric_eq_fromConstPair : η = fromConstPair Lorentz.contrMetric := by
  rw [Lorentz.contrMetric]
  rfl

lemma leftMetric_eq_fromConstPair : εL = fromConstPair Fermion.leftMetric := rfl

lemma rightMetric_eq_fromConstPair : εR = fromConstPair Fermion.rightMetric := rfl

lemma altLeftMetric_eq_fromConstPair : εL' = fromConstPair Fermion.altLeftMetric := rfl

lemma altRightMetric_eq_fromConstPair : εR' = fromConstPair Fermion.altRightMetric := rfl

/-!

### fromPairT

-/

lemma coMetric_eq_fromPairT : η' = fromPairT (Lorentz.coMetricVal) := by
  rw [coMetric_eq_fromConstPair, fromConstPair]
  congr 1
  exact Lorentz.coMetric_apply_one

lemma contrMetric_eq_fromPairT : η = fromPairT (Lorentz.contrMetricVal) := by
  rw [contrMetric_eq_fromConstPair, fromConstPair]
  congr 1
  exact Lorentz.contrMetric_apply_one

lemma leftMetric_eq_fromPairT : εL = fromPairT (Fermion.leftMetricVal) := by
  rw [leftMetric_eq_fromConstPair, fromConstPair]
  congr 1
  exact Fermion.leftMetric_apply_one

lemma rightMetric_eq_fromPairT : εR = fromPairT (Fermion.rightMetricVal) := by
  rw [rightMetric_eq_fromConstPair, fromConstPair]
  congr 1
  exact Fermion.rightMetric_apply_one

lemma altLeftMetric_eq_fromPairT : εL' = fromPairT (Fermion.altLeftMetricVal) := by
  rw [altLeftMetric_eq_fromConstPair, fromConstPair]
  congr 1
  exact Fermion.altLeftMetric_apply_one

lemma altRightMetric_eq_fromPairT : εR' = fromPairT (Fermion.altRightMetricVal) := by
  rw [altRightMetric_eq_fromConstPair, fromConstPair]
  congr 1
  exact Fermion.altRightMetric_apply_one

/-!

### complexCoBasis etc.

-/

open Lorentz in
lemma coMetric_eq_complexCoBasis : η' =
    fromPairT (complexCoBasis (Sum.inl 0) ⊗ₜ[ℂ] complexCoBasis (Sum.inl 0))
    - fromPairT (complexCoBasis (Sum.inr 0) ⊗ₜ[ℂ] complexCoBasis (Sum.inr 0))
    - fromPairT (complexCoBasis (Sum.inr 1) ⊗ₜ[ℂ] complexCoBasis (Sum.inr 1))
    - fromPairT (complexCoBasis (Sum.inr 2) ⊗ₜ[ℂ] complexCoBasis (Sum.inr 2)) := by
  rw [coMetric_eq_fromPairT, coMetricVal_expand_tmul]
  simp

open Lorentz in
lemma coMetric_eq_complexCoBasisFin4 : η' =
    fromPairT (complexCoBasisFin4 0 ⊗ₜ[ℂ] complexCoBasisFin4 0)
    - fromPairT (complexCoBasisFin4 1 ⊗ₜ[ℂ] complexCoBasisFin4 1)
    - fromPairT (complexCoBasisFin4 2 ⊗ₜ[ℂ] complexCoBasisFin4 2)
    - fromPairT (complexCoBasisFin4 3 ⊗ₜ[ℂ] complexCoBasisFin4 3) := by
  rw [coMetric_eq_complexCoBasis]
  simp [complexCoBasisFin4]
  rfl

open Lorentz in
lemma contrMetric_eq_complexContrBasis : η =
    fromPairT (complexContrBasis (Sum.inl 0) ⊗ₜ[ℂ] complexContrBasis (Sum.inl 0))
    - fromPairT (complexContrBasis (Sum.inr 0) ⊗ₜ[ℂ] complexContrBasis (Sum.inr 0))
    - fromPairT (complexContrBasis (Sum.inr 1) ⊗ₜ[ℂ] complexContrBasis (Sum.inr 1))
    - fromPairT (complexContrBasis (Sum.inr 2) ⊗ₜ[ℂ] complexContrBasis (Sum.inr 2)) := by
  rw [contrMetric_eq_fromPairT, contrMetricVal_expand_tmul]
  simp

open Lorentz in
lemma contrMetric_eq_complexContrBasisFin4 : η =
    fromPairT (complexContrBasisFin4 0 ⊗ₜ[ℂ] complexContrBasisFin4 0)
    - fromPairT (complexContrBasisFin4 1 ⊗ₜ[ℂ] complexContrBasisFin4 1)
    - fromPairT (complexContrBasisFin4 2 ⊗ₜ[ℂ] complexContrBasisFin4 2)
    - fromPairT (complexContrBasisFin4 3 ⊗ₜ[ℂ] complexContrBasisFin4 3) := by
  rw [contrMetric_eq_complexContrBasis]
  simp [complexContrBasisFin4]
  rfl

open Fermion in
lemma leftMetric_eq_leftBasis : εL =
    - fromPairT (leftBasis 0 ⊗ₜ[ℂ] leftBasis 1)
    + fromPairT (leftBasis 1 ⊗ₜ[ℂ] leftBasis 0) := by
  rw [leftMetric_eq_fromPairT, leftMetricVal_expand_tmul]
  simp

open Fermion in
lemma altLeftMetric_eq_altLeftBasis : εL' =
    fromPairT (altLeftBasis 0 ⊗ₜ[ℂ] altLeftBasis 1)
    - fromPairT (altLeftBasis 1 ⊗ₜ[ℂ] altLeftBasis 0) := by
  rw [altLeftMetric_eq_fromPairT, altLeftMetricVal_expand_tmul]
  simp

open Fermion in
lemma rightMetric_eq_rightBasis : εR =
    - fromPairT (rightBasis 0 ⊗ₜ[ℂ] rightBasis 1)
    + fromPairT (rightBasis 1 ⊗ₜ[ℂ] rightBasis 0) := by
  rw [rightMetric_eq_fromPairT, rightMetricVal_expand_tmul]
  simp

open Fermion in
lemma altRightMetric_eq_altRightBasis : εR' =
    fromPairT (altRightBasis 0 ⊗ₜ[ℂ] altRightBasis 1)
    - fromPairT (altRightBasis 1 ⊗ₜ[ℂ] altRightBasis 0) := by
  rw [altRightMetric_eq_fromPairT, altRightMetricVal_expand_tmul]
  simp

/-!

### basis

-/

open Lorentz in
lemma coMetric_eq_basis : η' =
    (Tensor.basis (S := complexLorentzTensor) ![Color.down, Color.down] (fun | 0 => 0 | 1 => 0))
    - (Tensor.basis (S := complexLorentzTensor) ![Color.down, Color.down] (fun | 0 => 1 | 1 => 1))
    - (Tensor.basis (S := complexLorentzTensor) ![Color.down, Color.down] (fun | 0 => 2 | 1 => 2))
    - (Tensor.basis (S := complexLorentzTensor) ![Color.down, Color.down]
      (fun | 0 => 3 | 1 => 3)) := by
  rw [coMetric_eq_complexCoBasisFin4]
  rw [show complexCoBasisFin4 = complexLorentzTensor.basis .down by rfl]
  conv_lhs =>
    enter [2]
    erw [fromPairT_apply_basis_repr]
  conv_lhs =>
    enter [1, 2]
    erw [fromPairT_apply_basis_repr]
  conv_lhs =>
    enter [1, 1, 2]
    erw [fromPairT_apply_basis_repr]
  conv_lhs =>
    enter [1, 1, 1]
    erw [fromPairT_apply_basis_repr]
  rfl

open Lorentz in
lemma contrMetric_eq_basis : η =
    (Tensor.basis (S := complexLorentzTensor) ![Color.up, Color.up] (fun | 0 => 0 | 1 => 0))
    - (Tensor.basis (S := complexLorentzTensor) ![Color.up, Color.up] (fun | 0 => 1 | 1 => 1))
    - (Tensor.basis (S := complexLorentzTensor) ![Color.up, Color.up] (fun | 0 => 2 | 1 => 2))
    - (Tensor.basis (S := complexLorentzTensor) ![Color.up, Color.up]
      (fun | 0 => 3 | 1 => 3)) := by
  rw [contrMetric_eq_complexContrBasisFin4]
  rw [show complexContrBasisFin4 = complexLorentzTensor.basis .up by rfl]
  conv_lhs =>
    enter [2]
    erw [fromPairT_apply_basis_repr]
  conv_lhs =>
    enter [1, 2]
    erw [fromPairT_apply_basis_repr]
  conv_lhs =>
    enter [1, 1, 2]
    erw [fromPairT_apply_basis_repr]
  conv_lhs =>
    enter [1, 1, 1]
    erw [fromPairT_apply_basis_repr]
  rfl

open Fermion in
lemma leftMetric_eq_basis : εL =
    - (Tensor.basis (S := complexLorentzTensor) ![Color.upL, Color.upL] (fun | 0 => 0 | 1 => 1))
    + (Tensor.basis (S := complexLorentzTensor)
      ![Color.upL, Color.upL] (fun | 0 => 1 | 1 => 0)) := by
  rw [leftMetric_eq_leftBasis]
  rw [show leftBasis = complexLorentzTensor.basis .upL by rfl]
  conv_lhs =>
    enter [2]
    erw [fromPairT_apply_basis_repr]
  conv_lhs =>
    enter [1, 1]
    erw [fromPairT_apply_basis_repr]
  rfl

open Fermion in
lemma altLeftMetric_eq_basis : εL' =
    (Tensor.basis (S := complexLorentzTensor) ![Color.downL, Color.downL] (fun | 0 => 0 | 1 => 1))
    - (Tensor.basis (S := complexLorentzTensor)
      ![Color.downL, Color.downL] (fun | 0 => 1 | 1 => 0)) := by
  rw [altLeftMetric_eq_altLeftBasis]
  rw [show altLeftBasis = complexLorentzTensor.basis .downL by rfl]
  conv_lhs =>
    enter [2]
    erw [fromPairT_apply_basis_repr]
  conv_lhs =>
    enter [1]
    erw [fromPairT_apply_basis_repr]
  rfl

open Fermion in
lemma rightMetric_eq_basis : εR =
    - (Tensor.basis (S := complexLorentzTensor) ![Color.upR, Color.upR] (fun | 0 => 0 | 1 => 1))
    + (Tensor.basis (S := complexLorentzTensor)
      ![Color.upR, Color.upR] (fun | 0 => 1 | 1 => 0)) := by
  rw [rightMetric_eq_rightBasis]
  rw [show rightBasis = complexLorentzTensor.basis .upR by rfl]
  conv_lhs =>
    enter [2]
    erw [fromPairT_apply_basis_repr]
  conv_lhs =>
    enter [1, 1]
    erw [fromPairT_apply_basis_repr]
  rfl

open Fermion in
lemma altRightMetric_eq_basis : εR' =
    (Tensor.basis (S := complexLorentzTensor)
      ![Color.downR, Color.downR] (fun | 0 => 0 | 1 => 1))
    - (Tensor.basis (S := complexLorentzTensor)
      ![Color.downR, Color.downR] (fun | 0 => 1 | 1 => 0)) := by
  rw [altRightMetric_eq_altRightBasis]
  rw [show altRightBasis = complexLorentzTensor.basis .downR by rfl]
  conv_lhs =>
    enter [2]
    erw [fromPairT_apply_basis_repr]
  conv_lhs =>
    enter [1]
    erw [fromPairT_apply_basis_repr]
  rfl

/-!

### ofRat

-/

lemma coMetric_eq_ofRat : η' = ofRat fun f =>
    if f 0 = 0 ∧ f 1 = 0 then 1 else
    if f 0 = f 1 then - 1 else 0 := by
  rw [coMetric_eq_basis]
  conv_lhs =>
    rw [basis_eq_ofRat, basis_eq_ofRat, basis_eq_ofRat, basis_eq_ofRat]
  rw [← map_sub, ← map_sub, ← map_sub]
  congr
  with_unfolding_all decide

lemma contrMetric_eq_ofRat : η = ofRat fun f =>
    if f 0 = 0 ∧ f 1 = 0 then 1 else
    if f 0 = f 1 then - 1 else 0 := by
  rw [contrMetric_eq_basis]
  conv_lhs =>
    rw [basis_eq_ofRat, basis_eq_ofRat, basis_eq_ofRat, basis_eq_ofRat]
  rw [← map_sub, ← map_sub, ← map_sub]
  congr
  with_unfolding_all decide

lemma leftMetric_eq_ofRat : εL = ofRat fun f =>
    if f 0 = 0 ∧ f 1 = 1 then - 1 else
    if f 1 = 0 ∧ f 0 = 1 then 1 else 0 := by
  rw [leftMetric_eq_basis]
  conv_lhs =>
    rw [basis_eq_ofRat, basis_eq_ofRat]
  rw [← map_neg, ← map_add]
  congr
  with_unfolding_all decide

lemma altLeftMetric_eq_ofRat : εL' = ofRat fun f =>
    if f 0 = 0 ∧ f 1 = 1 then 1 else
    if f 1 = 0 ∧ f 0 = 1 then - 1 else 0 := by
  rw [altLeftMetric_eq_basis]
  conv_lhs =>
    rw [basis_eq_ofRat, basis_eq_ofRat]
  rw [← map_sub]
  congr
  with_unfolding_all decide

lemma rightMetric_eq_ofRat : εR = ofRat fun f =>
    if f 0 = 0 ∧ f 1 = 1 then - 1 else
    if f 1 = 0 ∧ f 0 = 1 then 1 else 0 := by
  rw [rightMetric_eq_basis]
  conv_lhs =>
    rw [basis_eq_ofRat, basis_eq_ofRat]
  rw [← map_neg, ← map_add]
  congr
  with_unfolding_all decide

lemma altRightMetric_eq_ofRat : εR' = ofRat fun f =>
    if f 0 = 0 ∧ f 1 = 1 then 1 else
    if f 1 = 0 ∧ f 0 = 1 then - 1 else 0 := by
  rw [altRightMetric_eq_basis]
  conv_lhs =>
    rw [basis_eq_ofRat, basis_eq_ofRat]
  rw [← map_sub]
  congr
  with_unfolding_all decide

/-!

## Group actions

-/

open TensorSpecies

/-- The tensor `coMetric` is invariant under the action of `SL(2,ℂ)`. -/
lemma actionT_coMetric (g : SL(2,ℂ)) : g • η' = η' := by
  rw [metricTensor_invariant]

/-- The tensor `contrMetric` is invariant under the action of `SL(2,ℂ)`. -/
lemma actionT_contrMetric (g : SL(2,ℂ)) : g • η = η := by
  rw [metricTensor_invariant]

/-- The tensor `leftMetric` is invariant under the action of `SL(2,ℂ)`. -/
lemma actionT_leftMetric (g : SL(2,ℂ)) : g • εL = εL := by
  rw [metricTensor_invariant]

/-- The tensor `rightMetric` is invariant under the action of `SL(2,ℂ)`. -/
lemma actionT_rightMetric (g : SL(2,ℂ)) : g • εR = εR := by
  rw [metricTensor_invariant]

/-- The tensor `altLeftMetric` is invariant under the action of `SL(2,ℂ)`. -/
lemma actionT_altLeftMetric (g : SL(2,ℂ)) : g • εL' = εL' := by
  rw [metricTensor_invariant]

/-- The tensor `altRightMetric` is invariant under the action of `SL(2,ℂ)`. -/
lemma actionT_altRightMetric (g : SL(2,ℂ)) : g • εR' = εR' := by
  rw [metricTensor_invariant]

end complexLorentzTensor
