/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.OfGaussianInt
/-!

## Metrics as complex Lorentz tensors

-/

@[expose] public section

open Matrix
open MatrixGroups
open Complex
open TensorProduct
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
abbrev dualLeftMetric : ℂT[.downL, .downL] := complexLorentzTensor.metricTensor Color.downL

/-- The metric `ε_{dot a}_{dot a}` as a complex Lorentz tensor. -/
abbrev dualRightMetric : ℂT[.downR, .downR] := complexLorentzTensor.metricTensor Color.downR

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
scoped[complexLorentzTensor] notation "εL'" => dualLeftMetric

/-- The metric `ε_{dot a}_{dot a}` as a complex Lorentz tensors. -/
scoped[complexLorentzTensor] notation "εR'" => dualRightMetric

/-!

## Other forms

-/
open TensorSpecies
open Tensor
/-!

### fromConstPair

-/

lemma coMetric_eq_fromConstPair : η' = fromConstPair (S := complexLorentzTensor)
    (c1 := .down) (c2 := .down) Lorentz.ComplexCoVector.metric := by
  rw [Lorentz.ComplexCoVector.metric]
  rfl

lemma contrMetric_eq_fromConstPair : η = fromConstPair (S := complexLorentzTensor)
    (c1 := .up) (c2 := .up) Lorentz.ComplexVector.metric := by
  rw [Lorentz.ComplexVector.metric]
  rfl

lemma leftMetric_eq_fromConstPair : εL = fromConstPair Fermion.LeftHandedWeyl.metric := rfl

lemma rightMetric_eq_fromConstPair : εR = fromConstPair Fermion.RightHandedWeyl.metric := rfl

lemma dualLeftMetric_eq_fromConstPair : εL' = fromConstPair Fermion.DualLeftHandedWeyl.metric := rfl

lemma dualRightMetric_eq_fromConstPair :
    εR' = fromConstPair Fermion.DualRightHandedWeyl.metric := rfl

/-!

### fromPairT

-/

lemma coMetric_eq_fromPairT : η' = fromPairT (Lorentz.ComplexCoVector.metricVal) := by
  rw [coMetric_eq_fromConstPair, fromConstPair]
  congr 1
  exact Lorentz.ComplexCoVector.metric_apply_one

lemma contrMetric_eq_fromPairT : η = fromPairT (Lorentz.ComplexVector.metricVal) := by
  rw [contrMetric_eq_fromConstPair, fromConstPair]
  congr 1
  exact Lorentz.ComplexVector.metric_apply_one

lemma leftMetric_eq_fromPairT : εL = fromPairT (Fermion.LeftHandedWeyl.metricVal) := by
  rw [leftMetric_eq_fromConstPair, fromConstPair]
  congr 1
  exact Fermion.LeftHandedWeyl.metric_apply_one

lemma rightMetric_eq_fromPairT : εR = fromPairT (Fermion.RightHandedWeyl.metricVal) := by
  rw [rightMetric_eq_fromConstPair, fromConstPair]
  congr 1
  exact Fermion.RightHandedWeyl.metric_apply_one

lemma dualLeftMetric_eq_fromPairT : εL' = fromPairT (Fermion.DualLeftHandedWeyl.metricVal) := by
  rw [dualLeftMetric_eq_fromConstPair, fromConstPair]
  congr 1
  exact Fermion.DualLeftHandedWeyl.metric_apply_one

lemma dualRightMetric_eq_fromPairT : εR' = fromPairT (Fermion.DualRightHandedWeyl.metricVal) := by
  rw [dualRightMetric_eq_fromConstPair, fromConstPair]
  congr 1
  exact Fermion.DualRightHandedWeyl.metric_apply_one

/-!

### ComplexCoVector.basis etc.

-/

open Lorentz in
lemma coMetric_eq_complexCoVector_basis : η' =
    fromPairT (ComplexCoVector.basis (Sum.inl 0) ⊗ₜ[ℂ] ComplexCoVector.basis (Sum.inl 0))
    - fromPairT (ComplexCoVector.basis (Sum.inr 0) ⊗ₜ[ℂ] ComplexCoVector.basis (Sum.inr 0))
    - fromPairT (ComplexCoVector.basis (Sum.inr 1) ⊗ₜ[ℂ] ComplexCoVector.basis (Sum.inr 1))
    - fromPairT (ComplexCoVector.basis (Sum.inr 2) ⊗ₜ[ℂ] ComplexCoVector.basis (Sum.inr 2)) := by
  rw [coMetric_eq_fromPairT, ComplexCoVector.metricVal_expand_tmul]
  simp

open Lorentz in
lemma coMetric_eq_complexCoVector_basisFin4 : η' =
    fromPairT (ComplexCoVector.basisFin4 0 ⊗ₜ[ℂ] ComplexCoVector.basisFin4 0)
    - fromPairT (ComplexCoVector.basisFin4 1 ⊗ₜ[ℂ] ComplexCoVector.basisFin4 1)
    - fromPairT (ComplexCoVector.basisFin4 2 ⊗ₜ[ℂ] ComplexCoVector.basisFin4 2)
    - fromPairT (ComplexCoVector.basisFin4 3 ⊗ₜ[ℂ] ComplexCoVector.basisFin4 3) := by
  rw [coMetric_eq_complexCoVector_basis]
  simp [ComplexCoVector.basisFin4]
  rfl

open Lorentz in
lemma contrMetric_eq_complexVector_basis : η =
    fromPairT (ComplexVector.basis (Sum.inl 0) ⊗ₜ[ℂ] ComplexVector.basis (Sum.inl 0))
    - fromPairT (ComplexVector.basis (Sum.inr 0) ⊗ₜ[ℂ] ComplexVector.basis (Sum.inr 0))
    - fromPairT (ComplexVector.basis (Sum.inr 1) ⊗ₜ[ℂ] ComplexVector.basis (Sum.inr 1))
    - fromPairT (ComplexVector.basis (Sum.inr 2) ⊗ₜ[ℂ] ComplexVector.basis (Sum.inr 2)) := by
  rw [contrMetric_eq_fromPairT, ComplexVector.metricVal_expand_tmul]
  simp

open Lorentz in
lemma contrMetric_eq_complexVector_basisFin4 : η =
    fromPairT (ComplexVector.basisFin4 0 ⊗ₜ[ℂ] ComplexVector.basisFin4 0)
    - fromPairT (ComplexVector.basisFin4 1 ⊗ₜ[ℂ] ComplexVector.basisFin4 1)
    - fromPairT (ComplexVector.basisFin4 2 ⊗ₜ[ℂ] ComplexVector.basisFin4 2)
    - fromPairT (ComplexVector.basisFin4 3 ⊗ₜ[ℂ] ComplexVector.basisFin4 3) := by
  rw [contrMetric_eq_complexVector_basis]
  simp [ComplexVector.basisFin4]
  rfl

open Fermion in
lemma leftMetric_eq_leftHandedWeyl_basis : εL =
    - fromPairT (LeftHandedWeyl.basis 0 ⊗ₜ[ℂ] LeftHandedWeyl.basis 1)
    + fromPairT (LeftHandedWeyl.basis 1 ⊗ₜ[ℂ] LeftHandedWeyl.basis 0) := by
  rw [leftMetric_eq_fromPairT, LeftHandedWeyl.metricVal_expand_tmul]
  simp

open Fermion in
lemma dualLeftMetric_eq_dualLeftHandedWeyl_basis : εL' =
    fromPairT (DualLeftHandedWeyl.basis 0 ⊗ₜ[ℂ] DualLeftHandedWeyl.basis 1)
    - fromPairT (DualLeftHandedWeyl.basis 1 ⊗ₜ[ℂ] DualLeftHandedWeyl.basis 0) := by
  rw [dualLeftMetric_eq_fromPairT, DualLeftHandedWeyl.metricVal_expand_tmul]
  simp

open Fermion in
lemma rightMetric_eq_rightHandedWeyl_basis : εR =
    - fromPairT (RightHandedWeyl.basis 0 ⊗ₜ[ℂ] RightHandedWeyl.basis 1)
    + fromPairT (RightHandedWeyl.basis 1 ⊗ₜ[ℂ] RightHandedWeyl.basis 0) := by
  rw [rightMetric_eq_fromPairT, RightHandedWeyl.metricVal_expand_tmul]
  simp

open Fermion in
lemma dualRightMetric_eq_dualRightHandedWeyl_basis : εR' =
    fromPairT (DualRightHandedWeyl.basis 0 ⊗ₜ[ℂ] DualRightHandedWeyl.basis 1)
    - fromPairT (DualRightHandedWeyl.basis 1 ⊗ₜ[ℂ] DualRightHandedWeyl.basis 0) := by
  rw [dualRightMetric_eq_fromPairT, DualRightHandedWeyl.metricVal_expand_tmul]
  simp

/-!

### basis

-/

open Lorentz in
lemma coMetric_eq_basis : η' =
    (Tensor.basis (S := complexLorentzTensor) ![Color.down, Color.down]
      (fun | 0 => (Sum.inl 0 : Fin 1 ⊕ Fin 3) | 1 => (Sum.inl 0 : Fin 1 ⊕ Fin 3)))
    - (Tensor.basis (S := complexLorentzTensor) ![Color.down, Color.down]
      (fun | 0 => (Sum.inr 0 : Fin 1 ⊕ Fin 3) | 1 => (Sum.inr 0 : Fin 1 ⊕ Fin 3)))
    - (Tensor.basis (S := complexLorentzTensor) ![Color.down, Color.down]
      (fun | 0 => (Sum.inr 1 : Fin 1 ⊕ Fin 3) | 1 => (Sum.inr 1 : Fin 1 ⊕ Fin 3)))
    - (Tensor.basis (S := complexLorentzTensor) ![Color.down, Color.down]
      (fun | 0 => (Sum.inr 2 : Fin 1 ⊕ Fin 3) | 1 => (Sum.inr 2 : Fin 1 ⊕ Fin 3))) := by
  rw [coMetric_eq_complexCoVector_basis]
  conv_lhs =>
    enter [2]
    change fromPairT ((complexLorentzTensor.basis .down _) ⊗ₜ[ℂ]
      (complexLorentzTensor.basis .down _))
    rw [fromPairT_apply_basis_repr]
  conv_lhs =>
    enter [1, 2]
    change fromPairT ((complexLorentzTensor.basis .down _) ⊗ₜ[ℂ]
      (complexLorentzTensor.basis .down _))
    rw [fromPairT_apply_basis_repr]
  conv_lhs =>
    enter [1, 1, 2]
    change fromPairT ((complexLorentzTensor.basis .down _) ⊗ₜ[ℂ]
      (complexLorentzTensor.basis .down _))
    rw [fromPairT_apply_basis_repr]
  conv_lhs =>
    enter [1, 1, 1]
    change fromPairT ((complexLorentzTensor.basis .down _) ⊗ₜ[ℂ]
      (complexLorentzTensor.basis .down _))
    rw [fromPairT_apply_basis_repr]
  rfl

open Lorentz in
lemma contrMetric_eq_basis : η =
    (Tensor.basis (S := complexLorentzTensor) ![Color.up, Color.up]
      (fun | 0 => (Sum.inl 0 : Fin 1 ⊕ Fin 3) | 1 => (Sum.inl 0 : Fin 1 ⊕ Fin 3)))
    - (Tensor.basis (S := complexLorentzTensor) ![Color.up, Color.up]
      (fun | 0 => (Sum.inr 0 : Fin 1 ⊕ Fin 3) | 1 => (Sum.inr 0 : Fin 1 ⊕ Fin 3)))
    - (Tensor.basis (S := complexLorentzTensor) ![Color.up, Color.up]
      (fun | 0 => (Sum.inr 1 : Fin 1 ⊕ Fin 3) | 1 => (Sum.inr 1 : Fin 1 ⊕ Fin 3)))
    - (Tensor.basis (S := complexLorentzTensor) ![Color.up, Color.up]
      (fun | 0 => (Sum.inr 2 : Fin 1 ⊕ Fin 3) | 1 => (Sum.inr 2 : Fin 1 ⊕ Fin 3))) := by
  rw [contrMetric_eq_complexVector_basis]
  conv_lhs =>
    enter [2]
    change fromPairT ((complexLorentzTensor.basis .up _) ⊗ₜ[ℂ]
      (complexLorentzTensor.basis .up _))
    rw [fromPairT_apply_basis_repr]
  conv_lhs =>
    enter [1, 2]
    change fromPairT ((complexLorentzTensor.basis .up _) ⊗ₜ[ℂ]
      (complexLorentzTensor.basis .up _))
    rw [fromPairT_apply_basis_repr]
  conv_lhs =>
    enter [1, 1, 2]
    change fromPairT ((complexLorentzTensor.basis .up _) ⊗ₜ[ℂ]
      (complexLorentzTensor.basis .up _))
    rw [fromPairT_apply_basis_repr]
  conv_lhs =>
    enter [1, 1, 1]
    change fromPairT ((complexLorentzTensor.basis .up _) ⊗ₜ[ℂ]
      (complexLorentzTensor.basis .up _))
    rw [fromPairT_apply_basis_repr]
  rfl

open Fermion in
lemma leftMetric_eq_basis : εL =
    - (Tensor.basis (S := complexLorentzTensor) ![Color.upL, Color.upL]
      (fun | 0 => (0 : Fin 2) | 1 => (1 : Fin 2)))
    + (Tensor.basis (S := complexLorentzTensor)
      ![Color.upL, Color.upL] (fun | 0 => (1 : Fin 2) | 1 => (0 : Fin 2))) := by
  rw [leftMetric_eq_leftHandedWeyl_basis]
  conv_lhs =>
    enter [2]
    change fromPairT ((complexLorentzTensor.basis .upL _) ⊗ₜ[ℂ]
      (complexLorentzTensor.basis .upL _))
    rw [fromPairT_apply_basis_repr]
  conv_lhs =>
    enter [1, 1]
    change fromPairT ((complexLorentzTensor.basis .upL _) ⊗ₜ[ℂ]
      (complexLorentzTensor.basis .upL _))
    rw [fromPairT_apply_basis_repr]
  rfl

open Fermion in
lemma dualLeftMetric_eq_basis : εL' =
    (Tensor.basis (S := complexLorentzTensor) ![Color.downL, Color.downL]
      (fun | 0 => (0 : Fin 2) | 1 => (1 : Fin 2)))
    - (Tensor.basis (S := complexLorentzTensor)
      ![Color.downL, Color.downL] (fun | 0 => (1 : Fin 2) | 1 => (0 : Fin 2))) := by
  rw [dualLeftMetric_eq_dualLeftHandedWeyl_basis]
  conv_lhs =>
    enter [2]
    change fromPairT ((complexLorentzTensor.basis .downL _) ⊗ₜ[ℂ]
      (complexLorentzTensor.basis .downL _))
    rw [fromPairT_apply_basis_repr]
  conv_lhs =>
    enter [1]
    change fromPairT ((complexLorentzTensor.basis .downL _) ⊗ₜ[ℂ]
      (complexLorentzTensor.basis .downL _))
    rw [fromPairT_apply_basis_repr]
  rfl

open Fermion in
lemma rightMetric_eq_basis : εR =
    - (Tensor.basis (S := complexLorentzTensor) ![Color.upR, Color.upR]
      (fun | 0 => (0 : Fin 2) | 1 => (1 : Fin 2)))
    + (Tensor.basis (S := complexLorentzTensor)
      ![Color.upR, Color.upR] (fun | 0 => (1 : Fin 2) | 1 => (0 : Fin 2))) := by
  rw [rightMetric_eq_rightHandedWeyl_basis]
  conv_lhs =>
    enter [2]
    change fromPairT ((complexLorentzTensor.basis .upR _) ⊗ₜ[ℂ]
      (complexLorentzTensor.basis .upR _))
    rw [fromPairT_apply_basis_repr]
  conv_lhs =>
    enter [1, 1]
    change fromPairT ((complexLorentzTensor.basis .upR _) ⊗ₜ[ℂ]
      (complexLorentzTensor.basis .upR _))
    rw [fromPairT_apply_basis_repr]
  rfl

open Fermion in
lemma dualRightMetric_eq_basis : εR' =
    (Tensor.basis (S := complexLorentzTensor)
      ![Color.downR, Color.downR] (fun | 0 => (0 : Fin 2) | 1 => (1 : Fin 2)))
    - (Tensor.basis (S := complexLorentzTensor)
      ![Color.downR, Color.downR] (fun | 0 => (1 : Fin 2) | 1 => (0 : Fin 2))) := by
  rw [dualRightMetric_eq_dualRightHandedWeyl_basis]
  conv_lhs =>
    enter [2]
    change fromPairT ((complexLorentzTensor.basis .downR _) ⊗ₜ[ℂ]
      (complexLorentzTensor.basis .downR _))
    rw [fromPairT_apply_basis_repr]
  conv_lhs =>
    enter [1]
    change fromPairT ((complexLorentzTensor.basis .downR _) ⊗ₜ[ℂ]
      (complexLorentzTensor.basis .downR _))
    rw [fromPairT_apply_basis_repr]
  rfl

/-!

### ofGaussianInt

-/

set_option backward.isDefEq.respectTransparency false in
lemma coMetric_eq_ofGaussianInt : η' = ofGaussianInt fun f =>
    if f 0 = (Sum.inl 0 : Fin 1 ⊕ Fin 3) ∧ f 1 = (Sum.inl 0 : Fin 1 ⊕ Fin 3) then 1 else
    if f 0 = f 1 then - 1 else 0 := by
  rw [coMetric_eq_basis]
  conv_lhs =>
    rw [basis_eq_ofGaussianInt, basis_eq_ofGaussianInt, basis_eq_ofGaussianInt,
      basis_eq_ofGaussianInt]
  rw [← map_sub, ← map_sub, ← map_sub]
  congr
  with_unfolding_all decide

set_option backward.isDefEq.respectTransparency false in
lemma contrMetric_eq_ofGaussianInt : η = ofGaussianInt fun f =>
    if f 0 = (Sum.inl 0 : Fin 1 ⊕ Fin 3) ∧ f 1 = (Sum.inl 0 : Fin 1 ⊕ Fin 3) then 1 else
    if f 0 = f 1 then - 1 else 0 := by
  rw [contrMetric_eq_basis]
  conv_lhs =>
    rw [basis_eq_ofGaussianInt, basis_eq_ofGaussianInt, basis_eq_ofGaussianInt,
      basis_eq_ofGaussianInt]
  rw [← map_sub, ← map_sub, ← map_sub]
  congr
  with_unfolding_all decide

lemma leftMetric_eq_ofGaussianInt : εL =
    ofGaussianInt (c := ![Color.upL, Color.upL]) fun f =>
    if f = (fun | 0 => (0 : Fin 2) | 1 => (1 : Fin 2)) then - 1 else
    if f = (fun | 0 => (1 : Fin 2) | 1 => (0 : Fin 2)) then 1 else 0 := by
  rw [leftMetric_eq_basis]
  conv_lhs =>
    rw [basis_eq_ofGaussianInt, basis_eq_ofGaussianInt]
  rw [← map_neg, ← map_add]
  congr
  with_unfolding_all decide

lemma dualLeftMetric_eq_ofGaussianInt : εL' =
    ofGaussianInt (c := ![Color.downL, Color.downL]) fun f =>
    if f = (fun | 0 => (0 : Fin 2) | 1 => (1 : Fin 2)) then 1 else
    if f = (fun | 0 => (1 : Fin 2) | 1 => (0 : Fin 2)) then - 1 else 0 := by
  rw [dualLeftMetric_eq_basis]
  conv_lhs =>
    rw [basis_eq_ofGaussianInt, basis_eq_ofGaussianInt]
  rw [← map_sub]
  congr
  with_unfolding_all decide

lemma rightMetric_eq_ofGaussianInt : εR =
    ofGaussianInt (c := ![Color.upR, Color.upR]) fun f =>
    if f = (fun | 0 => (0 : Fin 2) | 1 => (1 : Fin 2)) then - 1 else
    if f = (fun | 0 => (1 : Fin 2) | 1 => (0 : Fin 2)) then 1 else 0 := by
  rw [rightMetric_eq_basis]
  conv_lhs =>
    rw [basis_eq_ofGaussianInt, basis_eq_ofGaussianInt]
  rw [← map_neg, ← map_add]
  congr
  with_unfolding_all decide

lemma dualRightMetric_eq_ofGaussianInt : εR' =
    ofGaussianInt (c := ![Color.downR, Color.downR]) fun f =>
    if f = (fun | 0 => (0 : Fin 2) | 1 => (1 : Fin 2)) then 1 else
    if f = (fun | 0 => (1 : Fin 2) | 1 => (0 : Fin 2)) then - 1 else 0 := by
  rw [dualRightMetric_eq_basis]
  conv_lhs =>
    rw [basis_eq_ofGaussianInt, basis_eq_ofGaussianInt]
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

/-- The tensor `dualLeftMetric` is invariant under the action of `SL(2,ℂ)`. -/
lemma actionT_dualLeftMetric (g : SL(2,ℂ)) : g • εL' = εL' := by
  rw [metricTensor_invariant]

/-- The tensor `dualRightMetric` is invariant under the action of `SL(2,ℂ)`. -/
lemma actionT_dualRightMetric (g : SL(2,ℂ)) : g • εR' = εR' := by
  rw [metricTensor_invariant]

end complexLorentzTensor
