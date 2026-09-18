/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.OfRat
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
    (c1 := .down) (c2 := .down) Lorentz.coMetric := by
  rw [Lorentz.coMetric]
  rfl

lemma contrMetric_eq_fromConstPair : η = fromConstPair (S := complexLorentzTensor)
    (c1 := .up) (c2 := .up) Lorentz.contrMetric := by
  rw [Lorentz.contrMetric]
  rfl

lemma leftMetric_eq_fromConstPair : εL = fromConstPair Fermion.leftMetric := rfl

lemma rightMetric_eq_fromConstPair : εR = fromConstPair Fermion.rightMetric := rfl

lemma dualLeftMetric_eq_fromConstPair : εL' = fromConstPair Fermion.dualLeftMetric := rfl

lemma dualRightMetric_eq_fromConstPair : εR' = fromConstPair Fermion.dualRightMetric := rfl

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

lemma dualLeftMetric_eq_fromPairT : εL' = fromPairT (Fermion.dualLeftMetricVal) := by
  rw [dualLeftMetric_eq_fromConstPair, fromConstPair]
  congr 1
  exact Fermion.dualLeftMetric_apply_one

lemma dualRightMetric_eq_fromPairT : εR' = fromPairT (Fermion.dualRightMetricVal) := by
  rw [dualRightMetric_eq_fromConstPair, fromConstPair]
  congr 1
  exact Fermion.dualRightMetric_apply_one

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
lemma leftMetric_eq_leftHandedWeyl_basis : εL =
    - fromPairT (LeftHandedWeyl.basis 0 ⊗ₜ[ℂ] LeftHandedWeyl.basis 1)
    + fromPairT (LeftHandedWeyl.basis 1 ⊗ₜ[ℂ] LeftHandedWeyl.basis 0) := by
  rw [leftMetric_eq_fromPairT, leftMetricVal_expand_tmul]
  simp

open Fermion in
lemma dualLeftMetric_eq_dualLeftHandedWeyl_basis : εL' =
    fromPairT (DualLeftHandedWeyl.basis 0 ⊗ₜ[ℂ] DualLeftHandedWeyl.basis 1)
    - fromPairT (DualLeftHandedWeyl.basis 1 ⊗ₜ[ℂ] DualLeftHandedWeyl.basis 0) := by
  rw [dualLeftMetric_eq_fromPairT, dualLeftMetricVal_expand_tmul]
  simp

open Fermion in
lemma rightMetric_eq_rightHandedWeyl_basis : εR =
    - fromPairT (RightHandedWeyl.basis 0 ⊗ₜ[ℂ] RightHandedWeyl.basis 1)
    + fromPairT (RightHandedWeyl.basis 1 ⊗ₜ[ℂ] RightHandedWeyl.basis 0) := by
  rw [rightMetric_eq_fromPairT, rightMetricVal_expand_tmul]
  simp

open Fermion in
lemma dualRightMetric_eq_dualRightHandedWeyl_basis : εR' =
    fromPairT (DualRightHandedWeyl.basis 0 ⊗ₜ[ℂ] DualRightHandedWeyl.basis 1)
    - fromPairT (DualRightHandedWeyl.basis 1 ⊗ₜ[ℂ] DualRightHandedWeyl.basis 0) := by
  rw [dualRightMetric_eq_fromPairT, dualRightMetricVal_expand_tmul]
  simp

/-!

### basis

-/

open Lorentz in
lemma coMetric_eq_basis : η' =
    (Tensor.basis (S := complexLorentzTensor) ![Color.down, Color.down]
      (fun | 0 => (0 : Fin 4) | 1 => (0 : Fin 4)))
    - (Tensor.basis (S := complexLorentzTensor) ![Color.down, Color.down]
      (fun | 0 => (1 : Fin 4) | 1 => (1 : Fin 4)))
    - (Tensor.basis (S := complexLorentzTensor) ![Color.down, Color.down]
      (fun | 0 => (2 : Fin 4) | 1 => (2 : Fin 4)))
    - (Tensor.basis (S := complexLorentzTensor) ![Color.down, Color.down]
      (fun | 0 => (3 : Fin 4) | 1 => (3 : Fin 4))) := by
  rw [coMetric_eq_complexCoBasisFin4]
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
      (fun | 0 => (0 : Fin 4) | 1 => (0 : Fin 4)))
    - (Tensor.basis (S := complexLorentzTensor) ![Color.up, Color.up]
      (fun | 0 => (1 : Fin 4) | 1 => (1 : Fin 4)))
    - (Tensor.basis (S := complexLorentzTensor) ![Color.up, Color.up]
      (fun | 0 => (2 : Fin 4) | 1 => (2 : Fin 4)))
    - (Tensor.basis (S := complexLorentzTensor) ![Color.up, Color.up]
      (fun | 0 => (3 : Fin 4) | 1 => (3 : Fin 4))) := by
  have h : ∀ i : Fin 4, fromPairT (complexContrBasisFin4 i ⊗ₜ[ℂ] complexContrBasisFin4 i) =
      Tensor.basis (S := complexLorentzTensor) ![Color.up, Color.up]
        (fun | 0 => i | 1 => i) := fun i => by
    change fromPairT ((complexLorentzTensor.basis .up i) ⊗ₜ[ℂ] (complexLorentzTensor.basis .up i))
    rw [fromPairT_apply_basis_repr]
  rw [contrMetric_eq_complexContrBasisFin4, h, h, h, h]

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

### ofRat

-/

set_option backward.isDefEq.respectTransparency false in
lemma coMetric_eq_ofRat : η' = ofRat fun f =>
    if f 0 = Fin.cast (by rfl) (0 : Fin 4) ∧ f 1 = Fin.cast (by rfl) (0 : Fin 4) then 1 else
    if f 0 = f 1 then - 1 else 0 := by
  rw [coMetric_eq_basis]
  conv_lhs =>
    rw [basis_eq_ofRat, basis_eq_ofRat, basis_eq_ofRat, basis_eq_ofRat]
  rw [← map_sub, ← map_sub, ← map_sub]
  congr
  with_unfolding_all decide

set_option backward.isDefEq.respectTransparency false in
lemma contrMetric_eq_ofRat : η = ofRat fun f =>
    if f 0 = Fin.cast (by rfl) (0 : Fin 4) ∧ f 1 = Fin.cast (by rfl) (0 : Fin 4) then 1 else
    if f 0 = f 1 then - 1 else 0 := by
  rw [contrMetric_eq_basis]
  conv_lhs =>
    rw [basis_eq_ofRat, basis_eq_ofRat, basis_eq_ofRat, basis_eq_ofRat]
  rw [← map_sub, ← map_sub, ← map_sub]
  congr
  with_unfolding_all decide

lemma leftMetric_eq_ofRat : εL = ofRat fun f =>
    if f 0 = Fin.cast (by rfl) (0 : Fin 2) ∧ f 1 = Fin.cast (by rfl) (1 : Fin 2) then - 1 else
    if f 1 = Fin.cast (by rfl) (0 : Fin 2) ∧ f 0 = Fin.cast (by rfl) (1 : Fin 2) then
      1 else 0 := by
  rw [leftMetric_eq_basis]
  conv_lhs =>
    rw [basis_eq_ofRat, basis_eq_ofRat]
  rw [← map_neg, ← map_add]
  congr
  with_unfolding_all decide

lemma dualLeftMetric_eq_ofRat : εL' = ofRat fun f =>
    if f 0 = Fin.cast (by rfl) (0 : Fin 2) ∧ f 1 = Fin.cast (by rfl) (1 : Fin 2) then 1 else
    if f 1 = Fin.cast (by rfl) (0 : Fin 2) ∧ f 0 = Fin.cast (by rfl) (1 : Fin 2) then
      - 1 else 0 := by
  rw [dualLeftMetric_eq_basis]
  conv_lhs =>
    rw [basis_eq_ofRat, basis_eq_ofRat]
  rw [← map_sub]
  congr
  with_unfolding_all decide

lemma rightMetric_eq_ofRat : εR = ofRat fun f =>
    if f 0 = Fin.cast (by rfl) (0 : Fin 2) ∧ f 1 = Fin.cast (by rfl) (1 : Fin 2) then - 1 else
    if f 1 = Fin.cast (by rfl) (0 : Fin 2) ∧ f 0 = Fin.cast (by rfl) (1 : Fin 2) then 1 else 0 := by
  rw [rightMetric_eq_basis]
  conv_lhs =>
    rw [basis_eq_ofRat, basis_eq_ofRat]
  rw [← map_neg, ← map_add]
  congr
  with_unfolding_all decide

lemma dualRightMetric_eq_ofRat : εR' = ofRat fun f =>
    if f 0 = Fin.cast (by rfl) (0 : Fin 2) ∧ f 1 = Fin.cast (by rfl) (1 : Fin 2) then 1 else
    if f 1 = Fin.cast (by rfl) (0 : Fin 2) ∧ f 0 = Fin.cast (by rfl) (1 : Fin 2) then
      - 1 else 0 := by
  rw [dualRightMetric_eq_basis]
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

/-- The tensor `dualLeftMetric` is invariant under the action of `SL(2,ℂ)`. -/
lemma actionT_dualLeftMetric (g : SL(2,ℂ)) : g • εL' = εL' := by
  rw [metricTensor_invariant]

/-- The tensor `dualRightMetric` is invariant under the action of `SL(2,ℂ)`. -/
lemma actionT_dualRightMetric (g : SL(2,ℂ)) : g • εR' = εR' := by
  rw [metricTensor_invariant]

end complexLorentzTensor
