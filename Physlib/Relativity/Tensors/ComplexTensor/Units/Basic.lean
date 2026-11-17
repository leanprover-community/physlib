/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.OfGaussianInt
/-!

## Unit tensors for complex Lorentz tensors

-/

@[expose] public section

open Matrix
open MatrixGroups
open Complex
open TensorProduct
noncomputable section

namespace complexLorentzTensor
open Fermion
open TensorSpecies
open Tensor
/-!

## Definitions.

-/

/-- The unit `δᵢⁱ` as a complex Lorentz tensor. -/
abbrev coContrUnit : ℂT[.down, .up] := complexLorentzTensor.unitTensor Color.up

/-- The unit `δⁱᵢ` as a complex Lorentz tensor. -/
abbrev contrCoUnit : ℂT[.up, .down] := complexLorentzTensor.unitTensor Color.down

/-- The unit `δₐᵃ` as a complex Lorentz tensor. -/
abbrev dualLeftLeftUnit : ℂT[.downL, .upL] := complexLorentzTensor.unitTensor Color.upL

/-- The unit `δᵃₐ` as a complex Lorentz tensor. -/
abbrev leftDualLeftUnit : ℂT[.upL, .downL] := complexLorentzTensor.unitTensor Color.downL

/-- The unit `δ_{dot a}^{dot a}` as a complex Lorentz tensor. -/
abbrev dualRightRightUnit : ℂT[.downR, .upR] := complexLorentzTensor.unitTensor Color.upR

/-- The unit `δ^{dot a}_{dot a}` as a complex Lorentz tensor. -/
abbrev rightDualRightUnit : ℂT[.upR, .downR] := complexLorentzTensor.unitTensor Color.downR

/-!

## Notation

-/

/-- The unit `δᵢⁱ` as a complex Lorentz tensor. -/
scoped[complexLorentzTensor] notation "δ'" => coContrUnit

/-- The unit `δⁱᵢ` as a complex Lorentz tensor. -/
scoped[complexLorentzTensor] notation "δ" => contrCoUnit

/-- The unit `δₐᵃ` as a complex Lorentz tensor. -/
scoped[complexLorentzTensor] notation "δL'" => dualLeftLeftUnit

/-- The unit `δᵃₐ` as a complex Lorentz tensor. -/
scoped[complexLorentzTensor] notation "δL" => leftDualLeftUnit

/-- The unit `δ_{dot a}^{dot a}` as a complex Lorentz tensor. -/
scoped[complexLorentzTensor] notation "δR'" => dualRightRightUnit

/-- The unit `δ^{dot a}_{dot a}` as a complex Lorentz tensor. -/
scoped[complexLorentzTensor] notation "δR" => rightDualRightUnit

/-!

## Other forms

-/

/-!

### fromConstPair

-/

lemma coContrUnit_eq_fromConstPair : δ' = fromConstPair Lorentz.ComplexVector.unit := by
  rw [Lorentz.ComplexVector.unit]
  rfl

lemma contrCoUnit_eq_fromConstPair : δ = fromConstPair Lorentz.ComplexCoVector.unit := by
  rw [Lorentz.ComplexCoVector.unit]
  rfl

lemma dualLeftLeftUnit_eq_fromConstPair : δL' = fromConstPair Fermion.LeftHandedWeyl.unit := by
  rw [Fermion.LeftHandedWeyl.unit]
  rfl

lemma leftDualLeftUnit_eq_fromConstPair : δL = fromConstPair Fermion.DualLeftHandedWeyl.unit := by
  rw [Fermion.DualLeftHandedWeyl.unit]
  rfl

lemma dualRightRightUnit_eq_fromConstPair : δR' = fromConstPair Fermion.RightHandedWeyl.unit := by
  rw [Fermion.RightHandedWeyl.unit]
  rfl

lemma rightDualRightUnit_eq_fromConstPair :
    δR = fromConstPair Fermion.DualRightHandedWeyl.unit := by
  rw [Fermion.DualRightHandedWeyl.unit]
  rfl

/-!

### fromPairT

-/

lemma coContrUnit_eq_fromPairT : δ' = fromPairT (Lorentz.ComplexVector.unitVal) := by
  rw [coContrUnit_eq_fromConstPair, fromConstPair]
  congr 1
  exact Lorentz.ComplexVector.unit_apply_one

lemma contrCoUnit_eq_fromPairT : δ = fromPairT (Lorentz.ComplexCoVector.unitVal) := by
  rw [contrCoUnit_eq_fromConstPair, fromConstPair]
  congr 1
  exact Lorentz.ComplexCoVector.unit_apply_one

lemma dualLeftLeftUnit_eq_fromPairT : δL' = fromPairT (Fermion.LeftHandedWeyl.unitVal) := by
  rw [dualLeftLeftUnit_eq_fromConstPair, fromConstPair]
  congr 1
  exact Fermion.LeftHandedWeyl.unit_apply_one

lemma leftDualLeftUnit_eq_fromPairT : δL = fromPairT (Fermion.DualLeftHandedWeyl.unitVal) := by
  rw [leftDualLeftUnit_eq_fromConstPair, fromConstPair]
  congr 1
  exact Fermion.DualLeftHandedWeyl.unit_apply_one

lemma dualRightRightUnit_eq_fromPairT : δR' = fromPairT (Fermion.RightHandedWeyl.unitVal) := by
  rw [dualRightRightUnit_eq_fromConstPair, fromConstPair]
  congr 1
  exact Fermion.RightHandedWeyl.unit_apply_one

lemma rightDualRightUnit_eq_fromPairT : δR = fromPairT (Fermion.DualRightHandedWeyl.unitVal) := by
  rw [rightDualRightUnit_eq_fromConstPair, fromConstPair]
  congr 1
  exact Fermion.DualRightHandedWeyl.unit_apply_one

/-!

### ComplexCoVector.basis etc.

-/

open Lorentz in
lemma coContrUnit_eq_complexCoVector_basis_complexVector_basis : δ' =
    ∑ i, fromPairT (ComplexCoVector.basis i ⊗ₜ[ℂ] ComplexVector.basis i) := by
  rw [coContrUnit_eq_fromPairT, ComplexVector.unitVal_expand_tmul]
  rfl

open Lorentz in
lemma coContrUnit_eq_complexCoVector_basisFin4_complexVector_basisFin4 : δ' =
    ∑ i, fromPairT (ComplexCoVector.basisFin4 i ⊗ₜ[ℂ] ComplexVector.basisFin4 i) := by
  rw [coContrUnit_eq_complexCoVector_basis_complexVector_basis]
  rw [← finSumFinEquiv.symm.sum_comp]
  simp [ComplexCoVector.basisFin4, ComplexVector.basisFin4]

open Lorentz in
lemma contrCoUnit_eq_complexVector_basis_complexCoVector_basis : δ =
    ∑ i, fromPairT (ComplexVector.basis i ⊗ₜ[ℂ] ComplexCoVector.basis i) := by
  rw [contrCoUnit_eq_fromPairT, ComplexCoVector.unitVal_expand_tmul]
  rfl

open Lorentz in
lemma contrCoUnit_eq_complexVector_basisFin4_complexCoVector_basisFin4 : δ =
    ∑ i, fromPairT (ComplexVector.basisFin4 i ⊗ₜ[ℂ] ComplexCoVector.basisFin4 i) := by
  rw [contrCoUnit_eq_complexVector_basis_complexCoVector_basis]
  rw [← finSumFinEquiv.symm.sum_comp]
  simp [ComplexVector.basisFin4, ComplexCoVector.basisFin4]

open Fermion in
lemma dualLeftLeftUnit_eq_basis : δL' =
    ∑ i, fromPairT (DualLeftHandedWeyl.basis i ⊗ₜ[ℂ] LeftHandedWeyl.basis i) := by
  rw [dualLeftLeftUnit_eq_fromPairT, LeftHandedWeyl.unitVal_expand_tmul]
  rfl

open Fermion in
lemma leftDualLeftUnit_eq_basis : δL =
    ∑ i, fromPairT (LeftHandedWeyl.basis i ⊗ₜ[ℂ] DualLeftHandedWeyl.basis i) := by
  rw [leftDualLeftUnit_eq_fromPairT, DualLeftHandedWeyl.unitVal_expand_tmul]
  rfl

open Fermion in
lemma dualRightRightUnit_eq_basis : δR' =
    ∑ i, fromPairT (DualRightHandedWeyl.basis i ⊗ₜ[ℂ] RightHandedWeyl.basis i) := by
  rw [dualRightRightUnit_eq_fromPairT, RightHandedWeyl.unitVal_expand_tmul]
  rfl

open Fermion in
lemma rightDualRightUnit_eq_basis : δR =
    ∑ i, fromPairT (RightHandedWeyl.basis i ⊗ₜ[ℂ] DualRightHandedWeyl.basis i) := by
  rw [rightDualRightUnit_eq_fromPairT, DualRightHandedWeyl.unitVal_expand_tmul]
  rfl

/-!

### basis

-/

lemma coContrUnit_eq_basis : δ' =
    ∑ i, Tensor.basis (S := complexLorentzTensor)
      ![Color.down, Color.up] (fun | 0 => i | 1 => i) := by
  rw [coContrUnit_eq_complexCoVector_basis_complexVector_basis]
  conv_lhs =>
    enter [2, x]
    change fromPairT ((complexLorentzTensor.basis .down x) ⊗ₜ[ℂ]
      (complexLorentzTensor.basis .up _))
    rw [fromPairT_apply_basis_repr]
  rfl

lemma contrCoUnit_eq_basis : δ =
    ∑ i, Tensor.basis (S := complexLorentzTensor)
      ![Color.up, Color.down] (fun | 0 => i | 1 => i) := by
  rw [contrCoUnit_eq_complexVector_basis_complexCoVector_basis]
  conv_lhs =>
    enter [2, x]
    change fromPairT ((complexLorentzTensor.basis .up x) ⊗ₜ[ℂ]
      (complexLorentzTensor.basis .down _))
    rw [fromPairT_apply_basis_repr]
  rfl

lemma dualLeftLeftUnit_eq_tensor_basis : δL' =
    ∑ i, Tensor.basis (S := complexLorentzTensor)
      ![Color.downL, Color.upL] (fun | 0 => i | 1 => i) := by
  rw [dualLeftLeftUnit_eq_basis]
  conv_lhs =>
    enter [2, x]
    change fromPairT ((complexLorentzTensor.basis .downL x) ⊗ₜ[ℂ]
      (complexLorentzTensor.basis .upL _))
    rw [fromPairT_apply_basis_repr]
  rfl

lemma leftDualLeftUnit_eq_tensor_basis : δL =
    ∑ i, Tensor.basis (S := complexLorentzTensor)
      ![Color.upL, Color.downL] (fun | 0 => i | 1 => i) := by
  rw [leftDualLeftUnit_eq_basis]
  conv_lhs =>
    enter [2, x]
    change fromPairT ((complexLorentzTensor.basis .upL x) ⊗ₜ[ℂ]
      (complexLorentzTensor.basis .downL _))
    rw [fromPairT_apply_basis_repr]
  rfl

lemma dualRightRightUnit_eq_tensor_basis : δR' =
    ∑ i, Tensor.basis (S := complexLorentzTensor)
      ![Color.downR, Color.upR] (fun | 0 => i | 1 => i) := by
  rw [dualRightRightUnit_eq_basis]
  conv_lhs =>
    enter [2, x]
    change fromPairT ((complexLorentzTensor.basis .downR x) ⊗ₜ[ℂ]
      (complexLorentzTensor.basis .upR _))
    rw [fromPairT_apply_basis_repr]
  rfl

lemma rightDualRightUnit_eq_tensor_basis : δR =
    ∑ i, Tensor.basis (S := complexLorentzTensor)
      ![Color.upR, Color.downR] (fun | 0 => i | 1 => i) := by
  rw [rightDualRightUnit_eq_basis]
  conv_lhs =>
    enter [2, x]
    change fromPairT ((complexLorentzTensor.basis .upR x) ⊗ₜ[ℂ]
      (complexLorentzTensor.basis .downR _))
    rw [fromPairT_apply_basis_repr]
  rfl

/-!

### ofGaussianInt

-/

set_option backward.isDefEq.respectTransparency false in
lemma coContrUnit_eq_ofGaussianInt : δ' = ofGaussianInt fun f =>
    if f 0 = f 1 then 1 else 0 := by
  rw [coContrUnit_eq_basis]
  conv_lhs =>
    enter [2, x]
    rw [basis_eq_ofGaussianInt]
  rw [← map_sum]
  congr
  with_unfolding_all decide

set_option backward.isDefEq.respectTransparency false in
lemma contrCoUnit_eq_ofGaussianInt : δ = ofGaussianInt fun f =>
    if f 0 = f 1 then 1 else 0 := by
  rw [contrCoUnit_eq_basis]
  conv_lhs =>
    enter [2, x]
    rw [basis_eq_ofGaussianInt]
  rw [← map_sum]
  congr
  with_unfolding_all decide

set_option backward.isDefEq.respectTransparency false in
lemma dualLeftLeftUnit_eq_ofGaussianInt : δL' = ofGaussianInt fun f =>
    if f 0 = f 1 then 1 else 0 := by
  rw [dualLeftLeftUnit_eq_tensor_basis]
  conv_lhs =>
    enter [2, x]
    rw [basis_eq_ofGaussianInt]
  rw [← map_sum]
  congr
  with_unfolding_all decide

set_option backward.isDefEq.respectTransparency false in
lemma leftDualLeftUnit_eq_ofGaussianInt : δL = ofGaussianInt fun f =>
    if f 0 = f 1 then 1 else 0 := by
  rw [leftDualLeftUnit_eq_tensor_basis]
  conv_lhs =>
    enter [2, x]
    rw [basis_eq_ofGaussianInt]
  rw [← map_sum]
  congr
  with_unfolding_all decide

set_option backward.isDefEq.respectTransparency false in
lemma dualRightRightUnit_eq_ofGaussianInt : δR' = ofGaussianInt fun f =>
    if f 0 = f 1 then 1 else 0 := by
  rw [dualRightRightUnit_eq_tensor_basis]
  conv_lhs =>
    enter [2, x]
    rw [basis_eq_ofGaussianInt]
  rw [← map_sum]
  congr
  with_unfolding_all decide

set_option backward.isDefEq.respectTransparency false in
lemma rightDualRightUnit_eq_ofGaussianInt : δR = ofGaussianInt fun f =>
    if f 0 = f 1 then 1 else 0 := by
  rw [rightDualRightUnit_eq_tensor_basis]
  conv_lhs =>
    enter [2, x]
    rw [basis_eq_ofGaussianInt]
  rw [← map_sum]
  congr
  with_unfolding_all decide

/-!

## Group actions

-/

set_option backward.isDefEq.respectTransparency false in
/-- The tensor `coContrUnit` is invariant under the action of `SL(2,ℂ)`. -/
lemma actionT_coContrUnit (g : SL(2,ℂ)) : g • δ' = δ' := by
  rw [unitTensor_invariant]

set_option backward.isDefEq.respectTransparency false in
/-- The tensor `contrCoUnit` is invariant under the action of `SL(2,ℂ)`. -/
lemma actionT_contrCoUnit (g : SL(2,ℂ)) : g • δ = δ := by
  rw [unitTensor_invariant]

set_option backward.isDefEq.respectTransparency false in
/-- The tensor `dualLeftLeftUnit` is invariant under the action of `SL(2,ℂ)`. -/
lemma actionT_dualLeftLeftUnit (g : SL(2,ℂ)) : g • δL' = δL' := by
  rw [unitTensor_invariant]

set_option backward.isDefEq.respectTransparency false in
/-- The tensor `leftDualLeftUnit` is invariant under the action of `SL(2,ℂ)`. -/
lemma actionT_leftDualLeftUnit (g : SL(2,ℂ)) : g • δL = δL := by
  rw [unitTensor_invariant]

set_option backward.isDefEq.respectTransparency false in
/-- The tensor `dualRightRightUnit` is invariant under the action of `SL(2,ℂ)`. -/
lemma actionT_dualRightRightUnit (g : SL(2,ℂ)) : g • δR' = δR' := by
  rw [unitTensor_invariant]

set_option backward.isDefEq.respectTransparency false in
/-- The tensor `rightDualRightUnit` is invariant under the action of `SL(2,ℂ)`. -/
lemma actionT_rightDualRightUnit (g : SL(2,ℂ)) : g • δR = δR := by
  rw [unitTensor_invariant]

end complexLorentzTensor
