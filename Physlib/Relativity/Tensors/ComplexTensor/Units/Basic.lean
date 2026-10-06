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

lemma coContrUnit_eq_fromConstPair : δ' = fromConstPair Lorentz.coContrUnit := by
  rw [Lorentz.coContrUnit]
  rfl

lemma contrCoUnit_eq_fromConstPair : δ = fromConstPair Lorentz.contrCoUnit := by
  rw [Lorentz.contrCoUnit]
  rfl

lemma dualLeftLeftUnit_eq_fromConstPair : δL' = fromConstPair Fermion.dualLeftLeftUnit := by
  rw [Fermion.dualLeftLeftUnit]
  rfl

lemma leftDualLeftUnit_eq_fromConstPair : δL = fromConstPair Fermion.leftDualLeftUnit := by
  rw [Fermion.leftDualLeftUnit]
  rfl

lemma dualRightRightUnit_eq_fromConstPair : δR' = fromConstPair Fermion.dualRightRightUnit := by
  rw [Fermion.dualRightRightUnit]
  rfl

lemma rightDualRightUnit_eq_fromConstPair : δR = fromConstPair Fermion.rightDualRightUnit := by
  rw [Fermion.rightDualRightUnit]
  rfl

/-!

### fromPairT

-/

lemma coContrUnit_eq_fromPairT : δ' = fromPairT (Lorentz.coContrUnitVal) := by
  rw [coContrUnit_eq_fromConstPair, fromConstPair]
  congr 1
  exact Lorentz.coContrUnit_apply_one

lemma contrCoUnit_eq_fromPairT : δ = fromPairT (Lorentz.contrCoUnitVal) := by
  rw [contrCoUnit_eq_fromConstPair, fromConstPair]
  congr 1
  exact Lorentz.contrCoUnit_apply_one

lemma dualLeftLeftUnit_eq_fromPairT : δL' = fromPairT (Fermion.dualLeftLeftUnitVal) := by
  rw [dualLeftLeftUnit_eq_fromConstPair, fromConstPair]
  congr 1
  exact Fermion.dualLeftLeftUnit_apply_one

lemma leftDualLeftUnit_eq_fromPairT : δL = fromPairT (Fermion.leftDualLeftUnitVal) := by
  rw [leftDualLeftUnit_eq_fromConstPair, fromConstPair]
  congr 1
  exact Fermion.leftDualLeftUnit_apply_one

lemma dualRightRightUnit_eq_fromPairT : δR' = fromPairT (Fermion.dualRightRightUnitVal) := by
  rw [dualRightRightUnit_eq_fromConstPair, fromConstPair]
  congr 1
  exact Fermion.dualRightRightUnit_apply_one

lemma rightDualRightUnit_eq_fromPairT : δR = fromPairT (Fermion.rightDualRightUnitVal) := by
  rw [rightDualRightUnit_eq_fromConstPair, fromConstPair]
  congr 1
  exact Fermion.rightDualRightUnit_apply_one

/-!

### complexCoBasis etc.

-/

open Lorentz in
lemma coContrUnit_eq_complexCoBasis_complexContrBasis : δ' =
    ∑ i, fromPairT (complexCoBasis i ⊗ₜ[ℂ] complexContrBasis i) := by
  rw [coContrUnit_eq_fromPairT, coContrUnitVal_expand_tmul]
  rfl

open Lorentz in
lemma coContrUnit_eq_complexCoBasisFin4_complexContrBasisFin4 : δ' =
    ∑ i, fromPairT (complexCoBasisFin4 i ⊗ₜ[ℂ] complexContrBasisFin4 i) := by
  rw [coContrUnit_eq_complexCoBasis_complexContrBasis]
  rw [← finSumFinEquiv.symm.sum_comp]
  simp [complexCoBasisFin4, complexContrBasisFin4]

open Lorentz in
lemma contrCoUnit_eq_complexContrBasis_complexCoBasis : δ =
    ∑ i, fromPairT (complexContrBasis i ⊗ₜ[ℂ] complexCoBasis i) := by
  rw [contrCoUnit_eq_fromPairT, contrCoUnitVal_expand_tmul]
  rfl

open Lorentz in
lemma contrCoUnit_eq_complexContrBasisFin4_complexCoBasisFin4 : δ =
    ∑ i, fromPairT (complexContrBasisFin4 i ⊗ₜ[ℂ] complexCoBasisFin4 i) := by
  rw [contrCoUnit_eq_complexContrBasis_complexCoBasis]
  rw [← finSumFinEquiv.symm.sum_comp]
  simp [complexContrBasisFin4, complexCoBasisFin4]

open Fermion in
lemma dualLeftLeftUnit_eq_basis : δL' =
    ∑ i, fromPairT (DualLeftHandedWeyl.basis i ⊗ₜ[ℂ] LeftHandedWeyl.basis i) := by
  rw [dualLeftLeftUnit_eq_fromPairT, dualLeftLeftUnitVal_expand_tmul]
  rfl

open Fermion in
lemma leftDualLeftUnit_eq_basis : δL =
    ∑ i, fromPairT (LeftHandedWeyl.basis i ⊗ₜ[ℂ] DualLeftHandedWeyl.basis i) := by
  rw [leftDualLeftUnit_eq_fromPairT, leftDualLeftUnitVal_expand_tmul]
  rfl

open Fermion in
lemma dualRightRightUnit_eq_basis : δR' =
    ∑ i, fromPairT (DualRightHandedWeyl.basis i ⊗ₜ[ℂ] RightHandedWeyl.basis i) := by
  rw [dualRightRightUnit_eq_fromPairT, dualRightRightUnitVal_expand_tmul]
  rfl

open Fermion in
lemma rightDualRightUnit_eq_basis : δR =
    ∑ i, fromPairT (RightHandedWeyl.basis i ⊗ₜ[ℂ] DualRightHandedWeyl.basis i) := by
  rw [rightDualRightUnit_eq_fromPairT, rightDualRightUnitVal_expand_tmul]
  rfl

/-!

### basis

-/

lemma coContrUnit_eq_basis : δ' =
    ∑ i, Tensor.basis (S := complexLorentzTensor)
      ![Color.down, Color.up] (fun | 0 => i | 1 => i) := by
  rw [coContrUnit_eq_complexCoBasisFin4_complexContrBasisFin4]
  conv_lhs =>
    enter [2, x]
    change fromPairT ((complexLorentzTensor.basis .down x) ⊗ₜ[ℂ]
      (complexLorentzTensor.basis .up _))
    rw [fromPairT_apply_basis_repr]
  rfl

lemma contrCoUnit_eq_basis : δ =
    ∑ i, Tensor.basis (S := complexLorentzTensor)
      ![Color.up, Color.down] (fun | 0 => i | 1 => i) := by
  rw [contrCoUnit_eq_complexContrBasisFin4_complexCoBasisFin4]
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
