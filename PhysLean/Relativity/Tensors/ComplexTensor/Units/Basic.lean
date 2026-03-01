/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.ComplexTensor.OfRat
/-!

## Unit tensors for complex Lorentz tensors

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
abbrev altLeftLeftUnit : ℂT[.downL, .upL] := complexLorentzTensor.unitTensor Color.upL

/-- The unit `δᵃₐ` as a complex Lorentz tensor. -/
abbrev leftAltLeftUnit : ℂT[.upL, .downL] := complexLorentzTensor.unitTensor Color.downL

/-- The unit `δ_{dot a}^{dot a}` as a complex Lorentz tensor. -/
abbrev altRightRightUnit : ℂT[.downR, .upR] := complexLorentzTensor.unitTensor Color.upR

/-- The unit `δ^{dot a}_{dot a}` as a complex Lorentz tensor. -/
abbrev rightAltRightUnit : ℂT[.upR, .downR] := complexLorentzTensor.unitTensor Color.downR

/-!

## Notation

-/

/-- The unit `δᵢⁱ` as a complex Lorentz tensor. -/
scoped[complexLorentzTensor] notation "δ'" => coContrUnit

/-- The unit `δⁱᵢ` as a complex Lorentz tensor. -/
scoped[complexLorentzTensor] notation "δ" => contrCoUnit

/-- The unit `δₐᵃ` as a complex Lorentz tensor. -/
scoped[complexLorentzTensor] notation "δL'" => altLeftLeftUnit

/-- The unit `δᵃₐ` as a complex Lorentz tensor. -/
scoped[complexLorentzTensor] notation "δL" => leftAltLeftUnit

/-- The unit `δ_{dot a}^{dot a}` as a complex Lorentz tensor. -/
scoped[complexLorentzTensor] notation "δR'" => altRightRightUnit

/-- The unit `δ^{dot a}_{dot a}` as a complex Lorentz tensor. -/
scoped[complexLorentzTensor] notation "δR" => rightAltRightUnit

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

lemma altLeftLeftUnit_eq_fromConstPair : δL' = fromConstPair Fermion.altLeftLeftUnit := by
  rw [Fermion.altLeftLeftUnit]
  rfl

lemma leftAltLeftUnit_eq_fromConstPair : δL = fromConstPair Fermion.leftAltLeftUnit := by
  rw [Fermion.leftAltLeftUnit]
  rfl

lemma altRightRightUnit_eq_fromConstPair : δR' = fromConstPair Fermion.altRightRightUnit := by
  rw [Fermion.altRightRightUnit]
  rfl

lemma rightAltRightUnit_eq_fromConstPair : δR = fromConstPair Fermion.rightAltRightUnit := by
  rw [Fermion.rightAltRightUnit]
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

lemma altLeftLeftUnit_eq_fromPairT : δL' = fromPairT (Fermion.altLeftLeftUnitVal) := by
  rw [altLeftLeftUnit_eq_fromConstPair, fromConstPair]
  congr 1
  exact Fermion.altLeftLeftUnit_apply_one

lemma leftAltLeftUnit_eq_fromPairT : δL = fromPairT (Fermion.leftAltLeftUnitVal) := by
  rw [leftAltLeftUnit_eq_fromConstPair, fromConstPair]
  congr 1
  exact Fermion.leftAltLeftUnit_apply_one

lemma altRightRightUnit_eq_fromPairT : δR' = fromPairT (Fermion.altRightRightUnitVal) := by
  rw [altRightRightUnit_eq_fromConstPair, fromConstPair]
  congr 1
  exact Fermion.altRightRightUnit_apply_one

lemma rightAltRightUnit_eq_fromPairT : δR = fromPairT (Fermion.rightAltRightUnitVal) := by
  rw [rightAltRightUnit_eq_fromConstPair, fromConstPair]
  congr 1
  exact Fermion.rightAltRightUnit_apply_one

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
lemma altLeftLeftUnit_eq_altLeftBasis_leftBasis : δL' =
    ∑ i, fromPairT (altLeftBasis i ⊗ₜ[ℂ] leftBasis i) := by
  rw [altLeftLeftUnit_eq_fromPairT, altLeftLeftUnitVal_expand_tmul]
  rfl

open Fermion in
lemma leftAltLeftUnit_eq_leftBasis_altLeftBasis : δL =
    ∑ i, fromPairT (leftBasis i ⊗ₜ[ℂ] altLeftBasis i) := by
  rw [leftAltLeftUnit_eq_fromPairT, leftAltLeftUnitVal_expand_tmul]
  rfl

open Fermion in
lemma altRightRightUnit_eq_altRightBasis_rightBasis : δR' =
    ∑ i, fromPairT (altRightBasis i ⊗ₜ[ℂ] rightBasis i) := by
  rw [altRightRightUnit_eq_fromPairT, altRightRightUnitVal_expand_tmul]
  rfl

open Fermion in
lemma rightAltRightUnit_eq_rightBasis_altRightBasis : δR =
    ∑ i, fromPairT (rightBasis i ⊗ₜ[ℂ] altRightBasis i) := by
  rw [rightAltRightUnit_eq_fromPairT, rightAltRightUnitVal_expand_tmul]
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

lemma altLeftLeftUnit_eq_basis : δL' =
    ∑ i, Tensor.basis (S := complexLorentzTensor)
      ![Color.downL, Color.upL] (fun | 0 => i | 1 => i) := by
  rw [altLeftLeftUnit_eq_altLeftBasis_leftBasis]
  conv_lhs =>
    enter [2, x]
    change fromPairT ((complexLorentzTensor.basis .downL x) ⊗ₜ[ℂ]
      (complexLorentzTensor.basis .upL _))
    rw [fromPairT_apply_basis_repr]
  rfl

lemma leftAltLeftUnit_eq_basis : δL =
    ∑ i, Tensor.basis (S := complexLorentzTensor)
      ![Color.upL, Color.downL] (fun | 0 => i | 1 => i) := by
  rw [leftAltLeftUnit_eq_leftBasis_altLeftBasis]
  conv_lhs =>
    enter [2, x]
    change fromPairT ((complexLorentzTensor.basis .upL x) ⊗ₜ[ℂ]
      (complexLorentzTensor.basis .downL _))
    rw [fromPairT_apply_basis_repr]
  rfl

lemma altRightRightUnit_eq_basis : δR' =
    ∑ i, Tensor.basis (S := complexLorentzTensor)
      ![Color.downR, Color.upR] (fun | 0 => i | 1 => i) := by
  rw [altRightRightUnit_eq_altRightBasis_rightBasis]
  conv_lhs =>
    enter [2, x]
    change fromPairT ((complexLorentzTensor.basis .downR x) ⊗ₜ[ℂ]
      (complexLorentzTensor.basis .upR _))
    rw [fromPairT_apply_basis_repr]
  rfl

lemma rightAltRightUnit_eq_basis : δR =
    ∑ i, Tensor.basis (S := complexLorentzTensor)
      ![Color.upR, Color.downR] (fun | 0 => i | 1 => i) := by
  rw [rightAltRightUnit_eq_rightBasis_altRightBasis]
  conv_lhs =>
    enter [2, x]
    change fromPairT ((complexLorentzTensor.basis .upR x) ⊗ₜ[ℂ]
      (complexLorentzTensor.basis .downR _))
    rw [fromPairT_apply_basis_repr]
  rfl

/-!

### ofRat

-/

lemma coContrUnit_eq_ofRat : δ' = ofRat fun f =>
    if f 0 = f 1 then 1 else 0 := by
  rw [coContrUnit_eq_basis]
  conv_lhs =>
    enter [2, x]
    rw [basis_eq_ofRat]
  rw [← map_sum]
  congr
  with_unfolding_all decide

lemma contrCoUnit_eq_ofRat : δ = ofRat fun f =>
    if f 0 = f 1 then 1 else 0 := by
  rw [contrCoUnit_eq_basis]
  conv_lhs =>
    enter [2, x]
    rw [basis_eq_ofRat]
  rw [← map_sum]
  congr
  with_unfolding_all decide

lemma altLeftLeftUnit_eq_ofRat : δL' = ofRat fun f =>
    if f 0 = f 1 then 1 else 0 := by
  rw [altLeftLeftUnit_eq_basis]
  conv_lhs =>
    enter [2, x]
    rw [basis_eq_ofRat]
  rw [← map_sum]
  congr
  with_unfolding_all decide

lemma leftAltLeftUnit_eq_ofRat : δL = ofRat fun f =>
    if f 0 = f 1 then 1 else 0 := by
  rw [leftAltLeftUnit_eq_basis]
  conv_lhs =>
    enter [2, x]
    rw [basis_eq_ofRat]
  rw [← map_sum]
  congr
  with_unfolding_all decide

lemma altRightRightUnit_eq_ofRat : δR' = ofRat fun f =>
    if f 0 = f 1 then 1 else 0 := by
  rw [altRightRightUnit_eq_basis]
  conv_lhs =>
    enter [2, x]
    rw [basis_eq_ofRat]
  rw [← map_sum]
  congr
  with_unfolding_all decide

lemma rightAltRightUnit_eq_ofRat : δR = ofRat fun f =>
    if f 0 = f 1 then 1 else 0 := by
  rw [rightAltRightUnit_eq_basis]
  conv_lhs =>
    enter [2, x]
    rw [basis_eq_ofRat]
  rw [← map_sum]
  congr
  with_unfolding_all decide

/-!

## Group actions

-/

/-- The tensor `coContrUnit` is invariant under the action of `SL(2,ℂ)`. -/
lemma actionT_coContrUnit (g : SL(2,ℂ)) : g • δ' = δ' := by
  rw [unitTensor_invariant]

/-- The tensor `contrCoUnit` is invariant under the action of `SL(2,ℂ)`. -/
lemma actionT_contrCoUnit (g : SL(2,ℂ)) : g • δ = δ := by
  rw [unitTensor_invariant]

/-- The tensor `altLeftLeftUnit` is invariant under the action of `SL(2,ℂ)`. -/
lemma actionT_altLeftLeftUnit (g : SL(2,ℂ)) : g • δL' = δL' := by
  rw [unitTensor_invariant]

/-- The tensor `leftAltLeftUnit` is invariant under the action of `SL(2,ℂ)`. -/
lemma actionT_leftAltLeftUnit (g : SL(2,ℂ)) : g • δL = δL := by
  rw [unitTensor_invariant]

/-- The tensor `altRightRightUnit` is invariant under the action of `SL(2,ℂ)`. -/
lemma actionT_altRightRightUnit (g : SL(2,ℂ)) : g • δR' = δR' := by
  rw [unitTensor_invariant]

/-- The tensor `rightAltRightUnit` is invariant under the action of `SL(2,ℂ)`. -/
lemma actionT_rightAltRightUnit (g : SL(2,ℂ)) : g • δR = δR := by
  rw [unitTensor_invariant]

end complexLorentzTensor
