/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Relativity.PauliMatrices.ToTensor
public import PhysLean.Relativity.Tensors.ComplexTensor.Units.Basic
/-!

## Contraction of indices of Pauli matrix.

The main result of this file is `pauliMatrix_contract_pauliMatrix` which states that
`η_{μν} σ^{μ α dot β} σ^{ν α' dot β'} = 2 ε^{αα'} ε^{dot β dot β'}`.

The current way this result is proved is by using tensor tree manipulations.
There is likely a more direct path to this result.

-/

@[expose] public section
open IndexNotation
open CategoryTheory
open MonoidalCategory
open Matrix
open TensorProduct
open CategoryTheory

namespace PauliMatrix
open Fermion
open complexLorentzTensor
open TensorSpecies
open Tensor

/-- The statement that ` σᵥᵃᵇ σᵛᵃ'ᵇ' = 2 εᵃᵃ' εᵇᵇ'`. -/
lemma pauliCo_contr_pauliContr :
    {σ_^^ | ν α β ⊗ σ^^^ | ν α' β' = (2 : ℂ) •ₜ εL | α α' ⊗ εR | β β'}ᵀ := by
  apply (Tensor.basis _).repr.injective
  ext b
  simp only [Tensorial.self_toTensor_apply]
  conv_rhs =>
    rw [permT_basis_repr_symm_apply]
    rw [_root_.map_smul]
    simp only [Nat.reduceAdd, Nat.succ_eq_add_one, Fin.isValue, Fin.succAbove_zero,
      Function.comp_apply, OverColor.mk_hom, OverColor.equivToHomEq_toEquiv, Finsupp.coe_smul,
      Pi.smul_apply, smul_eq_mul]
    rw (transparency := .instances) [prodT_basis_repr_apply]
    simp only [Nat.reduceAdd, Nat.succ_eq_add_one, Fin.isValue, Fin.succAbove_zero,
      Function.comp_apply]
    rw [leftMetric_eq_ofRat, rightMetric_eq_ofRat]
    simp only [Nat.reduceAdd, Nat.succ_eq_add_one, Fin.isValue, Fin.succAbove_zero,
      Function.comp_apply, cons_val_zero, cons_val_one, head_cons, ofRat_basis_repr_apply]
    rw [← PhysLean.RatComplexNum.toComplexNum.map_mul]
    change (2 : ℕ) * _
    rw [PhysLean.RatComplexNum.ofNat_mul_toComplexNum 2]
  rw [contrT_basis_repr_apply]
  conv_lhs =>
    enter [2, x]
    rw [prodT_basis_repr_apply]
    simp only [pauliCo_eq_ofRat, toTensor_eq_ofRat]
    simp only [Fin.isValue, ofRat_basis_repr_apply, Function.comp_apply, Monoidal.tensorUnit_obj,
      Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
      Action.FunctorCategoryEquivalence.functor_obj_obj, Functor.comp_obj,
      Discrete.functor_obj_eq_as, Fin.cast_eq_self]
    left
    rw [← PhysLean.RatComplexNum.toComplexNum.map_mul]
  conv_lhs =>
    enter [2, x]
    right
    rw (transparency := .instances) [contr_basis_ratComplexNum]
  conv_lhs =>
    enter [2, x]
    rw [← PhysLean.RatComplexNum.toComplexNum.map_mul]
  rw [← map_sum PhysLean.RatComplexNum.toComplexNum]
  apply (Function.Injective.eq_iff PhysLean.RatComplexNum.toComplexNum_injective).mpr
  revert b
  decide +kernel

lemma pauliCoDown_trace_pauliCo : {(σ___ | μ β α ⊗ σ_^^ | ν α β) = (2 •ₜ η' | μ ν)}ᵀ := by
  simp only [Tensorial.self_toTensor_apply]
  conv_lhs =>
    rw [pauliCoDown_eq_ofRat, pauliCo_eq_ofRat, prodT_ofRat_ofRat,
      contrT_ofRat, contrT_ofRat]
  conv_rhs =>
    rw [coMetric_eq_ofRat]
    rw [← map_nsmul]
  apply (Tensor.basis _).repr.injective
  ext b
  conv_rhs => rw [permT_basis_repr_symm_apply]
  simp only [ofRat_basis_repr_apply]
  apply (Function.Injective.eq_iff PhysLean.RatComplexNum.toComplexNum_injective).mpr
  revert b
  decide +kernel

lemma pauliCo_trace_pauliCoDown: {σ_^^ | μ α β ⊗ σ___ | ν β α = 2 •ₜ η' | μ ν}ᵀ := by
  simp only [Tensorial.self_toTensor_apply]
  conv_lhs =>
    rw [pauliCoDown_eq_ofRat, pauliCo_eq_ofRat]
    rw [prodT_ofRat_ofRat,
      contrT_ofRat, contrT_ofRat]
  conv_rhs =>
    rw [coMetric_eq_ofRat]
    rw [← map_nsmul]
  apply (Tensor.basis _).repr.injective
  ext b
  conv_rhs => rw [permT_basis_repr_symm_apply]
  simp only [ofRat_basis_repr_apply]
  apply (Function.Injective.eq_iff PhysLean.RatComplexNum.toComplexNum_injective).mpr
  decide +revert +kernel

lemma pauliContr_mul_pauliContrDown_add :
    {((σ^^^ | μ α β ⊗ σ^__ | ν β α') + (σ^^^ | ν α β ⊗ σ^__ | μ β α')) =
    2 •ₜ η | μ ν ⊗ δL | α α'}ᵀ := by
  simp only [Tensorial.self_toTensor_apply]
  conv_lhs =>
    rw [pauliContrDown_ofRat, toTensor_eq_ofRat, prodT_ofRat_ofRat,
      contrT_ofRat, permT_ofRat, ← map_add]
  conv_rhs =>
    rw [leftAltLeftUnit_eq_ofRat, contrMetric_eq_ofRat, prodT_ofRat_ofRat, ← map_nsmul,
      permT_ofRat]
  apply (Tensor.basis _).repr.injective
  ext b
  simp only [ofRat_basis_repr_apply]
  apply (Function.Injective.eq_iff PhysLean.RatComplexNum.toComplexNum_injective).mpr
  decide +revert +kernel

lemma auliContrDown_pauliContr_mul_add :
    {((σ^__ | μ β α ⊗ σ^^^ | ν α β') + (σ^__ | ν β α ⊗ σ^^^ | μ α β')) =
    2 •ₜ η | μ ν ⊗ δR' | β β'}ᵀ := by
  simp only [Tensorial.self_toTensor_apply]
  conv_lhs =>
    rw [pauliContrDown_ofRat, toTensor_eq_ofRat, prodT_ofRat_ofRat,
      contrT_ofRat, permT_ofRat, ← map_add]
  conv_rhs =>
    rw [altRightRightUnit_eq_ofRat, contrMetric_eq_ofRat, prodT_ofRat_ofRat, ← map_nsmul,
      permT_ofRat]
  apply (Tensor.basis _).repr.injective
  ext b
  simp only [ofRat_basis_repr_apply]
  apply (Function.Injective.eq_iff PhysLean.RatComplexNum.toComplexNum_injective).mpr
  decide +revert +kernel

end PauliMatrix
