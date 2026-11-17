/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.Matrix.Pre
public import Physlib.Relativity.Tensors.ComplexTensor.Vector.Contraction
/-!

# Unit for complex Lorentz vectors

-/

@[expose] public section
noncomputable section

open Module Matrix
open MatrixGroups
open Complex
open TensorProduct
open CategoryTheory.MonoidalCategory

namespace Lorentz

/-- The contra-co unit for complex lorentz vectors. Usually denoted `δⁱᵢ`. -/
def ComplexCoVector.unitVal : ComplexVector ⊗[ℂ] ComplexCoVector :=
  contrCoToMatrix.symm 1

/-- Expansion of `ComplexCoVector.unitVal` into basis. -/
lemma ComplexCoVector.unitVal_expand_tmul : ComplexCoVector.unitVal =
    ComplexVector.basis (Sum.inl 0) ⊗ₜ[ℂ] ComplexCoVector.basis (Sum.inl 0)
    + ComplexVector.basis (Sum.inr 0) ⊗ₜ[ℂ] ComplexCoVector.basis (Sum.inr 0)
    + ComplexVector.basis (Sum.inr 1) ⊗ₜ[ℂ] ComplexCoVector.basis (Sum.inr 1)
    + ComplexVector.basis (Sum.inr 2) ⊗ₜ[ℂ] ComplexCoVector.basis (Sum.inr 2) := by
  simp only [ComplexCoVector.unitVal, Fin.isValue]
  rw [contrCoToMatrix_symm_expand_tmul]
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton, Fin.sum_univ_three, ne_eq, reduceCtorEq, not_false_eq_true, one_apply_ne,
    zero_smul, add_zero, one_apply_eq, one_smul, zero_add, Sum.inr.injEq, zero_ne_one, Fin.reduceEq,
    one_ne_zero]
  rfl

lemma ComplexCoVector.unitVal_eq_sum_tmul : ComplexCoVector.unitVal =
    ∑ i, ComplexVector.basis i ⊗ₜ[ℂ] ComplexCoVector.basis i := by
  simp [ComplexCoVector.unitVal_expand_tmul, Fin.isValue, Fin.sum_univ_three]
  module

/-- The contra-co unit for complex lorentz vectors as a morphism
  `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ complexContr ⊗ complexCo`, manifesting the invariance under
  the `SL(2, ℂ)` action. -/
def ComplexCoVector.unit : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
    (ComplexVector.SL2CRep.tprod ComplexCoVector.SL2CRep) where
  toFun := fun a =>
    let a' : ℂ := a
    a' • ComplexCoVector.unitVal
  map_add' := fun x y => by
    simp only [add_smul]
  map_smul' := fun m x => by
    simp only [smul_smul]
    rfl
  isIntertwining' M := by
    refine LinearMap.ext fun x : ℂ => ?_
    change x • ComplexCoVector.unitVal =
      (TensorProduct.map (ComplexVector.SL2CRep M) (ComplexCoVector.SL2CRep M))
        (x • ComplexCoVector.unitVal)
    simp only [map_smul]
    apply congrArg
    simp only [ComplexCoVector.unitVal]
    rw [contrCoToMatrix_ρ_symm]
    apply congrArg
    simp

lemma ComplexCoVector.unit_apply_one : ComplexCoVector.unit (1 : ℂ) = ComplexCoVector.unitVal := by
  change (1 : ℂ) • ComplexCoVector.unitVal = ComplexCoVector.unitVal
  rw [one_smul]

/-- The co-contra unit for complex lorentz vectors. Usually denoted `δᵢⁱ`. -/
def ComplexVector.unitVal : ComplexCoVector ⊗[ℂ] ComplexVector :=
  coContrToMatrix.symm 1

/-- Expansion of `ComplexVector.unitVal` into basis. -/
lemma ComplexVector.unitVal_expand_tmul : ComplexVector.unitVal =
    ComplexCoVector.basis (Sum.inl 0) ⊗ₜ[ℂ] ComplexVector.basis (Sum.inl 0)
    + ComplexCoVector.basis (Sum.inr 0) ⊗ₜ[ℂ] ComplexVector.basis (Sum.inr 0)
    + ComplexCoVector.basis (Sum.inr 1) ⊗ₜ[ℂ] ComplexVector.basis (Sum.inr 1)
    + ComplexCoVector.basis (Sum.inr 2) ⊗ₜ[ℂ] ComplexVector.basis (Sum.inr 2) := by
  simp only [ComplexVector.unitVal, Fin.isValue]
  rw [coContrToMatrix_symm_expand_tmul]
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton, Fin.sum_univ_three, ne_eq, reduceCtorEq, not_false_eq_true, one_apply_ne,
    zero_smul, add_zero, one_apply_eq, one_smul, zero_add, Sum.inr.injEq, zero_ne_one, Fin.reduceEq,
    one_ne_zero]
  rfl

lemma ComplexVector.unitVal_eq_sum_tmul : ComplexVector.unitVal =
    ∑ i, ComplexCoVector.basis i ⊗ₜ[ℂ] ComplexVector.basis i := by
  simp [ComplexVector.unitVal_expand_tmul, Fin.isValue, Fin.sum_univ_three]
  module

/-- The co-contra unit for complex lorentz vectors as a morphism
  `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ complexCo ⊗ complexContr`, manifesting the invariance under
  the `SL(2, ℂ)` action. -/
def ComplexVector.unit : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
    (ComplexCoVector.SL2CRep.tprod ComplexVector.SL2CRep) where
  toFun := fun a =>
    let a' : ℂ := a
    a' • ComplexVector.unitVal
  map_add' := fun x y => by
    simp only [add_smul]
  map_smul' := fun m x => by
    simp only [smul_smul]
    rfl
  isIntertwining' M := by
    refine LinearMap.ext fun x : ℂ => ?_
    change x • ComplexVector.unitVal =
      (TensorProduct.map (ComplexCoVector.SL2CRep M) (ComplexVector.SL2CRep M))
        (x • ComplexVector.unitVal)
    simp only [map_smul]
    apply congrArg
    simp only [ComplexVector.unitVal]
    rw [coContrToMatrix_ρ_symm]
    apply congrArg
    symm
    refine transpose_eq_one.mp ?h.h.h.a
    simp

lemma ComplexVector.unit_apply_one : ComplexVector.unit (1 : ℂ) = ComplexVector.unitVal := by
  change (1 : ℂ) • ComplexVector.unitVal = ComplexVector.unitVal
  rw [one_smul]

/-!

## Contraction of the units

-/

/-- Contraction on the right with `ComplexCoVector.unit` does nothing. -/
lemma ComplexCoVector.contr_unit (x : ComplexCoVector) :
    (TensorProduct.lid ℂ _ <|
    ComplexCoVector.contr.toLinearMap.rTensor _ <|
    (TensorProduct.assoc ℂ _ _ _).symm <|
    x ⊗ₜ[ℂ] (ComplexCoVector.unit (1 : ℂ))) = x := by
  obtain ⟨c, hc⟩ :=
    (Submodule.mem_span_range_iff_exists_fun ℂ).mp (Basis.mem_span ComplexCoVector.basis x)
  subst hc
  simp [- Fintype.sum_sum_type, map_sum, tmul_sum, smul_tmul, ComplexCoVector.contr_basis',
    ComplexCoVector.unit_apply_one, ComplexCoVector.unitVal_eq_sum_tmul, sum_tmul]

/-- Contraction on the right with `ComplexVector.unit`. -/
lemma ComplexVector.contr_unit (x : ComplexVector) :
    (TensorProduct.lid ℂ _ <|
    ComplexVector.contr.toLinearMap.rTensor _ <|
    (TensorProduct.assoc ℂ _ _ _).symm <|
    x ⊗ₜ[ℂ] (ComplexVector.unit (1 : ℂ))) = x := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp
    (Basis.mem_span ComplexVector.basis x)
  subst hc
  simp [- Fintype.sum_sum_type, map_sum, tmul_sum, smul_tmul, ComplexVector.contr_basis',
    ComplexVector.unit_apply_one, ComplexVector.unitVal_eq_sum_tmul, sum_tmul]

/-!

## Symmetry properties of the units

-/

open CategoryTheory

lemma ComplexCoVector.unit_symm :
    ComplexCoVector.unit (1 : ℂ) = LinearMap.lTensor _ (LinearEquiv.refl _ _).toLinearMap
      (TensorProduct.comm ℂ _ _ (ComplexVector.unit (1 : ℂ))) := by
  rw [ComplexCoVector.unit_apply_one, ComplexCoVector.unitVal_expand_tmul]
  rw [ComplexVector.unit_apply_one, ComplexVector.unitVal_expand_tmul]
  rfl

lemma ComplexVector.unit_symm :
    (ComplexVector.unit (1 : ℂ)) = LinearMap.lTensor _ (LinearEquiv.refl _ _).toLinearMap
      (TensorProduct.comm ℂ _ _ (ComplexCoVector.unit (1 : ℂ))) := by
  rw [ComplexVector.unit_apply_one, ComplexVector.unitVal_expand_tmul]
  rw [ComplexCoVector.unit_apply_one, ComplexCoVector.unitVal_expand_tmul]
  rfl

end Lorentz
end
