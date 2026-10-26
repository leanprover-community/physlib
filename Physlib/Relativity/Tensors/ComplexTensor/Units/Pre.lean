/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.Matrix.Pre
public import Physlib.Relativity.Tensors.ComplexTensor.Vector.Pre.Contraction
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
def CoℂModule.unitVal : ContrℂModule ⊗[ℂ] CoℂModule :=
  contrCoToMatrix.symm 1

/-- Expansion of `CoℂModule.unitVal` into basis. -/
lemma CoℂModule.unitVal_expand_tmul : CoℂModule.unitVal =
    complexContrBasis (Sum.inl 0) ⊗ₜ[ℂ] complexCoBasis (Sum.inl 0)
    + complexContrBasis (Sum.inr 0) ⊗ₜ[ℂ] complexCoBasis (Sum.inr 0)
    + complexContrBasis (Sum.inr 1) ⊗ₜ[ℂ] complexCoBasis (Sum.inr 1)
    + complexContrBasis (Sum.inr 2) ⊗ₜ[ℂ] complexCoBasis (Sum.inr 2) := by
  simp only [CoℂModule.unitVal, Fin.isValue]
  rw [contrCoToMatrix_symm_expand_tmul]
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton, Fin.sum_univ_three, ne_eq, reduceCtorEq, not_false_eq_true, one_apply_ne,
    zero_smul, add_zero, one_apply_eq, one_smul, zero_add, Sum.inr.injEq, zero_ne_one, Fin.reduceEq,
    one_ne_zero]
  rfl

lemma CoℂModule.unitVal_eq_sum_tmul : CoℂModule.unitVal =
    ∑ i, complexContrBasis i ⊗ₜ[ℂ] complexCoBasis i := by
  simp [CoℂModule.unitVal_expand_tmul, Fin.isValue, Fin.sum_univ_three]
  module

/-- The contra-co unit for complex lorentz vectors as a morphism
  `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ complexContr ⊗ complexCo`, manifesting the invariance under
  the `SL(2, ℂ)` action. -/
def CoℂModule.unit : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
    (ContrℂModule.SL2CRep.tprod CoℂModule.SL2CRep) where
  toFun := fun a =>
    let a' : ℂ := a
    a' • CoℂModule.unitVal
  map_add' := fun x y => by
    simp only [add_smul]
  map_smul' := fun m x => by
    simp only [smul_smul]
    rfl
  isIntertwining' M := by
    refine LinearMap.ext fun x : ℂ => ?_
    change x • CoℂModule.unitVal =
      (TensorProduct.map (ContrℂModule.SL2CRep M) (CoℂModule.SL2CRep M)) (x • CoℂModule.unitVal)
    simp only [map_smul]
    apply congrArg
    simp only [CoℂModule.unitVal]
    rw [contrCoToMatrix_ρ_symm]
    apply congrArg
    simp

lemma CoℂModule.unit_apply_one : CoℂModule.unit (1 : ℂ) = CoℂModule.unitVal := by
  change (1 : ℂ) • CoℂModule.unitVal = CoℂModule.unitVal
  rw [one_smul]

/-- The co-contra unit for complex lorentz vectors. Usually denoted `δᵢⁱ`. -/
def ContrℂModule.unitVal : CoℂModule ⊗[ℂ] ContrℂModule :=
  coContrToMatrix.symm 1

/-- Expansion of `ContrℂModule.unitVal` into basis. -/
lemma ContrℂModule.unitVal_expand_tmul : ContrℂModule.unitVal =
    complexCoBasis (Sum.inl 0) ⊗ₜ[ℂ] complexContrBasis (Sum.inl 0)
    + complexCoBasis (Sum.inr 0) ⊗ₜ[ℂ] complexContrBasis (Sum.inr 0)
    + complexCoBasis (Sum.inr 1) ⊗ₜ[ℂ] complexContrBasis (Sum.inr 1)
    + complexCoBasis (Sum.inr 2) ⊗ₜ[ℂ] complexContrBasis (Sum.inr 2) := by
  simp only [ContrℂModule.unitVal, Fin.isValue]
  rw [coContrToMatrix_symm_expand_tmul]
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton, Fin.sum_univ_three, ne_eq, reduceCtorEq, not_false_eq_true, one_apply_ne,
    zero_smul, add_zero, one_apply_eq, one_smul, zero_add, Sum.inr.injEq, zero_ne_one, Fin.reduceEq,
    one_ne_zero]
  rfl

lemma ContrℂModule.unitVal_eq_sum_tmul : ContrℂModule.unitVal =
    ∑ i, complexCoBasis i ⊗ₜ[ℂ] complexContrBasis i := by
  simp [ContrℂModule.unitVal_expand_tmul, Fin.isValue, Fin.sum_univ_three]
  module

/-- The co-contra unit for complex lorentz vectors as a morphism
  `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ complexCo ⊗ complexContr`, manifesting the invariance under
  the `SL(2, ℂ)` action. -/
def ContrℂModule.unit : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
    (CoℂModule.SL2CRep.tprod ContrℂModule.SL2CRep) where
  toFun := fun a =>
    let a' : ℂ := a
    a' • ContrℂModule.unitVal
  map_add' := fun x y => by
    simp only [add_smul]
  map_smul' := fun m x => by
    simp only [smul_smul]
    rfl
  isIntertwining' M := by
    refine LinearMap.ext fun x : ℂ => ?_
    change x • ContrℂModule.unitVal =
      (TensorProduct.map (CoℂModule.SL2CRep M) (ContrℂModule.SL2CRep M)) (x • ContrℂModule.unitVal)
    simp only [map_smul]
    apply congrArg
    simp only [ContrℂModule.unitVal]
    rw [coContrToMatrix_ρ_symm]
    apply congrArg
    symm
    refine transpose_eq_one.mp ?h.h.h.a
    simp

lemma ContrℂModule.unit_apply_one : ContrℂModule.unit (1 : ℂ) = ContrℂModule.unitVal := by
  change (1 : ℂ) • ContrℂModule.unitVal = ContrℂModule.unitVal
  rw [one_smul]

/-!

## Contraction of the units

-/

/-- Contraction on the right with `CoℂModule.unit` does nothing. -/
lemma CoℂModule.contr_unit (x : CoℂModule) :
    (TensorProduct.lid ℂ _ <|
    CoℂModule.contr.toLinearMap.rTensor _ <|
    (TensorProduct.assoc ℂ _ _ _).symm <|
    x ⊗ₜ[ℂ] (CoℂModule.unit (1 : ℂ))) = x := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (Basis.mem_span complexCoBasis x)
  subst hc
  simp [- Fintype.sum_sum_type, map_sum, tmul_sum, smul_tmul, CoℂModule.contr_basis',
    CoℂModule.unit_apply_one, CoℂModule.unitVal_eq_sum_tmul, sum_tmul]

/-- Contraction on the right with `ContrℂModule.unit`. -/
lemma ContrℂModule.contr_unit (x : ContrℂModule) :
    (TensorProduct.lid ℂ _ <|
    ContrℂModule.contr.toLinearMap.rTensor _ <|
    (TensorProduct.assoc ℂ _ _ _).symm <|
    x ⊗ₜ[ℂ] (ContrℂModule.unit (1 : ℂ))) = x := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp
    (Basis.mem_span complexContrBasis x)
  subst hc
  simp [- Fintype.sum_sum_type, map_sum, tmul_sum, smul_tmul, ContrℂModule.contr_basis',
    ContrℂModule.unit_apply_one, ContrℂModule.unitVal_eq_sum_tmul, sum_tmul]

/-!

## Symmetry properties of the units

-/

open CategoryTheory

lemma CoℂModule.unit_symm :
    CoℂModule.unit (1 : ℂ) = LinearMap.lTensor _ (LinearEquiv.refl _ _).toLinearMap
      (TensorProduct.comm ℂ _ _ (ContrℂModule.unit (1 : ℂ))) := by
  rw [CoℂModule.unit_apply_one, CoℂModule.unitVal_expand_tmul]
  rw [ContrℂModule.unit_apply_one, ContrℂModule.unitVal_expand_tmul]
  rfl

lemma ContrℂModule.unit_symm :
    (ContrℂModule.unit (1 : ℂ)) = LinearMap.lTensor _ (LinearEquiv.refl _ _).toLinearMap
      (TensorProduct.comm ℂ _ _ (CoℂModule.unit (1 : ℂ))) := by
  rw [ContrℂModule.unit_apply_one, ContrℂModule.unitVal_expand_tmul]
  rw [CoℂModule.unit_apply_one, CoℂModule.unitVal_expand_tmul]
  rfl

end Lorentz
end
