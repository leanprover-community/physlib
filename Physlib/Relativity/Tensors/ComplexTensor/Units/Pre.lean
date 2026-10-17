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
def contrCoUnitVal : ContrℂModule ⊗[ℂ] CoℂModule :=
  contrCoToMatrix.symm 1

/-- Expansion of `contrCoUnitVal` into basis. -/
lemma contrCoUnitVal_expand_tmul : contrCoUnitVal =
    complexContrBasis (Sum.inl 0) ⊗ₜ[ℂ] complexCoBasis (Sum.inl 0)
    + complexContrBasis (Sum.inr 0) ⊗ₜ[ℂ] complexCoBasis (Sum.inr 0)
    + complexContrBasis (Sum.inr 1) ⊗ₜ[ℂ] complexCoBasis (Sum.inr 1)
    + complexContrBasis (Sum.inr 2) ⊗ₜ[ℂ] complexCoBasis (Sum.inr 2) := by
  simp only [contrCoUnitVal, Fin.isValue]
  rw [contrCoToMatrix_symm_expand_tmul]
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton, Fin.sum_univ_three, ne_eq, reduceCtorEq, not_false_eq_true, one_apply_ne,
    zero_smul, add_zero, one_apply_eq, one_smul, zero_add, Sum.inr.injEq, zero_ne_one, Fin.reduceEq,
    one_ne_zero]
  rfl

lemma contrCoUnitVal_eq_sum_tmul : contrCoUnitVal =
    ∑ i, complexContrBasis i ⊗ₜ[ℂ] complexCoBasis i := by
  simp [contrCoUnitVal_expand_tmul, Fin.isValue, Fin.sum_univ_three]
  module

/-- The contra-co unit for complex lorentz vectors as a morphism
  `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ complexContr ⊗ complexCo`, manifesting the invariance under
  the `SL(2, ℂ)` action. -/
def contrCoUnit : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
    (ContrℂModule.SL2CRep.tprod CoℂModule.SL2CRep) where
  toFun := fun a =>
    let a' : ℂ := a
    a' • contrCoUnitVal
  map_add' := fun x y => by
    simp only [add_smul]
  map_smul' := fun m x => by
    simp only [smul_smul]
    rfl
  isIntertwining' M := by
    refine LinearMap.ext fun x : ℂ => ?_
    change x • contrCoUnitVal =
      (TensorProduct.map (ContrℂModule.SL2CRep M) (CoℂModule.SL2CRep M)) (x • contrCoUnitVal)
    simp only [map_smul]
    apply congrArg
    simp only [contrCoUnitVal]
    rw [contrCoToMatrix_ρ_symm]
    apply congrArg
    simp

lemma contrCoUnit_apply_one : contrCoUnit (1 : ℂ) = contrCoUnitVal := by
  change (1 : ℂ) • contrCoUnitVal = contrCoUnitVal
  rw [one_smul]

/-- The co-contra unit for complex lorentz vectors. Usually denoted `δᵢⁱ`. -/
def coContrUnitVal : CoℂModule ⊗[ℂ] ContrℂModule :=
  coContrToMatrix.symm 1

/-- Expansion of `coContrUnitVal` into basis. -/
lemma coContrUnitVal_expand_tmul : coContrUnitVal =
    complexCoBasis (Sum.inl 0) ⊗ₜ[ℂ] complexContrBasis (Sum.inl 0)
    + complexCoBasis (Sum.inr 0) ⊗ₜ[ℂ] complexContrBasis (Sum.inr 0)
    + complexCoBasis (Sum.inr 1) ⊗ₜ[ℂ] complexContrBasis (Sum.inr 1)
    + complexCoBasis (Sum.inr 2) ⊗ₜ[ℂ] complexContrBasis (Sum.inr 2) := by
  simp only [coContrUnitVal, Fin.isValue]
  rw [coContrToMatrix_symm_expand_tmul]
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton, Fin.sum_univ_three, ne_eq, reduceCtorEq, not_false_eq_true, one_apply_ne,
    zero_smul, add_zero, one_apply_eq, one_smul, zero_add, Sum.inr.injEq, zero_ne_one, Fin.reduceEq,
    one_ne_zero]
  rfl

lemma coContrUnitVal_eq_sum_tmul : coContrUnitVal =
    ∑ i, complexCoBasis i ⊗ₜ[ℂ] complexContrBasis i := by
  simp [coContrUnitVal_expand_tmul, Fin.isValue, Fin.sum_univ_three]
  module

/-- The co-contra unit for complex lorentz vectors as a morphism
  `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ complexCo ⊗ complexContr`, manifesting the invariance under
  the `SL(2, ℂ)` action. -/
def coContrUnit : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
    (CoℂModule.SL2CRep.tprod ContrℂModule.SL2CRep) where
  toFun := fun a =>
    let a' : ℂ := a
    a' • coContrUnitVal
  map_add' := fun x y => by
    simp only [add_smul]
  map_smul' := fun m x => by
    simp only [smul_smul]
    rfl
  isIntertwining' M := by
    refine LinearMap.ext fun x : ℂ => ?_
    change x • coContrUnitVal =
      (TensorProduct.map (CoℂModule.SL2CRep M) (ContrℂModule.SL2CRep M)) (x • coContrUnitVal)
    simp only [map_smul]
    apply congrArg
    simp only [coContrUnitVal]
    rw [coContrToMatrix_ρ_symm]
    apply congrArg
    symm
    refine transpose_eq_one.mp ?h.h.h.a
    simp

lemma coContrUnit_apply_one : coContrUnit (1 : ℂ) = coContrUnitVal := by
  change (1 : ℂ) • coContrUnitVal = coContrUnitVal
  rw [one_smul]

/-!

## Contraction of the units

-/

/-- Contraction on the right with `contrCoUnit` does nothing. -/
lemma contr_contrCoUnit (x : CoℂModule) :
    (TensorProduct.lid ℂ _ <|
    coContrContraction.toLinearMap.rTensor _ <|
    (TensorProduct.assoc ℂ _ _ _).symm <|
    x ⊗ₜ[ℂ] (contrCoUnit (1 : ℂ))) = x := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (Basis.mem_span complexCoBasis x)
  subst hc
  simp [- Fintype.sum_sum_type, map_sum, tmul_sum, smul_tmul, coContrContraction_basis',
    contrCoUnit_apply_one, contrCoUnitVal_eq_sum_tmul, sum_tmul]

/-- Contraction on the right with `coContrUnit`. -/
lemma contr_coContrUnit (x : ContrℂModule) :
    (TensorProduct.lid ℂ _ <|
    contrCoContraction.toLinearMap.rTensor _ <|
    (TensorProduct.assoc ℂ _ _ _).symm <|
    x ⊗ₜ[ℂ] (coContrUnit (1 : ℂ))) = x := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp
    (Basis.mem_span complexContrBasis x)
  subst hc
  simp [- Fintype.sum_sum_type, map_sum, tmul_sum, smul_tmul, contrCoContraction_basis',
    coContrUnit_apply_one, coContrUnitVal_eq_sum_tmul, sum_tmul]

/-!

## Symmetry properties of the units

-/

open CategoryTheory

lemma contrCoUnit_symm :
    contrCoUnit (1 : ℂ) = LinearMap.lTensor _ (LinearEquiv.refl _ _).toLinearMap
      (TensorProduct.comm ℂ _ _ (coContrUnit (1 : ℂ))) := by
  rw [contrCoUnit_apply_one, contrCoUnitVal_expand_tmul]
  rw [coContrUnit_apply_one, coContrUnitVal_expand_tmul]
  rfl

lemma coContrUnit_symm :
    (coContrUnit (1 : ℂ)) = LinearMap.lTensor _ (LinearEquiv.refl _ _).toLinearMap
      (TensorProduct.comm ℂ _ _ (contrCoUnit (1 : ℂ))) := by
  rw [coContrUnit_apply_one, coContrUnitVal_expand_tmul]
  rw [contrCoUnit_apply_one, contrCoUnitVal_expand_tmul]
  rfl

end Lorentz
end
