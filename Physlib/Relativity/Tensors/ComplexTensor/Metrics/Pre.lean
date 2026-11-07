/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.Units.Pre
/-!

# Metric for complex Lorentz vectors

-/

@[expose] public section
noncomputable section

open Module Matrix
open MatrixGroups
open Complex
open TensorProduct
open CategoryTheory.MonoidalCategory

namespace Lorentz

/-- The metric `ηᵃᵃ` as an element of `(complexContr ⊗ complexContr).V`. -/
def ComplexVector.metricVal : (ComplexVector ⊗[ℂ] ComplexVector) :=
  contrContrToMatrix.symm ((@minkowskiMatrix 3).map ofRealHom)

/-- The expansion of `ComplexVector.metricVal` into basis vectors. -/
lemma ComplexVector.metricVal_expand_tmul : ComplexVector.metricVal =
    ComplexVector.basis (Sum.inl 0) ⊗ₜ[ℂ] ComplexVector.basis (Sum.inl 0)
    - ComplexVector.basis (Sum.inr 0) ⊗ₜ[ℂ] ComplexVector.basis (Sum.inr 0)
    - ComplexVector.basis (Sum.inr 1) ⊗ₜ[ℂ] ComplexVector.basis (Sum.inr 1)
    - ComplexVector.basis (Sum.inr 2) ⊗ₜ[ℂ] ComplexVector.basis (Sum.inr 2) := by
  simp only [ComplexVector.metricVal, Fin.isValue]
  rw [contrContrToMatrix_symm_expand_tmul]
  simp only [map_apply, ofRealHom_eq_coe, Fintype.sum_sum_type, Finset.univ_unique,
    Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton, Fin.sum_univ_three, ne_eq, reduceCtorEq,
    not_false_eq_true, minkowskiMatrix.off_diag_zero, Sum.inr.injEq, zero_ne_one, Fin.reduceEq,
    one_ne_zero]
  rw [minkowskiMatrix.inl_0_inl_0, minkowskiMatrix.inr_i_inr_i,
    minkowskiMatrix.inr_i_inr_i, minkowskiMatrix.inr_i_inr_i]
  simp only [ofReal_one, Fin.isValue, one_smul, ofReal_zero, zero_smul, add_zero, ofReal_neg,
    zero_add]
  module

/-- The metric `ηᵃᵃ` as a morphism `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ complexContr ⊗ complexContr`,
  making its invariance under the action of `SL(2,ℂ)`. -/
def ComplexVector.metric : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
    (ComplexVector.SL2CRep.tprod ComplexVector.SL2CRep) where
    toFun := fun a =>
      let a' : ℂ := a
      a' • ComplexVector.metricVal
    map_add' := fun x y => by
      simp only [add_smul]
    map_smul' := fun m x => by
      simp only [smul_smul]
      rfl
    isIntertwining' M := by
      refine LinearMap.ext fun x : ℂ => ?_
      change x • ComplexVector.metricVal =
        (TensorProduct.map (ComplexVector.SL2CRep M) (ComplexVector.SL2CRep M))
          (x • ComplexVector.metricVal)
      simp only [map_smul]
      apply congrArg
      simp only [ComplexVector.metricVal]
      rw [contrContrToMatrix_ρ_symm]
      apply congrArg
      simp only [LorentzGroup.toComplex_mul_minkowskiMatrix_mul_transpose]

lemma ComplexVector.metric_apply_one : ComplexVector.metric (1 : ℂ) = ComplexVector.metricVal := by
  change (1 : ℂ) • ComplexVector.metricVal = ComplexVector.metricVal
  simp only [one_smul]

/-- The metric `ηᵢᵢ` as an element of `(complexCo ⊗ complexCo).V`. -/
def ComplexCoVector.metricVal : (ComplexCoVector ⊗[ℂ] ComplexCoVector) :=
  coCoToMatrix.symm ((@minkowskiMatrix 3).map ofRealHom)

/-- The expansion of `ComplexCoVector.metricVal` into basis vectors. -/
lemma ComplexCoVector.metricVal_expand_tmul : ComplexCoVector.metricVal =
    ComplexCoVector.basis (Sum.inl 0) ⊗ₜ[ℂ] ComplexCoVector.basis (Sum.inl 0)
    - ComplexCoVector.basis (Sum.inr 0) ⊗ₜ[ℂ] ComplexCoVector.basis (Sum.inr 0)
    - ComplexCoVector.basis (Sum.inr 1) ⊗ₜ[ℂ] ComplexCoVector.basis (Sum.inr 1)
    - ComplexCoVector.basis (Sum.inr 2) ⊗ₜ[ℂ] ComplexCoVector.basis (Sum.inr 2) := by
  simp only [ComplexCoVector.metricVal, Fin.isValue]
  rw [coCoToMatrix_symm_expand_tmul]
  simp only [map_apply, ofRealHom_eq_coe, Fintype.sum_sum_type, Finset.univ_unique,
    Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton, Fin.sum_univ_three, ne_eq, reduceCtorEq,
    not_false_eq_true, minkowskiMatrix.off_diag_zero, Sum.inr.injEq, zero_ne_one, Fin.reduceEq,
    one_ne_zero]
  rw [minkowskiMatrix.inl_0_inl_0, minkowskiMatrix.inr_i_inr_i,
    minkowskiMatrix.inr_i_inr_i, minkowskiMatrix.inr_i_inr_i]
  simp only [ofReal_one, Fin.isValue, one_smul, ofReal_zero, zero_smul, add_zero, ofReal_neg,
    zero_add]
  module

/-- The metric `ηᵢᵢ` as a morphism `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ complexCo ⊗ complexCo`,
  making its invariance under the action of `SL(2,ℂ)`. -/
def ComplexCoVector.metric : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
    (ComplexCoVector.SL2CRep.tprod ComplexCoVector.SL2CRep) where
  toFun := fun a =>
    let a' : ℂ := a
    a' • ComplexCoVector.metricVal
  map_add' := fun x y => by
    simp only [add_smul]
  map_smul' := fun m x => by
    simp only [smul_smul]
    rfl
  isIntertwining' M := by
    refine LinearMap.ext fun x : ℂ => ?_
    change x • ComplexCoVector.metricVal =
      (TensorProduct.map (ComplexCoVector.SL2CRep M) (ComplexCoVector.SL2CRep M))
        (x • ComplexCoVector.metricVal)
    simp only [map_smul]
    apply congrArg
    simp only [ComplexCoVector.metricVal]
    rw [coCoToMatrix_ρ_symm]
    apply congrArg
    rw [LorentzGroup.toComplex_inv]
    simp only [LorentzGroup.inv_eq_dual, SL2C.toLorentzGroup_apply_coe,
      LorentzGroup.toComplex_transpose_mul_minkowskiMatrix_mul_self]

lemma ComplexCoVector.metric_apply_one :
    ComplexCoVector.metric (1 : ℂ) = ComplexCoVector.metricVal := by
  change (1 : ℂ) • ComplexCoVector.metricVal = ComplexCoVector.metricVal
  simp only [one_smul]

TODO "Prove that every intertwining map `Representation.trivial ℂ SL(2,ℂ) ℂ →
  ComplexVector.SL2CRep.tprod ComplexVector.SL2CRep` is a scalar multiple of `ComplexVector.metric`,
  and likewise for `ComplexCoVector.metric`: up to scale, the Minkowski metric is the unique
  `SL(2,ℂ)`-invariant element of `ComplexVector ⊗ ComplexVector`. Compare
  `SULieAlgebra.intertwiningMap_eq_smul_adjointℂContr`."

/-!

## Contraction of metrics

-/

lemma ComplexVector.contr_metric :
    (TensorProduct.comm ℂ _ _ <|
      (TensorProduct.lid ℂ _).lTensor _ <|
      (ComplexVector.contr.toLinearMap.rTensor _).lTensor _ <|
      (TensorProduct.assoc ℂ _ _ _).symm.toLinearMap.lTensor _<|
      TensorProduct.assoc ℂ _ _ (_ ⊗[ℂ] _) <|
      (ComplexVector.metric 1) ⊗ₜ[ℂ] (ComplexCoVector.metric 1)) = ComplexVector.unit (1 : ℝ) := by
  rw [ComplexVector.metric_apply_one, ComplexCoVector.metric_apply_one]
  rw [ComplexVector.metricVal_expand_tmul, ComplexCoVector.metricVal_expand_tmul]
  simp [Fin.isValue, tmul_sub, sub_tmul, map_sub]
  repeat rw [ComplexVector.contr_basis']
  simp only [Fin.isValue, ↓reduceIte, one_smul, reduceCtorEq, zero_smul, sub_zero, zero_sub,
    Sum.inr.injEq, one_ne_zero, Fin.reduceEq, sub_neg_eq_add, zero_ne_one, sub_self]
  rw [ComplexVector.unit_apply_one, ComplexVector.unitVal_expand_tmul]

lemma ComplexCoVector.contr_metric :
    (TensorProduct.comm ℂ _ _ <|
      (TensorProduct.lid ℂ _).lTensor _ <|
      (ComplexCoVector.contr.toLinearMap.rTensor _).lTensor _ <|
      (TensorProduct.assoc ℂ _ _ _).symm.toLinearMap.lTensor _<|
      TensorProduct.assoc ℂ _ _ (_ ⊗[ℂ] _) <|
      (ComplexCoVector.metric 1) ⊗ₜ[ℂ] (ComplexVector.metric 1)) =
      ComplexCoVector.unit (1 : ℝ) := by
  rw [ComplexCoVector.metric_apply_one, ComplexVector.metric_apply_one]
  rw [ComplexCoVector.metricVal_expand_tmul, ComplexVector.metricVal_expand_tmul]
  simp [Fin.isValue, tmul_sub, sub_tmul, map_sub]
  repeat rw [ComplexCoVector.contr_basis']
  simp [Fin.isValue, ↓reduceIte, one_smul, reduceCtorEq, Sum.inr.injEq, one_ne_zero,
    Fin.reduceEq, zero_ne_one]
  rw [ComplexCoVector.unit_apply_one, ComplexCoVector.unitVal_expand_tmul]

end Lorentz
end
