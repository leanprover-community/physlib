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
def ContrℂModule.metricVal : (ContrℂModule ⊗[ℂ] ContrℂModule) :=
  contrContrToMatrix.symm ((@minkowskiMatrix 3).map ofRealHom)

/-- The expansion of `ContrℂModule.metricVal` into basis vectors. -/
lemma ContrℂModule.metricVal_expand_tmul : ContrℂModule.metricVal =
    complexContrBasis (Sum.inl 0) ⊗ₜ[ℂ] complexContrBasis (Sum.inl 0)
    - complexContrBasis (Sum.inr 0) ⊗ₜ[ℂ] complexContrBasis (Sum.inr 0)
    - complexContrBasis (Sum.inr 1) ⊗ₜ[ℂ] complexContrBasis (Sum.inr 1)
    - complexContrBasis (Sum.inr 2) ⊗ₜ[ℂ] complexContrBasis (Sum.inr 2) := by
  simp only [ContrℂModule.metricVal, Fin.isValue]
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
def ContrℂModule.metric : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
    (ContrℂModule.SL2CRep.tprod ContrℂModule.SL2CRep) where
    toFun := fun a =>
      let a' : ℂ := a
      a' • ContrℂModule.metricVal
    map_add' := fun x y => by
      simp only [add_smul]
    map_smul' := fun m x => by
      simp only [smul_smul]
      rfl
    isIntertwining' M := by
      refine LinearMap.ext fun x : ℂ => ?_
      change x • ContrℂModule.metricVal =
        (TensorProduct.map (ContrℂModule.SL2CRep M) (ContrℂModule.SL2CRep M))
          (x • ContrℂModule.metricVal)
      simp only [map_smul]
      apply congrArg
      simp only [ContrℂModule.metricVal]
      rw [contrContrToMatrix_ρ_symm]
      apply congrArg
      simp only [LorentzGroup.toComplex_mul_minkowskiMatrix_mul_transpose]

lemma ContrℂModule.metric_apply_one : ContrℂModule.metric (1 : ℂ) = ContrℂModule.metricVal := by
  change (1 : ℂ) • ContrℂModule.metricVal = ContrℂModule.metricVal
  simp only [one_smul]

/-- The metric `ηᵢᵢ` as an element of `(complexCo ⊗ complexCo).V`. -/
def CoℂModule.metricVal : (CoℂModule ⊗[ℂ] CoℂModule) :=
  coCoToMatrix.symm ((@minkowskiMatrix 3).map ofRealHom)

/-- The expansion of `CoℂModule.metricVal` into basis vectors. -/
lemma CoℂModule.metricVal_expand_tmul : CoℂModule.metricVal =
    complexCoBasis (Sum.inl 0) ⊗ₜ[ℂ] complexCoBasis (Sum.inl 0)
    - complexCoBasis (Sum.inr 0) ⊗ₜ[ℂ] complexCoBasis (Sum.inr 0)
    - complexCoBasis (Sum.inr 1) ⊗ₜ[ℂ] complexCoBasis (Sum.inr 1)
    - complexCoBasis (Sum.inr 2) ⊗ₜ[ℂ] complexCoBasis (Sum.inr 2) := by
  simp only [CoℂModule.metricVal, Fin.isValue]
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
def CoℂModule.metric : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
    (CoℂModule.SL2CRep.tprod CoℂModule.SL2CRep) where
  toFun := fun a =>
    let a' : ℂ := a
    a' • CoℂModule.metricVal
  map_add' := fun x y => by
    simp only [add_smul]
  map_smul' := fun m x => by
    simp only [smul_smul]
    rfl
  isIntertwining' M := by
    refine LinearMap.ext fun x : ℂ => ?_
    change x • CoℂModule.metricVal =
      (TensorProduct.map (CoℂModule.SL2CRep M) (CoℂModule.SL2CRep M)) (x • CoℂModule.metricVal)
    simp only [map_smul]
    apply congrArg
    simp only [CoℂModule.metricVal]
    rw [coCoToMatrix_ρ_symm]
    apply congrArg
    rw [LorentzGroup.toComplex_inv]
    simp only [LorentzGroup.inv_eq_dual, SL2C.toLorentzGroup_apply_coe,
      LorentzGroup.toComplex_transpose_mul_minkowskiMatrix_mul_self]

lemma CoℂModule.metric_apply_one : CoℂModule.metric (1 : ℂ) = CoℂModule.metricVal := by
  change (1 : ℂ) • CoℂModule.metricVal = CoℂModule.metricVal
  simp only [one_smul]

TODO "Prove that every intertwining map `Representation.trivial ℂ SL(2,ℂ) ℂ →
  ContrℂModule.SL2CRep.tprod ContrℂModule.SL2CRep` is a scalar multiple of `ContrℂModule.metric`,
  and likewise for `CoℂModule.metric`: up to scale, the Minkowski metric is the unique
  `SL(2,ℂ)`-invariant element of `ContrℂModule ⊗ ContrℂModule`. Compare
  `SULieAlgebra.intertwiningMap_eq_smul_adjointℂContr`."

/-!

## Contraction of metrics

-/

lemma ContrℂModule.contr_metric :
    (TensorProduct.comm ℂ _ _ <|
      (TensorProduct.lid ℂ _).lTensor _ <|
      (ContrℂModule.contr.toLinearMap.rTensor _).lTensor _ <|
      (TensorProduct.assoc ℂ _ _ _).symm.toLinearMap.lTensor _<|
      TensorProduct.assoc ℂ _ _ (_ ⊗[ℂ] _) <|
      (ContrℂModule.metric 1) ⊗ₜ[ℂ] (CoℂModule.metric 1)) = ContrℂModule.unit (1 : ℝ) := by
  rw [ContrℂModule.metric_apply_one, CoℂModule.metric_apply_one]
  rw [ContrℂModule.metricVal_expand_tmul, CoℂModule.metricVal_expand_tmul]
  simp [Fin.isValue, tmul_sub, sub_tmul, map_sub]
  repeat rw [ContrℂModule.contr_basis']
  simp only [Fin.isValue, ↓reduceIte, one_smul, reduceCtorEq, zero_smul, sub_zero, zero_sub,
    Sum.inr.injEq, one_ne_zero, Fin.reduceEq, sub_neg_eq_add, zero_ne_one, sub_self]
  rw [ContrℂModule.unit_apply_one, ContrℂModule.unitVal_expand_tmul]

lemma CoℂModule.contr_metric :
    (TensorProduct.comm ℂ _ _ <|
      (TensorProduct.lid ℂ _).lTensor _ <|
      (CoℂModule.contr.toLinearMap.rTensor _).lTensor _ <|
      (TensorProduct.assoc ℂ _ _ _).symm.toLinearMap.lTensor _<|
      TensorProduct.assoc ℂ _ _ (_ ⊗[ℂ] _) <|
      (CoℂModule.metric 1) ⊗ₜ[ℂ] (ContrℂModule.metric 1)) = CoℂModule.unit (1 : ℝ) := by
  rw [CoℂModule.metric_apply_one, ContrℂModule.metric_apply_one]
  rw [CoℂModule.metricVal_expand_tmul, ContrℂModule.metricVal_expand_tmul]
  simp [Fin.isValue, tmul_sub, sub_tmul, map_sub]
  repeat rw [CoℂModule.contr_basis']
  simp [Fin.isValue, ↓reduceIte, one_smul, reduceCtorEq, Sum.inr.injEq, one_ne_zero,
    Fin.reduceEq, zero_ne_one]
  rw [CoℂModule.unit_apply_one, CoℂModule.unitVal_expand_tmul]

end Lorentz
end
