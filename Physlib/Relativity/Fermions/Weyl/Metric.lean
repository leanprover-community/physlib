/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Fermions.Weyl.Unit
/-!

# Metrics of Weyl fermions

We define the metrics for Weyl fermions, often denoted `ε` in the literature.
These allow us to go from left-handed to dual-left-handed Weyl fermions and back,
and from right-handed to dual-right-handed Weyl fermions and back.

-/

@[expose] public section

namespace Fermion
noncomputable section

open Module Matrix
open MatrixGroups
open Complex
open TensorProduct
open CategoryTheory.MonoidalCategory

/-- The raw `2x2` matrix corresponding to the metric for fermions. -/
def metricRaw : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

/-- Multiplying an element of `SL(2, ℂ)` on the left with the metric `𝓔` is equivalent
  to multiplying the inverse-transpose of that element on the right with the metric. -/
lemma comm_metricRaw (M : SL(2,ℂ)) : M.1 * metricRaw = metricRaw * (M.1⁻¹)ᵀ := by
  rw [metricRaw]
  rw [Lorentz.SL2C.inverse_coe, eta_fin_two M.1]
  rw [SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_fin_two, eta_fin_two !![M.1 1 1, -M.1 0 1; -M.1 1 0, M.1 0 0]ᵀ]
  simp only [Fin.isValue, mul_zero, mul_neg, mul_one, zero_add, add_zero, transpose_apply, of_apply,
    cons_val', cons_val_zero, empty_val', cons_val_fin_one, cons_val_one, cons_mul,
    Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons, head_cons, zero_smul, tail_cons, one_smul,
    empty_vecMul, neg_smul, neg_cons, neg_neg, neg_empty, empty_mul, Equiv.symm_apply_apply]

lemma metricRaw_comm (M : SL(2,ℂ)) : metricRaw * M.1 = (M.1⁻¹)ᵀ * metricRaw := by
  rw [metricRaw]
  rw [Lorentz.SL2C.inverse_coe, eta_fin_two M.1]
  rw [SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_fin_two, eta_fin_two !![M.1 1 1, -M.1 0 1; -M.1 1 0, M.1 0 0]ᵀ]
  simp only [Fin.isValue, zero_mul, one_mul, zero_add, neg_mul, add_zero, transpose_apply, of_apply,
    cons_val', cons_val_zero, empty_val', cons_val_fin_one, cons_val_one, cons_mul,
    Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons, head_cons, smul_cons, smul_eq_mul, mul_zero,
    mul_one, smul_empty, tail_cons, neg_smul, mul_neg, neg_cons, neg_neg, neg_zero, neg_empty,
    empty_vecMul, add_cons, empty_add_empty, empty_mul, Equiv.symm_apply_apply]

lemma star_comm_metricRaw (M : SL(2,ℂ)) : M.1.map star * metricRaw = metricRaw * ((M.1)⁻¹)ᴴ := by
  rw [metricRaw]
  rw [Lorentz.SL2C.inverse_coe, eta_fin_two M.1]
  rw [SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      eta_fin_two !![M.1 1 1, -M.1 0 1; -M.1 1 0, M.1 0 0]ᴴ]
  rw [eta_fin_two (!![M.1 0 0, M.1 0 1; M.1 1 0, M.1 1 1].map star)]
  simp

lemma metricRaw_comm_star (M : SL(2,ℂ)) : metricRaw * M.1.map star = ((M.1)⁻¹)ᴴ * metricRaw := by
  rw [metricRaw]
  rw [Lorentz.SL2C.inverse_coe, eta_fin_two M.1]
  rw [SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      eta_fin_two !![M.1 1 1, -M.1 0 1; -M.1 1 0, M.1 0 0]ᴴ]
  rw [eta_fin_two (!![M.1 0 0, M.1 0 1; M.1 1 0, M.1 1 1].map star)]
  simp

/-- The metric `εᵃᵃ` as an element of `(leftHanded ⊗ leftHanded).V`. -/
def leftMetricVal : LeftHandedWeyl ⊗[ℂ] LeftHandedWeyl :=
  leftLeftToMatrix.symm (- metricRaw)

/-- Expansion of `leftMetricVal` into the left basis. -/
lemma leftMetricVal_expand_tmul : leftMetricVal =
    - LeftHandedWeyl.basis 0 ⊗ₜ[ℂ] LeftHandedWeyl.basis 1 +
      LeftHandedWeyl.basis 1 ⊗ₜ[ℂ] LeftHandedWeyl.basis 0 := by
  simp only [leftMetricVal, Fin.isValue]
  rw [leftLeftToMatrix_symm_expand_tmul]
  simp only [metricRaw, Matrix.neg_apply, of_apply, cons_val', empty_val', cons_val_fin_one,
    Fin.sum_univ_two, Fin.isValue, cons_val_zero, cons_val_one, neg_zero, zero_smul, zero_add,
    neg_neg, one_smul, add_zero, add_left_inj]
  module

lemma leftMetricVal_expand_tmul' : leftMetricVal =
    LeftHandedWeyl.basis 1 ⊗ₜ[ℂ] LeftHandedWeyl.basis 0
    - LeftHandedWeyl.basis 0 ⊗ₜ[ℂ] LeftHandedWeyl.basis 1 := by rw [leftMetricVal_expand_tmul]; abel

/-- The metric `εᵃᵃ` as a morphism `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ leftHanded ⊗ leftHanded`,
  making manifest its invariance under the action of `SL(2,ℂ)`. -/
def leftMetric : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
    (LeftHandedWeyl.rep.tprod LeftHandedWeyl.rep) where
  toFun := fun a =>
    let a' : ℂ := a
    a' • leftMetricVal
  map_add' := fun x y => by
    simp only [add_smul]
  map_smul' := fun m x => by
    simp only [smul_smul]
    rfl
  isIntertwining' M := by
    refine LinearMap.ext fun x : ℂ => ?_
    change x • leftMetricVal =
      (TensorProduct.map (LeftHandedWeyl.rep M) (LeftHandedWeyl.rep M)) (x • leftMetricVal)
    simp only [map_smul]
    apply congrArg
    simp only [leftMetricVal, map_neg, neg_inj]
    rw [leftLeftToMatrix_ρ_symm]
    apply congrArg
    rw [comm_metricRaw, mul_assoc, ← @transpose_mul]
    simp only [SpecialLinearGroup.det_coe, isUnit_iff_ne_zero, ne_eq, one_ne_zero,
      not_false_eq_true, mul_nonsing_inv, transpose_one, mul_one]

lemma leftMetric_apply_one : leftMetric (1 : ℂ) = leftMetricVal := by
  change (1 : ℂ) • leftMetricVal = leftMetricVal
  simp only [one_smul]

/-- The metric `εᵃᵃ` is invariant under the action of `SL(2,ℂ)`. -/
lemma leftMetricVal_rep (M : SL(2,ℂ)) :
    TensorProduct.map (LeftHandedWeyl.rep M) (LeftHandedWeyl.rep M) leftMetricVal =
      leftMetricVal := by
  have h := LinearMap.congr_fun (leftMetric.isIntertwining' M) (1 : ℂ)
  simpa [leftMetric_apply_one, Representation.tprod_apply] using h.symm

/-- The metric `εₐₐ` as an element of `(dualLeftHanded ⊗ dualLeftHanded).V`. -/
def dualLeftMetricVal : (DualLeftHandedWeyl ⊗[ℂ] DualLeftHandedWeyl) :=
  dualLeftdualLeftToMatrix.symm metricRaw

/-- Expansion of `dualLeftMetricVal` into the left basis. -/
lemma dualLeftMetricVal_expand_tmul : dualLeftMetricVal =
    DualLeftHandedWeyl.basis 0 ⊗ₜ[ℂ] DualLeftHandedWeyl.basis 1 -
      DualLeftHandedWeyl.basis 1 ⊗ₜ[ℂ] DualLeftHandedWeyl.basis 0 := by
  simp only [dualLeftMetricVal, Fin.isValue]
  rw [dualLeftdualLeftToMatrix_symm_expand_tmul]
  simp only [metricRaw, of_apply, cons_val', empty_val', cons_val_fin_one, Fin.sum_univ_two,
    Fin.isValue, cons_val_zero, cons_val_one, zero_smul, one_smul, zero_add, add_zero]
  module

/-- The metric `εₐₐ` as a morphism `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ dualLeftHanded ⊗ dualLeftHanded`,
  making manifest its invariance under the action of `SL(2,ℂ)`. -/
def dualLeftMetric : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
    (DualLeftHandedWeyl.rep.tprod DualLeftHandedWeyl.rep) where
    toFun := fun a =>
      let a' : ℂ := a
      a' • dualLeftMetricVal
    map_add' := fun x y => by
      simp only [add_smul]
    map_smul' := fun m x => by
      simp only [smul_smul]
      rfl
    isIntertwining' M := by
      refine LinearMap.ext fun x : ℂ => ?_
      change x • dualLeftMetricVal =
        (TensorProduct.map (DualLeftHandedWeyl.rep M) (DualLeftHandedWeyl.rep M))
          (x • dualLeftMetricVal)
      simp only [map_smul]
      apply congrArg
      simp only [dualLeftMetricVal]
      rw [dualLeftdualLeftToMatrix_ρ_symm]
      apply congrArg
      rw [← metricRaw_comm, mul_assoc]
      simp only [SpecialLinearGroup.det_coe, isUnit_iff_ne_zero, ne_eq, one_ne_zero,
        not_false_eq_true, mul_nonsing_inv, mul_one]

lemma dualLeftMetric_apply_one : dualLeftMetric (1 : ℂ) = dualLeftMetricVal := by
  change (1 : ℂ) • dualLeftMetricVal = dualLeftMetricVal
  simp only [one_smul]

/-- The metric `ε^{dot a}^{dot a}` as an element of `(rightHanded ⊗ rightHanded).V`. -/
def rightMetricVal : (RightHandedWeyl ⊗[ℂ] RightHandedWeyl) :=
  rightRightToMatrix.symm (- metricRaw)

/-- Expansion of `rightMetricVal` into the left basis. -/
lemma rightMetricVal_expand_tmul : rightMetricVal =
    - RightHandedWeyl.basis 0 ⊗ₜ[ℂ] RightHandedWeyl.basis 1 +
      RightHandedWeyl.basis 1 ⊗ₜ[ℂ] RightHandedWeyl.basis 0 := by
  simp only [rightMetricVal, Fin.isValue]
  rw [rightRightToMatrix_symm_expand_tmul]
  simp only [metricRaw, Matrix.neg_apply, of_apply, cons_val', empty_val', cons_val_fin_one,
    Fin.sum_univ_two, Fin.isValue, cons_val_zero, cons_val_one, neg_zero, zero_smul, zero_add,
    neg_neg, one_smul, add_zero, add_left_inj]
  module

lemma rightMetricVal_expand_tmul' : rightMetricVal =
    RightHandedWeyl.basis 1 ⊗ₜ[ℂ] RightHandedWeyl.basis 0
    - RightHandedWeyl.basis 0 ⊗ₜ[ℂ] RightHandedWeyl.basis 1 := by
  rw [rightMetricVal_expand_tmul]
  abel

/-- The metric `ε^{dot a}^{dot a}` as a morphism `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ rightHanded ⊗ rightHanded`,
  making manifest its invariance under the action of `SL(2,ℂ)`. -/
def rightMetric : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
    (RightHandedWeyl.rep.tprod RightHandedWeyl.rep) where
  toFun := fun a =>
    let a' : ℂ := a
    a' • rightMetricVal
  map_add' := fun x y => by
    simp only [add_smul]
  map_smul' := fun m x => by
    simp only [smul_smul]
    rfl
  isIntertwining' M := by
    refine LinearMap.ext fun x : ℂ => ?_
    change x • rightMetricVal =
      (TensorProduct.map (RightHandedWeyl.rep M) (RightHandedWeyl.rep M)) (x • rightMetricVal)
    simp only [map_smul]
    apply congrArg
    simp only [rightMetricVal, map_neg, neg_inj]
    trans rightRightToMatrix.symm ((M.1).map star * metricRaw * ((M.1).map star)ᵀ)
    · apply congrArg
      rw [star_comm_metricRaw, mul_assoc]
      have h1 : ((M.1)⁻¹ᴴ * ((M.1).map star)ᵀ) = 1 := by
        trans (M.1)⁻¹ᴴ * ((M.1))ᴴ
        · rfl
        rw [← @conjTranspose_mul]
        simp only [SpecialLinearGroup.det_coe, isUnit_iff_ne_zero, ne_eq, one_ne_zero,
          not_false_eq_true, mul_nonsing_inv, conjTranspose_one]
      rw [h1]
      simp
    · rw [← rightRightToMatrix_ρ_symm metricRaw M]

lemma rightMetric_apply_one : rightMetric (1 : ℂ) = rightMetricVal := by
  change (1 : ℂ) • rightMetricVal = rightMetricVal
  simp only [one_smul]

/-- The metric `ε_{dot a}_{dot a}` as an element of `(dualRightHanded ⊗ dualRightHanded).V`. -/
def dualRightMetricVal : DualRightHandedWeyl ⊗[ℂ] DualRightHandedWeyl :=
  dualRightDualRightToMatrix.symm (metricRaw)

/-- Expansion of `rightMetricVal` into the left basis. -/
lemma dualRightMetricVal_expand_tmul : dualRightMetricVal =
    DualRightHandedWeyl.basis 0 ⊗ₜ[ℂ] DualRightHandedWeyl.basis 1 -
      DualRightHandedWeyl.basis 1 ⊗ₜ[ℂ] DualRightHandedWeyl.basis 0 := by
  simp only [dualRightMetricVal, Fin.isValue]
  rw [dualRightDualRightToMatrix_symm_expand_tmul]
  simp only [metricRaw, of_apply, cons_val', empty_val', cons_val_fin_one, Fin.sum_univ_two,
    Fin.isValue, cons_val_zero, cons_val_one, zero_smul, one_smul, zero_add, add_zero]
  module

/-- The metric `ε_{dot a}_{dot a}` as a morphism
  `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ dualRightHanded ⊗ dualRightHanded`,
  making manifest its invariance under the action of `SL(2,ℂ)`. -/
def dualRightMetric : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
    (DualRightHandedWeyl.rep.tprod DualRightHandedWeyl.rep) where
  toFun := fun a =>
      let a' : ℂ := a
      a' • dualRightMetricVal
  map_add' := fun x y => by
    simp only [add_smul]
  map_smul' := fun m x => by
    simp only [smul_smul]
    rfl
  isIntertwining' M := by
    refine LinearMap.ext fun x : ℂ => ?_
    change x • dualRightMetricVal =
      (TensorProduct.map (DualRightHandedWeyl.rep M) (DualRightHandedWeyl.rep M))
        (x • dualRightMetricVal)
    simp only [map_smul]
    apply congrArg
    trans dualRightDualRightToMatrix.symm
      (((M.1)⁻¹).conjTranspose * metricRaw * (((M.1)⁻¹).conjTranspose)ᵀ)
    · rw [dualRightMetricVal]
      apply congrArg
      rw [← metricRaw_comm_star, mul_assoc]
      have h1 : ((M.1).map star * (M.1)⁻¹ᴴᵀ) = 1 := by
        refine transpose_eq_one.mp ?_
        rw [@transpose_mul]
        simp only [transpose_transpose, RCLike.star_def]
        change (M.1)⁻¹ᴴ * (M.1)ᴴ = 1
        rw [← @conjTranspose_mul]
        simp
      rw [h1, mul_one]
    · rw [← dualRightDualRightToMatrix_ρ_symm metricRaw M]
      rfl

lemma dualRightMetric_apply_one : dualRightMetric (1 : ℂ) = dualRightMetricVal := by
  change (1 : ℂ) • dualRightMetricVal = dualRightMetricVal
  simp only [one_smul]

/-!

## Contraction of metrics

-/

lemma leftDualContraction_apply_metric :
    (TensorProduct.comm ℂ _ _ <|
      (TensorProduct.lid ℂ _).lTensor _ <|
      (leftDualContraction.toLinearMap.rTensor _).lTensor _ <|
      (TensorProduct.assoc ℂ _ _ _).symm.toLinearMap.lTensor _<|
      TensorProduct.assoc ℂ _ _ (_ ⊗[ℂ] _) <|
      (leftMetric 1) ⊗ₜ[ℂ] (dualLeftMetric 1)) = dualLeftLeftUnit (1 : ℂ) := by
  rw [leftMetric_apply_one, dualLeftMetric_apply_one]
  rw [leftMetricVal_expand_tmul', dualLeftMetricVal_expand_tmul]
  simp only [Fin.isValue, tmul_sub, sub_tmul, map_sub, assoc_tmul, LinearMap.lTensor_tmul,
    LinearEquiv.coe_coe, assoc_symm_tmul, LinearMap.rTensor_tmul,
    Representation.IntertwiningMap.coe_toLinearMap, LinearEquiv.lTensor_tmul, lid_tmul, tmul_smul,
    map_smul, comm_tmul]
  simp only [leftDualContraction_basis]
  simp only [Fin.isValue, Fin.val_one, Fin.val_zero, one_ne_zero, ↓reduceIte, one_smul, zero_ne_one]
  rw [dualLeftLeftUnit_apply_one, dualLeftLeftUnitVal_expand_tmul]
  rw [add_comm]
  module

lemma dualLeftContraction_apply_metric :
    (TensorProduct.comm ℂ _ _ <|
    (TensorProduct.lid ℂ _).lTensor _ <|
    (dualLeftContraction.toLinearMap.rTensor _).lTensor _ <|
    (TensorProduct.assoc ℂ _ _ _).symm.toLinearMap.lTensor _<|
    TensorProduct.assoc ℂ _ _ (_ ⊗[ℂ] _) <|
    (dualLeftMetric 1) ⊗ₜ[ℂ] (leftMetric 1)) = leftDualLeftUnit (1 : ℂ) := by
  rw [leftMetric_apply_one, dualLeftMetric_apply_one]
  rw [leftMetricVal_expand_tmul', dualLeftMetricVal_expand_tmul]
  simp only [Fin.isValue, tmul_sub, sub_tmul, map_sub, assoc_tmul, LinearMap.lTensor_tmul,
    LinearEquiv.coe_coe, assoc_symm_tmul, LinearMap.rTensor_tmul,
    Representation.IntertwiningMap.coe_toLinearMap, LinearEquiv.lTensor_tmul, lid_tmul, tmul_smul,
    map_smul, comm_tmul]
  simp only [dualLeftContraction_basis]
  simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.mod_succ, ↓reduceIte, one_smul, Nat.zero_mod,
    zero_ne_one, zero_smul, sub_zero, one_ne_zero, zero_sub, sub_neg_eq_add]
  rw [leftDualLeftUnit_apply_one, leftDualLeftUnitVal_expand_tmul]

lemma rightDualContraction_apply_metric :
    (TensorProduct.comm ℂ _ _ <|
    (TensorProduct.lid ℂ _).lTensor _ <|
    (rightDualContraction.toLinearMap.rTensor _).lTensor _ <|
    (TensorProduct.assoc ℂ _ _ _).symm.toLinearMap.lTensor _<|
    TensorProduct.assoc ℂ _ _ (_ ⊗[ℂ] _) <|
    (rightMetric 1) ⊗ₜ[ℂ] (dualRightMetric 1)) = dualRightRightUnit (1 : ℂ) := by
  rw [rightMetric_apply_one, dualRightMetric_apply_one]
  rw [rightMetricVal_expand_tmul', dualRightMetricVal_expand_tmul]
  simp only [Fin.isValue, tmul_sub, sub_tmul, map_sub, assoc_tmul, LinearMap.lTensor_tmul,
    LinearEquiv.coe_coe, assoc_symm_tmul, LinearMap.rTensor_tmul,
    Representation.IntertwiningMap.coe_toLinearMap, LinearEquiv.lTensor_tmul, lid_tmul, tmul_smul,
    map_smul, comm_tmul]
  simp only [rightDualContraction_basis]
  simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.mod_succ, Nat.zero_mod, one_ne_zero, ↓reduceIte,
    one_smul, zero_ne_one]
  rw [dualRightRightUnit_apply_one, dualRightRightUnitVal_expand_tmul]
  rw [add_comm]
  module

lemma dualRightContraction_apply_metric :
    (TensorProduct.comm ℂ _ _ <|
      (TensorProduct.lid ℂ _).lTensor _ <|
      (dualRightContraction.toLinearMap.rTensor _).lTensor _ <|
      (TensorProduct.assoc ℂ _ _ _).symm.toLinearMap.lTensor _<|
      TensorProduct.assoc ℂ _ _ (_ ⊗[ℂ] _) <|
      (dualRightMetric 1) ⊗ₜ[ℂ] (rightMetric 1)) = rightDualRightUnit (1 : ℂ) := by
  rw [rightMetric_apply_one, dualRightMetric_apply_one]
  rw [rightMetricVal_expand_tmul', dualRightMetricVal_expand_tmul]
  simp only [Fin.isValue, tmul_sub, sub_tmul, map_sub, assoc_tmul, LinearMap.lTensor_tmul,
    LinearEquiv.coe_coe, assoc_symm_tmul, LinearMap.rTensor_tmul,
    Representation.IntertwiningMap.coe_toLinearMap, LinearEquiv.lTensor_tmul, lid_tmul, tmul_smul,
    map_smul, comm_tmul]
  simp only [dualRightContraction_basis]
  simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.mod_succ, ↓reduceIte, one_smul, Nat.zero_mod,
    zero_ne_one, zero_smul, sub_zero, one_ne_zero, zero_sub, sub_neg_eq_add]
  rw [rightDualRightUnit_apply_one, rightDualRightUnitVal_expand_tmul]

end
end Fermion
