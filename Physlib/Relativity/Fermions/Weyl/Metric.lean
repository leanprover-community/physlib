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

/-!

## A. The underlying matrix

-/

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

/-!

## B. The metric for left-handed Weyl fermions

-/

/-- The metric `εᵃᵃ` as an element of `(leftHanded ⊗ leftHanded).V`. -/
def LeftHandedWeyl.metricVal : LeftHandedWeyl ⊗[ℂ] LeftHandedWeyl :=
  leftLeftToMatrix.symm (- metricRaw)

/-- Expansion of `LeftHandedWeyl.metricVal` into the left basis. -/
lemma LeftHandedWeyl.metricVal_expand_tmul : LeftHandedWeyl.metricVal =
    - LeftHandedWeyl.basis 0 ⊗ₜ[ℂ] LeftHandedWeyl.basis 1 +
      LeftHandedWeyl.basis 1 ⊗ₜ[ℂ] LeftHandedWeyl.basis 0 := by
  simp only [LeftHandedWeyl.metricVal, Fin.isValue]
  rw [leftLeftToMatrix_symm_expand_tmul]
  simp only [metricRaw, Matrix.neg_apply, of_apply, cons_val', empty_val', cons_val_fin_one,
    Fin.sum_univ_two, Fin.isValue, cons_val_zero, cons_val_one, neg_zero, zero_smul, zero_add,
    neg_neg, one_smul, add_zero, add_left_inj]
  module

lemma LeftHandedWeyl.metricVal_expand_tmul' : LeftHandedWeyl.metricVal =
    LeftHandedWeyl.basis 1 ⊗ₜ[ℂ] LeftHandedWeyl.basis 0
    - LeftHandedWeyl.basis 0 ⊗ₜ[ℂ] LeftHandedWeyl.basis 1 := by
  rw [LeftHandedWeyl.metricVal_expand_tmul]; abel

/-- The metric `εᵃᵃ` as a morphism `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ leftHanded ⊗ leftHanded`,
  making manifest its invariance under the action of `SL(2,ℂ)`. -/
def LeftHandedWeyl.metric : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
    (LeftHandedWeyl.rep.tprod LeftHandedWeyl.rep) where
  toFun := fun a =>
    let a' : ℂ := a
    a' • LeftHandedWeyl.metricVal
  map_add' := fun x y => by
    simp only [add_smul]
  map_smul' := fun m x => by
    simp only [smul_smul]
    rfl
  isIntertwining' M := by
    refine LinearMap.ext fun x : ℂ => ?_
    change x • LeftHandedWeyl.metricVal =
      (TensorProduct.map (LeftHandedWeyl.rep M) (LeftHandedWeyl.rep M))
        (x • LeftHandedWeyl.metricVal)
    simp only [map_smul]
    apply congrArg
    simp only [LeftHandedWeyl.metricVal, map_neg, neg_inj]
    rw [leftLeftToMatrix_ρ_symm]
    apply congrArg
    rw [comm_metricRaw, mul_assoc, ← @transpose_mul]
    simp only [SpecialLinearGroup.det_coe, isUnit_iff_ne_zero, ne_eq, one_ne_zero,
      not_false_eq_true, mul_nonsing_inv, transpose_one, mul_one]

lemma LeftHandedWeyl.metric_apply_one :
    LeftHandedWeyl.metric (1 : ℂ) = LeftHandedWeyl.metricVal := by
  change (1 : ℂ) • LeftHandedWeyl.metricVal = LeftHandedWeyl.metricVal
  simp only [one_smul]

/-!

## C. The metric for dual left-handed Weyl fermions

-/

/-- The metric `εₐₐ` as an element of `(dualLeftHanded ⊗ dualLeftHanded).V`. -/
def DualLeftHandedWeyl.metricVal : (DualLeftHandedWeyl ⊗[ℂ] DualLeftHandedWeyl) :=
  dualLeftdualLeftToMatrix.symm metricRaw

/-- Expansion of `DualLeftHandedWeyl.metricVal` into the left basis. -/
lemma DualLeftHandedWeyl.metricVal_expand_tmul : DualLeftHandedWeyl.metricVal =
    DualLeftHandedWeyl.basis 0 ⊗ₜ[ℂ] DualLeftHandedWeyl.basis 1 -
      DualLeftHandedWeyl.basis 1 ⊗ₜ[ℂ] DualLeftHandedWeyl.basis 0 := by
  simp only [DualLeftHandedWeyl.metricVal, Fin.isValue]
  rw [dualLeftdualLeftToMatrix_symm_expand_tmul]
  simp only [metricRaw, of_apply, cons_val', empty_val', cons_val_fin_one, Fin.sum_univ_two,
    Fin.isValue, cons_val_zero, cons_val_one, zero_smul, one_smul, zero_add, add_zero]
  module

/-- The metric `εₐₐ` as a morphism `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ dualLeftHanded ⊗ dualLeftHanded`,
  making manifest its invariance under the action of `SL(2,ℂ)`. -/
def DualLeftHandedWeyl.metric : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
    (DualLeftHandedWeyl.rep.tprod DualLeftHandedWeyl.rep) where
    toFun := fun a =>
      let a' : ℂ := a
      a' • DualLeftHandedWeyl.metricVal
    map_add' := fun x y => by
      simp only [add_smul]
    map_smul' := fun m x => by
      simp only [smul_smul]
      rfl
    isIntertwining' M := by
      refine LinearMap.ext fun x : ℂ => ?_
      change x • DualLeftHandedWeyl.metricVal =
        (TensorProduct.map (DualLeftHandedWeyl.rep M) (DualLeftHandedWeyl.rep M))
          (x • DualLeftHandedWeyl.metricVal)
      simp only [map_smul]
      apply congrArg
      simp only [DualLeftHandedWeyl.metricVal]
      rw [dualLeftdualLeftToMatrix_ρ_symm]
      apply congrArg
      rw [← metricRaw_comm, mul_assoc]
      simp only [SpecialLinearGroup.det_coe, isUnit_iff_ne_zero, ne_eq, one_ne_zero,
        not_false_eq_true, mul_nonsing_inv, mul_one]

lemma DualLeftHandedWeyl.metric_apply_one :
    DualLeftHandedWeyl.metric (1 : ℂ) = DualLeftHandedWeyl.metricVal := by
  change (1 : ℂ) • DualLeftHandedWeyl.metricVal = DualLeftHandedWeyl.metricVal
  simp only [one_smul]

/-!

## D. The metric for right-handed Weyl fermions

-/

/-- The metric `ε^{dot a}^{dot a}` as an element of `(rightHanded ⊗ rightHanded).V`. -/
def RightHandedWeyl.metricVal : (RightHandedWeyl ⊗[ℂ] RightHandedWeyl) :=
  rightRightToMatrix.symm (- metricRaw)

/-- Expansion of `RightHandedWeyl.metricVal` into the left basis. -/
lemma RightHandedWeyl.metricVal_expand_tmul : RightHandedWeyl.metricVal =
    - RightHandedWeyl.basis 0 ⊗ₜ[ℂ] RightHandedWeyl.basis 1 +
      RightHandedWeyl.basis 1 ⊗ₜ[ℂ] RightHandedWeyl.basis 0 := by
  simp only [RightHandedWeyl.metricVal, Fin.isValue]
  rw [rightRightToMatrix_symm_expand_tmul]
  simp only [metricRaw, Matrix.neg_apply, of_apply, cons_val', empty_val', cons_val_fin_one,
    Fin.sum_univ_two, Fin.isValue, cons_val_zero, cons_val_one, neg_zero, zero_smul, zero_add,
    neg_neg, one_smul, add_zero, add_left_inj]
  module

lemma RightHandedWeyl.metricVal_expand_tmul' : RightHandedWeyl.metricVal =
    RightHandedWeyl.basis 1 ⊗ₜ[ℂ] RightHandedWeyl.basis 0
    - RightHandedWeyl.basis 0 ⊗ₜ[ℂ] RightHandedWeyl.basis 1 := by
  rw [RightHandedWeyl.metricVal_expand_tmul]
  abel

/-- The metric `ε^{dot a}^{dot a}` as a morphism `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ rightHanded ⊗ rightHanded`,
  making manifest its invariance under the action of `SL(2,ℂ)`. -/
def RightHandedWeyl.metric : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
    (RightHandedWeyl.rep.tprod RightHandedWeyl.rep) where
  toFun := fun a =>
    let a' : ℂ := a
    a' • RightHandedWeyl.metricVal
  map_add' := fun x y => by
    simp only [add_smul]
  map_smul' := fun m x => by
    simp only [smul_smul]
    rfl
  isIntertwining' M := by
    refine LinearMap.ext fun x : ℂ => ?_
    change x • RightHandedWeyl.metricVal =
      (TensorProduct.map (RightHandedWeyl.rep M) (RightHandedWeyl.rep M))
        (x • RightHandedWeyl.metricVal)
    simp only [map_smul]
    apply congrArg
    simp only [RightHandedWeyl.metricVal, map_neg, neg_inj]
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

lemma RightHandedWeyl.metric_apply_one :
    RightHandedWeyl.metric (1 : ℂ) = RightHandedWeyl.metricVal := by
  change (1 : ℂ) • RightHandedWeyl.metricVal = RightHandedWeyl.metricVal
  simp only [one_smul]

/-!

## E. The metric for dual right-handed Weyl fermions

-/

/-- The metric `ε_{dot a}_{dot a}` as an element of `(dualRightHanded ⊗ dualRightHanded).V`. -/
def DualRightHandedWeyl.metricVal : DualRightHandedWeyl ⊗[ℂ] DualRightHandedWeyl :=
  dualRightDualRightToMatrix.symm (metricRaw)

/-- Expansion of `RightHandedWeyl.metricVal` into the left basis. -/
lemma DualRightHandedWeyl.metricVal_expand_tmul : DualRightHandedWeyl.metricVal =
    DualRightHandedWeyl.basis 0 ⊗ₜ[ℂ] DualRightHandedWeyl.basis 1 -
      DualRightHandedWeyl.basis 1 ⊗ₜ[ℂ] DualRightHandedWeyl.basis 0 := by
  simp only [DualRightHandedWeyl.metricVal, Fin.isValue]
  rw [dualRightDualRightToMatrix_symm_expand_tmul]
  simp only [metricRaw, of_apply, cons_val', empty_val', cons_val_fin_one, Fin.sum_univ_two,
    Fin.isValue, cons_val_zero, cons_val_one, zero_smul, one_smul, zero_add, add_zero]
  module

/-- The metric `ε_{dot a}_{dot a}` as a morphism
  `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ dualRightHanded ⊗ dualRightHanded`,
  making manifest its invariance under the action of `SL(2,ℂ)`. -/
def DualRightHandedWeyl.metric : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
    (DualRightHandedWeyl.rep.tprod DualRightHandedWeyl.rep) where
  toFun := fun a =>
      let a' : ℂ := a
      a' • DualRightHandedWeyl.metricVal
  map_add' := fun x y => by
    simp only [add_smul]
  map_smul' := fun m x => by
    simp only [smul_smul]
    rfl
  isIntertwining' M := by
    refine LinearMap.ext fun x : ℂ => ?_
    change x • DualRightHandedWeyl.metricVal =
      (TensorProduct.map (DualRightHandedWeyl.rep M) (DualRightHandedWeyl.rep M))
        (x • DualRightHandedWeyl.metricVal)
    simp only [map_smul]
    apply congrArg
    trans dualRightDualRightToMatrix.symm
      (((M.1)⁻¹).conjTranspose * metricRaw * (((M.1)⁻¹).conjTranspose)ᵀ)
    · rw [DualRightHandedWeyl.metricVal]
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

lemma DualRightHandedWeyl.metric_apply_one :
    DualRightHandedWeyl.metric (1 : ℂ) = DualRightHandedWeyl.metricVal := by
  change (1 : ℂ) • DualRightHandedWeyl.metricVal = DualRightHandedWeyl.metricVal
  simp only [one_smul]

TODO "Prove that every intertwining map `Representation.trivial ℂ SL(2,ℂ) ℂ →
  LeftHandedWeyl.rep.tprod LeftHandedWeyl.rep` is a scalar multiple of `LeftHandedWeyl.metric`, and
  likewise for `DualLeftHandedWeyl.metric`, `RightHandedWeyl.metric` and
  `DualRightHandedWeyl.metric`: up to scale, `ε` is the unique `SL(2,ℂ)`-invariant element of
  `LeftHandedWeyl ⊗ LeftHandedWeyl`. Compare `SULieAlgebra.intertwiningMap_eq_smul_adjointℂContr`."

/-!

## Contraction of metrics

-/

lemma LeftHandedWeyl.contr_metric :
    (TensorProduct.comm ℂ _ _ <|
      (TensorProduct.lid ℂ _).lTensor _ <|
      (LeftHandedWeyl.contr.toLinearMap.rTensor _).lTensor _ <|
      (TensorProduct.assoc ℂ _ _ _).symm.toLinearMap.lTensor _<|
      TensorProduct.assoc ℂ _ _ (_ ⊗[ℂ] _) <|
      (LeftHandedWeyl.metric 1) ⊗ₜ[ℂ] (DualLeftHandedWeyl.metric 1)) =
      LeftHandedWeyl.unit (1 : ℂ) := by
  rw [LeftHandedWeyl.metric_apply_one, DualLeftHandedWeyl.metric_apply_one]
  rw [LeftHandedWeyl.metricVal_expand_tmul', DualLeftHandedWeyl.metricVal_expand_tmul]
  simp only [Fin.isValue, tmul_sub, sub_tmul, map_sub, assoc_tmul, LinearMap.lTensor_tmul,
    LinearEquiv.coe_coe, assoc_symm_tmul, LinearMap.rTensor_tmul,
    Representation.IntertwiningMap.coe_toLinearMap, LinearEquiv.lTensor_tmul, lid_tmul, tmul_smul,
    map_smul, comm_tmul]
  simp only [LeftHandedWeyl.contr_basis]
  simp only [Fin.isValue, Fin.val_one, Fin.val_zero, one_ne_zero, ↓reduceIte, one_smul, zero_ne_one]
  rw [LeftHandedWeyl.unit_apply_one, LeftHandedWeyl.unitVal_expand_tmul]
  rw [add_comm]
  module

lemma DualLeftHandedWeyl.contr_metric :
    (TensorProduct.comm ℂ _ _ <|
    (TensorProduct.lid ℂ _).lTensor _ <|
    (DualLeftHandedWeyl.contr.toLinearMap.rTensor _).lTensor _ <|
    (TensorProduct.assoc ℂ _ _ _).symm.toLinearMap.lTensor _<|
    TensorProduct.assoc ℂ _ _ (_ ⊗[ℂ] _) <|
    (DualLeftHandedWeyl.metric 1) ⊗ₜ[ℂ] (LeftHandedWeyl.metric 1)) =
    DualLeftHandedWeyl.unit (1 : ℂ) := by
  rw [LeftHandedWeyl.metric_apply_one, DualLeftHandedWeyl.metric_apply_one]
  rw [LeftHandedWeyl.metricVal_expand_tmul', DualLeftHandedWeyl.metricVal_expand_tmul]
  simp only [Fin.isValue, tmul_sub, sub_tmul, map_sub, assoc_tmul, LinearMap.lTensor_tmul,
    LinearEquiv.coe_coe, assoc_symm_tmul, LinearMap.rTensor_tmul,
    Representation.IntertwiningMap.coe_toLinearMap, LinearEquiv.lTensor_tmul, lid_tmul, tmul_smul,
    map_smul, comm_tmul]
  simp only [DualLeftHandedWeyl.contr_basis]
  simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.mod_succ, ↓reduceIte, one_smul, Nat.zero_mod,
    zero_ne_one, zero_smul, sub_zero, one_ne_zero, zero_sub, sub_neg_eq_add]
  rw [DualLeftHandedWeyl.unit_apply_one, DualLeftHandedWeyl.unitVal_expand_tmul]

lemma RightHandedWeyl.contr_metric :
    (TensorProduct.comm ℂ _ _ <|
    (TensorProduct.lid ℂ _).lTensor _ <|
    (RightHandedWeyl.contr.toLinearMap.rTensor _).lTensor _ <|
    (TensorProduct.assoc ℂ _ _ _).symm.toLinearMap.lTensor _<|
    TensorProduct.assoc ℂ _ _ (_ ⊗[ℂ] _) <|
    (RightHandedWeyl.metric 1) ⊗ₜ[ℂ] (DualRightHandedWeyl.metric 1)) =
    RightHandedWeyl.unit (1 : ℂ) := by
  rw [RightHandedWeyl.metric_apply_one, DualRightHandedWeyl.metric_apply_one]
  rw [RightHandedWeyl.metricVal_expand_tmul', DualRightHandedWeyl.metricVal_expand_tmul]
  simp only [Fin.isValue, tmul_sub, sub_tmul, map_sub, assoc_tmul, LinearMap.lTensor_tmul,
    LinearEquiv.coe_coe, assoc_symm_tmul, LinearMap.rTensor_tmul,
    Representation.IntertwiningMap.coe_toLinearMap, LinearEquiv.lTensor_tmul, lid_tmul, tmul_smul,
    map_smul, comm_tmul]
  simp only [RightHandedWeyl.contr_basis]
  simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.mod_succ, Nat.zero_mod, one_ne_zero, ↓reduceIte,
    one_smul, zero_ne_one]
  rw [RightHandedWeyl.unit_apply_one, RightHandedWeyl.unitVal_expand_tmul]
  rw [add_comm]
  module

lemma DualRightHandedWeyl.contr_metric :
    (TensorProduct.comm ℂ _ _ <|
      (TensorProduct.lid ℂ _).lTensor _ <|
      (DualRightHandedWeyl.contr.toLinearMap.rTensor _).lTensor _ <|
      (TensorProduct.assoc ℂ _ _ _).symm.toLinearMap.lTensor _<|
      TensorProduct.assoc ℂ _ _ (_ ⊗[ℂ] _) <|
      (DualRightHandedWeyl.metric 1) ⊗ₜ[ℂ] (RightHandedWeyl.metric 1)) =
      DualRightHandedWeyl.unit (1 : ℂ) := by
  rw [RightHandedWeyl.metric_apply_one, DualRightHandedWeyl.metric_apply_one]
  rw [RightHandedWeyl.metricVal_expand_tmul', DualRightHandedWeyl.metricVal_expand_tmul]
  simp only [Fin.isValue, tmul_sub, sub_tmul, map_sub, assoc_tmul, LinearMap.lTensor_tmul,
    LinearEquiv.coe_coe, assoc_symm_tmul, LinearMap.rTensor_tmul,
    Representation.IntertwiningMap.coe_toLinearMap, LinearEquiv.lTensor_tmul, lid_tmul, tmul_smul,
    map_smul, comm_tmul]
  simp only [DualRightHandedWeyl.contr_basis]
  simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.mod_succ, ↓reduceIte, one_smul, Nat.zero_mod,
    zero_ne_one, zero_smul, sub_zero, one_ne_zero, zero_sub, sub_neg_eq_add]
  rw [DualRightHandedWeyl.unit_apply_one, DualRightHandedWeyl.unitVal_expand_tmul]

end
end Fermion
