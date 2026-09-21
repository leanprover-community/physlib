/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Units.Pre
/-!

# Metric for real Lorentz vectors

-/

@[expose] public section
noncomputable section

open Module Matrix MatrixGroups Complex TensorProduct CategoryTheory.MonoidalCategory

namespace Lorentz
open scoped TensorProduct

/-- The metric `ηᵃᵃ` as an element of `(ContrMod d ⊗[ℝ] ContrMod d)`. -/
def preContrMetricVal (d : ℕ := 3) : ContrMod d ⊗[ℝ] ContrMod d :=
  contrContrToMatrixRe.symm ((@minkowskiMatrix d))

lemma preContrMetricVal_expand_tmul_minkowskiMatrix {d : ℕ} : preContrMetricVal d =
    ∑ i, (minkowskiMatrix i i) • (contrBasis d i ⊗ₜ[ℝ] contrBasis d i) := by
  rw [preContrMetricVal, contrContrToMatrixRe_symm_expand_tmul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
    fun j _ hj => smul_eq_zero_of_left (minkowskiMatrix.off_diag_zero hj.symm) _

/-- Expansion of `preContrMetricVal` into basis. -/
lemma preContrMetricVal_expand_tmul {d : ℕ} : preContrMetricVal d =
    contrBasis d (Sum.inl 0) ⊗ₜ[ℝ] contrBasis d (Sum.inl 0) -
    ∑ i, contrBasis d (Sum.inr i) ⊗ₜ[ℝ] contrBasis d (Sum.inr i) := by
  rw [preContrMetricVal_expand_tmul_minkowskiMatrix]
  simp [Fintype.sum_sum_type, minkowskiMatrix.inl_0_inl_0, minkowskiMatrix.inr_i_inr_i,
    sub_eq_add_neg]

/-- The metric `ηᵃᵃ` as a morphism `𝟙_ (Rep ℝ (LorentzGroup d)) ⟶ ContrMod.rep ⊗ ContrMod.rep`,
  making its invariance under the action of `LorentzGroup d`. -/
def preContrMetric (d : ℕ := 3) :
    (Representation.trivial ℝ (LorentzGroup d) ℝ).IntertwiningMap
    ((ContrMod.rep).tprod (ContrMod.rep)) where
  toFun := fun a => a • (preContrMetricVal d)
  map_add' := fun x y => add_smul x y _
  map_smul' := fun m x => mul_smul m x _
  isIntertwining' M := by
    refine LinearMap.ext fun x : ℝ => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply]
    change x • (preContrMetricVal d) =
      (TensorProduct.map (ContrMod.rep M) (ContrMod.rep M)) (x • (preContrMetricVal d))
    simp only [map_smul]
    apply congrArg
    simp only [preContrMetricVal]
    conv_rhs =>
      rw [contrContrToMatrixRe_ρ_symm]
    apply congrArg
    simp

lemma preContrMetric_apply_one {d : ℕ} : (preContrMetric d) (1 : ℝ) = preContrMetricVal d :=
  one_smul ℝ _

/-- The metric `ηᵢᵢ` as an element of `(CoMod d ⊗[ℝ] CoMod d)`. -/
def preCoMetricVal (d : ℕ := 3) : CoMod d ⊗[ℝ] CoMod d :=
  coCoToMatrixRe.symm ((@minkowskiMatrix d))

lemma preCoMetricVal_expand_tmul_minkowskiMatrix {d : ℕ} : preCoMetricVal d =
    ∑ i, (minkowskiMatrix i i) • (coBasis d i ⊗ₜ[ℝ] coBasis d i) := by
  rw [preCoMetricVal, coCoToMatrixRe_symm_expand_tmul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
    fun j _ hj => smul_eq_zero_of_left (minkowskiMatrix.off_diag_zero hj.symm) _

/-- Expansion of `preContrMetricVal` into basis. -/
lemma preCoMetricVal_expand_tmul {d : ℕ} : preCoMetricVal d =
    coBasis d (Sum.inl 0) ⊗ₜ[ℝ] coBasis d (Sum.inl 0) -
    ∑ i, coBasis d (Sum.inr i) ⊗ₜ[ℝ] coBasis d (Sum.inr i) := by
  rw [preCoMetricVal_expand_tmul_minkowskiMatrix]
  simp [Fintype.sum_sum_type, minkowskiMatrix.inl_0_inl_0, minkowskiMatrix.inr_i_inr_i,
    sub_eq_add_neg]

/-- The metric `ηᵢᵢ` as a morphism `𝟙_ (Rep ℂ (LorentzGroup d))) ⟶ CoMod.rep ⊗ CoMod.rep`,
  making its invariance under the action of `LorentzGroup d`. -/
def preCoMetric (d : ℕ := 3) : (Representation.trivial ℝ (LorentzGroup d) ℝ).IntertwiningMap
    ((CoMod.rep).tprod (CoMod.rep)) where
  toFun := fun a => a • preCoMetricVal d
  map_add' := fun x y => add_smul x y _
  map_smul' := fun m x => mul_smul m x _
  isIntertwining' M := by
    refine LinearMap.ext fun x : ℝ => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply]
    change x • preCoMetricVal d =
      (TensorProduct.map (CoMod.rep M) (CoMod.rep M)) (x • preCoMetricVal d)
    simp only [_root_.map_smul]
    apply congrArg
    simp only [preCoMetricVal]
    rw [coCoToMatrixRe_ρ_symm]
    apply congrArg
    rw [← LorentzGroup.coe_inv, LorentzGroup.transpose_mul_minkowskiMatrix_mul_self]

lemma preCoMetric_apply_one {d : ℕ} : (preCoMetric d) (1 : ℝ) = preCoMetricVal d :=
  one_smul ℝ _

/-!

## Contraction of metrics

-/

open minkowskiMatrix in
lemma contrCoContract_apply_metric {d : ℕ} :
    (TensorProduct.comm ℝ _ _ <|
      (TensorProduct.lid ℝ _).lTensor _ <|
      (contrCoContract.toLinearMap.rTensor (CoMod d)).lTensor (ContrMod d) <|
      (TensorProduct.assoc ℝ (ContrMod d) (CoMod d) (CoMod d)).symm.toLinearMap.lTensor
        (ContrMod d) <|
      TensorProduct.assoc ℝ (ContrMod d) (ContrMod d) ((CoMod d) ⊗[ℝ] (CoMod d)) <|
      (preContrMetric d 1) ⊗ₜ[ℝ] (preCoMetric d 1)) = preCoContrUnit d (1 : ℝ) := by
  calc _
    _ = (TensorProduct.comm ℝ _ _ <|
      (TensorProduct.lid ℝ _).lTensor _ <|
      (contrCoContract.toLinearMap.rTensor (CoMod d)).lTensor (ContrMod d) <|
      (TensorProduct.assoc ℝ (ContrMod d) (CoMod d) (CoMod d)).symm.toLinearMap.lTensor
        (ContrMod d) <|
      TensorProduct.assoc ℝ (ContrMod d) (ContrMod d) ((CoMod d) ⊗[ℝ] (CoMod d)) <|
      ∑ i, ∑ j, ((η i i * η j j) •
      ((contrBasis d i ⊗ₜ[ℝ] contrBasis d i) ⊗ₜ[ℝ] (coBasis d j ⊗ₜ[ℝ] coBasis d j)))) := by
        congr
        rw [preContrMetric_apply_one, preCoMetric_apply_one,
          preContrMetricVal_expand_tmul_minkowskiMatrix,
          preCoMetricVal_expand_tmul_minkowskiMatrix, sum_tmul]
        simp_rw [tmul_sum, ← smul_tmul', tmul_smul, smul_smul]
    _ = (TensorProduct.comm ℝ _ _ <| (TensorProduct.lid ℝ _).lTensor _ <|
      ∑ i, ∑ j, (minkowskiMatrix i i * minkowskiMatrix j j) •
        (contrBasis d i ⊗ₜ[ℝ] (contrCoContract (contrBasis d i ⊗ₜ[ℝ] coBasis d j)
          ⊗ₜ[ℝ] coBasis d j))) := by
        congr
        simp [map_sum, map_smul]
    _ = (TensorProduct.comm ℝ _ _ <| (TensorProduct.lid ℝ _).lTensor _ <|
          ∑ i, contrBasis d i ⊗ₜ[ℝ] ((1 : ℝ) ⊗ₜ[ℝ] coBasis d i)) := by
        congr
        funext x
        rw [Finset.sum_eq_single_of_mem x (Finset.mem_univ x)]
        · simp [minkowskiMatrix.η_apply_mul_η_apply_diag, contrCoContract_basis]
        · intro b _ hb
          simp [contrCoContract_basis, ite_eq_right (Ne.symm hb)]
  rw [preCoContrUnit_apply_one, preCoContrUnitVal_expand_tmul]
  simp [map_sum]

open minkowskiMatrix in
lemma coContrContract_apply_metric {d : ℕ} :
    (TensorProduct.comm ℝ _ _ <|
    (TensorProduct.lid ℝ _).lTensor _ <|
    (coContrContract.toLinearMap.rTensor (ContrMod d)).lTensor (CoMod d) <|
    (TensorProduct.assoc ℝ (CoMod d) (ContrMod d) (ContrMod d)).symm.toLinearMap.lTensor
      (CoMod d) <|
    TensorProduct.assoc ℝ (CoMod d) (CoMod d) ((ContrMod d) ⊗[ℝ] (ContrMod d)) <|
    (preCoMetric d 1) ⊗ₜ[ℝ] (preContrMetric d 1)) = preContrCoUnit d (1 : ℝ) := by
  calc _
    _ = (TensorProduct.comm ℝ _ _ <| (TensorProduct.lid ℝ _).lTensor _ <|
      (coContrContract.toLinearMap.rTensor (ContrMod d)).lTensor (CoMod d) <|
      (TensorProduct.assoc ℝ (CoMod d) (ContrMod d) (ContrMod d)).symm.toLinearMap.lTensor
        (CoMod d) <|
      TensorProduct.assoc ℝ (CoMod d) (CoMod d) ((ContrMod d) ⊗[ℝ] (ContrMod d)) <|
      ∑ i, ∑ j, ((η i i * η j j) •
      ((coBasis d i ⊗ₜ[ℝ] coBasis d i) ⊗ₜ[ℝ] (contrBasis d j ⊗ₜ[ℝ] contrBasis d j)))) := by
        congr
        rw [preCoMetric_apply_one, preContrMetric_apply_one,
          preCoMetricVal_expand_tmul_minkowskiMatrix,
          preContrMetricVal_expand_tmul_minkowskiMatrix, sum_tmul]
        simp_rw [tmul_sum, ← smul_tmul', tmul_smul, smul_smul]
    _ = (TensorProduct.comm ℝ _ _ <| (TensorProduct.lid ℝ _).lTensor _ <|
      ∑ i, ∑ j, (minkowskiMatrix i i * minkowskiMatrix j j) •
        (coBasis d i ⊗ₜ[ℝ] (coContrContract (coBasis d i ⊗ₜ[ℝ] contrBasis d j)
          ⊗ₜ[ℝ] contrBasis d j))) := by
        congr
        simp [map_sum, map_smul]
    _ = (TensorProduct.comm ℝ _ _ <| (TensorProduct.lid ℝ _).lTensor _ <|
          ∑ i, coBasis d i ⊗ₜ[ℝ] ((1 : ℝ) ⊗ₜ[ℝ] contrBasis d i)) := by
        congr
        funext x
        rw [Finset.sum_eq_single_of_mem x (Finset.mem_univ x)]
        · simp [minkowskiMatrix.η_apply_mul_η_apply_diag, coContrContract_basis]
        · intro b _ hb
          simp [coContrContract_basis, ite_eq_right (Ne.symm hb)]
  rw [preContrCoUnit_apply_one, preContrCoUnitVal_expand_tmul]
  simp [map_sum]

end Lorentz
end
