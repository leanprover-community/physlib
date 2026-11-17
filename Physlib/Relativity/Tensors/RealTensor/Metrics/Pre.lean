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
def ContrMod.metricVal (d : ℕ := 3) : ContrMod d ⊗[ℝ] ContrMod d :=
  contrContrToMatrixRe.symm ((@minkowskiMatrix d))

lemma ContrMod.metricVal_expand_tmul_minkowskiMatrix {d : ℕ} : ContrMod.metricVal d =
    ∑ i, (minkowskiMatrix i i) • (contrBasis d i ⊗ₜ[ℝ] contrBasis d i) := by
  rw [ContrMod.metricVal, contrContrToMatrixRe_symm_expand_tmul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
    fun j _ hj => smul_eq_zero_of_left (minkowskiMatrix.off_diag_zero hj.symm) _

/-- Expansion of `ContrMod.metricVal` into basis. -/
lemma ContrMod.metricVal_expand_tmul {d : ℕ} : ContrMod.metricVal d =
    contrBasis d (Sum.inl 0) ⊗ₜ[ℝ] contrBasis d (Sum.inl 0) -
    ∑ i, contrBasis d (Sum.inr i) ⊗ₜ[ℝ] contrBasis d (Sum.inr i) := by
  rw [ContrMod.metricVal_expand_tmul_minkowskiMatrix]
  simp [Fintype.sum_sum_type, minkowskiMatrix.inl_0_inl_0, minkowskiMatrix.inr_i_inr_i,
    sub_eq_add_neg]

/-- The metric `ηᵃᵃ` as a morphism `𝟙_ (Rep ℝ (LorentzGroup d)) ⟶ ContrMod.rep ⊗ ContrMod.rep`,
  making its invariance under the action of `LorentzGroup d`. -/
def ContrMod.metric (d : ℕ := 3) :
    (Representation.trivial ℝ (LorentzGroup d) ℝ).IntertwiningMap
    ((ContrMod.rep).tprod (ContrMod.rep)) where
  toFun := fun a => a • (ContrMod.metricVal d)
  map_add' := fun x y => add_smul x y _
  map_smul' := fun m x => mul_smul m x _
  isIntertwining' M := by
    refine LinearMap.ext fun x : ℝ => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply]
    change x • (ContrMod.metricVal d) =
      (TensorProduct.map (ContrMod.rep M) (ContrMod.rep M)) (x • (ContrMod.metricVal d))
    simp only [map_smul]
    apply congrArg
    simp only [ContrMod.metricVal]
    conv_rhs =>
      rw [contrContrToMatrixRe_ρ_symm]
    apply congrArg
    simp

lemma ContrMod.metric_apply_one {d : ℕ} : (ContrMod.metric d) (1 : ℝ) = ContrMod.metricVal d :=
  one_smul ℝ _

/-- The metric `ηᵢᵢ` as an element of `(CoMod d ⊗[ℝ] CoMod d)`. -/
def CoMod.metricVal (d : ℕ := 3) : CoMod d ⊗[ℝ] CoMod d :=
  coCoToMatrixRe.symm ((@minkowskiMatrix d))

lemma CoMod.metricVal_expand_tmul_minkowskiMatrix {d : ℕ} : CoMod.metricVal d =
    ∑ i, (minkowskiMatrix i i) • (coBasis d i ⊗ₜ[ℝ] coBasis d i) := by
  rw [CoMod.metricVal, coCoToMatrixRe_symm_expand_tmul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
    fun j _ hj => smul_eq_zero_of_left (minkowskiMatrix.off_diag_zero hj.symm) _

/-- Expansion of `ContrMod.metricVal` into basis. -/
lemma CoMod.metricVal_expand_tmul {d : ℕ} : CoMod.metricVal d =
    coBasis d (Sum.inl 0) ⊗ₜ[ℝ] coBasis d (Sum.inl 0) -
    ∑ i, coBasis d (Sum.inr i) ⊗ₜ[ℝ] coBasis d (Sum.inr i) := by
  rw [CoMod.metricVal_expand_tmul_minkowskiMatrix]
  simp [Fintype.sum_sum_type, minkowskiMatrix.inl_0_inl_0, minkowskiMatrix.inr_i_inr_i,
    sub_eq_add_neg]

/-- The metric `ηᵢᵢ` as a morphism `𝟙_ (Rep ℂ (LorentzGroup d))) ⟶ CoMod.rep ⊗ CoMod.rep`,
  making its invariance under the action of `LorentzGroup d`. -/
def CoMod.metric (d : ℕ := 3) : (Representation.trivial ℝ (LorentzGroup d) ℝ).IntertwiningMap
    ((CoMod.rep).tprod (CoMod.rep)) where
  toFun := fun a => a • CoMod.metricVal d
  map_add' := fun x y => add_smul x y _
  map_smul' := fun m x => mul_smul m x _
  isIntertwining' M := by
    refine LinearMap.ext fun x : ℝ => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply]
    change x • CoMod.metricVal d =
      (TensorProduct.map (CoMod.rep M) (CoMod.rep M)) (x • CoMod.metricVal d)
    simp only [_root_.map_smul]
    apply congrArg
    simp only [CoMod.metricVal]
    rw [coCoToMatrixRe_ρ_symm]
    apply congrArg
    rw [← LorentzGroup.coe_inv, LorentzGroup.transpose_mul_minkowskiMatrix_mul_self]

lemma CoMod.metric_apply_one {d : ℕ} : (CoMod.metric d) (1 : ℝ) = CoMod.metricVal d :=
  one_smul ℝ _

/-!

## Contraction of metrics

-/

open minkowskiMatrix in
lemma ContrMod.contr_metric {d : ℕ} :
    (TensorProduct.comm ℝ _ _ <|
      (TensorProduct.lid ℝ _).lTensor _ <|
      (ContrMod.contr.toLinearMap.rTensor (CoMod d)).lTensor (ContrMod d) <|
      (TensorProduct.assoc ℝ (ContrMod d) (CoMod d) (CoMod d)).symm.toLinearMap.lTensor
        (ContrMod d) <|
      TensorProduct.assoc ℝ (ContrMod d) (ContrMod d) ((CoMod d) ⊗[ℝ] (CoMod d)) <|
      (ContrMod.metric d 1) ⊗ₜ[ℝ] (CoMod.metric d 1)) = ContrMod.unit d (1 : ℝ) := by
  calc _
    _ = (TensorProduct.comm ℝ _ _ <|
      (TensorProduct.lid ℝ _).lTensor _ <|
      (ContrMod.contr.toLinearMap.rTensor (CoMod d)).lTensor (ContrMod d) <|
      (TensorProduct.assoc ℝ (ContrMod d) (CoMod d) (CoMod d)).symm.toLinearMap.lTensor
        (ContrMod d) <|
      TensorProduct.assoc ℝ (ContrMod d) (ContrMod d) ((CoMod d) ⊗[ℝ] (CoMod d)) <|
      ∑ i, ∑ j, ((η i i * η j j) •
      ((contrBasis d i ⊗ₜ[ℝ] contrBasis d i) ⊗ₜ[ℝ] (coBasis d j ⊗ₜ[ℝ] coBasis d j)))) := by
        congr
        rw [ContrMod.metric_apply_one, CoMod.metric_apply_one,
          ContrMod.metricVal_expand_tmul_minkowskiMatrix,
          CoMod.metricVal_expand_tmul_minkowskiMatrix, sum_tmul]
        simp_rw [tmul_sum, ← smul_tmul', tmul_smul, smul_smul]
    _ = (TensorProduct.comm ℝ _ _ <| (TensorProduct.lid ℝ _).lTensor _ <|
      ∑ i, ∑ j, (minkowskiMatrix i i * minkowskiMatrix j j) •
        (contrBasis d i ⊗ₜ[ℝ] (ContrMod.contr (contrBasis d i ⊗ₜ[ℝ] coBasis d j)
          ⊗ₜ[ℝ] coBasis d j))) := by
        congr
        simp [map_sum, map_smul]
    _ = (TensorProduct.comm ℝ _ _ <| (TensorProduct.lid ℝ _).lTensor _ <|
          ∑ i, contrBasis d i ⊗ₜ[ℝ] ((1 : ℝ) ⊗ₜ[ℝ] coBasis d i)) := by
        congr
        funext x
        rw [Finset.sum_eq_single_of_mem x (Finset.mem_univ x)]
        · simp [minkowskiMatrix.η_apply_mul_η_apply_diag, ContrMod.contr_basis]
        · intro b _ hb
          simp [ContrMod.contr_basis, ite_eq_right (Ne.symm hb)]
  rw [ContrMod.unit_apply_one, ContrMod.unitVal_expand_tmul]
  simp [map_sum]

open minkowskiMatrix in
lemma CoMod.contr_metric {d : ℕ} :
    (TensorProduct.comm ℝ _ _ <|
    (TensorProduct.lid ℝ _).lTensor _ <|
    (CoMod.contr.toLinearMap.rTensor (ContrMod d)).lTensor (CoMod d) <|
    (TensorProduct.assoc ℝ (CoMod d) (ContrMod d) (ContrMod d)).symm.toLinearMap.lTensor
      (CoMod d) <|
    TensorProduct.assoc ℝ (CoMod d) (CoMod d) ((ContrMod d) ⊗[ℝ] (ContrMod d)) <|
    (CoMod.metric d 1) ⊗ₜ[ℝ] (ContrMod.metric d 1)) = CoMod.unit d (1 : ℝ) := by
  calc _
    _ = (TensorProduct.comm ℝ _ _ <| (TensorProduct.lid ℝ _).lTensor _ <|
      (CoMod.contr.toLinearMap.rTensor (ContrMod d)).lTensor (CoMod d) <|
      (TensorProduct.assoc ℝ (CoMod d) (ContrMod d) (ContrMod d)).symm.toLinearMap.lTensor
        (CoMod d) <|
      TensorProduct.assoc ℝ (CoMod d) (CoMod d) ((ContrMod d) ⊗[ℝ] (ContrMod d)) <|
      ∑ i, ∑ j, ((η i i * η j j) •
      ((coBasis d i ⊗ₜ[ℝ] coBasis d i) ⊗ₜ[ℝ] (contrBasis d j ⊗ₜ[ℝ] contrBasis d j)))) := by
        congr
        rw [CoMod.metric_apply_one, ContrMod.metric_apply_one,
          CoMod.metricVal_expand_tmul_minkowskiMatrix,
          ContrMod.metricVal_expand_tmul_minkowskiMatrix, sum_tmul]
        simp_rw [tmul_sum, ← smul_tmul', tmul_smul, smul_smul]
    _ = (TensorProduct.comm ℝ _ _ <| (TensorProduct.lid ℝ _).lTensor _ <|
      ∑ i, ∑ j, (minkowskiMatrix i i * minkowskiMatrix j j) •
        (coBasis d i ⊗ₜ[ℝ] (CoMod.contr (coBasis d i ⊗ₜ[ℝ] contrBasis d j)
          ⊗ₜ[ℝ] contrBasis d j))) := by
        congr
        simp [map_sum, map_smul]
    _ = (TensorProduct.comm ℝ _ _ <| (TensorProduct.lid ℝ _).lTensor _ <|
          ∑ i, coBasis d i ⊗ₜ[ℝ] ((1 : ℝ) ⊗ₜ[ℝ] contrBasis d i)) := by
        congr
        funext x
        rw [Finset.sum_eq_single_of_mem x (Finset.mem_univ x)]
        · simp [minkowskiMatrix.η_apply_mul_η_apply_diag, CoMod.contr_basis]
        · intro b _ hb
          simp [CoMod.contr_basis, ite_eq_right (Ne.symm hb)]
  rw [CoMod.unit_apply_one, CoMod.unitVal_expand_tmul]
  simp [map_sum]

end Lorentz
end
