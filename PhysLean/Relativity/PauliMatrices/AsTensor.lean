/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Relativity.Tensors.ComplexTensor.Weyl.Two
public import PhysLean.Relativity.Tensors.ComplexTensor.Vector.Pre.Basic
/-!

## Pauli matrices as a tensor

The results in this file are primarily used to show that
the pauli matrices in invariant under the `SL(2,ℂ)` action.

-/

@[expose] public section

namespace PauliMatrix

open Complex
open Lorentz
open Fermion
open TensorProduct
open CategoryTheory.MonoidalCategory

noncomputable section

open Matrix
open MatrixGroups
open Complex
open TensorProduct

/-- The tensor `σ^μ^a^{dot a}` based on the Pauli-matrices as an element of
  `complexContr ⊗ leftHanded ⊗ rightHanded`. -/
def asTensor : (complexContr ⊗ leftHanded ⊗ rightHanded).V :=
  ∑ i, complexContrBasis i ⊗ₜ leftRightToMatrix.symm (pauliBasis i)

/-- The expansion of `asTensor` into complexContrBasis basis vectors . -/
lemma asTensor_expand_complexContrBasis : asTensor =
    complexContrBasis (Sum.inl 0) ⊗ₜ leftRightToMatrix.symm (pauliBasis (Sum.inl 0))
    + complexContrBasis (Sum.inr 0) ⊗ₜ leftRightToMatrix.symm (pauliBasis (Sum.inr 0))
    + complexContrBasis (Sum.inr 1) ⊗ₜ leftRightToMatrix.symm (pauliBasis (Sum.inr 1))
    + complexContrBasis (Sum.inr 2) ⊗ₜ leftRightToMatrix.symm (pauliBasis (Sum.inr 2)) := by
  rfl

/-- The expansion of the pauli matrix `σ₀` in terms of a basis of tensor product vectors. -/
lemma leftRightToMatrix_σSA_inl_0_expand : leftRightToMatrix.symm (pauliBasis (Sum.inl 0)) =
    leftBasis 0 ⊗ₜ rightBasis 0 + leftBasis 1 ⊗ₜ rightBasis 1 := by
  rw [leftRightToMatrix_symm_expand_tmul]
  simp [pauliBasis, pauliSelfAdjoint, pauliMatrix]

  /-- The expansion of the pauli matrix `σ₁` in terms of a basis of tensor product vectors. -/
lemma leftRightToMatrix_σSA_inr_0_expand : leftRightToMatrix.symm (pauliBasis (Sum.inr 0)) =
    leftBasis 0 ⊗ₜ rightBasis 1 + leftBasis 1 ⊗ₜ rightBasis 0:= by
  rw [leftRightToMatrix_symm_expand_tmul]
  simp [pauliBasis, pauliSelfAdjoint, pauliMatrix]

/-- The expansion of the pauli matrix `σ₂` in terms of a basis of tensor product vectors. -/
lemma leftRightToMatrix_σSA_inr_1_expand : leftRightToMatrix.symm (pauliBasis (Sum.inr 1)) =
    -(I • leftBasis 0 ⊗ₜ[ℂ] rightBasis 1) + I • leftBasis 1 ⊗ₜ[ℂ] rightBasis 0 := by
  rw [leftRightToMatrix_symm_expand_tmul]
  simp [pauliBasis, pauliSelfAdjoint, pauliMatrix]

/-- The expansion of the pauli matrix `σ₃` in terms of a basis of tensor product vectors. -/
lemma leftRightToMatrix_σSA_inr_2_expand : leftRightToMatrix.symm (pauliBasis (Sum.inr 2)) =
    leftBasis 0 ⊗ₜ rightBasis 0 - leftBasis 1 ⊗ₜ rightBasis 1 := by
  rw [leftRightToMatrix_symm_expand_tmul]
  simp [pauliBasis, pauliSelfAdjoint, pauliMatrix]
  rfl

/-- The expansion of `asTensor` into complexContrBasis basis of tensor product vectors. -/
lemma asTensor_expand : asTensor =
    complexContrBasis (Sum.inl 0) ⊗ₜ (leftBasis 0 ⊗ₜ rightBasis 0)
    + complexContrBasis (Sum.inl 0) ⊗ₜ (leftBasis 1 ⊗ₜ rightBasis 1)
    + complexContrBasis (Sum.inr 0) ⊗ₜ (leftBasis 0 ⊗ₜ rightBasis 1)
    + complexContrBasis (Sum.inr 0) ⊗ₜ (leftBasis 1 ⊗ₜ rightBasis 0)
    - I • complexContrBasis (Sum.inr 1) ⊗ₜ (leftBasis 0 ⊗ₜ rightBasis 1)
    + I • complexContrBasis (Sum.inr 1) ⊗ₜ (leftBasis 1 ⊗ₜ rightBasis 0)
    + complexContrBasis (Sum.inr 2) ⊗ₜ (leftBasis 0 ⊗ₜ rightBasis 0)
    - complexContrBasis (Sum.inr 2) ⊗ₜ (leftBasis 1 ⊗ₜ rightBasis 1) := by
  rw [asTensor_expand_complexContrBasis]
  rw [leftRightToMatrix_σSA_inl_0_expand, leftRightToMatrix_σSA_inr_0_expand,
    leftRightToMatrix_σSA_inr_1_expand, leftRightToMatrix_σSA_inr_2_expand]
  simp only [CategoryTheory.Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, Fin.isValue, tmul_add, tmul_neg, tmul_smul,
    tmul_sub]
  rfl

/-- The tensor `σ^μ^a^{dot a}` based on the Pauli-matrices as a morphism,
  `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ complexContr ⊗ leftHanded ⊗ rightHanded` manifesting
  the invariance under the `SL(2,ℂ)` action. -/
def asConsTensor : 𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ complexContr ⊗ leftHanded ⊗ rightHanded where
  hom := ModuleCat.ofHom {
    toFun := fun a =>
      let a' : ℂ := a
      a' • asTensor,
    map_add' := fun x y => by
      simp only [add_smul],
    map_smul' := fun m x => by
      simp only [smul_smul]
      rfl}
  comm M := by
    refine ModuleCat.hom_ext ?_
    refine LinearMap.ext fun x : ℂ => ?_
    simp only [ModuleCat.hom_comp]
    change x • asTensor =
      (TensorProduct.map (complexContr.ρ M)
        (TensorProduct.map (leftHanded.ρ M) (rightHanded.ρ M))) (x • asTensor)
    simp only [map_smul]
    apply congrArg
    nth_rewrite 2 [asTensor]
    simp only [CategoryTheory.Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
      Action.FunctorCategoryEquivalence.functor_obj_obj, map_sum, map_tmul]
    symm
    calc _ = ∑ x, ((complexContr.ρ M) (complexContrBasis x) ⊗ₜ[ℂ]
      leftRightToMatrix.symm (SL2C.toSelfAdjointMap M (pauliBasis x))) := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [← leftRightToMatrix_ρ_symm_selfAdjoint]
      _ = ∑ x, ((∑ i, (SL2C.toLorentzGroup M).1 i x • (complexContrBasis i)) ⊗ₜ[ℂ]
          ∑ j, leftRightToMatrix.symm ((SL2C.toLorentzGroup M⁻¹).1 x j • (pauliBasis j))) := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [SL2CRep_ρ_basis, SL2C.toSelfAdjointMap_pauliBasis]
          simp only [SL2C.toLorentzGroup_apply_coe, Fintype.sum_sum_type, Finset.univ_unique,
            Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton, map_inv,
            LorentzGroup.inv_eq_dual, AddSubgroup.coe_add, selfAdjoint.val_smul,
            AddSubgroup.val_finset_sum, map_add, map_sum]
      _ = ∑ x, ∑ i, ∑ j, ((SL2C.toLorentzGroup M).1 i x • (complexContrBasis i)) ⊗ₜ[ℂ]
            leftRightToMatrix.symm.toLinearMap
              ((SL2C.toLorentzGroup M⁻¹).1 x j • (pauliBasis j)) := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [sum_tmul]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [tmul_sum]
          rfl
      _ = ∑ x, ∑ i, ∑ j, ((SL2C.toLorentzGroup M).1 i x • (complexContrBasis i)) ⊗ₜ[ℂ]
            ((SL2C.toLorentzGroup M⁻¹).1 x j • leftRightToMatrix.symm ((pauliBasis j))) := by
          refine Finset.sum_congr rfl (fun x _ => (Finset.sum_congr rfl (fun i _ =>
            (Finset.sum_congr rfl (fun j _ => ?_)))))
          simp only [SL2C.toLorentzGroup_apply_coe, map_inv, LorentzGroup.inv_eq_dual,
            LinearMap.map_smul_of_tower, LinearEquiv.coe_coe, tmul_smul]
      _ = ∑ x, ∑ i, ∑ j, ((SL2C.toLorentzGroup M).1 i x * (SL2C.toLorentzGroup M⁻¹).1 x j)
          • ((complexContrBasis i)) ⊗ₜ[ℂ] leftRightToMatrix.symm ((pauliBasis j)) := by
          refine Finset.sum_congr rfl (fun x _ => (Finset.sum_congr rfl (fun i _ =>
            (Finset.sum_congr rfl (fun j _ => ?_)))))
          rw [smul_tmul, smul_smul, tmul_smul]
      _ = ∑ i, ∑ x, ∑ j, ((SL2C.toLorentzGroup M).1 i x * (SL2C.toLorentzGroup M⁻¹).1 x j)
          • ((complexContrBasis i)) ⊗ₜ[ℂ] leftRightToMatrix.symm ((pauliBasis j)) := Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ x, ((SL2C.toLorentzGroup M).1 i x * (SL2C.toLorentzGroup M⁻¹).1 x j)
          • ((complexContrBasis i)) ⊗ₜ[ℂ] leftRightToMatrix.symm ((pauliBasis j)) :=
            Finset.sum_congr rfl (fun x _ => Finset.sum_comm)
      _ = ∑ i, ∑ j, (∑ x, (SL2C.toLorentzGroup M).1 i x * (SL2C.toLorentzGroup M⁻¹).1 x j)
          • ((complexContrBasis i)) ⊗ₜ[ℂ] leftRightToMatrix.symm ((pauliBasis j)) := by
          refine Finset.sum_congr rfl (fun i _ => (Finset.sum_congr rfl (fun j _ => ?_)))
          rw [Finset.sum_smul]
      _ = ∑ i, ∑ j, ((1 : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ) i j)
        • ((complexContrBasis i)) ⊗ₜ[ℂ] leftRightToMatrix.symm ((pauliBasis j)) := by
          refine Finset.sum_congr rfl (fun i _ => (Finset.sum_congr rfl (fun j _ => ?_)))
          congr
          change ((SL2C.toLorentzGroup M) * (SL2C.toLorentzGroup M⁻¹)).1 i j = _
          rw [← SL2C.toLorentzGroup.map_mul]
          simp only [mul_inv_cancel, _root_.map_one, lorentzGroupIsGroup_one_coe]
      _ = ∑ i, ((1 : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ) i i)
        • ((complexContrBasis i)) ⊗ₜ[ℂ] leftRightToMatrix.symm ((pauliBasis i)) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          refine Finset.sum_eq_single i (fun b _ hb => ?_) (fun hb => ?_)
          · simp [one_apply_ne' hb]
          · simp only [Finset.mem_univ, not_true_eq_false] at hb
      _ = asTensor := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp only [one_apply_eq, one_smul, CategoryTheory.Equivalence.symm_inverse,
          Action.functorCategoryEquivalence_functor,
          Action.FunctorCategoryEquivalence.functor_obj_obj]

/-- The map `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ complexContr ⊗ leftHanded ⊗ rightHanded` corresponding
  to Pauli matrices, when evaluated on `1` corresponds to the tensor `PauliMatrix.asTensor`. -/
lemma asConsTensor_apply_one : asConsTensor.hom (1 : ℂ) = asTensor := by
  change (1 : ℂ) • asTensor = asTensor
  simp only [one_smul]

end
end PauliMatrix
