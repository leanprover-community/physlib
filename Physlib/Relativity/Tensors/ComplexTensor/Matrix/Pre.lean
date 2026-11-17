/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.Vector.Basic
/-!

# Tensor products of two complex Lorentz vectors

-/

@[expose] public section
noncomputable section

open Module Matrix
open MatrixGroups
open Complex
open TensorProduct
open CategoryTheory.MonoidalCategory

namespace Lorentz

/-- Equivalence of `complexContr ⊗ complexContr` to `4 x 4` complex matrices. -/
def contrContrToMatrix : (ComplexVector ⊗[ℂ] ComplexVector) ≃ₗ[ℂ]
    Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ :=
  (Basis.tensorProduct ComplexVector.basis ComplexVector.basis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ ((Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3)

set_option backward.isDefEq.respectTransparency false in
/-- Expanding `contrContrToMatrix` in terms of the standard basis. -/
lemma contrContrToMatrix_symm_expand_tmul (M : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ) :
    contrContrToMatrix.symm M =
    ∑ i, ∑ j, M i j • (ComplexVector.basis i ⊗ₜ[ℂ] ComplexVector.basis j) := by
  simp only [contrContrToMatrix, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℂ (s := Finset.univ)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    exact congrArg _ (Basis.tensorProduct_apply ComplexVector.basis ComplexVector.basis i j)
  · simp

/-- Equivalence of `complexCo ⊗ complexCo` to `4 x 4` complex matrices. -/
def coCoToMatrix : (ComplexCoVector ⊗[ℂ] ComplexCoVector) ≃ₗ[ℂ]
    Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ :=
  (Basis.tensorProduct ComplexCoVector.basis ComplexCoVector.basis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ ((Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3)

set_option backward.isDefEq.respectTransparency false in
/-- Expanding `coCoToMatrix` in terms of the standard basis. -/
lemma coCoToMatrix_symm_expand_tmul (M : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ) :
    coCoToMatrix.symm M =
      ∑ i, ∑ j, M i j • (ComplexCoVector.basis i ⊗ₜ[ℂ] ComplexCoVector.basis j) := by
  simp only [coCoToMatrix, LinearEquiv.trans_symm, LinearEquiv.trans_apply, Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℂ (s := Finset.univ)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    exact congrArg _ (Basis.tensorProduct_apply ComplexCoVector.basis ComplexCoVector.basis i j)
  · simp

/-- Equivalence of `complexContr ⊗ complexCo` to `4 x 4` complex matrices. -/
def contrCoToMatrix : (ComplexVector ⊗[ℂ] ComplexCoVector) ≃ₗ[ℂ]
    Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ :=
  (Basis.tensorProduct ComplexVector.basis ComplexCoVector.basis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ ((Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3)

set_option backward.isDefEq.respectTransparency false in
/-- Expansion of `contrCoToMatrix` in terms of the standard basis. -/
lemma contrCoToMatrix_symm_expand_tmul (M : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ) :
    contrCoToMatrix.symm M =
      ∑ i, ∑ j, M i j • (ComplexVector.basis i ⊗ₜ[ℂ] ComplexCoVector.basis j) := by
  simp only [contrCoToMatrix, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℂ (s := Finset.univ)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    exact congrArg _ (Basis.tensorProduct_apply ComplexVector.basis ComplexCoVector.basis i j)
  · simp

/-- Equivalence of `complexCo ⊗ complexContr` to `4 x 4` complex matrices. -/
def coContrToMatrix : (ComplexCoVector ⊗[ℂ] ComplexVector) ≃ₗ[ℂ]
    Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ :=
  (Basis.tensorProduct ComplexCoVector.basis ComplexVector.basis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ ((Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3)

set_option backward.isDefEq.respectTransparency false in
/-- Expansion of `coContrToMatrix` in terms of the standard basis. -/
lemma coContrToMatrix_symm_expand_tmul (M : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ) :
    coContrToMatrix.symm M =
      ∑ i, ∑ j, M i j • (ComplexCoVector.basis i ⊗ₜ[ℂ] ComplexVector.basis j) := by
  simp only [coContrToMatrix, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℂ (s := Finset.univ)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    exact congrArg _ (Basis.tensorProduct_apply ComplexCoVector.basis ComplexVector.basis i j)
  · simp

/-!

## Group actions

-/

set_option backward.isDefEq.respectTransparency false in
lemma contrContrToMatrix_ρ (v : (ComplexVector ⊗[ℂ] ComplexVector)) (M : SL(2,ℂ)) :
    contrContrToMatrix (TensorProduct.map (ComplexVector.SL2CRep M) (ComplexVector.SL2CRep M) v) =
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M)) * contrContrToMatrix v *
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M))ᵀ := by
  nth_rewrite 1 [contrContrToMatrix]
  simp only [LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3)) ((LinearMap.toMatrix
      (ComplexVector.basis.tensorProduct ComplexVector.basis)
      (ComplexVector.basis.tensorProduct ComplexVector.basis)
      (TensorProduct.map (ComplexVector.SL2CRep M) (ComplexVector.SL2CRep M)))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ ((Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)))
      ((ComplexVector.basis.tensorProduct ComplexVector.basis).repr v)))
  · apply congrArg
    exact (LinearMap.toMatrix_mulVec_repr (ComplexVector.basis.tensorProduct ComplexVector.basis)
      (ComplexVector.basis.tensorProduct ComplexVector.basis)
      (TensorProduct.map (ComplexVector.SL2CRep M) (ComplexVector.SL2CRep M)) v).symm
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix ComplexVector.basis ComplexVector.basis) (ComplexVector.SL2CRep M))
        ((LinearMap.toMatrix ComplexVector.basis ComplexVector.basis)
          (ComplexVector.SL2CRep M)) (i, j) k)
        * contrContrToMatrix v k.1 k.2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply, Matrix.transpose_apply]
  have h1 : ∑ x, (∑ x1, LorentzGroup.toComplex (SL2C.toLorentzGroup M) i x1 *
      contrContrToMatrix v x1 x) * LorentzGroup.toComplex (SL2C.toLorentzGroup M) j x
      = ∑ x, ∑ x1, (LorentzGroup.toComplex (SL2C.toLorentzGroup M) i x1
      * contrContrToMatrix v x1 x) * LorentzGroup.toComplex (SL2C.toLorentzGroup M) j x := by
    congr
    funext x
    rw [Finset.sum_mul]
  rw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [ComplexVector.basis_ρ_apply]
  ring

set_option backward.isDefEq.respectTransparency false in
lemma coCoToMatrix_ρ (v : (ComplexCoVector ⊗[ℂ] ComplexCoVector)) (M : SL(2,ℂ)) :
    coCoToMatrix (TensorProduct.map (ComplexCoVector.SL2CRep M) (ComplexCoVector.SL2CRep M) v) =
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ᵀ * coCoToMatrix v *
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ := by
  nth_rewrite 1 [coCoToMatrix]
  simp only [LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3)) ((LinearMap.toMatrix
      (ComplexCoVector.basis.tensorProduct ComplexCoVector.basis)
      (ComplexCoVector.basis.tensorProduct ComplexCoVector.basis)
      (TensorProduct.map (ComplexCoVector.SL2CRep M) (ComplexCoVector.SL2CRep M))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ ((Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)))
      ((ComplexCoVector.basis.tensorProduct ComplexCoVector.basis).repr v))))
  · apply congrArg
    exact (LinearMap.toMatrix_mulVec_repr
      (ComplexCoVector.basis.tensorProduct ComplexCoVector.basis)
      (ComplexCoVector.basis.tensorProduct ComplexCoVector.basis)
      (TensorProduct.map (ComplexCoVector.SL2CRep M) (ComplexCoVector.SL2CRep M)) v).symm
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix ComplexCoVector.basis ComplexCoVector.basis)
          (ComplexCoVector.SL2CRep M))
        ((LinearMap.toMatrix ComplexCoVector.basis ComplexCoVector.basis)
          (ComplexCoVector.SL2CRep M)) (i, j) k)
        * coCoToMatrix v k.1 k.2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply, Matrix.transpose_apply]
  have h1 : ∑ x, (∑ x1, (LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ x1 i *
      coCoToMatrix v x1 x) * (LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ x j
      = ∑ x, ∑ x1, ((LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ x1 i
      * coCoToMatrix v x1 x) * (LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ x j := by
    congr
    funext x
    rw [Finset.sum_mul]
  rw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [ComplexCoVector.basis_ρ_apply, transpose_apply]
  ring

set_option backward.isDefEq.respectTransparency false in
lemma contrCoToMatrix_ρ (v : (ComplexVector ⊗[ℂ] ComplexCoVector)) (M : SL(2,ℂ)) :
    contrCoToMatrix (TensorProduct.map (ComplexVector.SL2CRep M) (ComplexCoVector.SL2CRep M) v) =
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M)) * contrCoToMatrix v *
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ := by
  nth_rewrite 1 [contrCoToMatrix]
  simp only [LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3)) ((LinearMap.toMatrix
      (ComplexVector.basis.tensorProduct ComplexCoVector.basis)
      (ComplexVector.basis.tensorProduct ComplexCoVector.basis)
      (TensorProduct.map (ComplexVector.SL2CRep M) (ComplexCoVector.SL2CRep M))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ ((Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)))
      ((ComplexVector.basis.tensorProduct ComplexCoVector.basis).repr v))))
  · apply congrArg
    exact (LinearMap.toMatrix_mulVec_repr (ComplexVector.basis.tensorProduct ComplexCoVector.basis)
      (ComplexVector.basis.tensorProduct ComplexCoVector.basis)
      (TensorProduct.map (ComplexVector.SL2CRep M) (ComplexCoVector.SL2CRep M)) v).symm
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix ComplexVector.basis ComplexVector.basis) (ComplexVector.SL2CRep M))
        ((LinearMap.toMatrix ComplexCoVector.basis ComplexCoVector.basis)
          (ComplexCoVector.SL2CRep M)) (i, j) k)
        * contrCoToMatrix v k.1 k.2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply]
  have h1 : ∑ x, (∑ x1, LorentzGroup.toComplex (SL2C.toLorentzGroup M) i x1 *
      contrCoToMatrix v x1 x) * (LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ x j
      = ∑ x, ∑ x1, (LorentzGroup.toComplex (SL2C.toLorentzGroup M) i x1
      * contrCoToMatrix v x1 x) * (LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ x j := by
    congr
    funext x
    rw [Finset.sum_mul]
  rw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [ComplexVector.basis_ρ_apply, ComplexCoVector.basis_ρ_apply, transpose_apply]
  ring

set_option backward.isDefEq.respectTransparency false in
lemma coContrToMatrix_ρ (v : (ComplexCoVector ⊗[ℂ] ComplexVector)) (M : SL(2,ℂ)) :
    coContrToMatrix (TensorProduct.map (ComplexCoVector.SL2CRep M) (ComplexVector.SL2CRep M) v) =
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ᵀ * coContrToMatrix v *
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M))ᵀ := by
  nth_rewrite 1 [coContrToMatrix]
  simp only [LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3)) ((LinearMap.toMatrix
      (ComplexCoVector.basis.tensorProduct ComplexVector.basis)
      (ComplexCoVector.basis.tensorProduct ComplexVector.basis)
      (TensorProduct.map (ComplexCoVector.SL2CRep M) (ComplexVector.SL2CRep M))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ ((Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)))
      ((ComplexCoVector.basis.tensorProduct ComplexVector.basis).repr v))))
  · apply congrArg
    exact (LinearMap.toMatrix_mulVec_repr (ComplexCoVector.basis.tensorProduct ComplexVector.basis)
      (ComplexCoVector.basis.tensorProduct ComplexVector.basis)
      (TensorProduct.map (ComplexCoVector.SL2CRep M) (ComplexVector.SL2CRep M)) v).symm
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix ComplexCoVector.basis ComplexCoVector.basis)
          (ComplexCoVector.SL2CRep M))
        ((LinearMap.toMatrix ComplexVector.basis ComplexVector.basis)
          (ComplexVector.SL2CRep M)) (i, j) k)
        * coContrToMatrix v k.1 k.2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply, Matrix.transpose_apply]
  have h1 : ∑ x, (∑ x1, (LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ x1 i *
      coContrToMatrix v x1 x) * (LorentzGroup.toComplex (SL2C.toLorentzGroup M)) j x
      = ∑ x, ∑ x1, ((LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ x1 i
      * coContrToMatrix v x1 x) * (LorentzGroup.toComplex (SL2C.toLorentzGroup M)) j x := by
    congr
    funext x
    rw [Finset.sum_mul]
  rw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [ComplexCoVector.basis_ρ_apply, ComplexVector.basis_ρ_apply, transpose_apply]
  ring

/-!

## The symm version of the group actions.

-/

lemma contrContrToMatrix_ρ_symm (v : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (ComplexVector.SL2CRep M) (ComplexVector.SL2CRep M)
      (contrContrToMatrix.symm v) =
    contrContrToMatrix.symm ((LorentzGroup.toComplex (SL2C.toLorentzGroup M)) * v *
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M))ᵀ) := by
  have h1 := contrContrToMatrix_ρ (contrContrToMatrix.symm v) M
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [← h1, LinearEquiv.symm_apply_apply]

lemma coCoToMatrix_ρ_symm (v : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (ComplexCoVector.SL2CRep M) (ComplexCoVector.SL2CRep M)
      (coCoToMatrix.symm v) =
    coCoToMatrix.symm ((LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ᵀ * v *
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹) := by
  have h1 := coCoToMatrix_ρ (coCoToMatrix.symm v) M
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [← h1, LinearEquiv.symm_apply_apply]

lemma contrCoToMatrix_ρ_symm (v : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (ComplexVector.SL2CRep M) (ComplexCoVector.SL2CRep M)
      (contrCoToMatrix.symm v) =
    contrCoToMatrix.symm ((LorentzGroup.toComplex (SL2C.toLorentzGroup M)) * v *
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹) := by
  have h1 := contrCoToMatrix_ρ (contrCoToMatrix.symm v) M
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [← h1, LinearEquiv.symm_apply_apply]

lemma coContrToMatrix_ρ_symm (v : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (ComplexCoVector.SL2CRep M) (ComplexVector.SL2CRep M)
      (coContrToMatrix.symm v) =
    coContrToMatrix.symm ((LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ᵀ * v *
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M))ᵀ) := by
  have h1 := coContrToMatrix_ρ (coContrToMatrix.symm v) M
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [← h1, LinearEquiv.symm_apply_apply]

end Lorentz
end
