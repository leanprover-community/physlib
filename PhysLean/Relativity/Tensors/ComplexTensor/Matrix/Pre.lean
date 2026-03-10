/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Relativity.Tensors.ComplexTensor.Vector.Pre.Basic
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
def contrContrToMatrix : (complexContr ⊗ complexContr).V ≃ₗ[ℂ]
    Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ :=
  (Basis.tensorProduct complexContrBasis complexContrBasis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ ((Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3)

/-- Expanding `contrContrToMatrix` in terms of the standard basis. -/
lemma contrContrToMatrix_symm_expand_tmul (M : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ) :
    contrContrToMatrix.symm M =
    ∑ i, ∑ j, M i j • (complexContrBasis i ⊗ₜ[ℂ] complexContrBasis j) := by
  simp only [contrContrToMatrix, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℂ (s := Finset.univ)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    erw [Basis.tensorProduct_apply complexContrBasis complexContrBasis i j]
    rfl
  · simp

/-- Equivalence of `complexCo ⊗ complexCo` to `4 x 4` complex matrices. -/
def coCoToMatrix : (complexCo ⊗ complexCo).V ≃ₗ[ℂ]
    Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ :=
  (Basis.tensorProduct complexCoBasis complexCoBasis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ ((Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3)

/-- Expanding `coCoToMatrix` in terms of the standard basis. -/
lemma coCoToMatrix_symm_expand_tmul (M : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ) :
    coCoToMatrix.symm M = ∑ i, ∑ j, M i j • (complexCoBasis i ⊗ₜ[ℂ] complexCoBasis j) := by
  simp only [coCoToMatrix, LinearEquiv.trans_symm, LinearEquiv.trans_apply, Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℂ (s := Finset.univ)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    erw [Basis.tensorProduct_apply complexCoBasis complexCoBasis i j]
    rfl
  · simp

/-- Equivalence of `complexContr ⊗ complexCo` to `4 x 4` complex matrices. -/
def contrCoToMatrix : (complexContr ⊗ complexCo).V ≃ₗ[ℂ]
    Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ :=
  (Basis.tensorProduct complexContrBasis complexCoBasis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ ((Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3)

/-- Expansion of `contrCoToMatrix` in terms of the standard basis. -/
lemma contrCoToMatrix_symm_expand_tmul (M : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ) :
    contrCoToMatrix.symm M = ∑ i, ∑ j, M i j • (complexContrBasis i ⊗ₜ[ℂ] complexCoBasis j) := by
  simp only [contrCoToMatrix, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℂ (s := Finset.univ)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    erw [Basis.tensorProduct_apply complexContrBasis complexCoBasis i j]
    rfl
  · simp

/-- Equivalence of `complexCo ⊗ complexContr` to `4 x 4` complex matrices. -/
def coContrToMatrix : (complexCo ⊗ complexContr).V ≃ₗ[ℂ]
    Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ :=
  (Basis.tensorProduct complexCoBasis complexContrBasis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ ((Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3)

/-- Expansion of `coContrToMatrix` in terms of the standard basis. -/
lemma coContrToMatrix_symm_expand_tmul (M : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ) :
    coContrToMatrix.symm M = ∑ i, ∑ j, M i j • (complexCoBasis i ⊗ₜ[ℂ] complexContrBasis j) := by
  simp only [coContrToMatrix, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℂ (s := Finset.univ)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    erw [Basis.tensorProduct_apply complexCoBasis complexContrBasis i j]
    rfl
  · simp

/-!

## Group actions

-/

lemma contrContrToMatrix_ρ (v : (complexContr ⊗ complexContr).V) (M : SL(2,ℂ)) :
    contrContrToMatrix (TensorProduct.map (complexContr.ρ M) (complexContr.ρ M) v) =
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M)) * contrContrToMatrix v *
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M))ᵀ := by
  nth_rewrite 1 [contrContrToMatrix]
  simp only [LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3)) ((LinearMap.toMatrix
      (complexContrBasis.tensorProduct complexContrBasis)
      (complexContrBasis.tensorProduct complexContrBasis)
      (TensorProduct.map (complexContr.ρ M) (complexContr.ρ M)))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ ((Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)))
      ((complexContrBasis.tensorProduct complexContrBasis).repr v)))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr (complexContrBasis.tensorProduct complexContrBasis)
      (complexContrBasis.tensorProduct complexContrBasis)
      (TensorProduct.map (complexContr.ρ M) (complexContr.ρ M)) v)
    erw [h1]
    rfl
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix complexContrBasis complexContrBasis) (complexContr.ρ M))
        ((LinearMap.toMatrix complexContrBasis complexContrBasis) (complexContr.ρ M)) (i, j) k)
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
  erw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [complexContrBasis_ρ_apply]
  ring

lemma coCoToMatrix_ρ (v : (complexCo ⊗ complexCo).V) (M : SL(2,ℂ)) :
    coCoToMatrix (TensorProduct.map (complexCo.ρ M) (complexCo.ρ M) v) =
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ᵀ * coCoToMatrix v *
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ := by
  nth_rewrite 1 [coCoToMatrix]
  simp only [LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3)) ((LinearMap.toMatrix
      (complexCoBasis.tensorProduct complexCoBasis)
      (complexCoBasis.tensorProduct complexCoBasis)
      (TensorProduct.map (complexCo.ρ M) (complexCo.ρ M))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ ((Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)))
      ((complexCoBasis.tensorProduct complexCoBasis).repr v))))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr (complexCoBasis.tensorProduct complexCoBasis)
      (complexCoBasis.tensorProduct complexCoBasis)
      (TensorProduct.map (complexCo.ρ M) (complexCo.ρ M)) v)
    erw [h1]
    rfl
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix complexCoBasis complexCoBasis) (complexCo.ρ M))
        ((LinearMap.toMatrix complexCoBasis complexCoBasis) (complexCo.ρ M)) (i, j) k)
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
  erw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [complexCoBasis_ρ_apply, transpose_apply]
  ring

lemma contrCoToMatrix_ρ (v : (complexContr ⊗ complexCo).V) (M : SL(2,ℂ)) :
    contrCoToMatrix (TensorProduct.map (complexContr.ρ M) (complexCo.ρ M) v) =
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M)) * contrCoToMatrix v *
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ := by
  nth_rewrite 1 [contrCoToMatrix]
  simp only [LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3)) ((LinearMap.toMatrix
      (complexContrBasis.tensorProduct complexCoBasis)
      (complexContrBasis.tensorProduct complexCoBasis)
      (TensorProduct.map (complexContr.ρ M) (complexCo.ρ M))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ ((Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)))
      ((complexContrBasis.tensorProduct complexCoBasis).repr v))))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr (complexContrBasis.tensorProduct complexCoBasis)
      (complexContrBasis.tensorProduct complexCoBasis)
      (TensorProduct.map (complexContr.ρ M) (complexCo.ρ M)) v)
    erw [h1]
    rfl
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix complexContrBasis complexContrBasis) (complexContr.ρ M))
        ((LinearMap.toMatrix complexCoBasis complexCoBasis) (complexCo.ρ M)) (i, j) k)
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
  erw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [complexContrBasis_ρ_apply, complexCoBasis_ρ_apply, transpose_apply]
  ring

lemma coContrToMatrix_ρ (v : (complexCo ⊗ complexContr).V) (M : SL(2,ℂ)) :
    coContrToMatrix (TensorProduct.map (complexCo.ρ M) (complexContr.ρ M) v) =
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ᵀ * coContrToMatrix v *
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M))ᵀ := by
  nth_rewrite 1 [coContrToMatrix]
  simp only [LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3)) ((LinearMap.toMatrix
      (complexCoBasis.tensorProduct complexContrBasis)
      (complexCoBasis.tensorProduct complexContrBasis)
      (TensorProduct.map (complexCo.ρ M) (complexContr.ρ M))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ ((Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)))
      ((complexCoBasis.tensorProduct complexContrBasis).repr v))))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr (complexCoBasis.tensorProduct complexContrBasis)
      (complexCoBasis.tensorProduct complexContrBasis)
      (TensorProduct.map (complexCo.ρ M) (complexContr.ρ M)) v)
    erw [h1]
    rfl
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix complexCoBasis complexCoBasis) (complexCo.ρ M))
        ((LinearMap.toMatrix complexContrBasis complexContrBasis) (complexContr.ρ M)) (i, j) k)
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
  erw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [complexCoBasis_ρ_apply, complexContrBasis_ρ_apply, transpose_apply]
  ring

/-!

## The symm version of the group actions.

-/

lemma contrContrToMatrix_ρ_symm (v : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (complexContr.ρ M) (complexContr.ρ M) (contrContrToMatrix.symm v) =
    contrContrToMatrix.symm ((LorentzGroup.toComplex (SL2C.toLorentzGroup M)) * v *
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M))ᵀ) := by
  have h1 := contrContrToMatrix_ρ (contrContrToMatrix.symm v) M
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [← h1]
  simp

lemma coCoToMatrix_ρ_symm (v : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (complexCo.ρ M) (complexCo.ρ M) (coCoToMatrix.symm v) =
    coCoToMatrix.symm ((LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ᵀ * v *
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹) := by
  have h1 := coCoToMatrix_ρ (coCoToMatrix.symm v) M
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [← h1]
  simp

lemma contrCoToMatrix_ρ_symm (v : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (complexContr.ρ M) (complexCo.ρ M) (contrCoToMatrix.symm v) =
    contrCoToMatrix.symm ((LorentzGroup.toComplex (SL2C.toLorentzGroup M)) * v *
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹) := by
  have h1 := contrCoToMatrix_ρ (contrCoToMatrix.symm v) M
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [← h1]
  simp

lemma coContrToMatrix_ρ_symm (v : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (complexCo.ρ M) (complexContr.ρ M) (coContrToMatrix.symm v) =
    coContrToMatrix.symm ((LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ᵀ * v *
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M))ᵀ) := by
  have h1 := coContrToMatrix_ρ (coContrToMatrix.symm v) M
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [← h1]
  simp

end Lorentz
end
