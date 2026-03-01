/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.ComplexTensor.Weyl.Basic
/-!

# Tensor product of two Weyl fermion

-/

namespace Fermion
noncomputable section

open Module Matrix
open MatrixGroups
open Complex
open TensorProduct
open CategoryTheory.MonoidalCategory

/-!

## Equivalences to matrices.

-/

/-- Equivalence of `leftHanded ⊗ leftHanded` to `2 x 2` complex matrices. -/
def leftLeftToMatrix : (leftHanded ⊗ leftHanded).V ≃ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct leftBasis leftBasis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

/-- Expanding `leftLeftToMatrix` in terms of the standard basis. -/
lemma leftLeftToMatrix_symm_expand_tmul (M : Matrix (Fin 2) (Fin 2) ℂ) :
    leftLeftToMatrix.symm M = ∑ i, ∑ j, M i j • (leftBasis i ⊗ₜ[ℂ] leftBasis j) := by
  simp only [leftLeftToMatrix, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℂ (s := Finset.univ)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    exact congrArg _ (Basis.tensorProduct_apply leftBasis leftBasis i j)
  · simp

/-- Equivalence of `altLeftHanded ⊗ altLeftHanded` to `2 x 2` complex matrices. -/
def altLeftaltLeftToMatrix : (altLeftHanded ⊗ altLeftHanded).V ≃ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct altLeftBasis altLeftBasis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

/-- Expanding `altLeftaltLeftToMatrix` in terms of the standard basis. -/
lemma altLeftaltLeftToMatrix_symm_expand_tmul (M : Matrix (Fin 2) (Fin 2) ℂ) :
    altLeftaltLeftToMatrix.symm M = ∑ i, ∑ j, M i j • (altLeftBasis i ⊗ₜ[ℂ] altLeftBasis j) := by
  simp only [altLeftaltLeftToMatrix, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℂ (s := Finset.univ)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    exact congrArg _ (Basis.tensorProduct_apply altLeftBasis altLeftBasis i j)
  · simp

/-- Equivalence of `leftHanded ⊗ altLeftHanded` to `2 x 2` complex matrices. -/
def leftAltLeftToMatrix : (leftHanded ⊗ altLeftHanded).V ≃ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct leftBasis altLeftBasis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

/-- Expanding `leftAltLeftToMatrix` in terms of the standard basis. -/
lemma leftAltLeftToMatrix_symm_expand_tmul (M : Matrix (Fin 2) (Fin 2) ℂ) :
    leftAltLeftToMatrix.symm M = ∑ i, ∑ j, M i j • (leftBasis i ⊗ₜ[ℂ] altLeftBasis j) := by
  simp only [leftAltLeftToMatrix, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℂ (s := Finset.univ)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    exact congrArg _ (Basis.tensorProduct_apply leftBasis altLeftBasis i j)
  · simp

/-- Equivalence of `altLeftHanded ⊗ leftHanded` to `2 x 2` complex matrices. -/
def altLeftLeftToMatrix : (altLeftHanded ⊗ leftHanded).V ≃ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct altLeftBasis leftBasis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

/-- Expanding `altLeftLeftToMatrix` in terms of the standard basis. -/
lemma altLeftLeftToMatrix_symm_expand_tmul (M : Matrix (Fin 2) (Fin 2) ℂ) :
    altLeftLeftToMatrix.symm M = ∑ i, ∑ j, M i j • (altLeftBasis i ⊗ₜ[ℂ] leftBasis j) := by
  simp only [altLeftLeftToMatrix, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℂ (s := Finset.univ)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    exact congrArg _ (Basis.tensorProduct_apply altLeftBasis leftBasis i j)
  · simp

/-- Equivalence of `rightHanded ⊗ rightHanded` to `2 x 2` complex matrices. -/
def rightRightToMatrix : (rightHanded ⊗ rightHanded).V ≃ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct rightBasis rightBasis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

/-- Expanding `rightRightToMatrix` in terms of the standard basis. -/
lemma rightRightToMatrix_symm_expand_tmul (M : Matrix (Fin 2) (Fin 2) ℂ) :
    rightRightToMatrix.symm M = ∑ i, ∑ j, M i j • (rightBasis i ⊗ₜ[ℂ] rightBasis j) := by
  simp only [rightRightToMatrix, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℂ (s := Finset.univ)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    exact congrArg _ (Basis.tensorProduct_apply rightBasis rightBasis i j)
  · simp

/-- Equivalence of `altRightHanded ⊗ altRightHanded` to `2 x 2` complex matrices. -/
def altRightAltRightToMatrix : (altRightHanded ⊗ altRightHanded).V ≃ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct altRightBasis altRightBasis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

/-- Expanding `altRightAltRightToMatrix` in terms of the standard basis. -/
lemma altRightAltRightToMatrix_symm_expand_tmul (M : Matrix (Fin 2) (Fin 2) ℂ) :
    altRightAltRightToMatrix.symm M =
    ∑ i, ∑ j, M i j • (altRightBasis i ⊗ₜ[ℂ] altRightBasis j) := by
  simp only [altRightAltRightToMatrix, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℂ (s := Finset.univ)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    exact congrArg _ (Basis.tensorProduct_apply altRightBasis altRightBasis i j)
  · simp

/-- Equivalence of `rightHanded ⊗ altRightHanded` to `2 x 2` complex matrices. -/
def rightAltRightToMatrix : (rightHanded ⊗ altRightHanded).V ≃ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct rightBasis altRightBasis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

/-- Expanding `rightAltRightToMatrix` in terms of the standard basis. -/
lemma rightAltRightToMatrix_symm_expand_tmul (M : Matrix (Fin 2) (Fin 2) ℂ) :
    rightAltRightToMatrix.symm M = ∑ i, ∑ j, M i j • (rightBasis i ⊗ₜ[ℂ] altRightBasis j) := by
  simp only [rightAltRightToMatrix, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℂ (s := Finset.univ)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    exact congrArg _ (Basis.tensorProduct_apply rightBasis altRightBasis i j)
  · simp

/-- Equivalence of `altRightHanded ⊗ rightHanded` to `2 x 2` complex matrices. -/
def altRightRightToMatrix : (altRightHanded ⊗ rightHanded).V ≃ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct altRightBasis rightBasis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

/-- Expanding `altRightRightToMatrix` in terms of the standard basis. -/
lemma altRightRightToMatrix_symm_expand_tmul (M : Matrix (Fin 2) (Fin 2) ℂ) :
    altRightRightToMatrix.symm M = ∑ i, ∑ j, M i j • (altRightBasis i ⊗ₜ[ℂ] rightBasis j) := by
  simp only [altRightRightToMatrix, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℂ (s := Finset.univ)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    exact congrArg _ (Basis.tensorProduct_apply altRightBasis rightBasis i j)
  · simp

/-- Equivalence of `altLeftHanded ⊗ altRightHanded` to `2 x 2` complex matrices. -/
def altLeftAltRightToMatrix : (altLeftHanded ⊗ altRightHanded).V ≃ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct altLeftBasis altRightBasis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

/-- Expanding `altLeftAltRightToMatrix` in terms of the standard basis. -/
lemma altLeftAltRightToMatrix_symm_expand_tmul (M : Matrix (Fin 2) (Fin 2) ℂ) :
    altLeftAltRightToMatrix.symm M = ∑ i, ∑ j, M i j • (altLeftBasis i ⊗ₜ[ℂ] altRightBasis j) := by
  simp only [altLeftAltRightToMatrix, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℂ (s := Finset.univ)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    exact congrArg _ (Basis.tensorProduct_apply altLeftBasis altRightBasis i j)
  · simp

/-- Equivalence of `leftHanded ⊗ rightHanded` to `2 x 2` complex matrices. -/
def leftRightToMatrix : (leftHanded ⊗ rightHanded).V ≃ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct leftBasis rightBasis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

/-- Expanding `leftRightToMatrix` in terms of the standard basis. -/
lemma leftRightToMatrix_symm_expand_tmul (M : Matrix (Fin 2) (Fin 2) ℂ) :
    leftRightToMatrix.symm M = ∑ i, ∑ j, M i j • (leftBasis i ⊗ₜ[ℂ] rightBasis j) := by
  simp only [leftRightToMatrix, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℂ (s := Finset.univ)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    exact congrArg _ (Basis.tensorProduct_apply leftBasis rightBasis i j)
  · simp

/-!

## Group actions

-/

/-- The group action of `SL(2,ℂ)` on `leftHanded ⊗ leftHanded` is equivalent to
  `M.1 * leftLeftToMatrix v * (M.1)ᵀ`. -/
lemma leftLeftToMatrix_ρ (v : (leftHanded ⊗ leftHanded).V) (M : SL(2,ℂ)) :
    leftLeftToMatrix (TensorProduct.map (leftHanded.ρ M) (leftHanded.ρ M) v) =
    M.1 * leftLeftToMatrix v * (M.1)ᵀ := by
  nth_rewrite 1 [leftLeftToMatrix]
  simp only [LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)) ((LinearMap.toMatrix
      (leftBasis.tensorProduct leftBasis) (leftBasis.tensorProduct leftBasis)
      (TensorProduct.map (leftHanded.ρ M) (leftHanded.ρ M)))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2))
      ((leftBasis.tensorProduct leftBasis).repr (v))))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr (leftBasis.tensorProduct leftBasis)
      (leftBasis.tensorProduct leftBasis) (TensorProduct.map (leftHanded.ρ M) (leftHanded.ρ M)) v)
    erw [h1]
    rfl
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix leftBasis leftBasis) (leftHanded.ρ M))
        ((LinearMap.toMatrix leftBasis leftBasis) (leftHanded.ρ M)) (i, j) k)
        * leftLeftToMatrix v k.1 k.2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply, Matrix.transpose_apply]
  have h1 : ∑ x : Fin 2, (∑ j : Fin 2, M.1 i j * leftLeftToMatrix v j x) * M.1 j x
    = ∑ x : Fin 2, ∑ x1 : Fin 2, (M.1 i x1 * leftLeftToMatrix v x1 x) * M.1 j x := by
    congr
    funext x
    rw [Finset.sum_mul]
  erw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [leftBasis_ρ_apply]
  rw [mul_assoc]
  nth_rewrite 2 [mul_comm]
  rw [← mul_assoc]

/-- The group action of `SL(2,ℂ)` on `altLeftHanded ⊗ altLeftHanded` is equivalent to
  `(M.1⁻¹)ᵀ * leftLeftToMatrix v * (M.1⁻¹)`. -/
lemma altLeftaltLeftToMatrix_ρ (v : (altLeftHanded ⊗ altLeftHanded).V) (M : SL(2,ℂ)) :
    altLeftaltLeftToMatrix (TensorProduct.map (altLeftHanded.ρ M) (altLeftHanded.ρ M) v) =
    (M.1⁻¹)ᵀ * altLeftaltLeftToMatrix v * (M.1⁻¹) := by
  nth_rewrite 1 [altLeftaltLeftToMatrix]
  simp only [LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)) ((LinearMap.toMatrix
      (altLeftBasis.tensorProduct altLeftBasis) (altLeftBasis.tensorProduct altLeftBasis)
      (TensorProduct.map (altLeftHanded.ρ M) (altLeftHanded.ρ M)))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2))
      ((altLeftBasis.tensorProduct altLeftBasis).repr v)))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr (altLeftBasis.tensorProduct altLeftBasis)
      (altLeftBasis.tensorProduct altLeftBasis)
      (TensorProduct.map (altLeftHanded.ρ M) (altLeftHanded.ρ M)) v)
    erw [h1]
    rfl
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix altLeftBasis altLeftBasis) (altLeftHanded.ρ M))
        ((LinearMap.toMatrix altLeftBasis altLeftBasis) (altLeftHanded.ρ M)) (i, j) k)
        * altLeftaltLeftToMatrix v k.1 k.2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply, Matrix.transpose_apply]
  have h1 : ∑ x : Fin 2, (∑ x1 : Fin 2, (M.1)⁻¹ x1 i * altLeftaltLeftToMatrix v x1 x) * (M.1)⁻¹ x j
    = ∑ x : Fin 2, ∑ x1 : Fin 2, ((M.1)⁻¹ x1 i * altLeftaltLeftToMatrix v x1 x) * (M.1)⁻¹ x j := by
    congr
    funext x
    rw [Finset.sum_mul]
  erw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [altLeftBasis_ρ_apply, transpose_apply]
  ring

/-- The group action of `SL(2,ℂ)` on `leftHanded ⊗ altLeftHanded` is equivalent to
  `M.1 * leftAltLeftToMatrix v * (M.1⁻¹)`. -/
lemma leftAltLeftToMatrix_ρ (v : (leftHanded ⊗ altLeftHanded).V) (M : SL(2,ℂ)) :
    leftAltLeftToMatrix (TensorProduct.map (leftHanded.ρ M) (altLeftHanded.ρ M) v) =
    M.1 * leftAltLeftToMatrix v * (M.1⁻¹) := by
  nth_rewrite 1 [leftAltLeftToMatrix]
  simp only [LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)) ((LinearMap.toMatrix
      (leftBasis.tensorProduct altLeftBasis) (leftBasis.tensorProduct altLeftBasis)
      (TensorProduct.map (leftHanded.ρ M) (altLeftHanded.ρ M)))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2))
      ((leftBasis.tensorProduct altLeftBasis).repr (v))))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr (leftBasis.tensorProduct altLeftBasis)
      (leftBasis.tensorProduct altLeftBasis)
      (TensorProduct.map (leftHanded.ρ M) (altLeftHanded.ρ M)) v)
    erw [h1]
    rfl
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix leftBasis leftBasis) (leftHanded.ρ M))
        ((LinearMap.toMatrix altLeftBasis altLeftBasis) (altLeftHanded.ρ M)) (i, j) k)
        * leftAltLeftToMatrix v k.1 k.2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply]
  have h1 : ∑ x : Fin 2, (∑ x1 : Fin 2, M.1 i x1 * leftAltLeftToMatrix v x1 x) * (M.1⁻¹) x j
    = ∑ x : Fin 2, ∑ x1 : Fin 2, (M.1 i x1 * leftAltLeftToMatrix v x1 x) * (M.1⁻¹) x j := by
    congr
    funext x
    rw [Finset.sum_mul]
  erw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [leftBasis_ρ_apply, altLeftBasis_ρ_apply, transpose_apply]
  ring

/-- The group action of `SL(2,ℂ)` on `altLeftHanded ⊗ leftHanded` is equivalent to
  `(M.1⁻¹)ᵀ * leftAltLeftToMatrix v * (M.1)ᵀ`. -/
lemma altLeftLeftToMatrix_ρ (v : (altLeftHanded ⊗ leftHanded).V) (M : SL(2,ℂ)) :
    altLeftLeftToMatrix (TensorProduct.map (altLeftHanded.ρ M) (leftHanded.ρ M) v) =
    (M.1⁻¹)ᵀ * altLeftLeftToMatrix v * (M.1)ᵀ := by
  nth_rewrite 1 [altLeftLeftToMatrix]
  simp only [LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)) ((LinearMap.toMatrix
      (altLeftBasis.tensorProduct leftBasis) (altLeftBasis.tensorProduct leftBasis)
      (TensorProduct.map (altLeftHanded.ρ M) (leftHanded.ρ M)))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2))
      ((altLeftBasis.tensorProduct leftBasis).repr (v))))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr (altLeftBasis.tensorProduct leftBasis)
      (altLeftBasis.tensorProduct leftBasis)
      (TensorProduct.map (altLeftHanded.ρ M) (leftHanded.ρ M)) v)
    erw [h1]
    rfl
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix altLeftBasis altLeftBasis) (altLeftHanded.ρ M))
        ((LinearMap.toMatrix leftBasis leftBasis) (leftHanded.ρ M)) (i, j) k)
        * altLeftLeftToMatrix v k.1 k.2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply, Matrix.transpose_apply]
  have h1 : ∑ x : Fin 2, (∑ x1 : Fin 2, (M.1)⁻¹ x1 i * altLeftLeftToMatrix v x1 x) * M.1 j x
    = ∑ x : Fin 2, ∑ x1 : Fin 2, ((M.1)⁻¹ x1 i * altLeftLeftToMatrix v x1 x) * M.1 j x:= by
    congr
    funext x
    rw [Finset.sum_mul]
  erw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [altLeftBasis_ρ_apply, transpose_apply, leftBasis_ρ_apply]
  ring

/-- The group action of `SL(2,ℂ)` on `rightHanded ⊗ rightHanded` is equivalent to
  `(M.1.map star) * rightRightToMatrix v * ((M.1.map star))ᵀ`. -/
lemma rightRightToMatrix_ρ (v : (rightHanded ⊗ rightHanded).V) (M : SL(2,ℂ)) :
    rightRightToMatrix (TensorProduct.map (rightHanded.ρ M) (rightHanded.ρ M) v) =
    (M.1.map star) * rightRightToMatrix v * ((M.1.map star))ᵀ := by
  nth_rewrite 1 [rightRightToMatrix]
  simp only [LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)) ((LinearMap.toMatrix
      (rightBasis.tensorProduct rightBasis) (rightBasis.tensorProduct rightBasis)
      (TensorProduct.map (rightHanded.ρ M) (rightHanded.ρ M)))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2))
      ((rightBasis.tensorProduct rightBasis).repr (v))))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr (rightBasis.tensorProduct rightBasis)
      (rightBasis.tensorProduct rightBasis)
      (TensorProduct.map (rightHanded.ρ M) (rightHanded.ρ M)) v)
    erw [h1]
    rfl
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix rightBasis rightBasis) (rightHanded.ρ M))
        ((LinearMap.toMatrix rightBasis rightBasis) (rightHanded.ρ M)) (i, j) k)
        * rightRightToMatrix v k.1 k.2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply, Matrix.transpose_apply]
  have h1 : ∑ x : Fin 2, (∑ x1 : Fin 2, (M.1.map star) i x1 * rightRightToMatrix v x1 x) *
      (M.1.map star) j x = ∑ x : Fin 2, ∑ x1 : Fin 2,
      ((M.1.map star) i x1 * rightRightToMatrix v x1 x) * (M.1.map star) j x:= by
    congr
    funext x
    rw [Finset.sum_mul]
  erw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [rightBasis_ρ_apply]
  ring

/-- The group action of `SL(2,ℂ)` on `altRightHanded ⊗ altRightHanded` is equivalent to
  `((M.1⁻¹).conjTranspose * rightRightToMatrix v * (((M.1⁻¹).conjTranspose)ᵀ`. -/
lemma altRightAltRightToMatrix_ρ (v : (altRightHanded ⊗ altRightHanded).V) (M : SL(2,ℂ)) :
    altRightAltRightToMatrix (TensorProduct.map (altRightHanded.ρ M) (altRightHanded.ρ M) v) =
    ((M.1⁻¹).conjTranspose) * altRightAltRightToMatrix v * (((M.1⁻¹).conjTranspose)ᵀ) := by
  nth_rewrite 1 [altRightAltRightToMatrix]
  simp only [LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)) ((LinearMap.toMatrix
      (altRightBasis.tensorProduct altRightBasis) (altRightBasis.tensorProduct altRightBasis)
      (TensorProduct.map (altRightHanded.ρ M) (altRightHanded.ρ M)))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2))
      ((altRightBasis.tensorProduct altRightBasis).repr (v))))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr (altRightBasis.tensorProduct altRightBasis)
      (altRightBasis.tensorProduct altRightBasis)
      (TensorProduct.map (altRightHanded.ρ M) (altRightHanded.ρ M)) v)
    erw [h1]
    rfl
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix altRightBasis altRightBasis) (altRightHanded.ρ M))
        ((LinearMap.toMatrix altRightBasis altRightBasis) (altRightHanded.ρ M)) (i, j) k)
        * altRightAltRightToMatrix v k.1 k.2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply, Matrix.transpose_apply]
  have h1 : ∑ x : Fin 2, (∑ x1 : Fin 2, (↑M)⁻¹ᴴ i x1 * altRightAltRightToMatrix v x1 x) *
      (↑M)⁻¹ᴴ j x = ∑ x : Fin 2, ∑ x1 : Fin 2,
      ((↑M)⁻¹ᴴ i x1 * altRightAltRightToMatrix v x1 x) * (↑M)⁻¹ᴴ j x := by
    congr
    funext x
    rw [Finset.sum_mul]
  erw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [altRightBasis_ρ_apply]
  ring

/-- The group action of `SL(2,ℂ)` on `rightHanded ⊗ altRightHanded` is equivalent to
  `(M.1.map star) * rightAltRightToMatrix v * (((M.1⁻¹).conjTranspose)ᵀ`. -/
lemma rightAltRightToMatrix_ρ (v : (rightHanded ⊗ altRightHanded).V) (M : SL(2,ℂ)) :
    rightAltRightToMatrix (TensorProduct.map (rightHanded.ρ M) (altRightHanded.ρ M) v) =
    (M.1.map star) * rightAltRightToMatrix v * (((M.1⁻¹).conjTranspose)ᵀ) := by
  nth_rewrite 1 [rightAltRightToMatrix]
  simp only [LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)) ((LinearMap.toMatrix
      (rightBasis.tensorProduct altRightBasis) (rightBasis.tensorProduct altRightBasis)
      (TensorProduct.map (rightHanded.ρ M) (altRightHanded.ρ M)))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2))
      ((rightBasis.tensorProduct altRightBasis).repr (v))))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr (rightBasis.tensorProduct altRightBasis)
    (rightBasis.tensorProduct altRightBasis)
    (TensorProduct.map (rightHanded.ρ M) (altRightHanded.ρ M)) v)
    erw [h1]
    rfl
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix rightBasis rightBasis) (rightHanded.ρ M))
        ((LinearMap.toMatrix altRightBasis altRightBasis) (altRightHanded.ρ M)) (i, j) k)
        * rightAltRightToMatrix v k.1 k.2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply, Matrix.transpose_apply]
  have h1 : ∑ x : Fin 2, (∑ x1 : Fin 2, (M.1.map star) i x1 * rightAltRightToMatrix v x1 x)
      * (↑M)⁻¹ᴴ j x = ∑ x : Fin 2, ∑ x1 : Fin 2,
      ((M.1.map star) i x1 * rightAltRightToMatrix v x1 x) * (↑M)⁻¹ᴴ j x := by
    congr
    funext x
    rw [Finset.sum_mul]
  erw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [rightBasis_ρ_apply, altRightBasis_ρ_apply]
  ring

/-- The group action of `SL(2,ℂ)` on `altRightHanded ⊗ rightHanded` is equivalent to
  `((M.1⁻¹).conjTranspose * rightAltRightToMatrix v * ((M.1.map star)).ᵀ`. -/
lemma altRightRightToMatrix_ρ (v : (altRightHanded ⊗ rightHanded).V) (M : SL(2,ℂ)) :
    altRightRightToMatrix (TensorProduct.map (altRightHanded.ρ M) (rightHanded.ρ M) v) =
    ((M.1⁻¹).conjTranspose) * altRightRightToMatrix v * (M.1.map star)ᵀ := by
  nth_rewrite 1 [altRightRightToMatrix]
  simp only [LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)) ((LinearMap.toMatrix
      (altRightBasis.tensorProduct rightBasis) (altRightBasis.tensorProduct rightBasis)
      (TensorProduct.map (altRightHanded.ρ M) (rightHanded.ρ M)))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2))
      ((altRightBasis.tensorProduct rightBasis).repr (v))))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr (altRightBasis.tensorProduct rightBasis)
      (altRightBasis.tensorProduct rightBasis)
      (TensorProduct.map (altRightHanded.ρ M) (rightHanded.ρ M)) v)
    erw [h1]
    rfl
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix altRightBasis altRightBasis) (altRightHanded.ρ M))
        ((LinearMap.toMatrix rightBasis rightBasis) (rightHanded.ρ M)) (i, j) k)
        * altRightRightToMatrix v k.1 k.2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply, Matrix.transpose_apply]
  have h1 : ∑ x : Fin 2, (∑ x1 : Fin 2,
      (↑M)⁻¹ᴴ i x1 * altRightRightToMatrix v x1 x) * (M.1.map star) j x
      = ∑ x : Fin 2, ∑ x1 : Fin 2, ((↑M)⁻¹ᴴ i x1 * altRightRightToMatrix v x1 x) *
      (M.1.map star) j x := by
    congr
    funext x
    rw [Finset.sum_mul]
  erw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [altRightBasis_ρ_apply, rightBasis_ρ_apply]
  ring

lemma altLeftAltRightToMatrix_ρ (v : (altLeftHanded ⊗ altRightHanded).V) (M : SL(2,ℂ)) :
    altLeftAltRightToMatrix (TensorProduct.map (altLeftHanded.ρ M) (altRightHanded.ρ M) v) =
    (M.1⁻¹)ᵀ * altLeftAltRightToMatrix v * ((M.1⁻¹).conjTranspose)ᵀ := by
  nth_rewrite 1 [altLeftAltRightToMatrix]
  simp only [LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)) ((LinearMap.toMatrix
      (altLeftBasis.tensorProduct altRightBasis) (altLeftBasis.tensorProduct altRightBasis)
      (TensorProduct.map (altLeftHanded.ρ M) (altRightHanded.ρ M)))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2))
      ((altLeftBasis.tensorProduct altRightBasis).repr (v))))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr (altLeftBasis.tensorProduct altRightBasis)
      (altLeftBasis.tensorProduct altRightBasis)
      (TensorProduct.map (altLeftHanded.ρ M) (altRightHanded.ρ M)) v)
    erw [h1]
    rfl
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix altLeftBasis altLeftBasis) (altLeftHanded.ρ M))
        ((LinearMap.toMatrix altRightBasis altRightBasis) (altRightHanded.ρ M)) (i, j) k)
        * altLeftAltRightToMatrix v k.1 k.2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply, Matrix.transpose_apply]
  have h1 : ∑ x : Fin 2, (∑ x1 : Fin 2, (M.1)⁻¹ x1 i * altLeftAltRightToMatrix v x1 x) *
      (M.1)⁻¹ᴴ j x = ∑ x : Fin 2, ∑ x1 : Fin 2,
      ((M.1)⁻¹ x1 i * altLeftAltRightToMatrix v x1 x) * (M.1)⁻¹ᴴ j x:= by
    congr
    funext x
    rw [Finset.sum_mul]
  erw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [altLeftBasis_ρ_apply, transpose_apply, altRightBasis_ρ_apply]
  ring

lemma leftRightToMatrix_ρ (v : (leftHanded ⊗ rightHanded).V) (M : SL(2,ℂ)) :
    leftRightToMatrix (TensorProduct.map (leftHanded.ρ M) (rightHanded.ρ M) v) =
    M.1 * leftRightToMatrix v * (M.1)ᴴ := by
  nth_rewrite 1 [leftRightToMatrix]
  simp only [LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)) ((LinearMap.toMatrix
      (leftBasis.tensorProduct rightBasis) (leftBasis.tensorProduct rightBasis)
      (TensorProduct.map (leftHanded.ρ M) (rightHanded.ρ M)))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2))
      ((leftBasis.tensorProduct rightBasis).repr (v))))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr (leftBasis.tensorProduct rightBasis)
      (leftBasis.tensorProduct rightBasis)
      (TensorProduct.map (leftHanded.ρ M) (rightHanded.ρ M)) v)
    erw [h1]
    rfl
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix leftBasis leftBasis) (leftHanded.ρ M))
        ((LinearMap.toMatrix rightBasis rightBasis) (rightHanded.ρ M)) (i, j) k)
        * leftRightToMatrix v k.1 k.2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply]
  have h1 : ∑ x : Fin 2, (∑ x1 : Fin 2, M.1 i x1 * leftRightToMatrix v x1 x) * (M.1)ᴴ x j
    = ∑ x : Fin 2, ∑ x1 : Fin 2, (M.1 i x1 * leftRightToMatrix v x1 x) * (M.1)ᴴ x j := by
    congr
    funext x
    rw [Finset.sum_mul]
  erw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [leftBasis_ρ_apply, rightBasis_ρ_apply]
  rw [Matrix.conjTranspose]
  simp only [RCLike.star_def, map_apply, transpose_apply]
  ring

/-!

## The symm version of the group actions.

-/

lemma leftLeftToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (leftHanded.ρ M) (leftHanded.ρ M) (leftLeftToMatrix.symm v) =
    leftLeftToMatrix.symm (M.1 * v * (M.1)ᵀ) := by
  have h1 := leftLeftToMatrix_ρ (leftLeftToMatrix.symm v) M
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [← h1]
  simp

lemma altLeftaltLeftToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (altLeftHanded.ρ M) (altLeftHanded.ρ M) (altLeftaltLeftToMatrix.symm v) =
    altLeftaltLeftToMatrix.symm ((M.1⁻¹)ᵀ * v * (M.1⁻¹)) := by
  have h1 := altLeftaltLeftToMatrix_ρ (altLeftaltLeftToMatrix.symm v) M
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [← h1]
  simp

lemma leftAltLeftToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (leftHanded.ρ M) (altLeftHanded.ρ M) (leftAltLeftToMatrix.symm v) =
    leftAltLeftToMatrix.symm (M.1 * v * (M.1⁻¹)) := by
  have h1 := leftAltLeftToMatrix_ρ (leftAltLeftToMatrix.symm v) M
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [← h1]
  simp

lemma altLeftLeftToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (altLeftHanded.ρ M) (leftHanded.ρ M) (altLeftLeftToMatrix.symm v) =
    altLeftLeftToMatrix.symm ((M.1⁻¹)ᵀ * v * (M.1)ᵀ) := by
  have h1 := altLeftLeftToMatrix_ρ (altLeftLeftToMatrix.symm v) M
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [← h1]
  simp

lemma rightRightToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (rightHanded.ρ M) (rightHanded.ρ M) (rightRightToMatrix.symm v) =
    rightRightToMatrix.symm ((M.1.map star) * v * ((M.1.map star))ᵀ) := by
  have h1 := rightRightToMatrix_ρ (rightRightToMatrix.symm v) M
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [← h1]
  simp

lemma altRightAltRightToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (altRightHanded.ρ M) (altRightHanded.ρ M) (altRightAltRightToMatrix.symm v) =
    altRightAltRightToMatrix.symm (((M.1⁻¹).conjTranspose) * v * ((M.1⁻¹).conjTranspose)ᵀ) := by
  have h1 := altRightAltRightToMatrix_ρ (altRightAltRightToMatrix.symm v) M
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [← h1]
  simp

lemma rightAltRightToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (rightHanded.ρ M) (altRightHanded.ρ M) (rightAltRightToMatrix.symm v) =
    rightAltRightToMatrix.symm ((M.1.map star) * v * (((M.1⁻¹).conjTranspose)ᵀ)) := by
  have h1 := rightAltRightToMatrix_ρ (rightAltRightToMatrix.symm v) M
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [← h1]
  simp

lemma altRightRightToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (altRightHanded.ρ M) (rightHanded.ρ M) (altRightRightToMatrix.symm v) =
    altRightRightToMatrix.symm (((M.1⁻¹).conjTranspose) * v * (M.1.map star)ᵀ) := by
  have h1 := altRightRightToMatrix_ρ (altRightRightToMatrix.symm v) M
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [← h1]
  simp

lemma altLeftAltRightToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (altLeftHanded.ρ M) (altRightHanded.ρ M) (altLeftAltRightToMatrix.symm v) =
    altLeftAltRightToMatrix.symm ((M.1⁻¹)ᵀ * v * ((M.1⁻¹).conjTranspose)ᵀ) := by
  have h1 := altLeftAltRightToMatrix_ρ (altLeftAltRightToMatrix.symm v) M
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [← h1]
  simp

lemma leftRightToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (leftHanded.ρ M) (rightHanded.ρ M) (leftRightToMatrix.symm v) =
    leftRightToMatrix.symm (M.1 * v * (M.1)ᴴ) := by
  have h1 := leftRightToMatrix_ρ (leftRightToMatrix.symm v) M
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [← h1]
  simp

open Lorentz

lemma altLeftAltRightToMatrix_ρ_symm_selfAdjoint (v : Matrix (Fin 2) (Fin 2) ℂ)
    (hv : IsSelfAdjoint v) (M : SL(2,ℂ)) :
    TensorProduct.map (altLeftHanded.ρ M) (altRightHanded.ρ M) (altLeftAltRightToMatrix.symm v) =
    altLeftAltRightToMatrix.symm (SL2C.toSelfAdjointMap (M.transpose⁻¹) ⟨v, hv⟩) := by
  rw [altLeftAltRightToMatrix_ρ_symm]
  apply congrArg
  simp only [SL2C.toSelfAdjointMap_apply_coe, SpecialLinearGroup.coe_inv,
    SpecialLinearGroup.coe_transpose]
  congr 1
  · rw [SL2C.inverse_coe]
    simp only [SpecialLinearGroup.coe_inv]
    rw [@adjugate_transpose]
  · rw [SL2C.inverse_coe]
    simp only [SpecialLinearGroup.coe_inv]
    rw [← @adjugate_transpose]
    rfl

lemma leftRightToMatrix_ρ_symm_selfAdjoint (v : Matrix (Fin 2) (Fin 2) ℂ)
    (hv : IsSelfAdjoint v) (M : SL(2,ℂ)) :
    TensorProduct.map (leftHanded.ρ M) (rightHanded.ρ M) (leftRightToMatrix.symm v) =
    leftRightToMatrix.symm (SL2C.toSelfAdjointMap M ⟨v, hv⟩) := by
  rw [leftRightToMatrix_ρ_symm]
  rfl

end
end Fermion
