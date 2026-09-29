/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Fermions.Weyl.LeftHanded
public import Physlib.Relativity.Fermions.Weyl.RightHanded
public import Physlib.Relativity.Fermions.Weyl.DualLeftHanded
public import Physlib.Relativity.Fermions.Weyl.DualRightHanded
public import Physlib.Relativity.SL2C.Basic
/-!

# Tensor product of two Weyl fermion

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

## Equivalences to matrices.

-/

/-- Equivalence of `leftHanded ⊗ leftHanded` to `2 x 2` complex matrices. -/
def leftLeftToMatrix : (LeftHandedWeyl ⊗[ℂ] LeftHandedWeyl) ≃ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct LeftHandedWeyl.basis LeftHandedWeyl.basis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

set_option backward.isDefEq.respectTransparency false in
/-- Expanding `leftLeftToMatrix` in terms of the standard basis. -/
lemma leftLeftToMatrix_symm_expand_tmul (M : Matrix (Fin 2) (Fin 2) ℂ) :
    leftLeftToMatrix.symm M = ∑ i, ∑ j, M i j •
      (LeftHandedWeyl.basis i ⊗ₜ[ℂ] LeftHandedWeyl.basis j) := by
  simp only [leftLeftToMatrix, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℂ (s := Finset.univ)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    exact congrArg _ (Basis.tensorProduct_apply LeftHandedWeyl.basis LeftHandedWeyl.basis i j)
  · simp

/-- Equivalence of `dualLeftHanded ⊗ dualLeftHanded` to `2 x 2` complex matrices. -/
def dualLeftdualLeftToMatrix : (DualLeftHandedWeyl ⊗[ℂ] DualLeftHandedWeyl) ≃ₗ[ℂ]
    Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct DualLeftHandedWeyl.basis DualLeftHandedWeyl.basis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

set_option backward.isDefEq.respectTransparency false in
/-- Expanding `dualLeftdualLeftToMatrix` in terms of the standard basis. -/
lemma dualLeftdualLeftToMatrix_symm_expand_tmul (M : Matrix (Fin 2) (Fin 2) ℂ) :
    dualLeftdualLeftToMatrix.symm M = ∑ i, ∑ j, M i j •
      (DualLeftHandedWeyl.basis i ⊗ₜ[ℂ] DualLeftHandedWeyl.basis j) := by
  simp only [dualLeftdualLeftToMatrix, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℂ (s := Finset.univ)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    exact congrArg _ (Basis.tensorProduct_apply
      DualLeftHandedWeyl.basis DualLeftHandedWeyl.basis i j)
  · simp

/-- Equivalence of `leftHanded ⊗ dualLeftHanded` to `2 x 2` complex matrices. -/
def leftDualLeftToMatrix : (LeftHandedWeyl ⊗[ℂ] DualLeftHandedWeyl) ≃ₗ[ℂ]
    Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct LeftHandedWeyl.basis DualLeftHandedWeyl.basis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

set_option backward.isDefEq.respectTransparency false in
/-- Expanding `leftDualLeftToMatrix` in terms of the standard basis. -/
lemma leftDualLeftToMatrix_symm_expand_tmul (M : Matrix (Fin 2) (Fin 2) ℂ) :
    leftDualLeftToMatrix.symm M = ∑ i, ∑ j, M i j •
      (LeftHandedWeyl.basis i ⊗ₜ[ℂ] DualLeftHandedWeyl.basis j) := by
  simp only [leftDualLeftToMatrix, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℂ (s := Finset.univ)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    exact congrArg _ (Basis.tensorProduct_apply LeftHandedWeyl.basis DualLeftHandedWeyl.basis i j)
  · simp

/-- Equivalence of `dualLeftHanded ⊗ leftHanded` to `2 x 2` complex matrices. -/
def dualLeftLeftToMatrix : (DualLeftHandedWeyl ⊗[ℂ] LeftHandedWeyl) ≃ₗ[ℂ]
    Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct DualLeftHandedWeyl.basis LeftHandedWeyl.basis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

set_option backward.isDefEq.respectTransparency false in
/-- Expanding `dualLeftLeftToMatrix` in terms of the standard basis. -/
lemma dualLeftLeftToMatrix_symm_expand_tmul (M : Matrix (Fin 2) (Fin 2) ℂ) :
    dualLeftLeftToMatrix.symm M = ∑ i, ∑ j, M i j •
      (DualLeftHandedWeyl.basis i ⊗ₜ[ℂ] LeftHandedWeyl.basis j) := by
  simp only [dualLeftLeftToMatrix, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℂ (s := Finset.univ)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    exact congrArg _ (Basis.tensorProduct_apply DualLeftHandedWeyl.basis LeftHandedWeyl.basis i j)
  · simp

/-- Equivalence of `rightHanded ⊗ rightHanded` to `2 x 2` complex matrices. -/
def rightRightToMatrix : (RightHandedWeyl ⊗[ℂ] RightHandedWeyl) ≃ₗ[ℂ]
    Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct RightHandedWeyl.basis RightHandedWeyl.basis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

set_option backward.isDefEq.respectTransparency false in
/-- Expanding `rightRightToMatrix` in terms of the standard basis. -/
lemma rightRightToMatrix_symm_expand_tmul (M : Matrix (Fin 2) (Fin 2) ℂ) :
    rightRightToMatrix.symm M = ∑ i, ∑ j, M i j •
      (RightHandedWeyl.basis i ⊗ₜ[ℂ] RightHandedWeyl.basis j) := by
  simp only [rightRightToMatrix, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℂ (s := Finset.univ)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    exact congrArg _ (Basis.tensorProduct_apply RightHandedWeyl.basis RightHandedWeyl.basis i j)
  · simp

/-- Equivalence of `dualRightHanded ⊗ dualRightHanded` to `2 x 2` complex matrices. -/
def dualRightDualRightToMatrix : (DualRightHandedWeyl ⊗[ℂ] DualRightHandedWeyl) ≃ₗ[ℂ]
    Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct DualRightHandedWeyl.basis DualRightHandedWeyl.basis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

set_option backward.isDefEq.respectTransparency false in
/-- Expanding `dualRightDualRightToMatrix` in terms of the standard basis. -/
lemma dualRightDualRightToMatrix_symm_expand_tmul (M : Matrix (Fin 2) (Fin 2) ℂ) :
    dualRightDualRightToMatrix.symm M =
    ∑ i, ∑ j, M i j • (DualRightHandedWeyl.basis i ⊗ₜ[ℂ] DualRightHandedWeyl.basis j) := by
  simp only [dualRightDualRightToMatrix, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℂ (s := Finset.univ)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    exact congrArg _
      (Basis.tensorProduct_apply DualRightHandedWeyl.basis DualRightHandedWeyl.basis i j)
  · simp

/-- Equivalence of `rightHanded ⊗ dualRightHanded` to `2 x 2` complex matrices. -/
def rightDualRightToMatrix : (RightHandedWeyl ⊗[ℂ] DualRightHandedWeyl) ≃ₗ[ℂ]
    Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct RightHandedWeyl.basis DualRightHandedWeyl.basis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

set_option backward.isDefEq.respectTransparency false in
/-- Expanding `rightDualRightToMatrix` in terms of the standard basis. -/
lemma rightDualRightToMatrix_symm_expand_tmul (M : Matrix (Fin 2) (Fin 2) ℂ) :
    rightDualRightToMatrix.symm M = ∑ i, ∑ j, M i j •
      (RightHandedWeyl.basis i ⊗ₜ[ℂ] DualRightHandedWeyl.basis j) := by
  simp only [rightDualRightToMatrix, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℂ (s := Finset.univ)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    exact congrArg _ (Basis.tensorProduct_apply RightHandedWeyl.basis DualRightHandedWeyl.basis i j)
  · simp

/-- Equivalence of `dualRightHanded ⊗ rightHanded` to `2 x 2` complex matrices. -/
def dualRightRightToMatrix : (DualRightHandedWeyl ⊗[ℂ] RightHandedWeyl) ≃ₗ[ℂ]
    Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct DualRightHandedWeyl.basis RightHandedWeyl.basis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

set_option backward.isDefEq.respectTransparency false in
/-- Expanding `dualRightRightToMatrix` in terms of the standard basis. -/
lemma dualRightRightToMatrix_symm_expand_tmul (M : Matrix (Fin 2) (Fin 2) ℂ) :
    dualRightRightToMatrix.symm M = ∑ i, ∑ j, M i j •
      (DualRightHandedWeyl.basis i ⊗ₜ[ℂ] RightHandedWeyl.basis j) := by
  simp only [dualRightRightToMatrix, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℂ (s := Finset.univ)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    exact congrArg _ (Basis.tensorProduct_apply DualRightHandedWeyl.basis RightHandedWeyl.basis i j)
  · simp

/-- Equivalence of `dualLeftHanded ⊗ dualRightHanded` to `2 x 2` complex matrices. -/
def dualLeftDualRightToMatrix : (DualLeftHandedWeyl ⊗[ℂ] DualRightHandedWeyl) ≃ₗ[ℂ]
    Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct DualLeftHandedWeyl.basis DualRightHandedWeyl.basis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

set_option backward.isDefEq.respectTransparency false in
/-- Expanding `dualLeftDualRightToMatrix` in terms of the standard basis. -/
lemma dualLeftDualRightToMatrix_symm_expand_tmul (M : Matrix (Fin 2) (Fin 2) ℂ) :
    dualLeftDualRightToMatrix.symm M = ∑ i, ∑ j, M i j •
      (DualLeftHandedWeyl.basis i ⊗ₜ[ℂ] DualRightHandedWeyl.basis j) := by
  simp only [dualLeftDualRightToMatrix, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℂ (s := Finset.univ)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    exact congrArg _
      (Basis.tensorProduct_apply DualLeftHandedWeyl.basis DualRightHandedWeyl.basis i j)
  · simp

/-- Equivalence of `leftHanded ⊗ rightHanded` to `2 x 2` complex matrices. -/
def leftRightToMatrix : (LeftHandedWeyl ⊗[ℂ] RightHandedWeyl) ≃ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct LeftHandedWeyl.basis RightHandedWeyl.basis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

set_option backward.isDefEq.respectTransparency false in
/-- Expanding `leftRightToMatrix` in terms of the standard basis. -/
lemma leftRightToMatrix_symm_expand_tmul (M : Matrix (Fin 2) (Fin 2) ℂ) :
    leftRightToMatrix.symm M = ∑ i, ∑ j, M i j •
      (LeftHandedWeyl.basis i ⊗ₜ[ℂ] RightHandedWeyl.basis j) := by
  simp only [leftRightToMatrix, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℂ (s := Finset.univ)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    exact congrArg _ (Basis.tensorProduct_apply LeftHandedWeyl.basis RightHandedWeyl.basis i j)
  · simp

/-- The coercion of `Finsupp.linearEquivFunOnFinite` to a function is the underlying
finitely-supported function, used to bridge it with `Matrix.mulVec`. -/
private lemma coe_linearEquivFunOnFinite (g : (Fin 2 × Fin 2) →₀ ℂ) :
    Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) g = ⇑g := rfl

/-!

## Group actions

-/

set_option backward.isDefEq.respectTransparency false in
/-- The group action of `SL(2,ℂ)` on `leftHanded ⊗ leftHanded` is equivalent to
  `M.1 * leftLeftToMatrix v * (M.1)ᵀ`. -/
lemma leftLeftToMatrix_ρ (v : (LeftHandedWeyl ⊗[ℂ] LeftHandedWeyl)) (M : SL(2,ℂ)) :
    leftLeftToMatrix (TensorProduct.map (LeftHandedWeyl.rep M) (LeftHandedWeyl.rep M) v) =
    M.1 * leftLeftToMatrix v * (M.1)ᵀ := by
  nth_rewrite 1 [leftLeftToMatrix]
  simp only [LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)) ((LinearMap.toMatrix
      (LeftHandedWeyl.basis.tensorProduct LeftHandedWeyl.basis)
        (LeftHandedWeyl.basis.tensorProduct LeftHandedWeyl.basis)
      (TensorProduct.map (LeftHandedWeyl.rep M) (LeftHandedWeyl.rep M)))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2))
      ((LeftHandedWeyl.basis.tensorProduct LeftHandedWeyl.basis).repr (v))))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr (LeftHandedWeyl.basis.tensorProduct
      LeftHandedWeyl.basis)
      (LeftHandedWeyl.basis.tensorProduct LeftHandedWeyl.basis)
        (TensorProduct.map (LeftHandedWeyl.rep M) (LeftHandedWeyl.rep M)) v)
    simp only [coe_linearEquivFunOnFinite]
    rw [h1]
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix LeftHandedWeyl.basis LeftHandedWeyl.basis) (LeftHandedWeyl.rep M))
        ((LinearMap.toMatrix LeftHandedWeyl.basis LeftHandedWeyl.basis)
          (LeftHandedWeyl.rep M)) (i, j) k)
        * leftLeftToMatrix v k.1 k.2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply, Matrix.transpose_apply]
  have h1 : ∑ x : Fin 2, (∑ j : Fin 2, M.1 i j * leftLeftToMatrix v j x) * M.1 j x
    = ∑ x : Fin 2, ∑ x1 : Fin 2, (M.1 i x1 * leftLeftToMatrix v x1 x) * M.1 j x := by
    congr
    funext x
    rw [Finset.sum_mul]
  rw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [LeftHandedWeyl.rep_toMatrix]
  rw [mul_assoc]
  nth_rewrite 2 [mul_comm]
  rw [← mul_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The group action of `SL(2,ℂ)` on `dualLeftHanded ⊗ dualLeftHanded` is equivalent to
  `(M.1⁻¹)ᵀ * leftLeftToMatrix v * (M.1⁻¹)`. -/
lemma dualLeftdualLeftToMatrix_ρ (v : (DualLeftHandedWeyl ⊗[ℂ] DualLeftHandedWeyl)) (M : SL(2,ℂ)) :
    dualLeftdualLeftToMatrix (TensorProduct.map (DualLeftHandedWeyl.rep M)
      (DualLeftHandedWeyl.rep M) v) =
    (M.1⁻¹)ᵀ * dualLeftdualLeftToMatrix v * (M.1⁻¹) := by
  nth_rewrite 1 [dualLeftdualLeftToMatrix]
  simp only [LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)) ((LinearMap.toMatrix
      (DualLeftHandedWeyl.basis.tensorProduct DualLeftHandedWeyl.basis)
        (DualLeftHandedWeyl.basis.tensorProduct DualLeftHandedWeyl.basis)
      (TensorProduct.map (DualLeftHandedWeyl.rep M) (DualLeftHandedWeyl.rep M)))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2))
      ((DualLeftHandedWeyl.basis.tensorProduct DualLeftHandedWeyl.basis).repr v)))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr (DualLeftHandedWeyl.basis.tensorProduct
      DualLeftHandedWeyl.basis)
      (DualLeftHandedWeyl.basis.tensorProduct DualLeftHandedWeyl.basis)
      (TensorProduct.map (DualLeftHandedWeyl.rep M) (DualLeftHandedWeyl.rep M)) v)
    simp only [coe_linearEquivFunOnFinite]
    rw [h1]
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix DualLeftHandedWeyl.basis DualLeftHandedWeyl.basis)
          (DualLeftHandedWeyl.rep M))
        ((LinearMap.toMatrix DualLeftHandedWeyl.basis DualLeftHandedWeyl.basis)
          (DualLeftHandedWeyl.rep M)) (i, j) k)
        * dualLeftdualLeftToMatrix v k.1 k.2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply, Matrix.transpose_apply]
  have h1 : ∑ x : Fin 2, (∑ x1 : Fin 2, (M.1)⁻¹ x1 i *
    dualLeftdualLeftToMatrix v x1 x) * (M.1)⁻¹ x j
    = ∑ x : Fin 2, ∑ x1 : Fin 2, ((M.1)⁻¹ x1 i *
    dualLeftdualLeftToMatrix v x1 x) * (M.1)⁻¹ x j := by
    congr
    funext x
    rw [Finset.sum_mul]
  rw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [DualLeftHandedWeyl.rep_toMatrix, transpose_apply]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- The group action of `SL(2,ℂ)` on `leftHanded ⊗ dualLeftHanded` is equivalent to
  `M.1 * leftDualLeftToMatrix v * (M.1⁻¹)`. -/
lemma leftDualLeftToMatrix_ρ (v : (LeftHandedWeyl ⊗[ℂ] DualLeftHandedWeyl)) (M : SL(2,ℂ)) :
    leftDualLeftToMatrix (TensorProduct.map (LeftHandedWeyl.rep M) (DualLeftHandedWeyl.rep M) v) =
    M.1 * leftDualLeftToMatrix v * (M.1⁻¹) := by
  nth_rewrite 1 [leftDualLeftToMatrix]
  simp only [LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)) ((LinearMap.toMatrix
      (LeftHandedWeyl.basis.tensorProduct DualLeftHandedWeyl.basis)
        (LeftHandedWeyl.basis.tensorProduct DualLeftHandedWeyl.basis)
      (TensorProduct.map (LeftHandedWeyl.rep M) (DualLeftHandedWeyl.rep M)))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2))
      ((LeftHandedWeyl.basis.tensorProduct DualLeftHandedWeyl.basis).repr (v))))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr (LeftHandedWeyl.basis.tensorProduct
        DualLeftHandedWeyl.basis)
      (LeftHandedWeyl.basis.tensorProduct DualLeftHandedWeyl.basis)
      (TensorProduct.map (LeftHandedWeyl.rep M) (DualLeftHandedWeyl.rep M)) v)
    simp only [coe_linearEquivFunOnFinite]
    rw [h1]
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix LeftHandedWeyl.basis LeftHandedWeyl.basis) (LeftHandedWeyl.rep M))
        ((LinearMap.toMatrix DualLeftHandedWeyl.basis DualLeftHandedWeyl.basis)
          (DualLeftHandedWeyl.rep M)) (i, j) k)
        * leftDualLeftToMatrix v k.1 k.2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply]
  have h1 : ∑ x : Fin 2, (∑ x1 : Fin 2, M.1 i x1 * leftDualLeftToMatrix v x1 x) * (M.1⁻¹) x j
    = ∑ x : Fin 2, ∑ x1 : Fin 2, (M.1 i x1 * leftDualLeftToMatrix v x1 x) * (M.1⁻¹) x j := by
    congr
    funext x
    rw [Finset.sum_mul]
  rw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [LeftHandedWeyl.rep_toMatrix, DualLeftHandedWeyl.rep_toMatrix, transpose_apply]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- The group action of `SL(2,ℂ)` on `dualLeftHanded ⊗ leftHanded` is equivalent to
  `(M.1⁻¹)ᵀ * leftDualLeftToMatrix v * (M.1)ᵀ`. -/
lemma dualLeftLeftToMatrix_ρ (v : (DualLeftHandedWeyl ⊗[ℂ] LeftHandedWeyl)) (M : SL(2,ℂ)) :
    dualLeftLeftToMatrix (TensorProduct.map (DualLeftHandedWeyl.rep M) (LeftHandedWeyl.rep M) v) =
    (M.1⁻¹)ᵀ * dualLeftLeftToMatrix v * (M.1)ᵀ := by
  nth_rewrite 1 [dualLeftLeftToMatrix]
  simp only [LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)) ((LinearMap.toMatrix
      (DualLeftHandedWeyl.basis.tensorProduct LeftHandedWeyl.basis)
        (DualLeftHandedWeyl.basis.tensorProduct LeftHandedWeyl.basis)
      (TensorProduct.map (DualLeftHandedWeyl.rep M) (LeftHandedWeyl.rep M)))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2))
      ((DualLeftHandedWeyl.basis.tensorProduct LeftHandedWeyl.basis).repr (v))))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr (DualLeftHandedWeyl.basis.tensorProduct
        LeftHandedWeyl.basis)
      (DualLeftHandedWeyl.basis.tensorProduct LeftHandedWeyl.basis)
      (TensorProduct.map (DualLeftHandedWeyl.rep M) (LeftHandedWeyl.rep M)) v)
    simp only [coe_linearEquivFunOnFinite]
    rw [h1]
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix DualLeftHandedWeyl.basis DualLeftHandedWeyl.basis)
          (DualLeftHandedWeyl.rep M))
        ((LinearMap.toMatrix LeftHandedWeyl.basis LeftHandedWeyl.basis)
          (LeftHandedWeyl.rep M)) (i, j) k)
        * dualLeftLeftToMatrix v k.1 k.2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply, Matrix.transpose_apply]
  have h1 : ∑ x : Fin 2, (∑ x1 : Fin 2, (M.1)⁻¹ x1 i * dualLeftLeftToMatrix v x1 x) * M.1 j x
    = ∑ x : Fin 2, ∑ x1 : Fin 2, ((M.1)⁻¹ x1 i * dualLeftLeftToMatrix v x1 x) * M.1 j x:= by
    congr
    funext x
    rw [Finset.sum_mul]
  rw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [DualLeftHandedWeyl.rep_toMatrix, transpose_apply, LeftHandedWeyl.rep_toMatrix]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- The group action of `SL(2,ℂ)` on `rightHanded ⊗ rightHanded` is equivalent to
  `(M.1.map star) * rightRightToMatrix v * ((M.1.map star))ᵀ`. -/
lemma rightRightToMatrix_ρ (v : (RightHandedWeyl ⊗[ℂ] RightHandedWeyl)) (M : SL(2,ℂ)) :
    rightRightToMatrix (TensorProduct.map (RightHandedWeyl.rep M) (RightHandedWeyl.rep M) v) =
    (M.1.map star) * rightRightToMatrix v * ((M.1.map star))ᵀ := by
  nth_rewrite 1 [rightRightToMatrix]
  simp only [LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)) ((LinearMap.toMatrix
      (RightHandedWeyl.basis.tensorProduct RightHandedWeyl.basis)
        (RightHandedWeyl.basis.tensorProduct RightHandedWeyl.basis)
      (TensorProduct.map (RightHandedWeyl.rep M) (RightHandedWeyl.rep M)))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2))
      ((RightHandedWeyl.basis.tensorProduct RightHandedWeyl.basis).repr (v))))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr (RightHandedWeyl.basis.tensorProduct
        RightHandedWeyl.basis)
      (RightHandedWeyl.basis.tensorProduct RightHandedWeyl.basis)
      (TensorProduct.map (RightHandedWeyl.rep M) (RightHandedWeyl.rep M)) v)
    simp only [coe_linearEquivFunOnFinite]
    rw [h1]
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix RightHandedWeyl.basis RightHandedWeyl.basis) (RightHandedWeyl.rep M))
        ((LinearMap.toMatrix RightHandedWeyl.basis RightHandedWeyl.basis)
          (RightHandedWeyl.rep M)) (i, j) k)
        * rightRightToMatrix v k.1 k.2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply, Matrix.transpose_apply]
  have h1 : ∑ x : Fin 2, (∑ x1 : Fin 2, (M.1.map star) i x1 * rightRightToMatrix v x1 x) *
      (M.1.map star) j x = ∑ x : Fin 2, ∑ x1 : Fin 2,
      ((M.1.map star) i x1 * rightRightToMatrix v x1 x) * (M.1.map star) j x:= by
    congr
    funext x
    rw [Finset.sum_mul]
  rw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [RightHandedWeyl.rep_toMatrix]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- The group action of `SL(2,ℂ)` on `dualRightHanded ⊗ dualRightHanded` is equivalent to
  `((M.1⁻¹).conjTranspose * rightRightToMatrix v * (((M.1⁻¹).conjTranspose)ᵀ`. -/
lemma dualRightDualRightToMatrix_ρ (v : (DualRightHandedWeyl ⊗[ℂ] DualRightHandedWeyl))
    (M : SL(2,ℂ)) :
    dualRightDualRightToMatrix (TensorProduct.map (DualRightHandedWeyl.rep M)
      (DualRightHandedWeyl.rep M) v) =
    ((M.1⁻¹).conjTranspose) * dualRightDualRightToMatrix v * (((M.1⁻¹).conjTranspose)ᵀ) := by
  nth_rewrite 1 [dualRightDualRightToMatrix]
  simp only [LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)) ((LinearMap.toMatrix
      (DualRightHandedWeyl.basis.tensorProduct DualRightHandedWeyl.basis)
        (DualRightHandedWeyl.basis.tensorProduct DualRightHandedWeyl.basis)
      (TensorProduct.map (DualRightHandedWeyl.rep M) (DualRightHandedWeyl.rep M)))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2))
      ((DualRightHandedWeyl.basis.tensorProduct DualRightHandedWeyl.basis).repr (v))))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr (DualRightHandedWeyl.basis.tensorProduct
        DualRightHandedWeyl.basis)
      (DualRightHandedWeyl.basis.tensorProduct DualRightHandedWeyl.basis)
      (TensorProduct.map (DualRightHandedWeyl.rep M) (DualRightHandedWeyl.rep M)) v)
    simp only [coe_linearEquivFunOnFinite]
    rw [h1]
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix DualRightHandedWeyl.basis DualRightHandedWeyl.basis)
          (DualRightHandedWeyl.rep M))
        ((LinearMap.toMatrix DualRightHandedWeyl.basis DualRightHandedWeyl.basis)
          (DualRightHandedWeyl.rep M)) (i, j) k)
        * dualRightDualRightToMatrix v k.1 k.2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply, Matrix.transpose_apply]
  have h1 : ∑ x : Fin 2, (∑ x1 : Fin 2, (↑M)⁻¹ᴴ i x1 * dualRightDualRightToMatrix v x1 x) *
      (↑M)⁻¹ᴴ j x = ∑ x : Fin 2, ∑ x1 : Fin 2,
      ((↑M)⁻¹ᴴ i x1 * dualRightDualRightToMatrix v x1 x) * (↑M)⁻¹ᴴ j x := by
    congr
    funext x
    rw [Finset.sum_mul]
  rw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [DualRightHandedWeyl.rep_toMatrix]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- The group action of `SL(2,ℂ)` on `rightHanded ⊗ dualRightHanded` is equivalent to
  `(M.1.map star) * rightDualRightToMatrix v * (((M.1⁻¹).conjTranspose)ᵀ`. -/
lemma rightDualRightToMatrix_ρ (v : (RightHandedWeyl ⊗[ℂ] DualRightHandedWeyl)) (M : SL(2,ℂ)) :
    rightDualRightToMatrix (TensorProduct.map (RightHandedWeyl.rep M)
      (DualRightHandedWeyl.rep M) v) =
    (M.1.map star) * rightDualRightToMatrix v * (((M.1⁻¹).conjTranspose)ᵀ) := by
  nth_rewrite 1 [rightDualRightToMatrix]
  simp only [LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)) ((LinearMap.toMatrix
      (RightHandedWeyl.basis.tensorProduct DualRightHandedWeyl.basis)
        (RightHandedWeyl.basis.tensorProduct DualRightHandedWeyl.basis)
      (TensorProduct.map (RightHandedWeyl.rep M) (DualRightHandedWeyl.rep M)))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2))
      ((RightHandedWeyl.basis.tensorProduct DualRightHandedWeyl.basis).repr (v))))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr (RightHandedWeyl.basis.tensorProduct
      DualRightHandedWeyl.basis)
    (RightHandedWeyl.basis.tensorProduct DualRightHandedWeyl.basis)
    (TensorProduct.map (RightHandedWeyl.rep M) (DualRightHandedWeyl.rep M)) v)
    simp only [coe_linearEquivFunOnFinite]
    rw [h1]
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix RightHandedWeyl.basis RightHandedWeyl.basis)
          (RightHandedWeyl.rep M))
        ((LinearMap.toMatrix DualRightHandedWeyl.basis DualRightHandedWeyl.basis)
          (DualRightHandedWeyl.rep M)) (i, j) k)
        * rightDualRightToMatrix v k.1 k.2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply, Matrix.transpose_apply]
  have h1 : ∑ x : Fin 2, (∑ x1 : Fin 2, (M.1.map star) i x1 * rightDualRightToMatrix v x1 x)
      * (↑M)⁻¹ᴴ j x = ∑ x : Fin 2, ∑ x1 : Fin 2,
      ((M.1.map star) i x1 * rightDualRightToMatrix v x1 x) * (↑M)⁻¹ᴴ j x := by
    congr
    funext x
    rw [Finset.sum_mul]
  rw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [RightHandedWeyl.rep_toMatrix, DualRightHandedWeyl.rep_toMatrix]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- The group action of `SL(2,ℂ)` on `dualRightHanded ⊗ rightHanded` is equivalent to
  `((M.1⁻¹).conjTranspose * rightDualRightToMatrix v * ((M.1.map star)).ᵀ`. -/
lemma dualRightRightToMatrix_ρ (v : (DualRightHandedWeyl ⊗[ℂ] RightHandedWeyl)) (M : SL(2,ℂ)) :
    dualRightRightToMatrix (TensorProduct.map (DualRightHandedWeyl.rep M)
      (RightHandedWeyl.rep M) v) =
    ((M.1⁻¹).conjTranspose) * dualRightRightToMatrix v * (M.1.map star)ᵀ := by
  nth_rewrite 1 [dualRightRightToMatrix]
  simp only [LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)) ((LinearMap.toMatrix
      (DualRightHandedWeyl.basis.tensorProduct RightHandedWeyl.basis)
        (DualRightHandedWeyl.basis.tensorProduct RightHandedWeyl.basis)
      (TensorProduct.map (DualRightHandedWeyl.rep M) (RightHandedWeyl.rep M)))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2))
      ((DualRightHandedWeyl.basis.tensorProduct RightHandedWeyl.basis).repr (v))))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr
      (DualRightHandedWeyl.basis.tensorProduct RightHandedWeyl.basis)
      (DualRightHandedWeyl.basis.tensorProduct RightHandedWeyl.basis)
      (TensorProduct.map (DualRightHandedWeyl.rep M) (RightHandedWeyl.rep M)) v)
    simp only [coe_linearEquivFunOnFinite]
    rw [h1]
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix DualRightHandedWeyl.basis DualRightHandedWeyl.basis)
          (DualRightHandedWeyl.rep M))
        ((LinearMap.toMatrix RightHandedWeyl.basis RightHandedWeyl.basis)
          (RightHandedWeyl.rep M)) (i, j) k)
        * dualRightRightToMatrix v k.1 k.2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply, Matrix.transpose_apply]
  have h1 : ∑ x : Fin 2, (∑ x1 : Fin 2,
      (↑M)⁻¹ᴴ i x1 * dualRightRightToMatrix v x1 x) * (M.1.map star) j x
      = ∑ x : Fin 2, ∑ x1 : Fin 2, ((↑M)⁻¹ᴴ i x1 * dualRightRightToMatrix v x1 x) *
      (M.1.map star) j x := by
    congr
    funext x
    rw [Finset.sum_mul]
  rw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [DualRightHandedWeyl.rep_toMatrix, RightHandedWeyl.rep_toMatrix]
  ring

set_option backward.isDefEq.respectTransparency false in
lemma dualLeftDualRightToMatrix_ρ (v : (DualLeftHandedWeyl ⊗[ℂ] DualRightHandedWeyl))
    (M : SL(2,ℂ)) :
    dualLeftDualRightToMatrix (TensorProduct.map (DualLeftHandedWeyl.rep M)
      (DualRightHandedWeyl.rep M) v) =
    (M.1⁻¹)ᵀ * dualLeftDualRightToMatrix v * ((M.1⁻¹).conjTranspose)ᵀ := by
  nth_rewrite 1 [dualLeftDualRightToMatrix]
  simp only [LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)) ((LinearMap.toMatrix
      (DualLeftHandedWeyl.basis.tensorProduct DualRightHandedWeyl.basis)
        (DualLeftHandedWeyl.basis.tensorProduct DualRightHandedWeyl.basis)
      (TensorProduct.map (DualLeftHandedWeyl.rep M) (DualRightHandedWeyl.rep M)))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2))
      ((DualLeftHandedWeyl.basis.tensorProduct DualRightHandedWeyl.basis).repr (v))))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr (DualLeftHandedWeyl.basis.tensorProduct
      DualRightHandedWeyl.basis)
      (DualLeftHandedWeyl.basis.tensorProduct DualRightHandedWeyl.basis)
      (TensorProduct.map (DualLeftHandedWeyl.rep M) (DualRightHandedWeyl.rep M)) v)
    simp only [coe_linearEquivFunOnFinite]
    rw [h1]
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix DualLeftHandedWeyl.basis DualLeftHandedWeyl.basis)
          (DualLeftHandedWeyl.rep M))
        ((LinearMap.toMatrix DualRightHandedWeyl.basis DualRightHandedWeyl.basis)
          (DualRightHandedWeyl.rep M)) (i, j) k)
        * dualLeftDualRightToMatrix v k.1 k.2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply, Matrix.transpose_apply]
  have h1 : ∑ x : Fin 2, (∑ x1 : Fin 2, (M.1)⁻¹ x1 i * dualLeftDualRightToMatrix v x1 x) *
      (M.1)⁻¹ᴴ j x = ∑ x : Fin 2, ∑ x1 : Fin 2,
      ((M.1)⁻¹ x1 i * dualLeftDualRightToMatrix v x1 x) * (M.1)⁻¹ᴴ j x:= by
    congr
    funext x
    rw [Finset.sum_mul]
  rw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [DualLeftHandedWeyl.rep_toMatrix, transpose_apply, DualRightHandedWeyl.rep_toMatrix]
  ring

set_option backward.isDefEq.respectTransparency false in
lemma leftRightToMatrix_ρ (v : (LeftHandedWeyl ⊗[ℂ] RightHandedWeyl)) (M : SL(2,ℂ)) :
    leftRightToMatrix (TensorProduct.map (LeftHandedWeyl.rep M) (RightHandedWeyl.rep M) v) =
    M.1 * leftRightToMatrix v * (M.1)ᴴ := by
  nth_rewrite 1 [leftRightToMatrix]
  simp only [LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)) ((LinearMap.toMatrix
      (LeftHandedWeyl.basis.tensorProduct RightHandedWeyl.basis) (LeftHandedWeyl.basis.tensorProduct
        RightHandedWeyl.basis)
      (TensorProduct.map (LeftHandedWeyl.rep M) (RightHandedWeyl.rep M)))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2))
      ((LeftHandedWeyl.basis.tensorProduct RightHandedWeyl.basis).repr (v))))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr (LeftHandedWeyl.basis.tensorProduct
      RightHandedWeyl.basis)
      (LeftHandedWeyl.basis.tensorProduct RightHandedWeyl.basis)
      (TensorProduct.map (LeftHandedWeyl.rep M) (RightHandedWeyl.rep M)) v)
    simp only [coe_linearEquivFunOnFinite]
    rw [h1]
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix LeftHandedWeyl.basis LeftHandedWeyl.basis) (LeftHandedWeyl.rep M))
        ((LinearMap.toMatrix RightHandedWeyl.basis RightHandedWeyl.basis)
          (RightHandedWeyl.rep M)) (i, j) k)
        * leftRightToMatrix v k.1 k.2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply]
  have h1 : ∑ x : Fin 2, (∑ x1 : Fin 2, M.1 i x1 * leftRightToMatrix v x1 x) * (M.1)ᴴ x j
    = ∑ x : Fin 2, ∑ x1 : Fin 2, (M.1 i x1 * leftRightToMatrix v x1 x) * (M.1)ᴴ x j := by
    congr
    funext x
    rw [Finset.sum_mul]
  rw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [LeftHandedWeyl.rep_toMatrix, RightHandedWeyl.rep_toMatrix]
  rw [Matrix.conjTranspose]
  simp only [RCLike.star_def, map_apply, transpose_apply]
  ring

/-!

## The symm version of the group actions.

-/

lemma leftLeftToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (LeftHandedWeyl.rep M) (LeftHandedWeyl.rep M) (leftLeftToMatrix.symm v) =
    leftLeftToMatrix.symm (M.1 * v * (M.1)ᵀ) := by
  have h1 := leftLeftToMatrix_ρ (leftLeftToMatrix.symm v) M
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [← h1, LinearEquiv.symm_apply_apply]

lemma dualLeftdualLeftToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (DualLeftHandedWeyl.rep M) (DualLeftHandedWeyl.rep M)
      (dualLeftdualLeftToMatrix.symm v) =
    dualLeftdualLeftToMatrix.symm ((M.1⁻¹)ᵀ * v * (M.1⁻¹)) := by
  have h1 := dualLeftdualLeftToMatrix_ρ (dualLeftdualLeftToMatrix.symm v) M
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [← h1, LinearEquiv.symm_apply_apply]

lemma leftDualLeftToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (LeftHandedWeyl.rep M) (DualLeftHandedWeyl.rep M)
      (leftDualLeftToMatrix.symm v) =
    leftDualLeftToMatrix.symm (M.1 * v * (M.1⁻¹)) := by
  have h1 := leftDualLeftToMatrix_ρ (leftDualLeftToMatrix.symm v) M
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [← h1, LinearEquiv.symm_apply_apply]

lemma dualLeftLeftToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (DualLeftHandedWeyl.rep M) (LeftHandedWeyl.rep M)
      (dualLeftLeftToMatrix.symm v) =
    dualLeftLeftToMatrix.symm ((M.1⁻¹)ᵀ * v * (M.1)ᵀ) := by
  have h1 := dualLeftLeftToMatrix_ρ (dualLeftLeftToMatrix.symm v) M
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [← h1, LinearEquiv.symm_apply_apply]

lemma rightRightToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (RightHandedWeyl.rep M) (RightHandedWeyl.rep M) (rightRightToMatrix.symm v) =
    rightRightToMatrix.symm ((M.1.map star) * v * ((M.1.map star))ᵀ) := by
  have h1 := rightRightToMatrix_ρ (rightRightToMatrix.symm v) M
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [← h1, LinearEquiv.symm_apply_apply]

lemma dualRightDualRightToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (DualRightHandedWeyl.rep M) (DualRightHandedWeyl.rep M)
      (dualRightDualRightToMatrix.symm v) =
    dualRightDualRightToMatrix.symm (((M.1⁻¹).conjTranspose) * v * ((M.1⁻¹).conjTranspose)ᵀ) := by
  have h1 := dualRightDualRightToMatrix_ρ (dualRightDualRightToMatrix.symm v) M
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [← h1, LinearEquiv.symm_apply_apply]

lemma rightDualRightToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (RightHandedWeyl.rep M) (DualRightHandedWeyl.rep M)
      (rightDualRightToMatrix.symm v) =
    rightDualRightToMatrix.symm ((M.1.map star) * v * (((M.1⁻¹).conjTranspose)ᵀ)) := by
  have h1 := rightDualRightToMatrix_ρ (rightDualRightToMatrix.symm v) M
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [← h1, LinearEquiv.symm_apply_apply]

lemma dualRightRightToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (DualRightHandedWeyl.rep M) (RightHandedWeyl.rep M)
      (dualRightRightToMatrix.symm v) =
    dualRightRightToMatrix.symm (((M.1⁻¹).conjTranspose) * v * (M.1.map star)ᵀ) := by
  have h1 := dualRightRightToMatrix_ρ (dualRightRightToMatrix.symm v) M
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [← h1, LinearEquiv.symm_apply_apply]

lemma dualLeftDualRightToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (DualLeftHandedWeyl.rep M) (DualRightHandedWeyl.rep M)
      (dualLeftDualRightToMatrix.symm v) =
    dualLeftDualRightToMatrix.symm ((M.1⁻¹)ᵀ * v * ((M.1⁻¹).conjTranspose)ᵀ) := by
  have h1 := dualLeftDualRightToMatrix_ρ (dualLeftDualRightToMatrix.symm v) M
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [← h1, LinearEquiv.symm_apply_apply]

lemma leftRightToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (LeftHandedWeyl.rep M) (RightHandedWeyl.rep M) (leftRightToMatrix.symm v) =
    leftRightToMatrix.symm (M.1 * v * (M.1)ᴴ) := by
  have h1 := leftRightToMatrix_ρ (leftRightToMatrix.symm v) M
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [← h1, LinearEquiv.symm_apply_apply]

open Lorentz

lemma dualLeftDualRightToMatrix_ρ_symm_selfAdjoint (v : Matrix (Fin 2) (Fin 2) ℂ)
    (hv : IsSelfAdjoint v) (M : SL(2,ℂ)) :
    TensorProduct.map (DualLeftHandedWeyl.rep M) (DualRightHandedWeyl.rep M)
      (dualLeftDualRightToMatrix.symm v) =
    dualLeftDualRightToMatrix.symm (SL2C.toSelfAdjointMap (M.transpose⁻¹) ⟨v, hv⟩) := by
  rw [dualLeftDualRightToMatrix_ρ_symm]
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
    TensorProduct.map (LeftHandedWeyl.rep M) (RightHandedWeyl.rep M) (leftRightToMatrix.symm v) =
    leftRightToMatrix.symm (SL2C.toSelfAdjointMap M ⟨v, hv⟩) := by
  rw [leftRightToMatrix_ρ_symm]
  rfl

end
end Fermion
