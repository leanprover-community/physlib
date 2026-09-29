/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Vector.Pre.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Matrix
/-!

# Tensor products of two real Lorentz vectors

-/

@[expose] public section
noncomputable section

open Matrix Module MatrixGroups Complex TensorProduct

namespace Lorentz

/-- Equivalence of `ContrMod ⊗ ContrMod` to `(1 + d) x (1 + d)` real matrices. -/
def contrContrToMatrixRe {d : ℕ} : (ContrMod d ⊗[ℝ] ContrMod d) ≃ₗ[ℝ]
    Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ :=
  (Basis.tensorProduct (contrBasis d) (contrBasis d)).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℝ ℝ ((Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)) ≪≫ₗ
  LinearEquiv.curry ℝ ℝ (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d)

set_option backward.isDefEq.respectTransparency false in
/-- Expanding `contrContrToMatrixRe` in terms of the standard basis. -/
lemma contrContrToMatrixRe_symm_expand_tmul (M : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) :
    contrContrToMatrixRe.symm M = ∑ i, ∑ j, M i j • (contrBasis d i ⊗ₜ[ℝ] contrBasis d j) := by
  simp only [contrContrToMatrixRe, LinearEquiv.trans_symm,
    LinearEquiv.trans_apply, Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℝ (s := Finset.univ)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    erw [Basis.tensorProduct_apply (contrBasis d) (contrBasis d) i j]
    rfl
  · simp

/-- Equivalence of `CoMod ⊗ CoMod` to `(1 + d) x (1 + d)` real matrices. -/
def coCoToMatrixRe {d : ℕ} : (CoMod d ⊗[ℝ] CoMod d) ≃ₗ[ℝ]
    Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ :=
  (Basis.tensorProduct (coBasis d) (coBasis d)).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℝ ℝ ((Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)) ≪≫ₗ
  LinearEquiv.curry ℝ ℝ (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d)

set_option backward.isDefEq.respectTransparency false in
/-- Expanding `coCoToMatrixRe` in terms of the standard basis. -/
lemma coCoToMatrixRe_symm_expand_tmul (M : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) :
    coCoToMatrixRe.symm M = ∑ i, ∑ j, M i j • (coBasis d i ⊗ₜ[ℝ] coBasis d j) := by
  simp only [coCoToMatrixRe, LinearEquiv.trans_symm, LinearEquiv.trans_apply, Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℝ (s := Finset.univ)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    erw [Basis.tensorProduct_apply (coBasis d) (coBasis d) i j]
    rfl
  · simp

/-- Equivalence of `ContrMod d ⊗ CoMod d` to `(1 + d) x (1 + d)` real matrices. -/
def contrCoToMatrixRe {d : ℕ} : (ContrMod d ⊗[ℝ] CoMod d) ≃ₗ[ℝ]
    Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ :=
  (Basis.tensorProduct (contrBasis d) (coBasis d)).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℝ ℝ ((Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)) ≪≫ₗ
  LinearEquiv.curry ℝ ℝ (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d)

set_option backward.isDefEq.respectTransparency false in
/-- Expansion of ` (coBasis d) (coBasis d)` in terms of the standard basis. -/
lemma contrCoToMatrixRe_symm_expand_tmul (M : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) :
    contrCoToMatrixRe.symm M = ∑ i, ∑ j, M i j • (contrBasis d i ⊗ₜ[ℝ] coBasis d j) := by
  simp only [contrCoToMatrixRe, LinearEquiv.trans_symm,
    LinearEquiv.trans_apply, Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℝ (s := Finset.univ)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    erw [Basis.tensorProduct_apply _ _ i j]
    rfl
  · simp

/-- Equivalence of `CoMod d ⊗ ContrMod d` to `(1 + d) x (1 + d)` real matrices. -/
def coContrToMatrixRe : (CoMod d ⊗[ℝ] ContrMod d) ≃ₗ[ℝ]
    Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ :=
  (Basis.tensorProduct (coBasis d) (contrBasis d)).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℝ ℝ ((Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)) ≪≫ₗ
  LinearEquiv.curry ℝ ℝ (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d)

set_option backward.isDefEq.respectTransparency false in
/-- Expansion of `coContrToMatrixRe` in terms of the standard basis. -/
lemma coContrToMatrixRe_symm_expand_tmul (M : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) :
    coContrToMatrixRe.symm M = ∑ i, ∑ j, M i j • (coBasis d i ⊗ₜ[ℝ] contrBasis d j) := by
  simp only [coContrToMatrixRe, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℝ (s := Finset.univ)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    erw [Basis.tensorProduct_apply _ _ i j]
    rfl
  · simp

/-!

## Group actions

-/

set_option backward.isDefEq.respectTransparency false in
lemma contrContrToMatrixRe_ρ {d : ℕ} (v : (ContrMod d ⊗[ℝ] ContrMod d)) (M : LorentzGroup d) :
    contrContrToMatrixRe (TensorProduct.map (ContrMod.rep M) (ContrMod.rep M) v) =
    M.1 * contrContrToMatrixRe v * Mᵀ := by
  nth_rewrite 1 [contrContrToMatrixRe]
  simp only [LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℝ ℝ (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d)) ((LinearMap.toMatrix
      ((contrBasis d).tensorProduct (contrBasis d))
      ((contrBasis d).tensorProduct (contrBasis d))
      (TensorProduct.map (ContrMod.rep M) (ContrMod.rep M)))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℝ ℝ ((Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)))
      (((contrBasis d).tensorProduct (contrBasis d)).repr v)))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr ((contrBasis d).tensorProduct (contrBasis d))
      ((contrBasis d).tensorProduct (contrBasis d))
      (TensorProduct.map (ContrMod.rep M) (ContrMod.rep M)) v)
    erw [h1]
    rfl
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix (contrBasis d) (contrBasis d)) (ContrMod.rep M))
        ((LinearMap.toMatrix (contrBasis d) (contrBasis d)) (ContrMod.rep M)) (i, j) k)
        * contrContrToMatrixRe v k.1 k.2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply, Matrix.transpose_apply]
  conv_rhs =>
    enter [2, x]
    rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [contrBasis_ρ_apply]
  ring

set_option backward.isDefEq.respectTransparency false in
lemma coCoToMatrixRe_ρ {d : ℕ} (v : (CoMod d ⊗[ℝ] CoMod d)) (M : LorentzGroup d) :
    coCoToMatrixRe (TensorProduct.map (CoMod.rep M) (CoMod.rep M) v) =
    M.1⁻¹ᵀ * coCoToMatrixRe v * M⁻¹ := by
  nth_rewrite 1 [coCoToMatrixRe]
  simp only [LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℝ ℝ (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d)) ((LinearMap.toMatrix
      ((coBasis d).tensorProduct (coBasis d))
      ((coBasis d).tensorProduct (coBasis d))
      (TensorProduct.map (CoMod.rep M) (CoMod.rep M))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℝ ℝ ((Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)))
      (((coBasis d).tensorProduct (coBasis d)).repr v))))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr ((coBasis d).tensorProduct (coBasis d))
      ((coBasis d).tensorProduct (coBasis d))
      (TensorProduct.map (CoMod.rep M) (CoMod.rep M)) v)
    erw [h1]
    rfl
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix (coBasis d) (coBasis d)) (CoMod.rep M))
        ((LinearMap.toMatrix (coBasis d) (coBasis d)) (CoMod.rep M)) (i, j) k)
        * coCoToMatrixRe v k.1 k.2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply, Matrix.transpose_apply]
  conv_rhs =>
    enter [2, x]
    rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [coBasis_ρ_apply, ← LorentzGroup.coe_inv, transpose_apply]
  ring

set_option backward.isDefEq.respectTransparency false in
lemma contrCoToMatrixRe_ρ {d : ℕ} (v : (ContrMod d ⊗[ℝ] CoMod d)) (M : LorentzGroup d) :
    contrCoToMatrixRe (TensorProduct.map (ContrMod.rep M) (CoMod.rep M) v) =
    M.1 * contrCoToMatrixRe v * M.1⁻¹ := by
  nth_rewrite 1 [contrCoToMatrixRe]
  simp only [LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℝ ℝ (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d)) ((LinearMap.toMatrix
      ((contrBasis d).tensorProduct (coBasis d))
      ((contrBasis d).tensorProduct (coBasis d))
      (TensorProduct.map (ContrMod.rep M) (CoMod.rep M))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℝ ℝ ((Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)))
      (((contrBasis d).tensorProduct (coBasis d)).repr v))))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr ((contrBasis d).tensorProduct (coBasis d))
      ((contrBasis d).tensorProduct (coBasis d))
      (TensorProduct.map (ContrMod.rep M) (CoMod.rep M)) v)
    erw [h1]
    rfl
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix (contrBasis d) (contrBasis d)) (ContrMod.rep M))
        ((LinearMap.toMatrix (coBasis d) (coBasis d)) (CoMod.rep M)) (i, j) k)
        * contrCoToMatrixRe v k.1 k.2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply]
  conv_rhs =>
    enter [2, x]
    rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [contrBasis_ρ_apply, coBasis_ρ_apply, transpose_apply]
  ring

set_option backward.isDefEq.respectTransparency false in
lemma coContrToMatrixRe_ρ {d : ℕ} (v : (CoMod d ⊗[ℝ] ContrMod d)) (M : LorentzGroup d) :
    coContrToMatrixRe (TensorProduct.map (CoMod.rep M) (ContrMod.rep M) v) =
    M.1⁻¹ᵀ * coContrToMatrixRe v * M.1ᵀ := by
  nth_rewrite 1 [coContrToMatrixRe]
  simp only [LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℝ ℝ (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d)) ((LinearMap.toMatrix
      ((coBasis d).tensorProduct (contrBasis d))
      ((coBasis d).tensorProduct (contrBasis d))
      (TensorProduct.map (CoMod.rep M) (ContrMod.rep M))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℝ ℝ ((Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)))
      (((coBasis d).tensorProduct (contrBasis d)).repr v))))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr ((coBasis d).tensorProduct (contrBasis d))
      ((coBasis d).tensorProduct (contrBasis d))
      (TensorProduct.map (CoMod.rep M) (ContrMod.rep M)) v)
    erw [h1]
    rfl
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix (coBasis d) (coBasis d)) (CoMod.rep M))
        ((LinearMap.toMatrix (contrBasis d) (contrBasis d)) (ContrMod.rep M)) (i, j) k)
        * coContrToMatrixRe v k.1 k.2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply, Matrix.transpose_apply]
  conv_rhs =>
    enter [2, x]
    rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [coBasis_ρ_apply, contrBasis_ρ_apply, transpose_apply]
  ring

/-!

## The symm version of the group actions.

-/

lemma contrContrToMatrixRe_ρ_symm {d : ℕ} (v : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ)
    (M : LorentzGroup d) :
    TensorProduct.map (ContrMod.rep M) (ContrMod.rep M) (contrContrToMatrixRe.symm v) =
    contrContrToMatrixRe.symm (M.1 * v * M.1ᵀ) := by
  refine contrContrToMatrixRe.injective ?_
  simp [contrContrToMatrixRe_ρ]

lemma coCoToMatrixRe_ρ_symm {d : ℕ} (v : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ)
    (M : LorentzGroup d) :
    TensorProduct.map (CoMod.rep M) (CoMod.rep M) (coCoToMatrixRe.symm v) =
    coCoToMatrixRe.symm (M.1⁻¹ᵀ * v * M.1⁻¹) := by
  have h1 := coCoToMatrixRe_ρ (coCoToMatrixRe.symm v) M
  simp only [LinearEquiv.apply_symm_apply, ← LorentzGroup.coe_inv] at h1
  simp only [← LorentzGroup.coe_inv]
  rw [← h1]
  simp

lemma contrCoToMatrixRe_ρ_symm {d : ℕ} (v : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ)
    (M : LorentzGroup d) :
    TensorProduct.map (ContrMod.rep M) (CoMod.rep M) (contrCoToMatrixRe.symm v) =
    contrCoToMatrixRe.symm (M.1 * v * M.1⁻¹) := by
  have h1 := contrCoToMatrixRe_ρ (contrCoToMatrixRe.symm v) M
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [← h1, LinearEquiv.symm_apply_apply]

lemma coContrToMatrixRe_ρ_symm {d : ℕ} (v : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ)
    (M : LorentzGroup d) :
    TensorProduct.map (CoMod.rep M) (ContrMod.rep M) (coContrToMatrixRe.symm v) =
    coContrToMatrixRe.symm (M.1⁻¹ᵀ * v * M.1ᵀ) := by
  have h1 := coContrToMatrixRe_ρ (coContrToMatrixRe.symm v) M
  simp only [LinearEquiv.apply_symm_apply] at h1
  rw [← h1, LinearEquiv.symm_apply_apply]

end Lorentz
end
