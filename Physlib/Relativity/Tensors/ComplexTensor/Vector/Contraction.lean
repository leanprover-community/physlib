/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.Vector.Basic
/-!

# Contraction of Lorentz vectors

-/

@[expose] public section

noncomputable section

open Module Matrix
open MatrixGroups
open Complex
open TensorProduct
open CategoryTheory.MonoidalCategory

namespace Lorentz

/-- The bi-linear map corresponding to contraction of a contravariant Lorentz vector with a
  covariant Lorentz vector. -/
def ComplexVector.contrBi : ComplexVector →ₗ[ℂ] ComplexCoVector →ₗ[ℂ] ℂ where
  toFun ψ := {
    toFun := fun φ => ψ.toFin13ℂ ⬝ᵥ φ.toFin13ℂ,
    map_add' := by
      intro φ φ'
      simp only [map_add]
      rw [dotProduct_add]
    map_smul' := by
      intro r φ
      simp only [LinearEquiv.map_smul]
      rw [dotProduct_smul]
      rfl}
  map_add' ψ ψ':= by
    refine LinearMap.ext (fun φ => ?_)
    simp only [map_add, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
    rw [add_dotProduct]
  map_smul' r ψ := by
    refine LinearMap.ext (fun φ => ?_)
    simp only [LinearEquiv.map_smul, LinearMap.coe_mk, AddHom.coe_mk]
    rw [smul_dotProduct]
    rfl

/-- The bi-linear map corresponding to contraction of a covariant Lorentz vector with a
  contravariant Lorentz vector. -/
def ComplexCoVector.contrBi : ComplexCoVector →ₗ[ℂ] ComplexVector →ₗ[ℂ] ℂ where
  toFun φ := {
    toFun := fun ψ => φ.toFin13ℂ ⬝ᵥ ψ.toFin13ℂ,
    map_add' := by
      intro ψ ψ'
      simp only [map_add]
      rw [dotProduct_add]
    map_smul' := by
      intro r ψ
      simp only [LinearEquiv.map_smul]
      rw [dotProduct_smul]
      rfl}
  map_add' φ φ' := by
    refine LinearMap.ext (fun ψ => ?_)
    simp only [map_add, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
    rw [add_dotProduct]
  map_smul' r φ := by
    refine LinearMap.ext (fun ψ => ?_)
    simp only [LinearEquiv.map_smul, LinearMap.coe_mk, AddHom.coe_mk]
    rw [smul_dotProduct]
    rfl

/-- The linear map from complexContr ⊗ complexCo to ℂ given by
    summing over components of contravariant Lorentz vector and
    covariant Lorentz vector in the
    standard basis (i.e. the dot product).
    In terms of index notation this is the contraction is ψⁱ φᵢ. -/
def ComplexVector.contr : (ComplexVector.SL2CRep.tprod ComplexCoVector.SL2CRep).IntertwiningMap
    (Representation.trivial ℂ SL(2,ℂ) ℂ) where
  toLinearMap := TensorProduct.lift ComplexVector.contrBi
  isIntertwining' M := TensorProduct.ext' fun ψ φ => by
    change ((LorentzGroup.toComplex (SL2C.toLorentzGroup M)) *ᵥ ψ.toFin13ℂ) ⬝ᵥ
      ((LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ᵀ *ᵥ φ.toFin13ℂ) =
        ψ.toFin13ℂ ⬝ᵥ φ.toFin13ℂ
    rw [dotProduct_mulVec, vecMul_transpose, mulVec_mulVec]
    rw [inv_mul_of_invertible (LorentzGroup.toComplex (SL2C.toLorentzGroup M))]
    simp

lemma ComplexVector.contr_tmul (ψ : ComplexVector) (φ : ComplexCoVector) :
    ComplexVector.contr (ψ ⊗ₜ φ) = ψ.toFin13ℂ ⬝ᵥ φ.toFin13ℂ := by
  rfl

lemma ComplexVector.contr_basis (i j : Fin 4) :
    ComplexVector.contr (ComplexVector.basisFin4 i ⊗ₜ ComplexCoVector.basisFin4 j) =
    if i.1 = j.1 then (1 : ℂ) else 0 := by
  rw [ComplexVector.contr_tmul]
  simp only [ComplexVector.basisFin4, Basis.coe_reindex, Function.comp_apply,
    ComplexVector.basis_toFin13ℂ, ComplexCoVector.basisFin4, ComplexCoVector.basis_toFin13ℂ,
    dotProduct_single, mul_one]
  rw [Pi.single_apply]
  refine ite_congr ?h₁ (congrFun rfl) (congrFun rfl)
  simp only [EmbeddingLike.apply_eq_iff_eq, Fin.ext_iff, eq_comm]

lemma ComplexVector.contr_basis' (i j : Fin 1 ⊕ Fin 3) :
    ComplexVector.contr (ComplexVector.basis i ⊗ₜ ComplexCoVector.basis j) =
    if i = j then (1 : ℂ) else 0 := by
  rw [ComplexVector.contr_tmul]
  simp only [ComplexVector.basis_toFin13ℂ, ComplexCoVector.basis_toFin13ℂ, dotProduct_single,
    mul_one]
  rw [Pi.single_apply]
  refine ite_congr ?h₁ (congrFun rfl) (congrFun rfl)
  exact Eq.propIntro (fun a => id (Eq.symm a)) fun a => id (Eq.symm a)

/-- The linear map from complexCo ⊗ complexContr to ℂ given by
    summing over components of covariant Lorentz vector and
    contravariant Lorentz vector in the
    standard basis (i.e. the dot product).
    In terms of index notation this is the contraction is φᵢ ψⁱ. -/
def ComplexCoVector.contr : (ComplexCoVector.SL2CRep.tprod ComplexVector.SL2CRep).IntertwiningMap
    (Representation.trivial ℂ SL(2,ℂ) ℂ) where
  toLinearMap := TensorProduct.lift ComplexCoVector.contrBi
  isIntertwining' M := TensorProduct.ext' fun φ ψ => by
    change ((LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ᵀ *ᵥ φ.toFin13ℂ) ⬝ᵥ
      ((LorentzGroup.toComplex (SL2C.toLorentzGroup M)) *ᵥ ψ.toFin13ℂ) = φ.toFin13ℂ ⬝ᵥ ψ.toFin13ℂ
    rw [dotProduct_mulVec, mulVec_transpose, vecMul_vecMul]
    rw [inv_mul_of_invertible (LorentzGroup.toComplex (SL2C.toLorentzGroup M))]
    simp

lemma ComplexCoVector.contr_tmul (φ : ComplexCoVector) (ψ : ComplexVector) :
    ComplexCoVector.contr (φ ⊗ₜ ψ) = φ.toFin13ℂ ⬝ᵥ ψ.toFin13ℂ := by
  rfl

lemma ComplexCoVector.contr_basis (i j : Fin 4) :
    ComplexCoVector.contr (ComplexCoVector.basisFin4 i ⊗ₜ ComplexVector.basisFin4 j) =
    if i.1 = j.1 then (1 : ℂ) else 0 := by
  rw [ComplexCoVector.contr_tmul]
  simp only [ComplexCoVector.basisFin4, Basis.coe_reindex, Function.comp_apply,
    ComplexCoVector.basis_toFin13ℂ, ComplexVector.basisFin4, ComplexVector.basis_toFin13ℂ,
    dotProduct_single, mul_one]
  rw [Pi.single_apply]
  refine ite_congr ?h₁ (congrFun rfl) (congrFun rfl)
  simp only [eq_comm, EmbeddingLike.apply_eq_iff_eq, Fin.ext_iff]

lemma ComplexCoVector.contr_basis' (i j : Fin 1 ⊕ Fin 3) :
    ComplexCoVector.contr (ComplexCoVector.basis i ⊗ₜ ComplexVector.basis j) =
    if i = j then (1 : ℂ) else 0 := by
  rw [ComplexCoVector.contr_tmul]
  simp only [ComplexCoVector.basis_toFin13ℂ, ComplexVector.basis_toFin13ℂ, dotProduct_single,
    mul_one]
  rw [Pi.single_apply]
  refine ite_congr ?h₁ (congrFun rfl) (congrFun rfl)
  simp only [eq_comm]

TODO "Prove the analogue of `SULieAlgebra.intertwiningMap_eq_smul_adjointℂContr` for complex
  Lorentz vectors: every intertwining map `ComplexVector.SL2CRep.tprod ComplexCoVector.SL2CRep →
  Representation.trivial ℂ SL(2,ℂ) ℂ` is a scalar multiple of `ComplexVector.contr`, and likewise
  for `ComplexCoVector.contr`. This is Schur's lemma for the vector representation of `SL(2,ℂ)`,
  which is irreducible."

/-!

## Symmetry

-/

lemma ComplexVector.contr_tmul_symm (φ : ComplexVector) (ψ : ComplexCoVector) :
    ComplexVector.contr (φ ⊗ₜ ψ) = ComplexCoVector.contr (ψ ⊗ₜ φ) := by
  rw [ComplexVector.contr_tmul, ComplexCoVector.contr_tmul, dotProduct_comm]

lemma ComplexCoVector.contr_tmul_symm (φ : ComplexCoVector) (ψ : ComplexVector) :
    ComplexCoVector.contr (φ ⊗ₜ ψ) = ComplexVector.contr (ψ ⊗ₜ φ) := by
  rw [ComplexVector.contr_tmul_symm]

end Lorentz
end
