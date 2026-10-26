/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.Vector.Pre.Basic
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
def contrCoContrBi : ContrℂModule →ₗ[ℂ] CoℂModule →ₗ[ℂ] ℂ where
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
def contrContrCoBi : CoℂModule →ₗ[ℂ] ContrℂModule →ₗ[ℂ] ℂ where
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
def ContrℂModule.contr : (ContrℂModule.SL2CRep.tprod CoℂModule.SL2CRep).IntertwiningMap
    (Representation.trivial ℂ SL(2,ℂ) ℂ) where
  toLinearMap := TensorProduct.lift contrCoContrBi
  isIntertwining' M := TensorProduct.ext' fun ψ φ => by
    change ((LorentzGroup.toComplex (SL2C.toLorentzGroup M)) *ᵥ ψ.toFin13ℂ) ⬝ᵥ
      ((LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ᵀ *ᵥ φ.toFin13ℂ) =
        ψ.toFin13ℂ ⬝ᵥ φ.toFin13ℂ
    rw [dotProduct_mulVec, vecMul_transpose, mulVec_mulVec]
    rw [inv_mul_of_invertible (LorentzGroup.toComplex (SL2C.toLorentzGroup M))]
    simp

lemma ContrℂModule.contr_tmul (ψ : ContrℂModule) (φ : CoℂModule) :
    ContrℂModule.contr (ψ ⊗ₜ φ) = ψ.toFin13ℂ ⬝ᵥ φ.toFin13ℂ := by
  rfl

lemma ContrℂModule.contr_basis (i j : Fin 4) :
    ContrℂModule.contr (complexContrBasisFin4 i ⊗ₜ complexCoBasisFin4 j) =
    if i.1 = j.1 then (1 : ℂ) else 0 := by
  rw [ContrℂModule.contr_tmul]
  simp only [complexContrBasisFin4, Basis.coe_reindex, Function.comp_apply,
    complexContrBasis_toFin13ℂ, complexCoBasisFin4, complexCoBasis_toFin13ℂ, dotProduct_single,
    mul_one]
  rw [Pi.single_apply]
  refine ite_congr ?h₁ (congrFun rfl) (congrFun rfl)
  simp only [EmbeddingLike.apply_eq_iff_eq, Fin.ext_iff, eq_comm]

lemma ContrℂModule.contr_basis' (i j : Fin 1 ⊕ Fin 3) :
    ContrℂModule.contr (complexContrBasis i ⊗ₜ complexCoBasis j) =
    if i = j then (1 : ℂ) else 0 := by
  rw [ContrℂModule.contr_tmul]
  simp only [complexContrBasis_toFin13ℂ, complexCoBasis_toFin13ℂ, dotProduct_single, mul_one]
  rw [Pi.single_apply]
  refine ite_congr ?h₁ (congrFun rfl) (congrFun rfl)
  exact Eq.propIntro (fun a => id (Eq.symm a)) fun a => id (Eq.symm a)

/-- The linear map from complexCo ⊗ complexContr to ℂ given by
    summing over components of covariant Lorentz vector and
    contravariant Lorentz vector in the
    standard basis (i.e. the dot product).
    In terms of index notation this is the contraction is φᵢ ψⁱ. -/
def CoℂModule.contr : (CoℂModule.SL2CRep.tprod ContrℂModule.SL2CRep).IntertwiningMap
    (Representation.trivial ℂ SL(2,ℂ) ℂ) where
  toLinearMap := TensorProduct.lift contrContrCoBi
  isIntertwining' M := TensorProduct.ext' fun φ ψ => by
    change ((LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ᵀ *ᵥ φ.toFin13ℂ) ⬝ᵥ
      ((LorentzGroup.toComplex (SL2C.toLorentzGroup M)) *ᵥ ψ.toFin13ℂ) = φ.toFin13ℂ ⬝ᵥ ψ.toFin13ℂ
    rw [dotProduct_mulVec, mulVec_transpose, vecMul_vecMul]
    rw [inv_mul_of_invertible (LorentzGroup.toComplex (SL2C.toLorentzGroup M))]
    simp

lemma CoℂModule.contr_tmul (φ : CoℂModule) (ψ : ContrℂModule) :
    CoℂModule.contr (φ ⊗ₜ ψ) = φ.toFin13ℂ ⬝ᵥ ψ.toFin13ℂ := by
  rfl

lemma CoℂModule.contr_basis (i j : Fin 4) :
    CoℂModule.contr (complexCoBasisFin4 i ⊗ₜ complexContrBasisFin4 j) =
    if i.1 = j.1 then (1 : ℂ) else 0 := by
  rw [CoℂModule.contr_tmul]
  simp only [complexCoBasisFin4, Basis.coe_reindex, Function.comp_apply, complexCoBasis_toFin13ℂ,
    complexContrBasisFin4, complexContrBasis_toFin13ℂ, dotProduct_single, mul_one]
  rw [Pi.single_apply]
  refine ite_congr ?h₁ (congrFun rfl) (congrFun rfl)
  simp only [eq_comm, EmbeddingLike.apply_eq_iff_eq, Fin.ext_iff]

lemma CoℂModule.contr_basis' (i j : Fin 1 ⊕ Fin 3) :
    CoℂModule.contr (complexCoBasis i ⊗ₜ complexContrBasis j) =
    if i = j then (1 : ℂ) else 0 := by
  rw [CoℂModule.contr_tmul]
  simp only [complexCoBasis_toFin13ℂ, complexContrBasis_toFin13ℂ, dotProduct_single, mul_one]
  rw [Pi.single_apply]
  refine ite_congr ?h₁ (congrFun rfl) (congrFun rfl)
  simp only [eq_comm]

TODO "Prove the analogue of `SULieAlgebra.intertwiningMap_eq_smul_adjointℂContr` for complex
  Lorentz vectors: every intertwining map `ContrℂModule.SL2CRep.tprod CoℂModule.SL2CRep →
  Representation.trivial ℂ SL(2,ℂ) ℂ` is a scalar multiple of `ContrℂModule.contr`, and likewise
  for `CoℂModule.contr`. This is Schur's lemma for the vector representation of `SL(2,ℂ)`,
  which is irreducible."

/-!

## Symmetry

-/

lemma ContrℂModule.contr_tmul_symm (φ : ContrℂModule) (ψ : CoℂModule) :
    ContrℂModule.contr (φ ⊗ₜ ψ) = CoℂModule.contr (ψ ⊗ₜ φ) := by
  rw [ContrℂModule.contr_tmul, CoℂModule.contr_tmul, dotProduct_comm]

lemma CoℂModule.contr_tmul_symm (φ : CoℂModule) (ψ : ContrℂModule) :
    CoℂModule.contr (φ ⊗ₜ ψ) = ContrℂModule.contr (ψ ⊗ₜ φ) := by
  rw [ContrℂModule.contr_tmul_symm]

end Lorentz
end
