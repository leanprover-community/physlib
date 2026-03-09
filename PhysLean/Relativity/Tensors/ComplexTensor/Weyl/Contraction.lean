/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Relativity.Tensors.ComplexTensor.Weyl.Basic
/-!

# Contraction of Weyl fermions

We define the contraction of Weyl fermions.

-/

@[expose] public section

namespace Fermion
noncomputable section

open Matrix
open MatrixGroups
open Complex
open TensorProduct

/-!

## Contraction of Weyl fermions.

-/
open CategoryTheory.MonoidalCategory

/-- The bi-linear map corresponding to contraction of a left-handed Weyl fermion with a
  alt-left-handed Weyl fermion. -/
def leftAltBi : leftHanded →ₗ[ℂ] altLeftHanded →ₗ[ℂ] ℂ where
  toFun ψ := {
    toFun := fun φ => ψ.toFin2ℂ ⬝ᵥ φ.toFin2ℂ,
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

/-- The bi-linear map corresponding to contraction of a alt-left-handed Weyl fermion with a
  left-handed Weyl fermion. -/
def altLeftBi : altLeftHanded →ₗ[ℂ] leftHanded →ₗ[ℂ] ℂ where
  toFun ψ := {
    toFun := fun φ => ψ.toFin2ℂ ⬝ᵥ φ.toFin2ℂ,
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
    simp only [map_add, add_dotProduct, vec2_dotProduct, Fin.isValue, LinearMap.coe_mk,
      AddHom.coe_mk, LinearMap.add_apply]
  map_smul' ψ ψ' := by
    refine LinearMap.ext (fun φ => ?_)
    simp only [_root_.map_smul, smul_dotProduct, vec2_dotProduct, Fin.isValue, smul_eq_mul,
      LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply]

/-- The bi-linear map corresponding to contraction of a right-handed Weyl fermion with a
  alt-right-handed Weyl fermion. -/
def rightAltBi : rightHanded →ₗ[ℂ] altRightHanded →ₗ[ℂ] ℂ where
  toFun ψ := {
    toFun := fun φ => ψ.toFin2ℂ ⬝ᵥ φ.toFin2ℂ,
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

/-- The bi-linear map corresponding to contraction of a alt-right-handed Weyl fermion with a
  right-handed Weyl fermion. -/
def altRightBi : altRightHanded →ₗ[ℂ] rightHanded →ₗ[ℂ] ℂ where
  toFun ψ := {
    toFun := fun φ => ψ.toFin2ℂ ⬝ᵥ φ.toFin2ℂ,
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
    simp only [map_add, add_dotProduct, vec2_dotProduct, Fin.isValue, LinearMap.coe_mk,
      AddHom.coe_mk, LinearMap.add_apply]
  map_smul' ψ ψ' := by
    refine LinearMap.ext (fun φ => ?_)
    simp only [_root_.map_smul, smul_dotProduct, vec2_dotProduct, Fin.isValue, smul_eq_mul,
      LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply]

/-- The linear map from leftHandedWeyl ⊗ altLeftHandedWeyl to ℂ given by
    summing over components of leftHandedWeyl and altLeftHandedWeyl in the
    standard basis (i.e. the dot product).
    Physically, the contraction of a left-handed Weyl fermion with a alt-left-handed Weyl fermion.
    In index notation this is ψ^a φ_a. -/
def leftAltContraction : leftHanded ⊗ altLeftHanded ⟶ 𝟙_ (Rep ℂ SL(2,ℂ)) where
  hom := ModuleCat.ofHom <| TensorProduct.lift leftAltBi
  comm M := ModuleCat.hom_ext <| TensorProduct.ext' fun ψ φ => by
    change (M.1 *ᵥ ψ.toFin2ℂ) ⬝ᵥ (M.1⁻¹ᵀ *ᵥ φ.toFin2ℂ) = ψ.toFin2ℂ ⬝ᵥ φ.toFin2ℂ
    rw [dotProduct_mulVec, vecMul_transpose, mulVec_mulVec]
    simp

lemma leftAltContraction_hom_tmul (ψ : leftHanded) (φ : altLeftHanded) :
    leftAltContraction.hom (ψ ⊗ₜ φ) = ψ.toFin2ℂ ⬝ᵥ φ.toFin2ℂ := by
  rfl

lemma leftAltContraction_basis (i j : Fin 2) :
    leftAltContraction.hom (leftBasis i ⊗ₜ altLeftBasis j) = if i.1 = j.1 then (1 : ℂ) else 0 := by
  rw [leftAltContraction_hom_tmul]
  simp only [leftBasis_toFin2ℂ, altLeftBasis_toFin2ℂ, dotProduct_single, mul_one]
  rw [Pi.single_apply]
  simp only [Fin.ext_iff]
  refine ite_congr ?h₁ (congrFun rfl) (congrFun rfl)
  exact Eq.propIntro (fun a => id (Eq.symm a)) fun a => id (Eq.symm a)

/-- The linear map from altLeftHandedWeyl ⊗ leftHandedWeyl to ℂ given by
    summing over components of altLeftHandedWeyl and leftHandedWeyl in the
    standard basis (i.e. the dot product).
    Physically, the contraction of a alt-left-handed Weyl fermion with a left-handed Weyl fermion.
    In index notation this is φ_a ψ^a. -/
def altLeftContraction : altLeftHanded ⊗ leftHanded ⟶ 𝟙_ (Rep ℂ SL(2,ℂ)) where
  hom := ModuleCat.ofHom <| TensorProduct.lift altLeftBi
  comm M := ModuleCat.hom_ext <| TensorProduct.ext' fun φ ψ => by
    change (M.1⁻¹ᵀ *ᵥ φ.toFin2ℂ) ⬝ᵥ (M.1 *ᵥ ψ.toFin2ℂ) = φ.toFin2ℂ ⬝ᵥ ψ.toFin2ℂ
    rw [dotProduct_mulVec, mulVec_transpose, vecMul_vecMul]
    simp

lemma altLeftContraction_hom_tmul (φ : altLeftHanded) (ψ : leftHanded) :
    altLeftContraction.hom (φ ⊗ₜ ψ) = φ.toFin2ℂ ⬝ᵥ ψ.toFin2ℂ := by
  rfl

lemma altLeftContraction_basis (i j : Fin 2) :
    altLeftContraction.hom (altLeftBasis i ⊗ₜ leftBasis j) = if i.1 = j.1 then (1 : ℂ) else 0 := by
  rw [altLeftContraction_hom_tmul]
  simp only [altLeftBasis_toFin2ℂ, leftBasis_toFin2ℂ, dotProduct_single, mul_one]
  rw [Pi.single_apply]
  simp only [Fin.ext_iff]
  refine ite_congr ?h₁ (congrFun rfl) (congrFun rfl)
  exact Eq.propIntro (fun a => id (Eq.symm a)) fun a => id (Eq.symm a)

/--
The linear map from `rightHandedWeyl ⊗ altRightHandedWeyl` to `ℂ` given by
  summing over components of `rightHandedWeyl` and `altRightHandedWeyl` in the
  standard basis (i.e. the dot product).
  The contraction of a right-handed Weyl fermion with a left-handed Weyl fermion.
  In index notation this is `ψ^{dot a} φ_{dot a}`.
-/
def rightAltContraction : rightHanded ⊗ altRightHanded ⟶ 𝟙_ (Rep ℂ SL(2,ℂ)) where
  hom := ModuleCat.ofHom <| TensorProduct.lift rightAltBi
  comm M := ModuleCat.hom_ext <| TensorProduct.ext' fun ψ φ => by
    change (M.1.map star *ᵥ ψ.toFin2ℂ) ⬝ᵥ (M.1⁻¹.conjTranspose *ᵥ φ.toFin2ℂ) =
      ψ.toFin2ℂ ⬝ᵥ φ.toFin2ℂ
    have h1 : (M.1)⁻¹ᴴ = ((M.1)⁻¹.map star)ᵀ := by rfl
    rw [dotProduct_mulVec, h1, vecMul_transpose, mulVec_mulVec]
    have h2 : ((M.1)⁻¹.map star * (M.1).map star) = 1 := by
      refine transpose_inj.mp ?_
      rw [transpose_mul]
      change M.1.conjTranspose * (M.1)⁻¹.conjTranspose = 1ᵀ
      rw [← @conjTranspose_mul]
      simp only [SpecialLinearGroup.det_coe, isUnit_iff_ne_zero, ne_eq, one_ne_zero,
        not_false_eq_true, nonsing_inv_mul, conjTranspose_one, transpose_one]
    rw [h2]
    simp only [one_mulVec, vec2_dotProduct, Fin.isValue, RightHandedModule.toFin2ℂEquiv_apply,
      AltRightHandedModule.toFin2ℂEquiv_apply]

lemma rightAltContraction_hom_tmul (ψ : rightHanded) (φ : altRightHanded) :
    rightAltContraction.hom (ψ ⊗ₜ φ) = ψ.toFin2ℂ ⬝ᵥ φ.toFin2ℂ := by
  rfl

lemma rightAltContraction_basis (i j : Fin 2) :
    rightAltContraction.hom (rightBasis i ⊗ₜ altRightBasis j) =
    if i.1 = j.1 then (1 : ℂ) else 0 := by
  rw [rightAltContraction_hom_tmul]
  simp only [rightBasis_toFin2ℂ, altRightBasis_toFin2ℂ, dotProduct_single, mul_one]
  rw [Pi.single_apply]
  simp only [Fin.ext_iff]
  refine ite_congr ?h₁ (congrFun rfl) (congrFun rfl)
  exact Eq.propIntro (fun a => id (Eq.symm a)) fun a => id (Eq.symm a)

/--
  The linear map from altRightHandedWeyl ⊗ rightHandedWeyl to ℂ given by
    summing over components of altRightHandedWeyl and rightHandedWeyl in the
    standard basis (i.e. the dot product).
  The contraction of a right-handed Weyl fermion with a left-handed Weyl fermion.
    In index notation this is φ_{dot a} ψ^{dot a}.
-/
def altRightContraction : altRightHanded ⊗ rightHanded ⟶ 𝟙_ (Rep ℂ SL(2,ℂ)) where
  hom := ModuleCat.ofHom <| TensorProduct.lift altRightBi
  comm M := ModuleCat.hom_ext <| TensorProduct.ext' fun φ ψ => by
    change (M.1⁻¹.conjTranspose *ᵥ φ.toFin2ℂ) ⬝ᵥ (M.1.map star *ᵥ ψ.toFin2ℂ) =
      φ.toFin2ℂ ⬝ᵥ ψ.toFin2ℂ
    have h1 : (M.1)⁻¹ᴴ = ((M.1)⁻¹.map star)ᵀ := by rfl
    rw [dotProduct_mulVec, h1, mulVec_transpose, vecMul_vecMul]
    have h2 : ((M.1)⁻¹.map star * (M.1).map star) = 1 := by
      refine transpose_inj.mp ?_
      rw [transpose_mul]
      change M.1.conjTranspose * (M.1)⁻¹.conjTranspose = 1ᵀ
      rw [← @conjTranspose_mul]
      simp only [SpecialLinearGroup.det_coe, isUnit_iff_ne_zero, ne_eq, one_ne_zero,
        not_false_eq_true, nonsing_inv_mul, conjTranspose_one, transpose_one]
    rw [h2]
    simp only [vecMul_one, vec2_dotProduct, Fin.isValue, AltRightHandedModule.toFin2ℂEquiv_apply,
      RightHandedModule.toFin2ℂEquiv_apply]

lemma altRightContraction_hom_tmul (φ : altRightHanded) (ψ : rightHanded) :
    altRightContraction.hom (φ ⊗ₜ ψ) = φ.toFin2ℂ ⬝ᵥ ψ.toFin2ℂ := by
  rfl

lemma altRightContraction_basis (i j : Fin 2) :
    altRightContraction.hom (altRightBasis i ⊗ₜ rightBasis j) =
    if i.1 = j.1 then (1 : ℂ) else 0 := by
  rw [altRightContraction_hom_tmul]
  simp only [altRightBasis_toFin2ℂ, rightBasis_toFin2ℂ, dotProduct_single, mul_one]
  rw [Pi.single_apply]
  simp only [Fin.ext_iff]
  refine ite_congr ?h₁ (congrFun rfl) (congrFun rfl)
  exact Eq.propIntro (fun a => id (Eq.symm a)) fun a => id (Eq.symm a)

/-!

## Symmetry properties

-/

lemma leftAltContraction_tmul_symm (ψ : leftHanded) (φ : altLeftHanded) :
    leftAltContraction.hom (ψ ⊗ₜ[ℂ] φ) = altLeftContraction.hom (φ ⊗ₜ[ℂ] ψ) := by
  rw [leftAltContraction_hom_tmul, altLeftContraction_hom_tmul, dotProduct_comm]

lemma altLeftContraction_tmul_symm (φ : altLeftHanded) (ψ : leftHanded) :
    altLeftContraction.hom (φ ⊗ₜ[ℂ] ψ) = leftAltContraction.hom (ψ ⊗ₜ[ℂ] φ) := by
  rw [leftAltContraction_tmul_symm]

lemma rightAltContraction_tmul_symm (ψ : rightHanded) (φ : altRightHanded) :
    rightAltContraction.hom (ψ ⊗ₜ[ℂ] φ) = altRightContraction.hom (φ ⊗ₜ[ℂ] ψ) := by
  rw [rightAltContraction_hom_tmul, altRightContraction_hom_tmul, dotProduct_comm]

lemma altRightContraction_tmul_symm (φ : altRightHanded) (ψ : rightHanded) :
    altRightContraction.hom (φ ⊗ₜ[ℂ] ψ) = rightAltContraction.hom (ψ ⊗ₜ[ℂ] φ) := by
  rw [rightAltContraction_tmul_symm]

end
end Fermion
