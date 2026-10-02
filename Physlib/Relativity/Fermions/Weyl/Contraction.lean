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
public import Mathlib.RepresentationTheory.Intertwining
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
/-- The bi-linear map corresponding to contraction of a left-handed Weyl fermion with a
  dual-left-handed Weyl fermion. -/
def leftDualBi : LeftHandedWeyl →ₗ[ℂ] DualLeftHandedWeyl →ₗ[ℂ] ℂ where
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

/-- The bi-linear map corresponding to contraction of a dual-left-handed Weyl fermion with a
  left-handed Weyl fermion. -/
def dualLeftBi : DualLeftHandedWeyl →ₗ[ℂ] LeftHandedWeyl →ₗ[ℂ] ℂ where
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
  dual-right-handed Weyl fermion. -/
def rightDualBi : RightHandedWeyl →ₗ[ℂ] DualRightHandedWeyl →ₗ[ℂ] ℂ where
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

/-- The bi-linear map corresponding to contraction of a dual-right-handed Weyl fermion with a
  right-handed Weyl fermion. -/
def dualRightBi : DualRightHandedWeyl →ₗ[ℂ] RightHandedWeyl →ₗ[ℂ] ℂ where
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

/-- The linear map from leftHandedWeyl ⊗ DualLeftHandedWeyl to ℂ given by
    summing over components of leftHandedWeyl and DualLeftHandedWeyl in the
    standard basis (i.e. the dot product).
    Physically, the contraction of a left-handed Weyl fermion with a dual-left-handed Weyl fermion.
    In index notation this is ψ^a φ_a. -/
def leftDualContraction : (LeftHandedWeyl.rep.tprod DualLeftHandedWeyl.rep).IntertwiningMap
    (Representation.trivial ℂ SL(2,ℂ) ℂ) where
  toLinearMap := TensorProduct.lift leftDualBi
  isIntertwining' M := TensorProduct.ext' fun ψ φ => by
    change (M.1 *ᵥ ψ.toFin2ℂ) ⬝ᵥ (M.1⁻¹ᵀ *ᵥ φ.toFin2ℂ) = ψ.toFin2ℂ ⬝ᵥ φ.toFin2ℂ
    rw [dotProduct_mulVec, vecMul_transpose, mulVec_mulVec]
    simp

lemma leftDualContraction_hom_tmul (ψ : LeftHandedWeyl)
    (φ : DualLeftHandedWeyl) :
    leftDualContraction (ψ ⊗ₜ φ) = ψ.toFin2ℂ ⬝ᵥ φ.toFin2ℂ := by
  rfl

lemma leftDualContraction_basis (i j : Fin 2) :
    leftDualContraction (LeftHandedWeyl.basis i ⊗ₜ DualLeftHandedWeyl.basis j) =
      if i.1 = j.1 then (1 : ℂ) else 0 := by
  rw [leftDualContraction_hom_tmul]
  simp only [LeftHandedWeyl.toFin2ℂ_eq_val, LeftHandedWeyl.basis_val,
    DualLeftHandedWeyl.toFin2ℂ_eq_val, DualLeftHandedWeyl.basis_val, dotProduct_single, mul_one]
  rw [Pi.single_apply]
  simp only [Fin.ext_iff]
  refine ite_congr ?h₁ (congrFun rfl) (congrFun rfl)
  exact Eq.propIntro (fun a => id (Eq.symm a)) fun a => id (Eq.symm a)

/-- The linear map from DualLeftHandedWeyl ⊗ leftHandedWeyl to ℂ given by
    summing over components of DualLeftHandedWeyl and leftHandedWeyl in the
    standard basis (i.e. the dot product).
    Physically, the contraction of a dual-left-handed Weyl fermion with a left-handed Weyl fermion.
    In index notation this is φ_a ψ^a. -/
def dualLeftContraction : (DualLeftHandedWeyl.rep.tprod LeftHandedWeyl.rep).IntertwiningMap
    (Representation.trivial ℂ SL(2,ℂ) ℂ) where
  toLinearMap := TensorProduct.lift dualLeftBi
  isIntertwining' M := TensorProduct.ext' fun φ ψ => by
    change (M.1⁻¹ᵀ *ᵥ φ.toFin2ℂ) ⬝ᵥ (M.1 *ᵥ ψ.toFin2ℂ) = φ.toFin2ℂ ⬝ᵥ ψ.toFin2ℂ
    rw [dotProduct_mulVec, mulVec_transpose, vecMul_vecMul]
    simp

lemma dualLeftContraction_hom_tmul (φ : DualLeftHandedWeyl) (ψ : LeftHandedWeyl) :
    dualLeftContraction (φ ⊗ₜ ψ) = φ.toFin2ℂ ⬝ᵥ ψ.toFin2ℂ := by
  rfl

lemma dualLeftContraction_basis (i j : Fin 2) :
    dualLeftContraction (DualLeftHandedWeyl.basis i ⊗ₜ LeftHandedWeyl.basis j) =
      if i.1 = j.1 then (1 : ℂ) else 0 := by
  rw [dualLeftContraction_hom_tmul]
  simp only [DualLeftHandedWeyl.toFin2ℂ_eq_val, DualLeftHandedWeyl.basis_val,
    LeftHandedWeyl.toFin2ℂ_eq_val, LeftHandedWeyl.basis_val, dotProduct_single, mul_one]
  rw [Pi.single_apply]
  simp only [Fin.ext_iff]
  refine ite_congr ?h₁ (congrFun rfl) (congrFun rfl)
  exact Eq.propIntro (fun a => id (Eq.symm a)) fun a => id (Eq.symm a)

/--
The linear map from `rightHandedWeyl ⊗ DualRightHandedWeyl` to `ℂ` given by
  summing over components of `rightHandedWeyl` and `DualRightHandedWeyl` in the
  standard basis (i.e. the dot product).
  The contraction of a right-handed Weyl fermion with a left-handed Weyl fermion.
  In index notation this is `ψ^{dot a} φ_{dot a}`.
-/
def rightDualContraction : (RightHandedWeyl.rep.tprod DualRightHandedWeyl.rep).IntertwiningMap
    (Representation.trivial ℂ SL(2,ℂ) ℂ) where
  toLinearMap := TensorProduct.lift rightDualBi
  isIntertwining' M := TensorProduct.ext' fun ψ φ => by
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
    simp only [one_mulVec, vec2_dotProduct, Fin.isValue, RightHandedWeyl.toFin2ℂEquiv_apply,
      DualRightHandedWeyl.toFin2ℂEquiv_apply]

lemma rightDualContraction_hom_tmul (ψ : RightHandedWeyl)
    (φ : DualRightHandedWeyl) :
    rightDualContraction (ψ ⊗ₜ φ) = ψ.toFin2ℂ ⬝ᵥ φ.toFin2ℂ := by
  rfl

lemma rightDualContraction_basis (i j : Fin 2) :
    rightDualContraction (RightHandedWeyl.basis i ⊗ₜ DualRightHandedWeyl.basis j) =
    if i.1 = j.1 then (1 : ℂ) else 0 := by
  rw [rightDualContraction_hom_tmul]
  simp only [RightHandedWeyl.toFin2ℂ_eq_val, RightHandedWeyl.basis_val,
    DualRightHandedWeyl.toFin2ℂ_eq_val, DualRightHandedWeyl.basis_val, dotProduct_single, mul_one]
  rw [Pi.single_apply]
  simp only [Fin.ext_iff]
  refine ite_congr ?h₁ (congrFun rfl) (congrFun rfl)
  exact Eq.propIntro (fun a => id (Eq.symm a)) fun a => id (Eq.symm a)

/--
  The linear map from DualRightHandedWeyl ⊗ rightHandedWeyl to ℂ given by
    summing over components of DualRightHandedWeyl and rightHandedWeyl in the
    standard basis (i.e. the dot product).
  The contraction of a right-handed Weyl fermion with a left-handed Weyl fermion.
    In index notation this is φ_{dot a} ψ^{dot a}.
-/
def dualRightContraction : (DualRightHandedWeyl.rep.tprod RightHandedWeyl.rep).IntertwiningMap
    (Representation.trivial ℂ SL(2,ℂ) ℂ) where
  toLinearMap := TensorProduct.lift dualRightBi
  isIntertwining' M := TensorProduct.ext' fun φ ψ => by
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
    simp only [vecMul_one, vec2_dotProduct, Fin.isValue, DualRightHandedWeyl.toFin2ℂEquiv_apply,
      RightHandedWeyl.toFin2ℂEquiv_apply]

lemma dualRightContraction_hom_tmul (φ : DualRightHandedWeyl)
    (ψ : RightHandedWeyl) :
    dualRightContraction (φ ⊗ₜ ψ) = φ.toFin2ℂ ⬝ᵥ ψ.toFin2ℂ := by
  rfl

lemma dualRightContraction_basis (i j : Fin 2) :
    dualRightContraction (DualRightHandedWeyl.basis i ⊗ₜ RightHandedWeyl.basis j) =
    if i.1 = j.1 then (1 : ℂ) else 0 := by
  rw [dualRightContraction_hom_tmul]
  simp only [DualRightHandedWeyl.toFin2ℂ_eq_val, DualRightHandedWeyl.basis_val,
    RightHandedWeyl.toFin2ℂ_eq_val, RightHandedWeyl.basis_val, dotProduct_single, mul_one]
  rw [Pi.single_apply]
  simp only [Fin.ext_iff]
  refine ite_congr ?h₁ (congrFun rfl) (congrFun rfl)
  exact Eq.propIntro (fun a => id (Eq.symm a)) fun a => id (Eq.symm a)

/-!

## Symmetry properties

-/

lemma leftDualContraction_tmul_symm (ψ : LeftHandedWeyl) (φ : DualLeftHandedWeyl) :
    leftDualContraction (ψ ⊗ₜ[ℂ] φ) = dualLeftContraction (φ ⊗ₜ[ℂ] ψ) := by
  rw [leftDualContraction_hom_tmul, dualLeftContraction_hom_tmul, dotProduct_comm]

lemma dualLeftContraction_tmul_symm (φ : DualLeftHandedWeyl) (ψ : LeftHandedWeyl) :
    dualLeftContraction (φ ⊗ₜ[ℂ] ψ) = leftDualContraction (ψ ⊗ₜ[ℂ] φ) := by
  rw [leftDualContraction_tmul_symm]

lemma rightDualContraction_tmul_symm (ψ : RightHandedWeyl) (φ : DualRightHandedWeyl) :
    rightDualContraction (ψ ⊗ₜ[ℂ] φ) = dualRightContraction (φ ⊗ₜ[ℂ] ψ) := by
  rw [rightDualContraction_hom_tmul, dualRightContraction_hom_tmul, dotProduct_comm]

lemma dualRightContraction_tmul_symm (φ : DualRightHandedWeyl) (ψ : RightHandedWeyl) :
    dualRightContraction (φ ⊗ₜ[ℂ] ψ) = rightDualContraction (ψ ⊗ₜ[ℂ] φ) := by
  rw [rightDualContraction_tmul_symm]

end
end Fermion
