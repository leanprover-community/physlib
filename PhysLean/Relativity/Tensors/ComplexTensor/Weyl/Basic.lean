/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Relativity.Tensors.ComplexTensor.Weyl.Modules
public import PhysLean.Relativity.SL2C.Basic
/-!

# Weyl fermions

A good reference for the material in this file is:
https://particle.physics.ucdavis.edu/modernsusy/slides/slideimages/spinorfeynrules.pdf

-/

@[expose] public section

namespace Fermion
noncomputable section

open Module Matrix
open MatrixGroups
open Complex
open TensorProduct

/-- The vector space ℂ^2 carrying the fundamental representation of SL(2,C).
  In index notation corresponds to a Weyl fermion with indices ψ^a. -/
def leftHanded : Rep ℂ SL(2,ℂ) := Rep.of {
  toFun := fun M => {
    toFun := fun (ψ : LeftHandedModule) =>
      LeftHandedModule.toFin2ℂEquiv.symm (M.1 *ᵥ ψ.toFin2ℂ),
    map_add' := by
      intro ψ ψ'
      simp [mulVec_add]
    map_smul' := by
      intro r ψ
      simp [mulVec_smul]}
  map_one' := by
    ext i
    simp
  map_mul' := fun M N => by
    simp only [SpecialLinearGroup.coe_mul]
    ext1 x
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply, LinearEquiv.apply_symm_apply,
      mulVec_mulVec]}

/-- The standard basis on left-handed Weyl fermions. -/
def leftBasis : Basis (Fin 2) ℂ leftHanded := Basis.ofEquivFun
  (Equiv.linearEquiv ℂ LeftHandedModule.toFin2ℂFun)

@[simp]
lemma leftBasis_ρ_apply (M : SL(2,ℂ)) (i j : Fin 2) :
    (LinearMap.toMatrix leftBasis leftBasis) (leftHanded.ρ M) i j = M.1 i j := by
  rw [LinearMap.toMatrix_apply]
  simp only [leftBasis, Basis.coe_ofEquivFun, Basis.ofEquivFun_repr_apply]
  change (M.1 *ᵥ (Pi.single j 1)) i = _
  simp

@[simp]
lemma leftBasis_toFin2ℂ (i : Fin 2) : (leftBasis i).toFin2ℂ = Pi.single i 1 := by
  simp only [leftBasis, Basis.coe_ofEquivFun]
  rfl

/-- The vector space ℂ^2 carrying the representation of SL(2,C) given by
    M → (M⁻¹)ᵀ. In index notation corresponds to a Weyl fermion with indices ψ_a. -/
def altLeftHanded : Rep ℂ SL(2,ℂ) := Rep.of {
  toFun := fun M => {
    toFun := fun (ψ : AltLeftHandedModule) =>
      AltLeftHandedModule.toFin2ℂEquiv.symm ((M.1⁻¹)ᵀ *ᵥ ψ.toFin2ℂ),
    map_add' := by
      intro ψ ψ'
      simp [mulVec_add]
    map_smul' := by
      intro r ψ
      simp [mulVec_smul]}
  map_one' := by
    ext i
    simp
  map_mul' := fun M N => by
    ext1 x
    simp only [SpecialLinearGroup.coe_mul, LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply,
      LinearEquiv.apply_symm_apply, mulVec_mulVec, EmbeddingLike.apply_eq_iff_eq]
    refine (congrFun (congrArg _ ?_) _)
    rw [Matrix.mul_inv_rev]
    exact transpose_mul _ _}

/-- The standard basis on alt-left-handed Weyl fermions. -/
def altLeftBasis : Basis (Fin 2) ℂ altLeftHanded := Basis.ofEquivFun
  (Equiv.linearEquiv ℂ AltLeftHandedModule.toFin2ℂFun)

@[simp]
lemma altLeftBasis_toFin2ℂ (i : Fin 2) : (altLeftBasis i).toFin2ℂ = Pi.single i 1 := by
  simp only [altLeftBasis, Basis.coe_ofEquivFun]
  rfl

@[simp]
lemma altLeftBasis_ρ_apply (M : SL(2,ℂ)) (i j : Fin 2) :
    (LinearMap.toMatrix altLeftBasis altLeftBasis) (altLeftHanded.ρ M) i j = (M.1⁻¹)ᵀ i j := by
  rw [LinearMap.toMatrix_apply]
  simp only [altLeftBasis, Basis.coe_ofEquivFun, Basis.ofEquivFun_repr_apply, transpose_apply]
  change ((M.1⁻¹)ᵀ *ᵥ (Pi.single j 1)) i = _
  simp

/-- The vector space ℂ^2 carrying the conjugate representation of SL(2,C).
  In index notation corresponds to a Weyl fermion with indices ψ^{dot a}. -/
def rightHanded : Rep ℂ SL(2,ℂ) := Rep.of {
  toFun := fun M => {
    toFun := fun (ψ : RightHandedModule) =>
      RightHandedModule.toFin2ℂEquiv.symm (M.1.map star *ᵥ ψ.toFin2ℂ),
    map_add' := by
      intro ψ ψ'
      simp [mulVec_add]
    map_smul' := by
      intro r ψ
      simp [mulVec_smul]}
  map_one' := by
    ext i
    simp
  map_mul' := fun M N => by
    ext1 x
    simp only [SpecialLinearGroup.coe_mul, RCLike.star_def, Matrix.map_mul, LinearMap.coe_mk,
      AddHom.coe_mk, Module.End.mul_apply, LinearEquiv.apply_symm_apply, mulVec_mulVec]}

/-- The standard basis on right-handed Weyl fermions. -/
def rightBasis : Basis (Fin 2) ℂ rightHanded := Basis.ofEquivFun
  (Equiv.linearEquiv ℂ RightHandedModule.toFin2ℂFun)

@[simp]
lemma rightBasis_toFin2ℂ (i : Fin 2) : (rightBasis i).toFin2ℂ = Pi.single i 1 := by
  simp only [rightBasis, Basis.coe_ofEquivFun]
  rfl

@[simp]
lemma rightBasis_ρ_apply (M : SL(2,ℂ)) (i j : Fin 2) :
    (LinearMap.toMatrix rightBasis rightBasis) (rightHanded.ρ M) i j = (M.1.map star) i j := by
  rw [LinearMap.toMatrix_apply]
  simp only [rightBasis, Basis.coe_ofEquivFun, Basis.ofEquivFun_repr_apply]
  change (M.1.map star *ᵥ (Pi.single j 1)) i = _
  simp [mulVec_single]

/-- The vector space ℂ^2 carrying the representation of SL(2,C) given by
    M → (M⁻¹)^†.
    In index notation this corresponds to a Weyl fermion with index `ψ_{dot a}`. -/
def altRightHanded : Rep ℂ SL(2,ℂ) := Rep.of {
  toFun := fun M => {
    toFun := fun (ψ : AltRightHandedModule) =>
      AltRightHandedModule.toFin2ℂEquiv.symm ((M.1⁻¹).conjTranspose *ᵥ ψ.toFin2ℂ),
    map_add' := by
      intro ψ ψ'
      simp [mulVec_add]
    map_smul' := by
      intro r ψ
      simp [mulVec_smul]}
  map_one' := by
    ext i
    simp
  map_mul' := fun M N => by
    ext1 x
    simp only [SpecialLinearGroup.coe_mul, LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply,
      LinearEquiv.apply_symm_apply, mulVec_mulVec, EmbeddingLike.apply_eq_iff_eq]
    refine (congrFun (congrArg _ ?_) _)
    rw [Matrix.mul_inv_rev]
    exact conjTranspose_mul _ _}

/-- The standard basis on alt-right-handed Weyl fermions. -/
def altRightBasis : Basis (Fin 2) ℂ altRightHanded := Basis.ofEquivFun
  (Equiv.linearEquiv ℂ AltRightHandedModule.toFin2ℂFun)

@[simp]
lemma altRightBasis_toFin2ℂ (i : Fin 2) : (altRightBasis i).toFin2ℂ = Pi.single i 1 := by
  simp only [altRightBasis, Basis.coe_ofEquivFun]
  rfl

@[simp]
lemma altRightBasis_ρ_apply (M : SL(2,ℂ)) (i j : Fin 2) :
    (LinearMap.toMatrix altRightBasis altRightBasis) (altRightHanded.ρ M) i j =
    ((M.1⁻¹).conjTranspose) i j := by
  rw [LinearMap.toMatrix_apply]
  simp only [altRightBasis, Basis.coe_ofEquivFun, Basis.ofEquivFun_repr_apply]
  change ((M.1⁻¹).conjTranspose *ᵥ (Pi.single j 1)) i = _
  simp [mulVec_single]

/-!

## Equivalences between Weyl fermion vector spaces.

-/

/-- The morphism between the representation `leftHanded` and the representation
  `altLeftHanded` defined by multiplying an element of
  `leftHanded` by the matrix `εᵃ⁰ᵃ¹ = !![0, 1; -1, 0]]`. -/
def leftHandedToAlt : leftHanded ⟶ altLeftHanded where
  hom := ModuleCat.ofHom {
    toFun := fun ψ => AltLeftHandedModule.toFin2ℂEquiv.symm (!![0, 1; -1, 0] *ᵥ ψ.toFin2ℂ),
    map_add' := by
      intro ψ ψ'
      simp only [mulVec_add, LinearEquiv.map_add]
    map_smul' := by
      intro a ψ
      simp only [mulVec_smul, LinearEquiv.map_smul]
      rfl}
  comm := by
    intro M
    refine ModuleCat.hom_ext ?_
    refine LinearMap.ext (fun ψ => ?_)
    change AltLeftHandedModule.toFin2ℂEquiv.symm (!![0, 1; -1, 0] *ᵥ M.1 *ᵥ ψ.val) =
      AltLeftHandedModule.toFin2ℂEquiv.symm ((M.1⁻¹)ᵀ *ᵥ !![0, 1; -1, 0] *ᵥ ψ.val)
    apply congrArg
    rw [mulVec_mulVec, mulVec_mulVec, Lorentz.SL2C.inverse_coe, eta_fin_two M.1]
    refine congrFun (congrArg _ ?_) _
    rw [SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_fin_two, eta_fin_two !![M.1 1 1, -M.1 0 1; -M.1 1 0, M.1 0 0]ᵀ]
    simp

lemma leftHandedToAlt_hom_apply (ψ : leftHanded) :
    leftHandedToAlt.hom ψ =
    AltLeftHandedModule.toFin2ℂEquiv.symm (!![0, 1; -1, 0] *ᵥ ψ.toFin2ℂ) := rfl

/-- The morphism from `altLeftHanded` to
  `leftHanded` defined by multiplying an element of
  altLeftHandedWeyl by the matrix `εₐ₁ₐ₂ = !![0, -1; 1, 0]`. -/
def leftHandedAltTo : altLeftHanded ⟶ leftHanded where
  hom := ModuleCat.ofHom {
    toFun := fun ψ =>
      LeftHandedModule.toFin2ℂEquiv.symm (!![0, -1; 1, 0] *ᵥ ψ.toFin2ℂ),
    map_add' := by
      intro ψ ψ'
      simp only [map_add]
      rw [mulVec_add, LinearEquiv.map_add]
    map_smul' := by
      intro a ψ
      simp only [LinearEquiv.map_smul]
      rw [mulVec_smul, LinearEquiv.map_smul]
      rfl}
  comm := by
    intro M
    refine ModuleCat.hom_ext ?_
    refine LinearMap.ext (fun ψ => ?_)
    change LeftHandedModule.toFin2ℂEquiv.symm (!![0, -1; 1, 0] *ᵥ (M.1⁻¹)ᵀ *ᵥ ψ.val) =
      LeftHandedModule.toFin2ℂEquiv.symm (M.1 *ᵥ !![0, -1; 1, 0] *ᵥ ψ.val)
    rw [EquivLike.apply_eq_iff_eq, mulVec_mulVec, mulVec_mulVec, Lorentz.SL2C.inverse_coe,
      eta_fin_two M.1]
    refine congrFun (congrArg _ ?_) _
    rw [SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_fin_two, eta_fin_two !![M.1 1 1, -M.1 0 1; -M.1 1 0, M.1 0 0]ᵀ]
    simp

lemma leftHandedAltTo_hom_apply (ψ : altLeftHanded) :
    leftHandedAltTo.hom ψ =
    LeftHandedModule.toFin2ℂEquiv.symm (!![0, -1; 1, 0] *ᵥ ψ.toFin2ℂ) := rfl

/-- The equivalence between the representation `leftHanded` and the representation
  `altLeftHanded` defined by multiplying an element of
  `leftHanded` by the matrix `εᵃ⁰ᵃ¹ = !![0, 1; -1, 0]]`. -/
def leftHandedAltEquiv : leftHanded ≅ altLeftHanded where
  hom := leftHandedToAlt
  inv := leftHandedAltTo
  hom_inv_id := by
    ext ψ
    simp only [Action.comp_hom, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
      Action.id_hom, ModuleCat.hom_id, LinearMap.id_coe, id_eq]
    rw [leftHandedAltTo_hom_apply, leftHandedToAlt_hom_apply]
    rw [AltLeftHandedModule.toFin2ℂ, LinearEquiv.apply_symm_apply, mulVec_mulVec]
    rw [show (!![0, -1; (1 : ℂ), 0] * !![0, 1; -1, 0]) = 1 by simpa using Eq.symm one_fin_two]
    rw [one_mulVec]
    rfl
  inv_hom_id := by
    ext ψ
    simp only [Action.comp_hom, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
      Action.id_hom, ModuleCat.hom_id, LinearMap.id_coe, id_eq]
    rw [leftHandedAltTo_hom_apply, leftHandedToAlt_hom_apply, LeftHandedModule.toFin2ℂ,
      LinearEquiv.apply_symm_apply, mulVec_mulVec]
    rw [show (!![0, (1 : ℂ); -1, 0] * !![0, -1; 1, 0]) = 1 by simpa using Eq.symm one_fin_two]
    rw [one_mulVec]
    rfl

/-- `leftHandedAltEquiv` acting on an element `ψ : leftHanded` corresponds
  to multiplying `ψ` by the matrix `!![0, 1; -1, 0]`. -/
lemma leftHandedAltEquiv_hom_hom_apply (ψ : leftHanded) :
    leftHandedAltEquiv.hom.hom ψ =
    AltLeftHandedModule.toFin2ℂEquiv.symm (!![0, 1; -1, 0] *ᵥ ψ.toFin2ℂ) := rfl

/-- The inverse of `leftHandedAltEquiv` acting on an element`ψ : altLeftHanded` corresponds
  to multiplying `ψ` by the matrix `!![0, -1; 1, 0]`. -/
lemma leftHandedAltEquiv_inv_hom_apply (ψ : altLeftHanded) :
    leftHandedAltEquiv.inv.hom ψ =
    LeftHandedModule.toFin2ℂEquiv.symm (!![0, -1; 1, 0] *ᵥ ψ.toFin2ℂ) := rfl

/-- The linear equivalence between `rightHandedWeyl` and `altRightHandedWeyl` given by multiplying
an element of `rightHandedWeyl` by the matrix `εᵃ⁰ᵃ¹ = !![0, 1; -1, 0]]`.
-/
informal_definition rightHandedWeylAltEquiv where
  deps := [``rightHanded, ``altRightHanded]
  tag := "6VZR4"

/-- The linear equivalence `rightHandedWeylAltEquiv` is equivariant with respect to the action of
`SL(2,C)` on `rightHandedWeyl` and `altRightHandedWeyl`.
-/
informal_lemma rightHandedWeylAltEquiv_equivariant where
  deps := [``rightHandedWeylAltEquiv]
  tag := "6VZSG"

end

end Fermion
