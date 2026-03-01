/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.ComplexTensor.Weyl.Two
import PhysLean.Relativity.Tensors.ComplexTensor.Weyl.Contraction
/-!

# Units of Weyl fermions

We define the units for Weyl fermions, often denoted `δ` in the literature.

-/

namespace Fermion
noncomputable section

open Module Matrix
open MatrixGroups
open Complex
open TensorProduct
open CategoryTheory.MonoidalCategory

/-- The left-alt-left unit `δᵃₐ` as an element of `(leftHanded ⊗ altLeftHanded).V`. -/
def leftAltLeftUnitVal : (leftHanded ⊗ altLeftHanded).V :=
  leftAltLeftToMatrix.symm 1

/-- Expansion of `leftAltLeftUnitVal` into the basis. -/
lemma leftAltLeftUnitVal_expand_tmul : leftAltLeftUnitVal =
    leftBasis 0 ⊗ₜ[ℂ] altLeftBasis 0 + leftBasis 1 ⊗ₜ[ℂ] altLeftBasis 1 := by
  simp only [leftAltLeftUnitVal, Fin.isValue]
  erw [leftAltLeftToMatrix_symm_expand_tmul]
  simp only [Fin.sum_univ_two, Fin.isValue, one_apply_eq, one_smul, ne_eq, zero_ne_one,
    not_false_eq_true, one_apply_ne, zero_smul, add_zero, one_ne_zero, zero_add]

/-- The left-alt-left unit `δᵃₐ` as a morphism `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ leftHanded ⊗ altLeftHanded `,
  manifesting the invariance under the `SL(2,ℂ)` action. -/
def leftAltLeftUnit : 𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ leftHanded ⊗ altLeftHanded where
  hom := ModuleCat.ofHom {
    toFun := fun a =>
      let a' : ℂ := a
      a' • leftAltLeftUnitVal,
    map_add' := fun x y => by
      simp only [add_smul]
    map_smul' := fun m x => by
      simp only [smul_smul]
      rfl}
  comm M := by
    refine ModuleCat.hom_ext ?_
    refine LinearMap.ext fun x : ℂ => ?_
    simp only [ModuleCat.hom_comp]
    change x • leftAltLeftUnitVal =
      (TensorProduct.map (leftHanded.ρ M) (altLeftHanded.ρ M)) (x • leftAltLeftUnitVal)
    simp only [map_smul]
    apply congrArg
    simp only [leftAltLeftUnitVal]
    rw [leftAltLeftToMatrix_ρ_symm]
    apply congrArg
    simp

lemma leftAltLeftUnit_apply_one : leftAltLeftUnit.hom (1 : ℂ) = leftAltLeftUnitVal := by
  change (1 : ℂ) • leftAltLeftUnitVal = leftAltLeftUnitVal
  simp only [one_smul]

/-- The alt-left-left unit `δₐᵃ` as an element of `(altLeftHanded ⊗ leftHanded).V`. -/
def altLeftLeftUnitVal : (altLeftHanded ⊗ leftHanded).V :=
  altLeftLeftToMatrix.symm 1

/-- Expansion of `altLeftLeftUnitVal` into the basis. -/
lemma altLeftLeftUnitVal_expand_tmul : altLeftLeftUnitVal =
    altLeftBasis 0 ⊗ₜ[ℂ] leftBasis 0 + altLeftBasis 1 ⊗ₜ[ℂ] leftBasis 1 := by
  simp only [altLeftLeftUnitVal, Fin.isValue]
  rw [altLeftLeftToMatrix_symm_expand_tmul]
  simp only [Fin.sum_univ_two, Fin.isValue, one_apply_eq, one_smul, ne_eq, zero_ne_one,
    not_false_eq_true, one_apply_ne, zero_smul, add_zero, one_ne_zero, zero_add]

/-- The alt-left-left unit `δₐᵃ` as a morphism `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ altLeftHanded ⊗ leftHanded `,
  manifesting the invariance under the `SL(2,ℂ)` action. -/
def altLeftLeftUnit : 𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ altLeftHanded ⊗ leftHanded where
  hom := ModuleCat.ofHom {
    toFun := fun a =>
      let a' : ℂ := a
      a' • altLeftLeftUnitVal,
    map_add' := fun x y => by
      simp only [add_smul]
    map_smul' := fun m x => by
      simp only [smul_smul]
      rfl}
  comm M := by
    refine ModuleCat.hom_ext ?_
    refine LinearMap.ext fun x : ℂ => ?_
    simp only [ModuleCat.hom_comp]
    change x • altLeftLeftUnitVal =
      (TensorProduct.map (altLeftHanded.ρ M) (leftHanded.ρ M)) (x • altLeftLeftUnitVal)
    simp only [map_smul]
    apply congrArg
    simp only [altLeftLeftUnitVal]
    rw [altLeftLeftToMatrix_ρ_symm]
    apply congrArg
    simp only [mul_one, ← transpose_mul, SpecialLinearGroup.det_coe, isUnit_iff_ne_zero, ne_eq,
      one_ne_zero, not_false_eq_true, mul_nonsing_inv, transpose_one]

/-- Applying the morphism `altLeftLeftUnit` to `1` returns `altLeftLeftUnitVal`. -/
lemma altLeftLeftUnit_apply_one : altLeftLeftUnit.hom (1 : ℂ) = altLeftLeftUnitVal := by
  change (1 : ℂ) • altLeftLeftUnitVal = altLeftLeftUnitVal
  simp only [one_smul]

/-- The right-alt-right unit `δ^{dot a}_{dot a}` as an element of
  `(rightHanded ⊗ altRightHanded).V`. -/
def rightAltRightUnitVal : (rightHanded ⊗ altRightHanded).V :=
  rightAltRightToMatrix.symm 1

/-- Expansion of `rightAltRightUnitVal` into the basis. -/
lemma rightAltRightUnitVal_expand_tmul : rightAltRightUnitVal =
    rightBasis 0 ⊗ₜ[ℂ] altRightBasis 0 + rightBasis 1 ⊗ₜ[ℂ] altRightBasis 1 := by
  simp only [rightAltRightUnitVal, Fin.isValue]
  rw [rightAltRightToMatrix_symm_expand_tmul]
  simp only [Fin.sum_univ_two, Fin.isValue, one_apply_eq, one_smul, ne_eq, zero_ne_one,
    not_false_eq_true, one_apply_ne, zero_smul, add_zero, one_ne_zero, zero_add]

/-- The right-alt-right unit `δ^{dot a}_{dot a}` as a morphism
  `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ rightHanded ⊗ altRightHanded`, manifesting
  the invariance under the `SL(2,ℂ)` action. -/
def rightAltRightUnit : 𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ rightHanded ⊗ altRightHanded where
  hom := ModuleCat.ofHom {
    toFun := fun a =>
      let a' : ℂ := a
      a' • rightAltRightUnitVal,
    map_add' := fun x y => by
      simp only [add_smul]
    map_smul' := fun m x => by
      simp only [smul_smul]
      rfl}
  comm M := by
    refine ModuleCat.hom_ext ?_
    refine LinearMap.ext fun x : ℂ => ?_
    simp only [ModuleCat.hom_comp]
    change x • rightAltRightUnitVal =
      (TensorProduct.map (rightHanded.ρ M) (altRightHanded.ρ M)) (x • rightAltRightUnitVal)
    simp only [map_smul]
    apply congrArg
    simp only [rightAltRightUnitVal]
    rw [rightAltRightToMatrix_ρ_symm]
    apply congrArg
    simp only [RCLike.star_def, mul_one]
    symm
    refine transpose_eq_one.mp ?h.h.h.a
    simp only [transpose_mul, transpose_transpose]
    change (M.1)⁻¹ᴴ * (M.1)ᴴ = 1
    rw [@conjTranspose_nonsing_inv]
    simp

lemma rightAltRightUnit_apply_one : rightAltRightUnit.hom (1 : ℂ) = rightAltRightUnitVal := by
  change (1 : ℂ) • rightAltRightUnitVal = rightAltRightUnitVal
  simp only [one_smul]

/-- The alt-right-right unit `δ_{dot a}^{dot a}` as an element of
  `(rightHanded ⊗ altRightHanded).V`. -/
def altRightRightUnitVal : (altRightHanded ⊗ rightHanded).V :=
  altRightRightToMatrix.symm 1

/-- Expansion of `altRightRightUnitVal` into the basis. -/
lemma altRightRightUnitVal_expand_tmul : altRightRightUnitVal =
    altRightBasis 0 ⊗ₜ[ℂ] rightBasis 0 + altRightBasis 1 ⊗ₜ[ℂ] rightBasis 1 := by
  simp only [altRightRightUnitVal, Fin.isValue]
  rw [altRightRightToMatrix_symm_expand_tmul]
  simp only [Fin.sum_univ_two, Fin.isValue, one_apply_eq, one_smul, ne_eq, zero_ne_one,
    not_false_eq_true, one_apply_ne, zero_smul, add_zero, one_ne_zero, zero_add]

/-- The alt-right-right unit `δ_{dot a}^{dot a}` as a morphism
  `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ altRightHanded ⊗ rightHanded`, manifesting
  the invariance under the `SL(2,ℂ)` action. -/
def altRightRightUnit : 𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ altRightHanded ⊗ rightHanded where
  hom := ModuleCat.ofHom {
    toFun := fun a =>
      let a' : ℂ := a
      a' • altRightRightUnitVal,
    map_add' := fun x y => by
      simp only [add_smul]
    map_smul' := fun m x => by
      simp only [smul_smul]
      rfl}
  comm M := by
    refine ModuleCat.hom_ext ?_
    refine LinearMap.ext fun x : ℂ => ?_
    simp only [ModuleCat.hom_comp]
    change x • altRightRightUnitVal =
      (TensorProduct.map (altRightHanded.ρ M) (rightHanded.ρ M)) (x • altRightRightUnitVal)
    simp only [map_smul]
    apply congrArg
    simp only [altRightRightUnitVal]
    rw [altRightRightToMatrix_ρ_symm]
    apply congrArg
    simp only [mul_one, RCLike.star_def]
    symm
    change (M.1)⁻¹ᴴ * (M.1)ᴴ = 1
    rw [@conjTranspose_nonsing_inv]
    simp

lemma altRightRightUnit_apply_one : altRightRightUnit.hom (1 : ℂ) = altRightRightUnitVal := by
  change (1 : ℂ) • altRightRightUnitVal = altRightRightUnitVal
  simp only [one_smul]

/-!

## Contraction of the units

-/

/-- Contraction on the right with `altLeftLeftUnit` does nothing. -/
lemma contr_altLeftLeftUnit (x : leftHanded) :
    (λ_ leftHanded).hom.hom
    (((leftAltContraction) ▷ leftHanded).hom
    ((α_ _ _ leftHanded).inv.hom
    (x ⊗ₜ[ℂ] altLeftLeftUnit.hom (1 : ℂ)))) = x := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (Basis.mem_span leftBasis x)
  subst hc
  rw [altLeftLeftUnit_apply_one, altLeftLeftUnitVal_expand_tmul]
  simp only [Action.tensorObj_V, Action.tensorUnit_V, Action.leftUnitor_hom_hom,
    Action.whiskerRight_hom, Action.associator_inv_hom, CategoryTheory.Equivalence.symm_inverse,
    Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
    Fin.sum_univ_two, Fin.isValue, tmul_add, add_tmul, smul_tmul, tmul_smul, map_add, map_smul,
    ModuleCat.MonoidalCategory.associator_inv_apply]
  have h1 (x y : leftHanded) (z : altLeftHanded) : (leftAltContraction.hom ▷ leftHanded.V)
    ((α_ leftHanded.V altLeftHanded.V leftHanded.V).inv (x ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] y))) =
    (leftAltContraction.hom (x ⊗ₜ[ℂ] z)) ⊗ₜ[ℂ] y := rfl
  erw [h1, h1, h1, h1]
  repeat rw [leftAltContraction_basis]
  simp only [Fin.isValue, Fin.val_zero, ↓reduceIte, Fin.val_one, one_ne_zero, zero_tmul, map_zero,
    smul_zero, add_zero, zero_ne_one, zero_add]
  erw [TensorProduct.lid_tmul, TensorProduct.lid_tmul]
  simp only [Fin.isValue, one_smul]

/-- Contraction on the right with `leftAltLeftUnit` does nothing. -/
lemma contr_leftAltLeftUnit (x : altLeftHanded) :
    (λ_ altLeftHanded).hom.hom
    (((altLeftContraction) ▷ altLeftHanded).hom
    ((α_ _ _ altLeftHanded).inv.hom
    (x ⊗ₜ[ℂ] leftAltLeftUnit.hom (1 : ℂ)))) = x := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (Basis.mem_span altLeftBasis x)
  subst hc
  rw [leftAltLeftUnit_apply_one, leftAltLeftUnitVal_expand_tmul]
  simp only [Action.tensorObj_V, Action.tensorUnit_V, Action.leftUnitor_hom_hom,
    Action.whiskerRight_hom, Action.associator_inv_hom, CategoryTheory.Equivalence.symm_inverse,
    Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
    Fin.sum_univ_two, Fin.isValue, tmul_add, add_tmul, smul_tmul, tmul_smul, map_add, map_smul,
    ModuleCat.MonoidalCategory.associator_inv_apply]
  have h1 (x y : altLeftHanded) (z : leftHanded) : (altLeftContraction.hom ▷ altLeftHanded.V)
    ((α_ altLeftHanded.V leftHanded.V altLeftHanded.V).inv (x ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] y))) =
    (altLeftContraction.hom (x ⊗ₜ[ℂ] z)) ⊗ₜ[ℂ] y := rfl
  erw [h1, h1, h1, h1]
  repeat rw [altLeftContraction_basis]
  simp only [Fin.isValue, Fin.val_zero, ↓reduceIte, Fin.val_one, one_ne_zero, zero_tmul, map_zero,
    smul_zero, add_zero, zero_ne_one, zero_add]
  erw [TensorProduct.lid_tmul, TensorProduct.lid_tmul]
  simp only [Fin.isValue, one_smul]

/-- Contraction on the right with `altRightRightUnit` does nothing. -/
lemma contr_altRightRightUnit (x : rightHanded) :
    (λ_ rightHanded).hom.hom
    (((rightAltContraction) ▷ rightHanded).hom
    ((α_ _ _ rightHanded).inv.hom
    (x ⊗ₜ[ℂ] altRightRightUnit.hom (1 : ℂ)))) = x := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (Basis.mem_span rightBasis x)
  subst hc
  rw [altRightRightUnit_apply_one, altRightRightUnitVal_expand_tmul]
  simp only [Action.tensorObj_V, Action.tensorUnit_V, Action.leftUnitor_hom_hom,
    Action.whiskerRight_hom, Action.associator_inv_hom, CategoryTheory.Equivalence.symm_inverse,
    Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
    Fin.sum_univ_two, Fin.isValue, tmul_add, add_tmul, smul_tmul, tmul_smul, map_add, map_smul,
    ModuleCat.MonoidalCategory.associator_inv_apply]
  have h1 (x y : rightHanded) (z : altRightHanded) : (rightAltContraction.hom ▷ rightHanded.V)
    ((α_ rightHanded.V altRightHanded.V rightHanded.V).inv (x ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] y))) =
    (rightAltContraction.hom (x ⊗ₜ[ℂ] z)) ⊗ₜ[ℂ] y := rfl
  erw [h1, h1, h1, h1]
  repeat rw [rightAltContraction_basis]
  simp only [Fin.isValue, Fin.val_zero, ↓reduceIte, Fin.val_one, one_ne_zero, zero_tmul, map_zero,
    smul_zero, add_zero, zero_ne_one, zero_add]
  erw [TensorProduct.lid_tmul, TensorProduct.lid_tmul]
  simp only [Fin.isValue, one_smul]

/-- Contraction on the right with `rightAltRightUnit` does nothing. -/
lemma contr_rightAltRightUnit (x : altRightHanded) :
    (λ_ altRightHanded).hom.hom
    (((altRightContraction) ▷ altRightHanded).hom
    ((α_ _ _ altRightHanded).inv.hom
    (x ⊗ₜ[ℂ] rightAltRightUnit.hom (1 : ℂ)))) = x := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (Basis.mem_span altRightBasis x)
  subst hc
  rw [rightAltRightUnit_apply_one, rightAltRightUnitVal_expand_tmul]
  simp only [Action.tensorObj_V, Action.tensorUnit_V, Action.leftUnitor_hom_hom,
    Action.whiskerRight_hom, Action.associator_inv_hom, CategoryTheory.Equivalence.symm_inverse,
    Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
    Fin.sum_univ_two, Fin.isValue, tmul_add, add_tmul, smul_tmul, tmul_smul, map_add, map_smul,
    ModuleCat.MonoidalCategory.associator_inv_apply]
  have h1 (x y : altRightHanded) (z : rightHanded) : (altRightContraction.hom ▷ altRightHanded.V)
    ((α_ altRightHanded.V rightHanded.V altRightHanded.V).inv (x ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] y))) =
    (altRightContraction.hom (x ⊗ₜ[ℂ] z)) ⊗ₜ[ℂ] y := rfl
  erw [h1, h1, h1, h1]
  repeat rw [altRightContraction_basis]
  simp only [Fin.isValue, Fin.val_zero, ↓reduceIte, Fin.val_one, one_ne_zero, zero_tmul, map_zero,
    smul_zero, add_zero, zero_ne_one, zero_add]
  erw [TensorProduct.lid_tmul, TensorProduct.lid_tmul]
  simp only [Fin.isValue, one_smul]

/-!

## Symmetry properties of the units

-/
open CategoryTheory

lemma altLeftLeftUnit_symm :
    (altLeftLeftUnit.hom (1 : ℂ)) = (altLeftHanded ◁ 𝟙 _).hom
    ((β_ leftHanded altLeftHanded).hom.hom (leftAltLeftUnit.hom (1 : ℂ))) := by
  rw [altLeftLeftUnit_apply_one, altLeftLeftUnitVal_expand_tmul]
  rw [leftAltLeftUnit_apply_one, leftAltLeftUnitVal_expand_tmul]
  rfl

lemma leftAltLeftUnit_symm :
    (leftAltLeftUnit.hom (1 : ℂ)) = (leftHanded ◁ 𝟙 _).hom ((β_ altLeftHanded leftHanded).hom.hom
    (altLeftLeftUnit.hom (1 : ℂ))) := by
  rw [altLeftLeftUnit_apply_one, altLeftLeftUnitVal_expand_tmul]
  rw [leftAltLeftUnit_apply_one, leftAltLeftUnitVal_expand_tmul]
  rfl

lemma altRightRightUnit_symm :
    (altRightRightUnit.hom (1 : ℂ)) = (altRightHanded ◁ 𝟙 _).hom
    ((β_ rightHanded altRightHanded).hom.hom (rightAltRightUnit.hom (1 : ℂ))) := by
  rw [altRightRightUnit_apply_one, altRightRightUnitVal_expand_tmul]
  rw [rightAltRightUnit_apply_one, rightAltRightUnitVal_expand_tmul]
  rfl

lemma rightAltRightUnit_symm :
    (rightAltRightUnit.hom (1 : ℂ)) = (rightHanded ◁ 𝟙 _).hom
    ((β_ altRightHanded rightHanded).hom.hom (altRightRightUnit.hom (1 : ℂ))) := by
  rw [altRightRightUnit_apply_one, altRightRightUnitVal_expand_tmul]
  rw [rightAltRightUnit_apply_one, rightAltRightUnitVal_expand_tmul]
  rfl

end
end Fermion
