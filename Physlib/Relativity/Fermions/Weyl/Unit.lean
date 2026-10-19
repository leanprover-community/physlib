/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Fermions.Weyl.Two
public import Physlib.Relativity.Fermions.Weyl.Contraction
/-!

# Units of Weyl fermions

We define the units for Weyl fermions, often denoted `δ` in the literature.

-/

@[expose] public section

namespace Fermion
noncomputable section

open Module Matrix
open MatrixGroups
open Complex
open TensorProduct
open CategoryTheory.MonoidalCategory

/-- The left-dual-left unit `δᵃₐ` as an element of `(leftHanded ⊗ dualLeftHanded).V`. -/
def leftDualLeftUnitVal : (LeftHandedWeyl ⊗[ℂ] DualLeftHandedWeyl) :=
  leftDualLeftToMatrix.symm 1

/-- Expansion of `leftDualLeftUnitVal` into the basis. -/
lemma leftDualLeftUnitVal_expand_tmul : leftDualLeftUnitVal =
    LeftHandedWeyl.basis 0 ⊗ₜ[ℂ] DualLeftHandedWeyl.basis 0 +
      LeftHandedWeyl.basis 1 ⊗ₜ[ℂ] DualLeftHandedWeyl.basis 1 := by
  simp only [leftDualLeftUnitVal, Fin.isValue]
  rw [leftDualLeftToMatrix_symm_expand_tmul]
  simp only [Fin.sum_univ_two, Fin.isValue, one_apply_eq, one_smul, ne_eq, zero_ne_one,
    not_false_eq_true, one_apply_ne, zero_smul, add_zero, one_ne_zero, zero_add]

/-- The left-dual-left unit `δᵃₐ` as a morphism `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ leftHanded ⊗ dualLeftHanded `,
  manifesting the invariance under the `SL(2,ℂ)` action. -/
def leftDualLeftUnit : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
    (LeftHandedWeyl.rep.tprod DualLeftHandedWeyl.rep) where
  toFun := fun a =>
    let a' : ℂ := a
    a' • leftDualLeftUnitVal
  map_add' := fun x y => by
    simp only [add_smul]
  map_smul' := fun m x => by
    simp only [smul_smul]
    rfl
  isIntertwining' M := by
    refine LinearMap.ext fun x : ℂ => ?_
    change x • leftDualLeftUnitVal =
      (TensorProduct.map (LeftHandedWeyl.rep M) (DualLeftHandedWeyl.rep M))
        (x • leftDualLeftUnitVal)
    simp only [map_smul]
    apply congrArg
    simp only [leftDualLeftUnitVal]
    rw [leftDualLeftToMatrix_ρ_symm]
    apply congrArg
    simp

lemma leftDualLeftUnit_apply_one : leftDualLeftUnit (1 : ℂ) = leftDualLeftUnitVal := by
  change (1 : ℂ) • leftDualLeftUnitVal = leftDualLeftUnitVal
  simp only [one_smul]

/-- The dual-left-left unit `δₐᵃ` as an element of `(dualLeftHanded ⊗ leftHanded).V`. -/
def dualLeftLeftUnitVal : (DualLeftHandedWeyl ⊗[ℂ] LeftHandedWeyl) :=
  dualLeftLeftToMatrix.symm 1

/-- Expansion of `dualLeftLeftUnitVal` into the basis. -/
lemma dualLeftLeftUnitVal_expand_tmul : dualLeftLeftUnitVal =
    DualLeftHandedWeyl.basis 0 ⊗ₜ[ℂ] LeftHandedWeyl.basis 0 +
      DualLeftHandedWeyl.basis 1 ⊗ₜ[ℂ] LeftHandedWeyl.basis 1 := by
  simp only [dualLeftLeftUnitVal, Fin.isValue]
  rw [dualLeftLeftToMatrix_symm_expand_tmul]
  simp only [Fin.sum_univ_two, Fin.isValue, one_apply_eq, one_smul, ne_eq, zero_ne_one,
    not_false_eq_true, one_apply_ne, zero_smul, add_zero, one_ne_zero, zero_add]

/-- The dual-left-left unit `δₐᵃ` as a morphism `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶
  dualLeftHanded ⊗ leftHanded `, manifesting the invariance under the `SL(2,ℂ)` action. -/
def dualLeftLeftUnit :
    (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
      (DualLeftHandedWeyl.rep.tprod LeftHandedWeyl.rep) where
  toFun := fun a =>
      let a' : ℂ := a
      a' • dualLeftLeftUnitVal
  map_add' := fun x y => by
    simp only [add_smul]
  map_smul' := fun m x => by
    simp only [smul_smul]
    rfl
  isIntertwining' M := by
    refine LinearMap.ext fun x : ℂ => ?_
    change x • dualLeftLeftUnitVal =
      (TensorProduct.map (DualLeftHandedWeyl.rep M) (LeftHandedWeyl.rep M))
        (x • dualLeftLeftUnitVal)
    simp only [map_smul]
    apply congrArg
    simp only [dualLeftLeftUnitVal]
    rw [dualLeftLeftToMatrix_ρ_symm]
    apply congrArg
    simp only [mul_one, ← transpose_mul, SpecialLinearGroup.det_coe, isUnit_iff_ne_zero, ne_eq,
      one_ne_zero, not_false_eq_true, mul_nonsing_inv, transpose_one]

/-- Applying the morphism `dualLeftLeftUnit` to `1` returns `dualLeftLeftUnitVal`. -/
lemma dualLeftLeftUnit_apply_one : dualLeftLeftUnit (1 : ℂ) = dualLeftLeftUnitVal := by
  change (1 : ℂ) • dualLeftLeftUnitVal = dualLeftLeftUnitVal
  simp only [one_smul]

/-- The right-dual-right unit `δ^{dot a}_{dot a}` as an element of
  `(rightHanded ⊗ dualRightHanded).V`. -/
def rightDualRightUnitVal : RightHandedWeyl ⊗[ℂ] DualRightHandedWeyl :=
  rightDualRightToMatrix.symm 1

/-- Expansion of `rightDualRightUnitVal` into the basis. -/
lemma rightDualRightUnitVal_expand_tmul : rightDualRightUnitVal =
    RightHandedWeyl.basis 0 ⊗ₜ[ℂ] DualRightHandedWeyl.basis 0 +
      RightHandedWeyl.basis 1 ⊗ₜ[ℂ] DualRightHandedWeyl.basis 1 := by
  simp only [rightDualRightUnitVal, Fin.isValue]
  rw [rightDualRightToMatrix_symm_expand_tmul]
  simp only [Fin.sum_univ_two, Fin.isValue, one_apply_eq, one_smul, ne_eq, zero_ne_one,
    not_false_eq_true, one_apply_ne, zero_smul, add_zero, one_ne_zero, zero_add]

/-- The right-dual-right unit `δ^{dot a}_{dot a}` as a morphism
  `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ rightHanded ⊗ dualRightHanded`, manifesting
  the invariance under the `SL(2,ℂ)` action. -/
def rightDualRightUnit : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
    (RightHandedWeyl.rep.tprod DualRightHandedWeyl.rep) where
  toFun := fun a =>
    let a' : ℂ := a
    a' • rightDualRightUnitVal
  map_add' := fun x y => by
    simp only [add_smul]
  map_smul' := fun m x => by
    simp only [smul_smul]
    rfl
  isIntertwining' M := by
    refine LinearMap.ext fun x : ℂ => ?_
    change x • rightDualRightUnitVal =
      (TensorProduct.map (RightHandedWeyl.rep M) (DualRightHandedWeyl.rep M))
        (x • rightDualRightUnitVal)
    simp only [map_smul]
    apply congrArg
    simp only [rightDualRightUnitVal]
    rw [rightDualRightToMatrix_ρ_symm]
    apply congrArg
    simp only [RCLike.star_def, mul_one]
    symm
    refine transpose_eq_one.mp ?h.h.h.a
    simp only [transpose_mul, transpose_transpose]
    change (M.1)⁻¹ᴴ * (M.1)ᴴ = 1
    rw [@conjTranspose_nonsing_inv]
    simp

lemma rightDualRightUnit_apply_one : rightDualRightUnit (1 : ℂ) = rightDualRightUnitVal := by
  change (1 : ℂ) • rightDualRightUnitVal = rightDualRightUnitVal
  simp only [one_smul]

/-- The dual-right-right unit `δ_{dot a}^{dot a}` as an element of
  `(rightHanded ⊗ dualRightHanded).V`. -/
def dualRightRightUnitVal : (DualRightHandedWeyl ⊗[ℂ] RightHandedWeyl) :=
  dualRightRightToMatrix.symm 1

/-- Expansion of `dualRightRightUnitVal` into the basis. -/
lemma dualRightRightUnitVal_expand_tmul : dualRightRightUnitVal =
    DualRightHandedWeyl.basis 0 ⊗ₜ[ℂ] RightHandedWeyl.basis 0 +
      DualRightHandedWeyl.basis 1 ⊗ₜ[ℂ] RightHandedWeyl.basis 1 := by
  simp only [dualRightRightUnitVal, Fin.isValue]
  rw [dualRightRightToMatrix_symm_expand_tmul]
  simp only [Fin.sum_univ_two, Fin.isValue, one_apply_eq, one_smul, ne_eq, zero_ne_one,
    not_false_eq_true, one_apply_ne, zero_smul, add_zero, one_ne_zero, zero_add]

/-- The dual-right-right unit `δ_{dot a}^{dot a}` as a morphism
  `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ dualRightHanded ⊗ rightHanded`, manifesting
  the invariance under the `SL(2,ℂ)` action. -/
def dualRightRightUnit : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
    (DualRightHandedWeyl.rep.tprod RightHandedWeyl.rep) where
  toFun := fun a =>
    let a' : ℂ := a
    a' • dualRightRightUnitVal
  map_add' := fun x y => by
    simp only [add_smul]
  map_smul' := fun m x => by
    simp only [smul_smul]
    rfl
  isIntertwining' M := by
    refine LinearMap.ext fun x : ℂ => ?_
    change x • dualRightRightUnitVal =
      (TensorProduct.map (DualRightHandedWeyl.rep M) (RightHandedWeyl.rep M))
        (x • dualRightRightUnitVal)
    simp only [map_smul]
    apply congrArg
    simp only [dualRightRightUnitVal]
    rw [dualRightRightToMatrix_ρ_symm]
    apply congrArg
    simp only [mul_one, RCLike.star_def]
    symm
    change (M.1)⁻¹ᴴ * (M.1)ᴴ = 1
    rw [@conjTranspose_nonsing_inv]
    simp

lemma dualRightRightUnit_apply_one : dualRightRightUnit (1 : ℂ) = dualRightRightUnitVal := by
  change (1 : ℂ) • dualRightRightUnitVal = dualRightRightUnitVal
  simp only [one_smul]

/-!

## Contraction of the units

-/

/-- Contraction on the right with `dualLeftLeftUnit` does nothing. -/
lemma contr_dualLeftLeftUnit (x : LeftHandedWeyl) :
    (TensorProduct.lid ℂ _ <|
    leftDualContraction.toLinearMap.rTensor _ <|
    (TensorProduct.assoc ℂ _ _ _).symm <|
    x ⊗ₜ[ℂ] (dualLeftLeftUnit (1 : ℂ))) = x := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp
    (Basis.mem_span LeftHandedWeyl.basis x)
  subst hc
  simp [- Fintype.sum_sum_type, smul_tmul, leftDualContraction_basis,
    dualLeftLeftUnit_apply_one, dualLeftLeftUnitVal_expand_tmul, add_tmul, tmul_add]

/-- Contraction on the right with `leftDualLeftUnit` does nothing. -/
lemma contr_leftDualLeftUnit (x : DualLeftHandedWeyl) :
    (TensorProduct.lid ℂ _ <|
    dualLeftContraction.toLinearMap.rTensor _ <|
    (TensorProduct.assoc ℂ _ _ _).symm <|
    x ⊗ₜ[ℂ] (leftDualLeftUnit (1 : ℂ))) = x := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp
    (Basis.mem_span DualLeftHandedWeyl.basis x)
  subst hc
  simp [- Fintype.sum_sum_type, smul_tmul, dualLeftContraction_basis,
    leftDualLeftUnit_apply_one, leftDualLeftUnitVal_expand_tmul, add_tmul, tmul_add]

/-- Contraction on the right with `dualRightRightUnit` does nothing. -/
lemma contr_dualRightRightUnit (x : RightHandedWeyl) :
    (TensorProduct.lid ℂ _ <|
    rightDualContraction.toLinearMap.rTensor _ <|
    (TensorProduct.assoc ℂ _ _ _).symm <|
    x ⊗ₜ[ℂ] (dualRightRightUnit (1 : ℂ))) = x := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp
    (Basis.mem_span RightHandedWeyl.basis x)
  subst hc
  simp [- Fintype.sum_sum_type, smul_tmul, rightDualContraction_basis,
    dualRightRightUnit_apply_one, dualRightRightUnitVal_expand_tmul, add_tmul, tmul_add]

/-- Contraction on the right with `rightDualRightUnit` does nothing. -/
lemma contr_rightDualRightUnit (x : DualRightHandedWeyl) :
    (TensorProduct.lid ℂ _ <|
    dualRightContraction.toLinearMap.rTensor _ <|
    (TensorProduct.assoc ℂ _ _ _).symm <|
    x ⊗ₜ[ℂ] (rightDualRightUnit (1 : ℂ))) = x := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp
    (Basis.mem_span DualRightHandedWeyl.basis x)
  subst hc
  simp [- Fintype.sum_sum_type, smul_tmul, dualRightContraction_basis,
    rightDualRightUnit_apply_one, rightDualRightUnitVal_expand_tmul, add_tmul, tmul_add]

/-!

## Symmetry properties of the units

-/
open CategoryTheory

lemma dualLeftLeftUnit_symm :
    dualLeftLeftUnit (1 : ℂ) = LinearMap.lTensor _ (LinearEquiv.refl _ _).toLinearMap
    (TensorProduct.comm ℂ _ _ (leftDualLeftUnit (1 : ℂ))) := by
  rw [dualLeftLeftUnit_apply_one, dualLeftLeftUnitVal_expand_tmul]
  rw [leftDualLeftUnit_apply_one, leftDualLeftUnitVal_expand_tmul]
  rfl

lemma leftDualLeftUnit_symm :
    leftDualLeftUnit (1 : ℂ) = LinearMap.lTensor _ (LinearEquiv.refl _ _).toLinearMap
      (TensorProduct.comm ℂ _ _ (dualLeftLeftUnit (1 : ℂ))) := by
  rw [dualLeftLeftUnit_apply_one, dualLeftLeftUnitVal_expand_tmul]
  rw [leftDualLeftUnit_apply_one, leftDualLeftUnitVal_expand_tmul]
  rfl

lemma dualRightRightUnit_symm :
    dualRightRightUnit (1 : ℂ) = LinearMap.lTensor _ (LinearEquiv.refl _ _).toLinearMap
      (TensorProduct.comm ℂ _ _ (rightDualRightUnit (1 : ℂ))) := by
  rw [dualRightRightUnit_apply_one, dualRightRightUnitVal_expand_tmul]
  rw [rightDualRightUnit_apply_one, rightDualRightUnitVal_expand_tmul]
  rfl

lemma rightDualRightUnit_symm :
    rightDualRightUnit (1 : ℂ) = LinearMap.lTensor _ (LinearEquiv.refl _ _).toLinearMap
      (TensorProduct.comm ℂ _ _ (dualRightRightUnit (1 : ℂ))) := by
  rw [dualRightRightUnit_apply_one, dualRightRightUnitVal_expand_tmul]
  rw [rightDualRightUnit_apply_one, rightDualRightUnitVal_expand_tmul]
  rfl

end
end Fermion
