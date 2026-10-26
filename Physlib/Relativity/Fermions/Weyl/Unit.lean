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
def DualLeftHandedWeyl.unitVal : (LeftHandedWeyl ⊗[ℂ] DualLeftHandedWeyl) :=
  leftDualLeftToMatrix.symm 1

/-- Expansion of `DualLeftHandedWeyl.unitVal` into the basis. -/
lemma DualLeftHandedWeyl.unitVal_expand_tmul : DualLeftHandedWeyl.unitVal =
    LeftHandedWeyl.basis 0 ⊗ₜ[ℂ] DualLeftHandedWeyl.basis 0 +
      LeftHandedWeyl.basis 1 ⊗ₜ[ℂ] DualLeftHandedWeyl.basis 1 := by
  simp only [DualLeftHandedWeyl.unitVal, Fin.isValue]
  rw [leftDualLeftToMatrix_symm_expand_tmul]
  simp only [Fin.sum_univ_two, Fin.isValue, one_apply_eq, one_smul, ne_eq, zero_ne_one,
    not_false_eq_true, one_apply_ne, zero_smul, add_zero, one_ne_zero, zero_add]

/-- The left-dual-left unit `δᵃₐ` as a morphism `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ leftHanded ⊗ dualLeftHanded `,
  manifesting the invariance under the `SL(2,ℂ)` action. -/
def DualLeftHandedWeyl.unit : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
    (LeftHandedWeyl.rep.tprod DualLeftHandedWeyl.rep) where
  toFun := fun a =>
    let a' : ℂ := a
    a' • DualLeftHandedWeyl.unitVal
  map_add' := fun x y => by
    simp only [add_smul]
  map_smul' := fun m x => by
    simp only [smul_smul]
    rfl
  isIntertwining' M := by
    refine LinearMap.ext fun x : ℂ => ?_
    change x • DualLeftHandedWeyl.unitVal =
      (TensorProduct.map (LeftHandedWeyl.rep M) (DualLeftHandedWeyl.rep M))
        (x • DualLeftHandedWeyl.unitVal)
    simp only [map_smul]
    apply congrArg
    simp only [DualLeftHandedWeyl.unitVal]
    rw [leftDualLeftToMatrix_ρ_symm]
    apply congrArg
    simp

lemma DualLeftHandedWeyl.unit_apply_one :
    DualLeftHandedWeyl.unit (1 : ℂ) = DualLeftHandedWeyl.unitVal := by
  change (1 : ℂ) • DualLeftHandedWeyl.unitVal = DualLeftHandedWeyl.unitVal
  simp only [one_smul]

/-- The dual-left-left unit `δₐᵃ` as an element of `(dualLeftHanded ⊗ leftHanded).V`. -/
def LeftHandedWeyl.unitVal : (DualLeftHandedWeyl ⊗[ℂ] LeftHandedWeyl) :=
  dualLeftLeftToMatrix.symm 1

/-- Expansion of `LeftHandedWeyl.unitVal` into the basis. -/
lemma LeftHandedWeyl.unitVal_expand_tmul : LeftHandedWeyl.unitVal =
    DualLeftHandedWeyl.basis 0 ⊗ₜ[ℂ] LeftHandedWeyl.basis 0 +
      DualLeftHandedWeyl.basis 1 ⊗ₜ[ℂ] LeftHandedWeyl.basis 1 := by
  simp only [LeftHandedWeyl.unitVal, Fin.isValue]
  rw [dualLeftLeftToMatrix_symm_expand_tmul]
  simp only [Fin.sum_univ_two, Fin.isValue, one_apply_eq, one_smul, ne_eq, zero_ne_one,
    not_false_eq_true, one_apply_ne, zero_smul, add_zero, one_ne_zero, zero_add]

/-- The dual-left-left unit `δₐᵃ` as a morphism `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶
  dualLeftHanded ⊗ leftHanded `, manifesting the invariance under the `SL(2,ℂ)` action. -/
def LeftHandedWeyl.unit :
    (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
      (DualLeftHandedWeyl.rep.tprod LeftHandedWeyl.rep) where
  toFun := fun a =>
      let a' : ℂ := a
      a' • LeftHandedWeyl.unitVal
  map_add' := fun x y => by
    simp only [add_smul]
  map_smul' := fun m x => by
    simp only [smul_smul]
    rfl
  isIntertwining' M := by
    refine LinearMap.ext fun x : ℂ => ?_
    change x • LeftHandedWeyl.unitVal =
      (TensorProduct.map (DualLeftHandedWeyl.rep M) (LeftHandedWeyl.rep M))
        (x • LeftHandedWeyl.unitVal)
    simp only [map_smul]
    apply congrArg
    simp only [LeftHandedWeyl.unitVal]
    rw [dualLeftLeftToMatrix_ρ_symm]
    apply congrArg
    simp only [mul_one, ← transpose_mul, SpecialLinearGroup.det_coe, isUnit_iff_ne_zero, ne_eq,
      one_ne_zero, not_false_eq_true, mul_nonsing_inv, transpose_one]

/-- Applying the morphism `LeftHandedWeyl.unit` to `1` returns `LeftHandedWeyl.unitVal`. -/
lemma LeftHandedWeyl.unit_apply_one : LeftHandedWeyl.unit (1 : ℂ) = LeftHandedWeyl.unitVal := by
  change (1 : ℂ) • LeftHandedWeyl.unitVal = LeftHandedWeyl.unitVal
  simp only [one_smul]

/-- The right-dual-right unit `δ^{dot a}_{dot a}` as an element of
  `(rightHanded ⊗ dualRightHanded).V`. -/
def DualRightHandedWeyl.unitVal : RightHandedWeyl ⊗[ℂ] DualRightHandedWeyl :=
  rightDualRightToMatrix.symm 1

/-- Expansion of `DualRightHandedWeyl.unitVal` into the basis. -/
lemma DualRightHandedWeyl.unitVal_expand_tmul : DualRightHandedWeyl.unitVal =
    RightHandedWeyl.basis 0 ⊗ₜ[ℂ] DualRightHandedWeyl.basis 0 +
      RightHandedWeyl.basis 1 ⊗ₜ[ℂ] DualRightHandedWeyl.basis 1 := by
  simp only [DualRightHandedWeyl.unitVal, Fin.isValue]
  rw [rightDualRightToMatrix_symm_expand_tmul]
  simp only [Fin.sum_univ_two, Fin.isValue, one_apply_eq, one_smul, ne_eq, zero_ne_one,
    not_false_eq_true, one_apply_ne, zero_smul, add_zero, one_ne_zero, zero_add]

/-- The right-dual-right unit `δ^{dot a}_{dot a}` as a morphism
  `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ rightHanded ⊗ dualRightHanded`, manifesting
  the invariance under the `SL(2,ℂ)` action. -/
def DualRightHandedWeyl.unit : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
    (RightHandedWeyl.rep.tprod DualRightHandedWeyl.rep) where
  toFun := fun a =>
    let a' : ℂ := a
    a' • DualRightHandedWeyl.unitVal
  map_add' := fun x y => by
    simp only [add_smul]
  map_smul' := fun m x => by
    simp only [smul_smul]
    rfl
  isIntertwining' M := by
    refine LinearMap.ext fun x : ℂ => ?_
    change x • DualRightHandedWeyl.unitVal =
      (TensorProduct.map (RightHandedWeyl.rep M) (DualRightHandedWeyl.rep M))
        (x • DualRightHandedWeyl.unitVal)
    simp only [map_smul]
    apply congrArg
    simp only [DualRightHandedWeyl.unitVal]
    rw [rightDualRightToMatrix_ρ_symm]
    apply congrArg
    simp only [RCLike.star_def, mul_one]
    symm
    refine transpose_eq_one.mp ?h.h.h.a
    simp only [transpose_mul, transpose_transpose]
    change (M.1)⁻¹ᴴ * (M.1)ᴴ = 1
    rw [@conjTranspose_nonsing_inv]
    simp

lemma DualRightHandedWeyl.unit_apply_one :
    DualRightHandedWeyl.unit (1 : ℂ) = DualRightHandedWeyl.unitVal := by
  change (1 : ℂ) • DualRightHandedWeyl.unitVal = DualRightHandedWeyl.unitVal
  simp only [one_smul]

/-- The dual-right-right unit `δ_{dot a}^{dot a}` as an element of
  `(rightHanded ⊗ dualRightHanded).V`. -/
def RightHandedWeyl.unitVal : (DualRightHandedWeyl ⊗[ℂ] RightHandedWeyl) :=
  dualRightRightToMatrix.symm 1

/-- Expansion of `RightHandedWeyl.unitVal` into the basis. -/
lemma RightHandedWeyl.unitVal_expand_tmul : RightHandedWeyl.unitVal =
    DualRightHandedWeyl.basis 0 ⊗ₜ[ℂ] RightHandedWeyl.basis 0 +
      DualRightHandedWeyl.basis 1 ⊗ₜ[ℂ] RightHandedWeyl.basis 1 := by
  simp only [RightHandedWeyl.unitVal, Fin.isValue]
  rw [dualRightRightToMatrix_symm_expand_tmul]
  simp only [Fin.sum_univ_two, Fin.isValue, one_apply_eq, one_smul, ne_eq, zero_ne_one,
    not_false_eq_true, one_apply_ne, zero_smul, add_zero, one_ne_zero, zero_add]

/-- The dual-right-right unit `δ_{dot a}^{dot a}` as a morphism
  `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ dualRightHanded ⊗ rightHanded`, manifesting
  the invariance under the `SL(2,ℂ)` action. -/
def RightHandedWeyl.unit : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
    (DualRightHandedWeyl.rep.tprod RightHandedWeyl.rep) where
  toFun := fun a =>
    let a' : ℂ := a
    a' • RightHandedWeyl.unitVal
  map_add' := fun x y => by
    simp only [add_smul]
  map_smul' := fun m x => by
    simp only [smul_smul]
    rfl
  isIntertwining' M := by
    refine LinearMap.ext fun x : ℂ => ?_
    change x • RightHandedWeyl.unitVal =
      (TensorProduct.map (DualRightHandedWeyl.rep M) (RightHandedWeyl.rep M))
        (x • RightHandedWeyl.unitVal)
    simp only [map_smul]
    apply congrArg
    simp only [RightHandedWeyl.unitVal]
    rw [dualRightRightToMatrix_ρ_symm]
    apply congrArg
    simp only [mul_one, RCLike.star_def]
    symm
    change (M.1)⁻¹ᴴ * (M.1)ᴴ = 1
    rw [@conjTranspose_nonsing_inv]
    simp

lemma RightHandedWeyl.unit_apply_one : RightHandedWeyl.unit (1 : ℂ) = RightHandedWeyl.unitVal := by
  change (1 : ℂ) • RightHandedWeyl.unitVal = RightHandedWeyl.unitVal
  simp only [one_smul]

/-!

## Contraction of the units

-/

/-- Contraction on the right with `LeftHandedWeyl.unit` does nothing. -/
lemma LeftHandedWeyl.contr_unit (x : LeftHandedWeyl) :
    (TensorProduct.lid ℂ _ <|
    LeftHandedWeyl.contr.toLinearMap.rTensor _ <|
    (TensorProduct.assoc ℂ _ _ _).symm <|
    x ⊗ₜ[ℂ] (LeftHandedWeyl.unit (1 : ℂ))) = x := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp
    (Basis.mem_span LeftHandedWeyl.basis x)
  subst hc
  simp [- Fintype.sum_sum_type, smul_tmul, LeftHandedWeyl.contr_basis,
    LeftHandedWeyl.unit_apply_one, LeftHandedWeyl.unitVal_expand_tmul, add_tmul, tmul_add]

/-- Contraction on the right with `DualLeftHandedWeyl.unit` does nothing. -/
lemma DualLeftHandedWeyl.contr_unit (x : DualLeftHandedWeyl) :
    (TensorProduct.lid ℂ _ <|
    DualLeftHandedWeyl.contr.toLinearMap.rTensor _ <|
    (TensorProduct.assoc ℂ _ _ _).symm <|
    x ⊗ₜ[ℂ] (DualLeftHandedWeyl.unit (1 : ℂ))) = x := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp
    (Basis.mem_span DualLeftHandedWeyl.basis x)
  subst hc
  simp [- Fintype.sum_sum_type, smul_tmul, DualLeftHandedWeyl.contr_basis,
    DualLeftHandedWeyl.unit_apply_one, DualLeftHandedWeyl.unitVal_expand_tmul, add_tmul, tmul_add]

/-- Contraction on the right with `RightHandedWeyl.unit` does nothing. -/
lemma RightHandedWeyl.contr_unit (x : RightHandedWeyl) :
    (TensorProduct.lid ℂ _ <|
    RightHandedWeyl.contr.toLinearMap.rTensor _ <|
    (TensorProduct.assoc ℂ _ _ _).symm <|
    x ⊗ₜ[ℂ] (RightHandedWeyl.unit (1 : ℂ))) = x := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp
    (Basis.mem_span RightHandedWeyl.basis x)
  subst hc
  simp [- Fintype.sum_sum_type, smul_tmul, RightHandedWeyl.contr_basis,
    RightHandedWeyl.unit_apply_one, RightHandedWeyl.unitVal_expand_tmul, add_tmul, tmul_add]

/-- Contraction on the right with `DualRightHandedWeyl.unit` does nothing. -/
lemma DualRightHandedWeyl.contr_unit (x : DualRightHandedWeyl) :
    (TensorProduct.lid ℂ _ <|
    DualRightHandedWeyl.contr.toLinearMap.rTensor _ <|
    (TensorProduct.assoc ℂ _ _ _).symm <|
    x ⊗ₜ[ℂ] (DualRightHandedWeyl.unit (1 : ℂ))) = x := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp
    (Basis.mem_span DualRightHandedWeyl.basis x)
  subst hc
  simp [- Fintype.sum_sum_type, smul_tmul, DualRightHandedWeyl.contr_basis,
    DualRightHandedWeyl.unit_apply_one, DualRightHandedWeyl.unitVal_expand_tmul, add_tmul, tmul_add]

/-!

## Symmetry properties of the units

-/
open CategoryTheory

lemma LeftHandedWeyl.unit_symm :
    LeftHandedWeyl.unit (1 : ℂ) = LinearMap.lTensor _ (LinearEquiv.refl _ _).toLinearMap
    (TensorProduct.comm ℂ _ _ (DualLeftHandedWeyl.unit (1 : ℂ))) := by
  rw [LeftHandedWeyl.unit_apply_one, LeftHandedWeyl.unitVal_expand_tmul]
  rw [DualLeftHandedWeyl.unit_apply_one, DualLeftHandedWeyl.unitVal_expand_tmul]
  rfl

lemma DualLeftHandedWeyl.unit_symm :
    DualLeftHandedWeyl.unit (1 : ℂ) = LinearMap.lTensor _ (LinearEquiv.refl _ _).toLinearMap
      (TensorProduct.comm ℂ _ _ (LeftHandedWeyl.unit (1 : ℂ))) := by
  rw [LeftHandedWeyl.unit_apply_one, LeftHandedWeyl.unitVal_expand_tmul]
  rw [DualLeftHandedWeyl.unit_apply_one, DualLeftHandedWeyl.unitVal_expand_tmul]
  rfl

lemma RightHandedWeyl.unit_symm :
    RightHandedWeyl.unit (1 : ℂ) = LinearMap.lTensor _ (LinearEquiv.refl _ _).toLinearMap
      (TensorProduct.comm ℂ _ _ (DualRightHandedWeyl.unit (1 : ℂ))) := by
  rw [RightHandedWeyl.unit_apply_one, RightHandedWeyl.unitVal_expand_tmul]
  rw [DualRightHandedWeyl.unit_apply_one, DualRightHandedWeyl.unitVal_expand_tmul]
  rfl

lemma DualRightHandedWeyl.unit_symm :
    DualRightHandedWeyl.unit (1 : ℂ) = LinearMap.lTensor _ (LinearEquiv.refl _ _).toLinearMap
      (TensorProduct.comm ℂ _ _ (RightHandedWeyl.unit (1 : ℂ))) := by
  rw [RightHandedWeyl.unit_apply_one, RightHandedWeyl.unitVal_expand_tmul]
  rw [DualRightHandedWeyl.unit_apply_one, DualRightHandedWeyl.unitVal_expand_tmul]
  rfl

end
end Fermion
