/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Matrix.Pre
public import Physlib.Relativity.Tensors.RealTensor.Vector.Pre.Contraction
/-!

# Unit for complex Lorentz vectors

-/

@[expose] public section
noncomputable section

open Module Matrix MatrixGroups Complex TensorProduct CategoryTheory.MonoidalCategory

namespace Lorentz

/-- The contra-co unit for complex lorentz vectors. Usually denoted `δⁱᵢ`. -/
def preContrCoUnitVal (d : ℕ := 3) : ContrMod d ⊗[ℝ] CoMod d :=
  contrCoToMatrixRe.symm 1

/-- Expansion of `preContrCoUnitVal` into basis. -/
lemma preContrCoUnitVal_expand_tmul {d : ℕ} : preContrCoUnitVal d =
    ∑ i, contrBasis d i ⊗ₜ[ℝ] coBasis d i := by
  simp only [preContrCoUnitVal]
  rw [contrCoToMatrixRe_symm_expand_tmul]
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton, ne_eq, reduceCtorEq, not_false_eq_true, one_apply_ne, zero_smul,
    Finset.sum_const_zero, add_zero, one_apply_eq, one_smul, zero_add]
  congr
  funext x
  rw [Finset.sum_eq_single x]
  · simp
  · simp only [Finset.mem_univ, ne_eq, smul_eq_zero, forall_const]
    intro b hb
    left
    refine one_apply_ne' ?_
    simp [hb]
  · simp

/-- The contra-co unit for complex lorentz vectors as a morphism
  `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ complexContr ⊗ complexCo`, manifesting the invariance under
  the `SL(2, ℂ)` action. -/
def preContrCoUnit (d : ℕ := 3) :
  (Representation.trivial ℝ (LorentzGroup d) ℝ).IntertwiningMap
    ((ContrMod.rep).tprod (CoMod.rep)) where
  toFun := fun a => a • preContrCoUnitVal d
  map_add' := fun x y => by
    simp only [add_smul]
  map_smul' := fun m x => by
    simp only [smul_smul]
    rfl
  isIntertwining' M := by
    refine LinearMap.ext fun x : ℝ => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply]
    change x • preContrCoUnitVal d =
      (TensorProduct.map (ContrMod.rep M) (CoMod.rep M)) (x • preContrCoUnitVal d)
    simp only [map_smul]
    apply congrArg
    simp only [preContrCoUnitVal]
    rw [contrCoToMatrixRe_ρ_symm]
    apply congrArg
    simp

lemma preContrCoUnit_apply_one {d : ℕ} : (preContrCoUnit d) (1 : ℝ) = preContrCoUnitVal d := by
  change (1 : ℝ) • preContrCoUnitVal d = preContrCoUnitVal d
  rw [one_smul]

/-- The co-contra unit for complex lorentz vectors. Usually denoted `δᵢⁱ`. -/
def preCoContrUnitVal (d : ℕ := 3) : CoMod d ⊗[ℝ] ContrMod d :=
  coContrToMatrixRe.symm 1

/-- Expansion of `preCoContrUnitVal` into basis. -/
lemma preCoContrUnitVal_expand_tmul {d : ℕ} : preCoContrUnitVal d =
    ∑ i, coBasis d i ⊗ₜ[ℝ] contrBasis d i := by
  simp only [preCoContrUnitVal]
  rw [coContrToMatrixRe_symm_expand_tmul]
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton, ne_eq, reduceCtorEq, not_false_eq_true, one_apply_ne, zero_smul,
    Finset.sum_const_zero, add_zero, one_apply_eq, one_smul, zero_add]
  congr
  funext x
  rw [Finset.sum_eq_single x]
  · simp
  · simp only [Finset.mem_univ, ne_eq, smul_eq_zero, forall_const]
    intro b hb
    left
    refine one_apply_ne' ?_
    simp [hb]
  · simp

/-- The co-contra unit for complex lorentz vectors as a morphism
  `𝟙_ (Rep ℝ (LorentzGroup d)) ⟶ CoMod.rep ⊗ ContrMod.rep`, manifesting the invariance under
  the `LorentzGroup d` action. -/
def preCoContrUnit (d : ℕ) : (Representation.trivial ℝ (LorentzGroup d) ℝ).IntertwiningMap
    ((CoMod.rep).tprod (ContrMod.rep)) where
  toFun := fun a => a • preCoContrUnitVal d
  map_add' := fun x y => by
    simp only [add_smul]
  map_smul' := fun m x => by
    simp only [smul_smul]
    rfl
  isIntertwining' M := by
    refine LinearMap.ext fun x : ℝ => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply]
    change x • preCoContrUnitVal d =
      (TensorProduct.map (CoMod.rep M) (ContrMod.rep M)) (x • preCoContrUnitVal d)
    simp only [map_smul]
    apply congrArg
    simp only [preCoContrUnitVal]
    rw [coContrToMatrixRe_ρ_symm]
    apply congrArg
    symm
    refine transpose_eq_one.mp ?h.h.h.a
    simp

lemma preCoContrUnit_apply_one {d : ℕ} : (preCoContrUnit d) (1 : ℝ) = preCoContrUnitVal d := by
  change (1 : ℝ) • preCoContrUnitVal d = preCoContrUnitVal d
  rw [one_smul]

/-!

## Contraction of the units

-/

/-- Contraction on the right with `contrCoUnit` does nothing. -/
lemma contr_preContrCoUnit {d : ℕ} (x : CoMod d) :
    (TensorProduct.lid ℝ _ <|
    coContrContract.toLinearMap.rTensor _ <|
    (TensorProduct.assoc ℝ (CoMod d) (ContrMod d) (CoMod d)).symm <|
    x ⊗ₜ[ℝ] (preContrCoUnit d (1 : ℝ))) = x := by
  have h1 : (TensorProduct.assoc ℝ (CoMod d) (ContrMod d) (CoMod d)).symm
      (x ⊗ₜ[ℝ] (preContrCoUnit d) (1 : ℝ))
      = ∑ i, (x ⊗ₜ[ℝ] contrBasis d i) ⊗ₜ[ℝ] coBasis d i := by
    rw [preContrCoUnit_apply_one, preContrCoUnitVal_expand_tmul]
    simp only [tmul_sum]
    simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
      Finset.sum_singleton, map_add, map_sum]
    rfl
  rw [h1]
  have h2 : coContrContract.toLinearMap.rTensor _ (∑ i, (x ⊗ₜ[ℝ] contrBasis d i) ⊗ₜ[ℝ] coBasis d i)
      = ∑ i, ((coContrContract) (x ⊗ₜ[ℝ] contrBasis d i)) ⊗ₜ[ℝ] coBasis d i := by
    rw [map_sum]
    rfl
  rw [h2]
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp (Basis.mem_span (coBasis d) x)
  have h3 (i : Fin 1 ⊕ Fin d) : (coContrContract)
        ((∑ i : Fin 1 ⊕ Fin d, c i • (coBasis d) i) ⊗ₜ[ℝ] (contrBasis d) i) = c i := by
      simp only [sum_tmul, smul_tmul, tmul_smul, map_sum, _root_.map_smul, smul_eq_mul]
      conv_lhs =>
        enter [2, x]
        rw [coContrContract_basis]
      simp
  conv_lhs =>
    enter [2, 2, i]
    rw [h3 i]
  rw [map_sum]
  rfl

/-- Contraction on the right with `coContrUnit`. -/
lemma contr_preCoContrUnit {d : ℕ} (x : ContrMod d) :
    (TensorProduct.lid ℝ _ <|
    contrCoContract.toLinearMap.rTensor _ <|
    (TensorProduct.assoc ℝ (ContrMod d) (CoMod d) (ContrMod d)).symm <|
    x ⊗ₜ[ℝ] (preCoContrUnit d (1 : ℝ))) = x := by
  have h1 : ((TensorProduct.assoc ℝ (ContrMod d) (CoMod d) (ContrMod d)).symm
      (x ⊗ₜ[ℝ] (preCoContrUnit d) (1 : ℝ)))
      = ∑ i, (x ⊗ₜ[ℝ] coBasis d i) ⊗ₜ[ℝ] contrBasis d i := by
    rw [preCoContrUnit_apply_one, preCoContrUnitVal_expand_tmul]
    simp only [tmul_sum]
    simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
      Finset.sum_singleton, map_add, map_sum]
    rfl
  rw [h1]
  have h2 :contrCoContract.toLinearMap.rTensor _ (∑ i, (x ⊗ₜ[ℝ] coBasis d i) ⊗ₜ[ℝ] contrBasis d i)
      = ∑ i, ((contrCoContract) (x ⊗ₜ[ℝ] coBasis d i)) ⊗ₜ[ℝ] contrBasis d i := by
    rw [map_sum]
    rfl
  rw [h2]
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp
    (Basis.mem_span (contrBasis d) x)
  have h3 (i : Fin 1 ⊕ Fin d) : (contrCoContract)
        ((∑ i : Fin 1 ⊕ Fin d, c i • (contrBasis d) i) ⊗ₜ[ℝ] (coBasis d) i) = c i := by
      simp only [sum_tmul, smul_tmul, tmul_smul, map_sum, map_smul, smul_eq_mul]
      conv_lhs =>
        enter [2, x]
        rw [contrCoContract_basis]
      simp
  conv_lhs =>
    enter [2, 2, i]
    rw [h3 i]
  rw [map_sum]
  rfl

/-!

## Symmetry properties of the units

-/

lemma preContrCoUnit_symm {d : ℕ} :
    (preContrCoUnit d) (1 : ℝ) = LinearMap.lTensor _ (LinearEquiv.cast (by rfl)).toLinearMap
      (TensorProduct.comm ℝ _ _ ((preCoContrUnit d) (1 : ℝ))) := by
  rw [preContrCoUnit_apply_one, preContrCoUnitVal_expand_tmul]
  rw [preCoContrUnit_apply_one, preCoContrUnitVal_expand_tmul]
  simp

lemma preCoContrUnit_symm {d : ℕ} :
    (preCoContrUnit d) (1 : ℝ) = LinearMap.lTensor _ (LinearEquiv.cast (by simp)).toLinearMap
    (TensorProduct.comm ℝ _ _ ((preContrCoUnit d) (1 : ℝ))) := by
  rw [preContrCoUnit_apply_one, preContrCoUnitVal_expand_tmul]
  rw [preCoContrUnit_apply_one, preCoContrUnitVal_expand_tmul]
  simp

end Lorentz
end
