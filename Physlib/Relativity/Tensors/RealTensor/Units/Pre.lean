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
def CoMod.unitVal (d : ℕ := 3) : ContrMod d ⊗[ℝ] CoMod d :=
  contrCoToMatrixRe.symm 1

/-- Expansion of `CoMod.unitVal` into basis. -/
lemma CoMod.unitVal_expand_tmul {d : ℕ} : CoMod.unitVal d =
    ∑ i, contrBasis d i ⊗ₜ[ℝ] coBasis d i := by
  simp only [CoMod.unitVal]
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
def CoMod.unit (d : ℕ := 3) :
  (Representation.trivial ℝ (LorentzGroup d) ℝ).IntertwiningMap
    ((ContrMod.rep).tprod (CoMod.rep)) where
  toFun := fun a => a • CoMod.unitVal d
  map_add' := fun x y => by
    simp only [add_smul]
  map_smul' := fun m x => by
    simp only [smul_smul]
    rfl
  isIntertwining' M := by
    refine LinearMap.ext fun x : ℝ => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply]
    change x • CoMod.unitVal d =
      (TensorProduct.map (ContrMod.rep M) (CoMod.rep M)) (x • CoMod.unitVal d)
    simp only [map_smul]
    apply congrArg
    simp only [CoMod.unitVal]
    rw [contrCoToMatrixRe_ρ_symm]
    apply congrArg
    simp

lemma CoMod.unit_apply_one {d : ℕ} : (CoMod.unit d) (1 : ℝ) = CoMod.unitVal d := by
  change (1 : ℝ) • CoMod.unitVal d = CoMod.unitVal d
  rw [one_smul]

/-- The co-contra unit for complex lorentz vectors. Usually denoted `δᵢⁱ`. -/
def ContrMod.unitVal (d : ℕ := 3) : CoMod d ⊗[ℝ] ContrMod d :=
  coContrToMatrixRe.symm 1

/-- Expansion of `ContrMod.unitVal` into basis. -/
lemma ContrMod.unitVal_expand_tmul {d : ℕ} : ContrMod.unitVal d =
    ∑ i, coBasis d i ⊗ₜ[ℝ] contrBasis d i := by
  simp only [ContrMod.unitVal]
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
def ContrMod.unit (d : ℕ) : (Representation.trivial ℝ (LorentzGroup d) ℝ).IntertwiningMap
    ((CoMod.rep).tprod (ContrMod.rep)) where
  toFun := fun a => a • ContrMod.unitVal d
  map_add' := fun x y => by
    simp only [add_smul]
  map_smul' := fun m x => by
    simp only [smul_smul]
    rfl
  isIntertwining' M := by
    refine LinearMap.ext fun x : ℝ => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply]
    change x • ContrMod.unitVal d =
      (TensorProduct.map (CoMod.rep M) (ContrMod.rep M)) (x • ContrMod.unitVal d)
    simp only [map_smul]
    apply congrArg
    simp only [ContrMod.unitVal]
    rw [coContrToMatrixRe_ρ_symm]
    apply congrArg
    symm
    refine transpose_eq_one.mp ?h.h.h.a
    simp

lemma ContrMod.unit_apply_one {d : ℕ} : (ContrMod.unit d) (1 : ℝ) = ContrMod.unitVal d := by
  change (1 : ℝ) • ContrMod.unitVal d = ContrMod.unitVal d
  rw [one_smul]

/-!

## Contraction of the units

-/

/-- Contraction on the right with `CoMod.unit` does nothing. -/
lemma CoMod.contr_unit {d : ℕ} (x : CoMod d) :
    (TensorProduct.lid ℝ _ <|
    CoMod.contr.toLinearMap.rTensor _ <|
    (TensorProduct.assoc ℝ (CoMod d) (ContrMod d) (CoMod d)).symm <|
    x ⊗ₜ[ℝ] (CoMod.unit d (1 : ℝ))) = x := by
  have h1 : (TensorProduct.assoc ℝ (CoMod d) (ContrMod d) (CoMod d)).symm
      (x ⊗ₜ[ℝ] (CoMod.unit d) (1 : ℝ))
      = ∑ i, (x ⊗ₜ[ℝ] contrBasis d i) ⊗ₜ[ℝ] coBasis d i := by
    rw [CoMod.unit_apply_one, CoMod.unitVal_expand_tmul]
    simp only [tmul_sum]
    simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
      Finset.sum_singleton, map_add, map_sum]
    rfl
  rw [h1]
  have h2 : CoMod.contr.toLinearMap.rTensor _ (∑ i, (x ⊗ₜ[ℝ] contrBasis d i) ⊗ₜ[ℝ] coBasis d i)
      = ∑ i, ((CoMod.contr) (x ⊗ₜ[ℝ] contrBasis d i)) ⊗ₜ[ℝ] coBasis d i := by
    rw [map_sum]
    rfl
  rw [h2]
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp (Basis.mem_span (coBasis d) x)
  have h3 (i : Fin 1 ⊕ Fin d) : (CoMod.contr)
        ((∑ i : Fin 1 ⊕ Fin d, c i • (coBasis d) i) ⊗ₜ[ℝ] (contrBasis d) i) = c i := by
      simp only [sum_tmul, smul_tmul, tmul_smul, map_sum, _root_.map_smul, smul_eq_mul]
      conv_lhs =>
        enter [2, x]
        rw [CoMod.contr_basis]
      simp
  conv_lhs =>
    enter [2, 2, i]
    rw [h3 i]
  rw [map_sum]
  rfl

/-- Contraction on the right with `ContrMod.unit` does nothing. -/
lemma ContrMod.contr_unit {d : ℕ} (x : ContrMod d) :
    (TensorProduct.lid ℝ _ <|
    ContrMod.contr.toLinearMap.rTensor _ <|
    (TensorProduct.assoc ℝ (ContrMod d) (CoMod d) (ContrMod d)).symm <|
    x ⊗ₜ[ℝ] (ContrMod.unit d (1 : ℝ))) = x := by
  have h1 : ((TensorProduct.assoc ℝ (ContrMod d) (CoMod d) (ContrMod d)).symm
      (x ⊗ₜ[ℝ] (ContrMod.unit d) (1 : ℝ)))
      = ∑ i, (x ⊗ₜ[ℝ] coBasis d i) ⊗ₜ[ℝ] contrBasis d i := by
    rw [ContrMod.unit_apply_one, ContrMod.unitVal_expand_tmul]
    simp only [tmul_sum]
    simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
      Finset.sum_singleton, map_add, map_sum]
    rfl
  rw [h1]
  have h2 :ContrMod.contr.toLinearMap.rTensor _ (∑ i, (x ⊗ₜ[ℝ] coBasis d i) ⊗ₜ[ℝ] contrBasis d i)
      = ∑ i, ((ContrMod.contr) (x ⊗ₜ[ℝ] coBasis d i)) ⊗ₜ[ℝ] contrBasis d i := by
    rw [map_sum]
    rfl
  rw [h2]
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp
    (Basis.mem_span (contrBasis d) x)
  have h3 (i : Fin 1 ⊕ Fin d) : (ContrMod.contr)
        ((∑ i : Fin 1 ⊕ Fin d, c i • (contrBasis d) i) ⊗ₜ[ℝ] (coBasis d) i) = c i := by
      simp only [sum_tmul, smul_tmul, tmul_smul, map_sum, map_smul, smul_eq_mul]
      conv_lhs =>
        enter [2, x]
        rw [ContrMod.contr_basis]
      simp
  conv_lhs =>
    enter [2, 2, i]
    rw [h3 i]
  rw [map_sum]
  rfl

/-!

## Symmetry properties of the units

-/

lemma CoMod.unit_symm {d : ℕ} :
    (CoMod.unit d) (1 : ℝ) = LinearMap.lTensor _ (LinearEquiv.cast (by rfl)).toLinearMap
      (TensorProduct.comm ℝ _ _ ((ContrMod.unit d) (1 : ℝ))) := by
  rw [CoMod.unit_apply_one, CoMod.unitVal_expand_tmul]
  rw [ContrMod.unit_apply_one, ContrMod.unitVal_expand_tmul]
  simp

lemma ContrMod.unit_symm {d : ℕ} :
    (ContrMod.unit d) (1 : ℝ) = LinearMap.lTensor _ (LinearEquiv.cast (by simp)).toLinearMap
    (TensorProduct.comm ℝ _ _ ((CoMod.unit d) (1 : ℝ))) := by
  rw [CoMod.unit_apply_one, CoMod.unitVal_expand_tmul]
  rw [ContrMod.unit_apply_one, ContrMod.unitVal_expand_tmul]
  simp

end Lorentz
end
