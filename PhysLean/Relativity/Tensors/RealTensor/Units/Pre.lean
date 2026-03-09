/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Relativity.Tensors.RealTensor.Matrix.Pre
public import PhysLean.Relativity.Tensors.RealTensor.Vector.Pre.Contraction
/-!

# Unit for complex Lorentz vectors

-/

@[expose] public section
noncomputable section

open Module Matrix MatrixGroups Complex TensorProduct CategoryTheory.MonoidalCategory
namespace Lorentz

/-- The contra-co unit for complex lorentz vectors. Usually denoted `δⁱᵢ`. -/
def preContrCoUnitVal (d : ℕ := 3) : (Contr d ⊗ Co d).V :=
  contrCoToMatrixRe.symm 1

/-- Expansion of `preContrCoUnitVal` into basis. -/
lemma preContrCoUnitVal_expand_tmul {d : ℕ} : preContrCoUnitVal d =
    ∑ i, contrBasis d i ⊗ₜ[ℝ] coBasis d i := by
  simp only [preContrCoUnitVal]
  rw [contrCoToMatrixRe_symm_expand_tmul]
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton, ne_eq, reduceCtorEq, not_false_eq_true, one_apply_ne, zero_smul,
    Finset.sum_const_zero, add_zero, one_apply_eq, one_smul, zero_add, add_right_inj]
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
def preContrCoUnit (d : ℕ := 3) : 𝟙_ (Rep ℝ (LorentzGroup d)) ⟶ Contr d ⊗ Co d where
  hom := ModuleCat.ofHom {
    toFun := fun a => a • preContrCoUnitVal d,
    map_add' := fun x y => by
      simp only [add_smul],
    map_smul' := fun m x => by
      simp only [smul_smul]
      rfl}
  comm M := by
    refine ModuleCat.hom_ext ?_
    refine LinearMap.ext fun x : ℝ => ?_
    simp only [Action.tensorObj_V, Action.tensorUnit_V, Action.tensorUnit_ρ,
      CategoryTheory.Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
      Action.FunctorCategoryEquivalence.functor_obj_obj, CategoryTheory.Category.id_comp,
      ModuleCat.hom_ofHom, Action.tensor_ρ, ModuleCat.hom_comp, LinearMap.coe_comp,
      Function.comp_apply]
    change x • preContrCoUnitVal d =
      (TensorProduct.map ((Contr d).ρ M) ((Co d).ρ M)) (x • preContrCoUnitVal d)
    simp only [Action.tensorObj_V, map_smul]
    apply congrArg
    simp only [preContrCoUnitVal]
    rw [contrCoToMatrixRe_ρ_symm]
    apply congrArg
    simp

lemma preContrCoUnit_apply_one {d : ℕ} : (preContrCoUnit d).hom (1 : ℝ) = preContrCoUnitVal d := by
  change (1 : ℝ) • preContrCoUnitVal d = preContrCoUnitVal d
  rw [one_smul]

/-- The co-contra unit for complex lorentz vectors. Usually denoted `δᵢⁱ`. -/
def preCoContrUnitVal (d : ℕ := 3) : (Co d ⊗ Contr d).V :=
  coContrToMatrixRe.symm 1

/-- Expansion of `preCoContrUnitVal` into basis. -/
lemma preCoContrUnitVal_expand_tmul {d : ℕ} : preCoContrUnitVal d =
    ∑ i, coBasis d i ⊗ₜ[ℝ] contrBasis d i := by
  simp only [preCoContrUnitVal]
  rw [coContrToMatrixRe_symm_expand_tmul]
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton, ne_eq, reduceCtorEq, not_false_eq_true, one_apply_ne, zero_smul,
    Finset.sum_const_zero, add_zero, one_apply_eq, one_smul, zero_add, add_right_inj]
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
  `𝟙_ (Rep ℝ (LorentzGroup d)) ⟶ Co d ⊗ Contr d`, manifesting the invariance under
  the `LorentzGroup d` action. -/
def preCoContrUnit (d : ℕ) : 𝟙_ (Rep ℝ (LorentzGroup d)) ⟶ Co d ⊗ Contr d where
  hom := ModuleCat.ofHom {
    toFun := fun a => a • preCoContrUnitVal d,
    map_add' := fun x y => by
      simp only [add_smul],
    map_smul' := fun m x => by
      simp only [smul_smul]
      rfl}
  comm M := by
    refine ModuleCat.hom_ext ?_
    refine LinearMap.ext fun x : ℝ => ?_
    simp only [Action.tensorObj_V, Action.tensorUnit_V, Action.tensorUnit_ρ,
      CategoryTheory.Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
      Action.FunctorCategoryEquivalence.functor_obj_obj, CategoryTheory.Category.id_comp,
      ModuleCat.hom_ofHom, Action.tensor_ρ, ModuleCat.hom_comp, LinearMap.coe_comp,
      Function.comp_apply]
    change x • preCoContrUnitVal d =
      (TensorProduct.map ((Co d).ρ M) ((Contr d).ρ M)) (x • preCoContrUnitVal d)
    simp only [Action.tensorObj_V, map_smul]
    apply congrArg
    simp only [preCoContrUnitVal]
    rw [coContrToMatrixRe_ρ_symm]
    apply congrArg
    symm
    refine transpose_eq_one.mp ?h.h.h.a
    simp

lemma preCoContrUnit_apply_one {d : ℕ} : (preCoContrUnit d).hom (1 : ℝ) = preCoContrUnitVal d := by
  change (1 : ℝ) • preCoContrUnitVal d = preCoContrUnitVal d
  rw [one_smul]

/-!

## Contraction of the units

-/

/-- Contraction on the right with `contrCoUnit` does nothing. -/
lemma contr_preContrCoUnit {d : ℕ} (x : Co d) :
    (λ_ (Co d)).hom.hom ((coContrContract ▷ (Co d)).hom
    ((α_ _ _ (Co d)).inv.hom (x ⊗ₜ[ℝ] (preContrCoUnit d).hom (1 : ℝ)))) = x := by
  have h1 : ((α_ (Co d) _ (Co d)).inv.hom (x ⊗ₜ[ℝ] (preContrCoUnit d).hom (1 : ℝ)))
      = ∑ i, (x ⊗ₜ[ℝ] contrBasis d i) ⊗ₜ[ℝ] coBasis d i := by
    rw [preContrCoUnit_apply_one, preContrCoUnitVal_expand_tmul]
    simp [tmul_sum, - Fintype.sum_sum_type]
  rw [h1]
  have h2 : (coContrContract ▷ (Co d)).hom (∑ i, (x ⊗ₜ[ℝ] contrBasis d i) ⊗ₜ[ℝ] coBasis d i)
      = ∑ i, ((coContrContract).hom (x ⊗ₜ[ℝ] contrBasis d i)) ⊗ₜ[ℝ] coBasis d i := by
    simp
  rw [h2]
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp (Basis.mem_span (coBasis d) x)
  have h3 (i : Fin 1 ⊕ Fin d) : (CategoryTheory.ConcreteCategory.hom coContrContract.hom)
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
lemma contr_preCoContrUnit {d : ℕ} (x : (Contr d)) :
    (λ_ (Contr d)).hom.hom ((contrCoContract ▷ (Contr d)).hom
    ((α_ _ _ (Contr d)).inv.hom (x ⊗ₜ[ℝ] (preCoContrUnit d).hom (1 : ℝ)))) = x := by
  have h1 : ((α_ (Contr d) _ (Contr d)).inv.hom (x ⊗ₜ[ℝ] (preCoContrUnit d).hom (1 : ℝ)))
      = ∑ i, (x ⊗ₜ[ℝ] coBasis d i) ⊗ₜ[ℝ] contrBasis d i := by
    rw [preCoContrUnit_apply_one, preCoContrUnitVal_expand_tmul]
    simp [tmul_sum, - Fintype.sum_sum_type]
  rw [h1]
  have h2 : (contrCoContract ▷ (Contr d)).hom (∑ i, (x ⊗ₜ[ℝ] coBasis d i) ⊗ₜ[ℝ] contrBasis d i)
      = ∑ i, ((contrCoContract).hom (x ⊗ₜ[ℝ] coBasis d i)) ⊗ₜ[ℝ] contrBasis d i := by
    simp
  rw [h2]
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp
    (Basis.mem_span (contrBasis d) x)
  have h3 (i : Fin 1 ⊕ Fin d) : (CategoryTheory.ConcreteCategory.hom contrCoContract.hom)
        ((∑ i : Fin 1 ⊕ Fin d, c i • (contrBasis d) i) ⊗ₜ[ℝ] (coBasis d) i) = c i := by
      simp only [sum_tmul, smul_tmul, tmul_smul, map_sum, _root_.map_smul, smul_eq_mul]
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

open CategoryTheory

lemma preContrCoUnit_symm {d : ℕ} :
    ((preContrCoUnit d).hom (1 : ℝ)) = ((Contr d) ◁ 𝟙 _).hom ((β_ (Co d) (Contr d)).hom.hom
    ((preCoContrUnit d).hom (1 : ℝ))) := by
  rw [preContrCoUnit_apply_one, preContrCoUnitVal_expand_tmul]
  rw [preCoContrUnit_apply_one, preCoContrUnitVal_expand_tmul]
  simp

lemma preCoContrUnit_symm {d : ℕ} :
    ((preCoContrUnit d).hom (1 : ℝ)) = ((Co d) ◁ 𝟙 _).hom ((β_ (Contr d) (Co d)).hom.hom
    ((preContrCoUnit d).hom (1 : ℝ))) := by
  rw [preContrCoUnit_apply_one, preContrCoUnitVal_expand_tmul]
  rw [preCoContrUnit_apply_one, preCoContrUnitVal_expand_tmul]
  simp

end Lorentz
end
