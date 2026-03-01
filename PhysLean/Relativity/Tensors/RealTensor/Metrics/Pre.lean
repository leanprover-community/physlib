/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.RealTensor.Units.Pre
/-!

# Metric for real Lorentz vectors

-/
noncomputable section

open Module Matrix MatrixGroups Complex TensorProduct CategoryTheory.MonoidalCategory
namespace Lorentz

/-- The metric `ηᵃᵃ` as an element of `(Contr d ⊗ Contr d).V`. -/
def preContrMetricVal (d : ℕ := 3) : (Contr d ⊗ Contr d).V :=
  contrContrToMatrixRe.symm ((@minkowskiMatrix d))

/-- Expansion of `preContrMetricVal` into basis. -/
lemma preContrMetricVal_expand_tmul {d : ℕ} : preContrMetricVal d =
    contrBasis d (Sum.inl 0) ⊗ₜ[ℝ] contrBasis d (Sum.inl 0) -
    ∑ i, contrBasis d (Sum.inr i) ⊗ₜ[ℝ] contrBasis d (Sum.inr i) := by
  simp only [preContrMetricVal, Fin.isValue]
  rw [contrContrToMatrixRe_symm_expand_tmul]
  simp only [Action.tensorObj_V, Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero,
    Fin.isValue, Finset.sum_singleton, ne_eq, reduceCtorEq, not_false_eq_true,
    minkowskiMatrix.off_diag_zero, zero_smul, Finset.sum_const_zero, add_zero,
    minkowskiMatrix.inl_0_inl_0, one_smul, zero_add]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr
  funext x
  rw [Finset.sum_eq_single x]
  · simp [minkowskiMatrix.inr_i_inr_i]
  · simp only [Finset.mem_univ, ne_eq, smul_eq_zero, forall_const]
    intro b hb
    left
    refine minkowskiMatrix.off_diag_zero ?_
    simp only [ne_eq, Sum.inr.injEq]
    exact fun a => hb (id (Eq.symm a))
  · simp

lemma preContrMetricVal_expand_tmul_minkowskiMatrix {d : ℕ} : preContrMetricVal d =
    ∑ i, (minkowskiMatrix i i) • (contrBasis d i ⊗ₜ[ℝ] contrBasis d i) := by
  rw [preContrMetricVal_expand_tmul]
  simp only [Action.tensorObj_V, Fin.isValue, Fintype.sum_sum_type, Finset.univ_unique,
    Fin.default_eq_zero, Finset.sum_singleton, minkowskiMatrix.inl_0_inl_0, one_smul,
    minkowskiMatrix.inr_i_inr_i, neg_smul, Finset.sum_neg_distrib]
  abel

/-- The metric `ηᵃᵃ` as a morphism `𝟙_ (Rep ℝ (LorentzGroup d)) ⟶ Contr d ⊗ Contr d`,
  making its invariance under the action of `LorentzGroup d`. -/
def preContrMetric (d : ℕ := 3) : 𝟙_ (Rep ℝ (LorentzGroup d)) ⟶ Contr d ⊗ Contr d where
  hom := ModuleCat.ofHom {
    toFun := fun a => a • (preContrMetricVal d),
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
    change x • (preContrMetricVal d) =
      (TensorProduct.map ((Contr d).ρ M) ((Contr d).ρ M)) (x • (preContrMetricVal d))
    simp only [Action.tensorObj_V, map_smul]
    apply congrArg
    simp only [preContrMetricVal]
    conv_rhs =>
      rw [contrContrToMatrixRe_ρ_symm]
    apply congrArg
    simp

lemma preContrMetric_apply_one {d : ℕ} : (preContrMetric d).hom (1 : ℝ) = preContrMetricVal d:= by
  change (1 : ℝ) • preContrMetricVal d = preContrMetricVal d
  rw [one_smul]

/-- The metric `ηᵢᵢ` as an element of `(Co d ⊗ Co d).V`. -/
def preCoMetricVal (d : ℕ := 3) : (Co d ⊗ Co d).V :=
  coCoToMatrixRe.symm ((@minkowskiMatrix d))

/-- Expansion of `preContrMetricVal` into basis. -/
lemma preCoMetricVal_expand_tmul {d : ℕ} : preCoMetricVal d =
    coBasis d (Sum.inl 0) ⊗ₜ[ℝ] coBasis d (Sum.inl 0) -
    ∑ i, coBasis d (Sum.inr i) ⊗ₜ[ℝ] coBasis d (Sum.inr i) := by
  simp only [preCoMetricVal, Fin.isValue]
  rw [coCoToMatrixRe_symm_expand_tmul]
  simp [minkowskiMatrix.inl_0_inl_0]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr
  funext x
  rw [Finset.sum_eq_single x]
  · simp [minkowskiMatrix.inr_i_inr_i]
  · simp only [Finset.mem_univ, ne_eq, smul_eq_zero, forall_const]
    intro b hb
    left
    refine minkowskiMatrix.off_diag_zero ?_
    simp only [ne_eq, Sum.inr.injEq]
    exact fun a => hb (id (Eq.symm a))
  · simp

lemma preCoMetricVal_expand_tmul_minkowskiMatrix {d : ℕ} : preCoMetricVal d =
    ∑ i, (minkowskiMatrix i i) • (coBasis d i ⊗ₜ[ℝ] coBasis d i) := by
  rw [preCoMetricVal_expand_tmul]
  simp only [Action.tensorObj_V, Fin.isValue, Fintype.sum_sum_type, Finset.univ_unique,
    Fin.default_eq_zero, Finset.sum_singleton, minkowskiMatrix.inl_0_inl_0, one_smul,
    minkowskiMatrix.inr_i_inr_i, neg_smul, Finset.sum_neg_distrib]
  abel

/-- The metric `ηᵢᵢ` as a morphism `𝟙_ (Rep ℂ (LorentzGroup d))) ⟶ Co d ⊗ Co d`,
  making its invariance under the action of `LorentzGroup d`. -/
def preCoMetric (d : ℕ := 3) : 𝟙_ (Rep ℝ (LorentzGroup d)) ⟶ Co d ⊗ Co d where
  hom := ModuleCat.ofHom {
    toFun := fun a => a • preCoMetricVal d,
    map_add' := fun x y => by
      simp only [add_smul],
    map_smul' := fun m x => by
      simp only [smul_smul]
      rfl}
  comm M := by
    refine ModuleCat.hom_ext ?_
    refine LinearMap.ext fun x : ℝ => ?_
    simp only [CategoryTheory.Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
      Action.FunctorCategoryEquivalence.functor_obj_obj, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
      LinearMap.coe_comp, Function.comp_apply]
    change x • preCoMetricVal d =
      (TensorProduct.map ((Co d).ρ M) ((Co d).ρ M)) (x • preCoMetricVal d)
    simp only [_root_.map_smul]
    apply congrArg
    simp only [preCoMetricVal]
    rw [coCoToMatrixRe_ρ_symm]
    apply congrArg
    rw [← LorentzGroup.coe_inv, LorentzGroup.transpose_mul_minkowskiMatrix_mul_self]

lemma preCoMetric_apply_one {d : ℕ} : (preCoMetric d).hom (1 : ℝ) = preCoMetricVal d := by
  change (1 : ℝ) • preCoMetricVal d = preCoMetricVal d
  rw [one_smul]

/-!

## Contraction of metrics

-/

lemma contrCoContract_apply_metric {d : ℕ} : (β_ (Contr d) (Co d)).hom.hom
    (((Contr d).V ◁ (λ_ (Co d).V).hom)
    (((Contr d).V ◁ contrCoContract.hom ▷ (Co d).V)
    (((Contr d).V ◁ (α_ (Contr d).V (Co d).V (Co d).V).inv)
    ((α_ (Contr d).V (Contr d).V ((Co d).V ⊗ (Co d).V)).hom
    ((preContrMetric d).hom (1 : ℝ) ⊗ₜ[ℝ] (preCoMetric d).hom (1 : ℝ)))))) =
    (preCoContrUnit d).hom (1 : ℝ) := by
  have h1 : ((preContrMetric d).hom (1 : ℝ) ⊗ₜ[ℝ] (preCoMetric d).hom (1 : ℝ)) =
      ∑ i, ∑ j, ((minkowskiMatrix i i * minkowskiMatrix j j) •
        ((contrBasis d i ⊗ₜ[ℝ] contrBasis d i) ⊗ₜ[ℝ] (coBasis d j ⊗ₜ[ℝ] coBasis d j))) := by
    rw [preContrMetric_apply_one, preCoMetric_apply_one,
      preContrMetricVal_expand_tmul_minkowskiMatrix, preCoMetricVal_expand_tmul_minkowskiMatrix]
    simp [tmul_sum, sum_tmul, - Fintype.sum_sum_type, Finset.smul_sum]
    rw [Finset.sum_comm]
    congr 1
    funext x
    congr 1
    funext y
    simp [smul_tmul, smul_smul]
    rw [mul_comm]
  rw [h1]
  have h2 : (α_ (Contr d).V (Contr d).V ((Co d).V ⊗ (Co d).V)).hom
      (∑ i, ∑ j, (minkowskiMatrix i i * minkowskiMatrix j j) •
      (contrBasis d i ⊗ₜ[ℝ] contrBasis d i) ⊗ₜ[ℝ] (coBasis d j ⊗ₜ[ℝ] coBasis d j)) =
      ∑ i, ∑ j, (minkowskiMatrix i i * minkowskiMatrix j j) •
      (contrBasis d i ⊗ₜ[ℝ] (contrBasis d i ⊗ₜ[ℝ] (coBasis d j ⊗ₜ[ℝ] coBasis d j))) := by
    simp [map_sum, - Fintype.sum_sum_type]
    rfl
  rw [h2]
  have h3 : ((Contr d).V ◁ (α_ (Contr d).V (Co d).V (Co d).V).inv)
      (∑ i, ∑ j, (minkowskiMatrix i i * minkowskiMatrix j j) •
      (contrBasis d i ⊗ₜ[ℝ] (contrBasis d i ⊗ₜ[ℝ] (coBasis d j ⊗ₜ[ℝ] coBasis d j)))) =
      ∑ i, ∑ j, (minkowskiMatrix i i * minkowskiMatrix j j) •
      (contrBasis d i ⊗ₜ[ℝ] ((contrBasis d i ⊗ₜ[ℝ] coBasis d j) ⊗ₜ[ℝ] coBasis d j)) := by
    simp [- Fintype.sum_sum_type]
    rfl
  rw [h3]
  have h4 : ((Contr d).V ◁ contrCoContract.hom ▷ (Co d).V)
      (∑ i, ∑ j, (minkowskiMatrix i i * minkowskiMatrix j j) •
      (contrBasis d i ⊗ₜ[ℝ] ((contrBasis d i ⊗ₜ[ℝ] coBasis d j) ⊗ₜ[ℝ] coBasis d j))) =
      ∑ i, ∑ j, (minkowskiMatrix i i * minkowskiMatrix j j) •
      (contrBasis d i ⊗ₜ[ℝ]
      (contrCoContract.hom (contrBasis d i ⊗ₜ[ℝ] coBasis d j) ⊗ₜ[ℝ] coBasis d j)) := by
    simp [- Fintype.sum_sum_type]
    rfl
  rw [h4]
  have h5 : ∑ i, ∑ j, (minkowskiMatrix i i * minkowskiMatrix j j) •
      (contrBasis d i ⊗ₜ[ℝ]
      (contrCoContract.hom (contrBasis d i ⊗ₜ[ℝ] coBasis d j) ⊗ₜ[ℝ] coBasis d j))
      = ∑ i, contrBasis d i ⊗ₜ[ℝ] ((1 : ℝ) ⊗ₜ[ℝ] coBasis d i) := by
    congr
    funext x
    rw [Finset.sum_eq_single x]
    · simp only [minkowskiMatrix.η_apply_mul_η_apply_diag, one_smul]
      rw [contrCoContract_basis]
      simp
    · intro b _ hb
      rw [contrCoContract_basis]
      rw [if_neg]
      · simp
      · exact id (Ne.symm hb)
    · simp
  rw [h5]
  have h6 : ((Contr d).V ◁ (λ_ (Co d).V).hom)
      (∑ i, contrBasis d i ⊗ₜ[ℝ] ((1 : ℝ) ⊗ₜ[ℝ] coBasis d i)) =
      ∑ i, contrBasis d i ⊗ₜ[ℝ] coBasis d i := by
    simp [- Fintype.sum_sum_type]
  rw [h6]
  rw [preCoContrUnit_apply_one, preCoContrUnitVal_expand_tmul]
  simp

lemma coContrContract_apply_metric {d : ℕ} : (β_ (Co d) (Contr d)).hom.hom
    (((Co d).V ◁ (λ_ (Contr d).V).hom)
    (((Co d).V ◁ coContrContract.hom ▷ (Contr d).V)
    (((Co d).V ◁ (α_ (Co d).V (Contr d).V (Contr d).V).inv)
    ((α_ (Co d).V (Co d).V ((Contr d).V ⊗ (Contr d).V)).hom
    ((preCoMetric d).hom (1 : ℝ) ⊗ₜ[ℝ] (preContrMetric d).hom (1 : ℝ)))))) =
    (preContrCoUnit d).hom (1 : ℝ) := by
  have h1 : ((preCoMetric d).hom (1 : ℝ) ⊗ₜ[ℝ] (preContrMetric d).hom (1 : ℝ)) =
      ∑ i, ∑ j, ((minkowskiMatrix i i * minkowskiMatrix j j) •
        ((coBasis d i ⊗ₜ[ℝ] coBasis d i) ⊗ₜ[ℝ] (contrBasis d j ⊗ₜ[ℝ] contrBasis d j))) := by
    rw [preCoMetric_apply_one, preContrMetric_apply_one,
      preCoMetricVal_expand_tmul_minkowskiMatrix, preContrMetricVal_expand_tmul_minkowskiMatrix]
    simp [tmul_sum, sum_tmul, - Fintype.sum_sum_type, Finset.smul_sum]
    rw [Finset.sum_comm]
    congr 1
    funext x
    congr 1
    funext y
    simp [smul_tmul, smul_smul]
    rw [mul_comm]
  rw [h1]
  have h2 : (α_ (Co d).V (Co d).V ((Contr d).V ⊗ (Contr d).V)).hom
      (∑ i, ∑ j, (minkowskiMatrix i i * minkowskiMatrix j j) •
      (coBasis d i ⊗ₜ[ℝ] coBasis d i) ⊗ₜ[ℝ] (contrBasis d j ⊗ₜ[ℝ] contrBasis d j)) =
      ∑ i, ∑ j, (minkowskiMatrix i i * minkowskiMatrix j j) •
      (coBasis d i ⊗ₜ[ℝ] (coBasis d i ⊗ₜ[ℝ] (contrBasis d j ⊗ₜ[ℝ] contrBasis d j))) := by
    simp [map_sum, - Fintype.sum_sum_type]
    rfl
  rw [h2]
  have h3 : ((Co d).V ◁ (α_ (Co d).V (Contr d).V (Contr d).V).inv)
      (∑ i, ∑ j, (minkowskiMatrix i i * minkowskiMatrix j j) •
      (coBasis d i ⊗ₜ[ℝ] (coBasis d i ⊗ₜ[ℝ] (contrBasis d j ⊗ₜ[ℝ] contrBasis d j)))) =
      ∑ i, ∑ j, (minkowskiMatrix i i * minkowskiMatrix j j) •
      (coBasis d i ⊗ₜ[ℝ] ((coBasis d i ⊗ₜ[ℝ] contrBasis d j) ⊗ₜ[ℝ] contrBasis d j)) := by
    simp [- Fintype.sum_sum_type]
    rfl
  rw [h3]
  have h4 : ((Co d).V ◁ coContrContract.hom ▷ (Contr d).V)
      (∑ i, ∑ j, (minkowskiMatrix i i * minkowskiMatrix j j) •
      (coBasis d i ⊗ₜ[ℝ] ((coBasis d i ⊗ₜ[ℝ] contrBasis d j) ⊗ₜ[ℝ] contrBasis d j))) =
      ∑ i, ∑ j, (minkowskiMatrix i i * minkowskiMatrix j j) •
      (coBasis d i ⊗ₜ[ℝ] (coContrContract.hom
      (coBasis d i ⊗ₜ[ℝ] contrBasis d j) ⊗ₜ[ℝ] contrBasis d j)) := by
    simp [- Fintype.sum_sum_type]
    rfl
  rw [h4]
  have h5 : ∑ i, ∑ j, (minkowskiMatrix i i * minkowskiMatrix j j) •
      (coBasis d i ⊗ₜ[ℝ]
      (coContrContract.hom (coBasis d i ⊗ₜ[ℝ] contrBasis d j) ⊗ₜ[ℝ] contrBasis d j))
      = ∑ i, coBasis d i ⊗ₜ[ℝ] ((1 : ℝ) ⊗ₜ[ℝ] contrBasis d i) := by
    congr
    funext x
    rw [Finset.sum_eq_single x]
    · simp only [minkowskiMatrix.η_apply_mul_η_apply_diag, one_smul]
      rw [coContrContract_basis]
      simp
    · intro b _ hb
      rw [coContrContract_basis]
      rw [if_neg]
      · simp
      · exact id (Ne.symm hb)
    · simp
  rw [h5]
  have h6 : ((Co d).V ◁ (λ_ (Contr d).V).hom)
      (∑ i, coBasis d i ⊗ₜ[ℝ] ((1 : ℝ) ⊗ₜ[ℝ] contrBasis d i)) =
      ∑ i, coBasis d i ⊗ₜ[ℝ] contrBasis d i := by
    simp [- Fintype.sum_sum_type]
  rw [h6]
  rw [preContrCoUnit_apply_one, preContrCoUnitVal_expand_tmul]
  simp

end Lorentz
end
