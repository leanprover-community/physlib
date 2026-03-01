/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QFT.PerturbationTheory.WickAlgebra.StaticWickTheorem
import PhysLean.QFT.PerturbationTheory.WickAlgebra.WicksTheorem
import PhysLean.QFT.PerturbationTheory.WickContraction.Sign.Join
import PhysLean.QFT.PerturbationTheory.WickContraction.TimeCond
/-!

# Wick's theorem for normal ordered lists

-/

namespace FieldSpecification
variable {𝓕 : FieldSpecification}
open FieldOpFreeAlgebra
namespace WickAlgebra
open WickContraction
open EqTimeOnly

/--
For a list `φs` of `𝓕.FieldOp`, then

`𝓣(φs) = ∑ φsΛ, φsΛ.sign • φsΛ.timeContract * 𝓣(𝓝([φsΛ]ᵘᶜ))`

where the sum is over all Wick contraction `φsΛ` which only have equal time contractions.

This result follows from
- `static_wick_theorem` to rewrite `𝓣(φs)` on the left hand side as a sum of
  `𝓣(φsΛ.staticWickTerm)`.
- `EqTimeOnly.timeOrder_staticContract_of_not_mem` and `timeOrder_timeOrder_mid` to set to
  those `𝓣(φsΛ.staticWickTerm)` for which `φsΛ` has a contracted pair which are not
  equal time to zero.
- `staticContract_eq_timeContract_of_eqTimeOnly` to rewrite the static contract
  in the remaining `𝓣(φsΛ.staticWickTerm)` as a time contract.
- `timeOrder_timeContract_mul_of_eqTimeOnly_left` to move the time contracts out of the time
  ordering.
-/
lemma timeOrder_ofFieldOpList_eqTimeOnly (φs : List 𝓕.FieldOp) :
    𝓣(ofFieldOpList φs) = ∑ (φsΛ : {φsΛ // φsΛ.EqTimeOnly (φs := φs)}),
    φsΛ.1.sign • φsΛ.1.timeContract.1 * 𝓣(𝓝(ofFieldOpList [φsΛ.1]ᵘᶜ)) := by
  rw [static_wick_theorem φs]
  let e2 : WickContraction φs.length ≃
    {φsΛ : WickContraction φs.length // φsΛ.EqTimeOnly} ⊕
    {φsΛ : WickContraction φs.length // ¬ φsΛ.EqTimeOnly} :=
    (Equiv.sumCompl _).symm
  rw [← e2.symm.sum_comp]
  simp only [Equiv.symm_symm, Algebra.smul_mul_assoc, Fintype.sum_sum_type,
    Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr, map_add, map_sum, e2]
  simp only [staticWickTerm, Algebra.smul_mul_assoc, map_smul]
  conv_lhs =>
    enter [2, 2, x]
    rw [timeOrder_timeOrder_left]
    rw [timeOrder_staticContract_of_not_mem _ x.2]
  simp only [zero_mul, map_zero, smul_zero, Finset.sum_const_zero, add_zero]
  congr
  funext x
  rw [staticContract_eq_timeContract_of_eqTimeOnly]
  rw [timeOrder_timeContract_mul_of_eqTimeOnly_left]
  exact x.2
  exact x.2

lemma timeOrder_ofFieldOpList_eq_eqTimeOnly_empty (φs : List 𝓕.FieldOp) :
    𝓣(ofFieldOpList φs) = 𝓣(𝓝(ofFieldOpList φs)) +
    ∑ (φsΛ : {φsΛ // φsΛ.EqTimeOnly (φs := φs) ∧ φsΛ ≠ empty}),
    φsΛ.1.sign • φsΛ.1.timeContract.1 * 𝓣(𝓝(ofFieldOpList [φsΛ.1]ᵘᶜ)) := by
  let e1 : {φsΛ : WickContraction φs.length // φsΛ.EqTimeOnly} ≃
      {φsΛ : {φsΛ : WickContraction φs.length // φsΛ.EqTimeOnly} // φsΛ.1 = empty} ⊕
      {φsΛ : {φsΛ : WickContraction φs.length // φsΛ.EqTimeOnly} // ¬ φsΛ.1 = empty} :=
      (Equiv.sumCompl _).symm
  rw [timeOrder_ofFieldOpList_eqTimeOnly, ← e1.symm.sum_comp]
  simp only [Equiv.symm_symm, Algebra.smul_mul_assoc, Fintype.sum_sum_type,
    Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr, ne_eq, e1]
  congr 1
  · let e2 : {φsΛ : {φsΛ : WickContraction φs.length // φsΛ.EqTimeOnly} // φsΛ.1 = empty } ≃
      Unit := {
      toFun := fun x => (), invFun := fun x => ⟨⟨empty, by simp⟩, rfl⟩,
      left_inv a := by
        ext
        simp [a.2], right_inv a := by simp}
    rw [← e2.symm.sum_comp]
    simp [e2, sign_empty]
  · let e2 : { φsΛ : {φsΛ : WickContraction φs.length // φsΛ.EqTimeOnly} // ¬ φsΛ.1 = empty } ≃
      {φsΛ // φsΛ.EqTimeOnly ∧ φsΛ ≠ empty} := {
        toFun := fun x => ⟨x, ⟨x.1.2, x.2⟩⟩, invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩,
        left_inv a := by rfl, right_inv a := by rfl }
    rw [← e2.symm.sum_comp]
    rfl

/--
For a list `φs` of `𝓕.FieldOp`, then

`𝓣(𝓝(φs)) = 𝓣(φs) - ∑ φsΛ, φsΛ.sign • φsΛ.timeContract.1 * 𝓣(𝓝([φsΛ]ᵘᶜ))`

where the sum is over all *non-empty* Wick contraction `φsΛ` which only
  have equal time contractions.

This result follows directly from
- `timeOrder_ofFieldOpList_eqTimeOnly`
-/
lemma normalOrder_timeOrder_ofFieldOpList_eq_eqTimeOnly_empty (φs : List 𝓕.FieldOp) :
    𝓣(𝓝(ofFieldOpList φs)) = 𝓣(ofFieldOpList φs) -
    ∑ (φsΛ : {φsΛ // φsΛ.EqTimeOnly (φs := φs) ∧ φsΛ ≠ empty}),
    φsΛ.1.sign • φsΛ.1.timeContract.1 * 𝓣(𝓝(ofFieldOpList [φsΛ.1]ᵘᶜ)) := by
  rw [timeOrder_ofFieldOpList_eq_eqTimeOnly_empty]
  simp

/--
For a list `φs` of `𝓕.FieldOp`, then `𝓣(φs)` is equal to the sum of

- `∑ φsΛ, φsΛ.wickTerm` where the sum is over all Wick contraction `φsΛ` which have
  no contractions of equal time.
- `∑ φsΛ, φsΛ.sign • φsΛ.timeContract * (∑ φssucΛ, φssucΛ.wickTerm)`, where
  the first sum is over all Wick contraction `φsΛ` which only have equal time contractions
  and the second sum is over all Wick contraction `φssucΛ` of the uncontracted elements of `φsΛ`
  which do not have any equal time contractions.

The proof proceeds as follows
- `wicks_theorem` is used to rewrite `𝓣(φs)` as a sum over all Wick contractions.
- The sum over all Wick contractions is then split additively into two parts based on having
  or not having an equal time contractions.
- Using `join`, the sum `∑ φsΛ, _` over Wick contractions which do have equal time contractions
  is split into two sums `∑ φsΛ, ∑ φsucΛ, _`, the first over non-zero elements
  which only have equal time contractions and the second over Wick contractions `φsucΛ` of
  `[φsΛ]ᵘᶜ` which do not have equal time contractions.
- `join_sign_timeContract` is then used to equate terms.
-/
lemma timeOrder_haveEqTime_split (φs : List 𝓕.FieldOp) :
    𝓣(ofFieldOpList φs) = (∑ (φsΛ : {φsΛ : WickContraction φs.length // ¬ HaveEqTime φsΛ}),
    φsΛ.1.sign • φsΛ.1.timeContract.1 * 𝓝(ofFieldOpList [φsΛ.1]ᵘᶜ))
    + ∑ (φsΛ : {φsΛ // φsΛ.EqTimeOnly (φs := φs) ∧ φsΛ ≠ empty}), φsΛ.1.sign • φsΛ.1.timeContract *
    (∑ φssucΛ : { φssucΛ : WickContraction [φsΛ.1]ᵘᶜ.length // ¬ φssucΛ.HaveEqTime },
      φssucΛ.1.wickTerm) := by
  rw [wicks_theorem]
  simp only [wickTerm]
  let e1 : WickContraction φs.length ≃ {φsΛ // HaveEqTime φsΛ} ⊕ {φsΛ // ¬ HaveEqTime φsΛ} := by
    exact (Equiv.sumCompl HaveEqTime).symm
  rw [← e1.symm.sum_comp]
  simp only [Equiv.symm_symm, Algebra.smul_mul_assoc, Fintype.sum_sum_type,
    Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr, ne_eq, e1]
  rw [add_comm]
  congr 1
  let f : WickContraction φs.length → 𝓕.WickAlgebra := fun φsΛ =>
    φsΛ.sign • (φsΛ.timeContract.1 * 𝓝(ofFieldOpList [φsΛ]ᵘᶜ))
  change ∑ (φsΛ : {φsΛ : WickContraction φs.length // HaveEqTime φsΛ}), f φsΛ.1 = _
  rw [sum_haveEqTime]
  congr
  funext φsΛ
  simp only [f]
  conv_lhs =>
    enter [2, φsucΛ]
    rw [← Algebra.smul_mul_assoc]
    rw [join_sign_timeContract φsΛ.1 φsucΛ.1]
  conv_lhs =>
    enter [2, φsucΛ]
    rw [mul_assoc]
  rw [← Finset.mul_sum, ← Algebra.smul_mul_assoc]
  congr
  funext φsΛ'
  simp only [ne_eq, Algebra.smul_mul_assoc]
  congr 1
  rw [@join_uncontractedListGet]

lemma normalOrder_timeOrder_ofFieldOpList_eq_not_haveEqTime_sub_inductive (φs : List 𝓕.FieldOp) :
    𝓣(𝓝(ofFieldOpList φs)) =
      (∑ (φsΛ : {φsΛ : WickContraction φs.length // ¬ HaveEqTime φsΛ}), φsΛ.1.wickTerm)
      + ∑ (φsΛ : {φsΛ // φsΛ.EqTimeOnly (φs := φs) ∧ φsΛ ≠ empty}),
        sign φs ↑φsΛ • (φsΛ.1).timeContract *
        (∑ φssucΛ : { φssucΛ : WickContraction [φsΛ.1]ᵘᶜ.length // ¬ φssucΛ.HaveEqTime },
        φssucΛ.1.wickTerm - 𝓣(𝓝(ofFieldOpList [φsΛ.1]ᵘᶜ))) := by
  rw [normalOrder_timeOrder_ofFieldOpList_eq_eqTimeOnly_empty,
    timeOrder_haveEqTime_split]
  rw [add_sub_assoc]
  congr 1
  simp only [ne_eq, Algebra.smul_mul_assoc]
  rw [← Finset.sum_sub_distrib]
  congr 1
  funext x
  simp only
  rw [← smul_sub, ← mul_sub]

lemma wicks_theorem_normal_order_empty : 𝓣(𝓝(ofFieldOpList [])) =
    ∑ (φsΛ : {φsΛ : WickContraction ([] : List 𝓕.FieldOp).length // ¬ HaveEqTime φsΛ}),
    φsΛ.1.wickTerm := by
  simp only [wickTerm]
  let e2 : {φsΛ : WickContraction ([] : List 𝓕.FieldOp).length // ¬ HaveEqTime φsΛ} ≃ Unit :=
    {
      toFun := fun x => (),
      invFun := fun x => ⟨empty, by simp⟩,
      left_inv := by
        intro a
        simp only [List.length_nil]
        apply Subtype.ext
        apply Subtype.ext
        simp only [empty]
        ext i
        simp only [Finset.notMem_empty, false_iff]
        by_contra hn
        have h2 := a.1.2.1 i hn
        rw [@Finset.card_eq_two] at h2
        obtain ⟨a, b, ha, hb, hab⟩ := h2
        exact Fin.elim0 a,
      right_inv := by intro a; simp}
  rw [← e2.symm.sum_comp]
  simp only [Finset.univ_unique, PUnit.default_eq_unit, List.length_nil, Equiv.coe_fn_symm_mk,
    sign_empty, timeContract_empty, OneMemClass.coe_one, one_smul, uncontractedListGet_empty,
    one_mul, Finset.sum_const, Finset.card_singleton, e2]
  have h1' : ofFieldOpList (𝓕 := 𝓕) [] = ofCrAnList [] := by rfl
  rw [h1']
  rw [normalOrder_ofCrAnList]
  simp only [normalOrderSign_nil, normalOrderList_nil, one_smul]
  rw [ofCrAnList, timeOrder_eq_ι_timeOrderF]
  rw [timeOrderF_ofCrAnListF]
  simp

/--For a list `φs` of `𝓕.FieldOp`, the normal-ordered version of Wick's theorem states that

`𝓣(𝓝(φs)) = ∑ φsΛ, φsΛ.wickTerm`

where the sum is over all Wick contraction `φsΛ` in which no two contracted elements
have the same time.

The proof proceeds by induction on `φs`, with the base case `[]` holding by following
through definitions. and the inductive case holding as a result of
- `timeOrder_haveEqTime_split`
- `normalOrder_timeOrder_ofFieldOpList_eq_eqTimeOnly_empty`
- and the induction hypothesis on `𝓣(𝓝([φsΛ.1]ᵘᶜ))` for contractions `φsΛ` of `φs` which only
  have equal time contractions and are non-empty.
-/
theorem wicks_theorem_normal_order : (φs : List 𝓕.FieldOp) →
    𝓣(𝓝(ofFieldOpList φs)) =
    ∑ (φsΛ : {φsΛ : WickContraction φs.length // ¬ HaveEqTime φsΛ}), φsΛ.1.wickTerm
  | [] => wicks_theorem_normal_order_empty
  | φ :: φs => by
    rw [normalOrder_timeOrder_ofFieldOpList_eq_not_haveEqTime_sub_inductive]
    simp only [Algebra.smul_mul_assoc, ne_eq, add_eq_left]
    apply Finset.sum_eq_zero
    intro φsΛ hφsΛ
    simp only [smul_eq_zero]
    right
    have ih := wicks_theorem_normal_order [φsΛ.1]ᵘᶜ
    rw [ih]
    simp [wickTerm]
termination_by φs => φs.length
decreasing_by
  simp only [uncontractedListGet, List.length_cons, List.length_map]
  rw [uncontractedList_length_eq_card]
  have hc := uncontracted_card_eq_iff φsΛ.1
  simp only [List.length_cons, φsΛ.2.2, iff_false] at hc
  have hc' := uncontracted_card_le φsΛ.1
  simp_all only [List.length_cons, Finset.mem_univ, gt_iff_lt]
  omega

end WickAlgebra
end FieldSpecification
