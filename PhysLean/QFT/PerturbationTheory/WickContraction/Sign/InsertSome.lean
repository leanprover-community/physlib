/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.QFT.PerturbationTheory.WickContraction.Sign.Basic
public import PhysLean.QFT.PerturbationTheory.WickContraction.InsertAndContract

/-!

# Sign on inserting and contracting

The main results of this file are `sign_insert_some_of_lt` and `sign_insert_some_of_not_lt` which
write the sign of `(φsΛ ↩Λ φ i (some k)).sign` in terms of the sign of `φsΛ`.
-/

@[expose] public section

open FieldSpecification
variable {𝓕 : FieldSpecification}

namespace WickContraction
variable {n : ℕ} (c : WickContraction n)
open PhysLean.List
open FieldStatistic

/-!

## Sign insert some

-/

lemma stat_ofFinset_eq_one_of_gradingCompliant (φs : List 𝓕.FieldOp)
    (a : Finset (Fin φs.length)) (φsΛ : WickContraction φs.length) (hg : GradingCompliant φs φsΛ)
    (hnon : ∀ i, φsΛ.getDual? i = none → i ∉ a)
    (hsom : ∀ i, (h : (φsΛ.getDual? i).isSome) → i ∈ a → (φsΛ.getDual? i).get h ∈ a) :
    (𝓕 |>ₛ ⟨φs.get, a⟩) = 1 := by
  rw [ofFinset_eq_prod]
  let e2 : Fin φs.length ≃ {x // (φsΛ.getDual? x).isSome} ⊕ {x // ¬ (φsΛ.getDual? x).isSome} := by
    exact (Equiv.sumCompl fun a => (φsΛ.getDual? a).isSome = true).symm
  rw [← e2.symm.prod_comp]
  simp only [Fin.getElem_fin, Fintype.prod_sum_type, instCommGroup]
  conv_lhs =>
    enter [2, 2, x]
    simp only [Equiv.symm_symm, Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr, e2]
    rw [if_neg (hnon x.1 (by simpa using x.2))]
  simp only [Equiv.symm_symm, Equiv.sumCompl_apply_inl, Finset.prod_const_one, mul_one, e2]
  rw [← φsΛ.sigmaContractedEquiv.prod_comp]
  rw [Fintype.prod_sigma]
  apply Fintype.prod_eq_one _
  intro x
  rw [prod_finset_eq_mul_fst_snd]
  simp only [sigmaContractedEquiv, Equiv.coe_fn_mk, mul_ite, ite_mul, one_mul, mul_one]
  split
  · split
    rw [hg x]
    simp only [mul_self]
    rename_i h1 h2
    have hsom' := hsom (φsΛ.sndFieldOfContract x) (by simp) h1
    simp only [sndFieldOfContract_getDual?, Option.get_some] at hsom'
    exact False.elim (h2 hsom')
  · split
    rename_i h1 h2
    have hsom' := hsom (φsΛ.fstFieldOfContract x) (by simp) h2
    simp only [fstFieldOfContract_getDual?, Option.get_some] at hsom'
    exact False.elim (h1 hsom')
    rfl

lemma signFinset_insertAndContract_some (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (i1 i2 : Fin φs.length)
    (j : φsΛ.uncontracted) :
    (φsΛ ↩Λ φ i (some j)).signFinset (finCongr (insertIdx_length_fin φ φs i).symm
    (i.succAbove i1)) (finCongr (insertIdx_length_fin φ φs i).symm (i.succAbove i2)) =
    if i.succAbove i1 < i ∧ i < i.succAbove i2 ∧ (i1 < j) then
      Insert.insert (finCongr (insertIdx_length_fin φ φs i).symm i)
      (insertAndContractLiftFinset φ i (φsΛ.signFinset i1 i2))
    else
      if i1 < j ∧ j < i2 ∧ ¬ i.succAbove i1 < i then
        (insertAndContractLiftFinset φ i (φsΛ.signFinset i1 i2)).erase
        (finCongr (insertIdx_length_fin φ φs i).symm (i.succAbove j))
      else
        (insertAndContractLiftFinset φ i (φsΛ.signFinset i1 i2)) := by
  ext k
  rcases insert_fin_eq_self φ i k with hk | hk
  · subst hk
    have h1 : Fin.cast (insertIdx_length_fin φ φs i).symm i ∈
      (if i.succAbove i1 < i ∧ i < i.succAbove i2 ∧ (i1 < j) then
      Insert.insert (finCongr (insertIdx_length_fin φ φs i).symm i)
      (insertAndContractLiftFinset φ i (φsΛ.signFinset i1 i2))
      else
        if i1 < j ∧ j < i2 ∧ ¬ i.succAbove i1 < i then
          (insertAndContractLiftFinset φ i (φsΛ.signFinset i1 i2)).erase
          (finCongr (insertIdx_length_fin φ φs i).symm (i.succAbove j))
        else
          (insertAndContractLiftFinset φ i (φsΛ.signFinset i1 i2))) ↔
          i.succAbove i1 < i ∧ i < i.succAbove i2 ∧ (i1 < j) := by
        split
        simp_all only [Nat.succ_eq_add_one, finCongr_apply, Finset.mem_insert,
          self_not_mem_insertAndContractLiftFinset, or_false, and_self]
        rename_i h
        simp only [Nat.succ_eq_add_one, not_lt, finCongr_apply, h, iff_false]
        split
        simp only [Finset.mem_erase, ne_eq, self_not_mem_insertAndContractLiftFinset, and_false,
          not_false_eq_true]
        simp
    rw [h1]
    simp only [Nat.succ_eq_add_one, signFinset, finCongr_apply, Finset.mem_filter, Finset.mem_univ,
      insertAndContract_some_getDual?_self_eq, reduceCtorEq, Option.isSome_some, Option.get_some,
      forall_const, false_or, true_and]
    rw [Fin.lt_def, Fin.lt_def, Fin.lt_def, Fin.lt_def]
    simp only [Fin.val_cast, Fin.val_fin_lt, and_congr_right_iff]
    intro h1 h2
    exact Fin.succAbove_lt_succAbove_iff
  · obtain ⟨k, hk⟩ := hk
    subst hk
    by_cases hkj : k = j.1
    · subst hkj
      conv_lhs=> simp only [Nat.succ_eq_add_one, signFinset, finCongr_apply, Finset.mem_filter,
        Finset.mem_univ, insertAndContract_some_getDual?_some_eq, reduceCtorEq, Option.isSome_some,
        Option.get_some, forall_const, false_or, true_and, not_lt]
      rw [Fin.lt_def, Fin.lt_def]
      simp only [Fin.val_cast, Fin.val_fin_lt, Nat.succ_eq_add_one, finCongr_apply, not_lt]
      conv_lhs =>
        enter [2, 2]
        rw [Fin.lt_def]
      simp only [Fin.val_cast, Fin.val_fin_lt]
      split
      · rename_i h
        simp_all only [and_true, Finset.mem_insert]
        rw [succAbove_mem_insertAndContractLiftFinset]
        simp only [Fin.ext_iff, Fin.val_cast]
        have h1 : ¬ (i.succAbove ↑j) = i := Fin.succAbove_ne i ↑j
        simp only [Fin.val_eq_val, h1, signFinset, Finset.mem_filter, Finset.mem_univ, true_and,
          false_or]
        rw [Fin.succAbove_lt_succAbove_iff, Fin.succAbove_lt_succAbove_iff]
        simp only [and_congr_right_iff, iff_self_and]
        intro h1 h2
        apply Or.inl
        have hj:= j.2
        simpa [uncontracted, -SetLike.coe_mem] using hj
      · rename_i h
        simp only [not_and, not_lt] at h
        rw [Fin.succAbove_lt_succAbove_iff, Fin.succAbove_lt_succAbove_iff]
        split
        · rename_i h1
          simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and, iff_false, not_and,
            not_lt]
          intro h1 h2
          omega
        · rename_i h1
          rw [succAbove_mem_insertAndContractLiftFinset]
          simp only [signFinset, Finset.mem_filter, Finset.mem_univ, true_and, and_congr_right_iff]
          intro h1 h2
          have hj:= j.2
          simp only [uncontracted, Finset.mem_filter, Finset.mem_univ, true_and] at hj
          simp only [hj, Option.isSome_none, Bool.false_eq_true, IsEmpty.forall_iff, or_self,
            iff_true, gt_iff_lt]
          omega
    · have h1 : Fin.cast (insertIdx_length_fin φ φs i).symm (i.succAbove k) ∈
        (if i.succAbove i1 < i ∧ i < i.succAbove i2 ∧ (i1 < j) then
        Insert.insert (finCongr (insertIdx_length_fin φ φs i).symm i)
        (insertAndContractLiftFinset φ i (φsΛ.signFinset i1 i2))
        else
        if i1 < j ∧ j < i2 ∧ ¬ i.succAbove i1 < i then
          (insertAndContractLiftFinset φ i (φsΛ.signFinset i1 i2)).erase
          (finCongr (insertIdx_length_fin φ φs i).symm (i.succAbove j))
        else
          (insertAndContractLiftFinset φ i (φsΛ.signFinset i1 i2))) ↔
          Fin.cast (insertIdx_length_fin φ φs i).symm (i.succAbove k) ∈
          (insertAndContractLiftFinset φ i (φsΛ.signFinset i1 i2)) := by
        split
        · simp only [Nat.succ_eq_add_one, finCongr_apply, Finset.mem_insert, or_iff_right_iff_imp]
          intro h
          simp only [Fin.ext_iff, Fin.val_cast] at h
          simp only [Fin.val_eq_val] at h
          have hn : ¬ i.succAbove k = i := Fin.succAbove_ne i k
          exact False.elim (hn h)
        · split
          simp only [Nat.succ_eq_add_one, finCongr_apply, Finset.mem_erase, ne_eq,
            and_iff_right_iff_imp]
          intro h
          simp only [Fin.ext_iff, Fin.val_cast]
          simp only [Fin.val_eq_val]
          rw [Function.Injective.eq_iff]
          exact hkj
          exact Fin.succAbove_right_injective
          · simp
      rw [h1]
      rw [succAbove_mem_insertAndContractLiftFinset]
      simp only [Nat.succ_eq_add_one, signFinset, finCongr_apply, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rw [Fin.lt_def, Fin.lt_def, Fin.lt_def, Fin.lt_def]
      simp only [Fin.val_cast, Fin.val_fin_lt]
      rw [Fin.succAbove_lt_succAbove_iff, Fin.succAbove_lt_succAbove_iff]
      simp only [and_congr_right_iff]
      intro h1 h2
      simp only [ne_eq, hkj, not_false_eq_true, insertAndContract_some_succAbove_getDual?_eq_option,
        Nat.succ_eq_add_one, Option.map_eq_none_iff, Option.isSome_map]
      conv_lhs =>
        rhs
        enter [h]
        rw [Fin.lt_def]
        simp only [Fin.val_cast, Option.get_map, Function.comp_apply, Fin.val_fin_lt]
        rw [Fin.succAbove_lt_succAbove_iff]

/--
Given a Wick contraction `φsΛ` the sign defined in the following way,
related to inserting a field `φ` at position `i` and contracting it with `j : φsΛ.uncontracted`.
- For each contracted pair `{a1, a2}` in `φsΛ` with `a1 < a2` the sign
  `𝓢(φ, φₐ₂)` if `a₁ < i ≤ a₂` and `a₁ < j`.
- For each contracted pair `{a1, a2}` in `φsΛ` with `a1 < a2` the sign
  `𝓢(φⱼ, φₐ₂)` if `a₁ < j < a₂` and `i < a₁`. -/
def signInsertSomeProd (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp) (φsΛ : WickContraction φs.length)
    (i : Fin φs.length.succ) (j : φsΛ.uncontracted) : ℂ :=
  ∏ (a : φsΛ.1),
    if i.succAbove (φsΛ.fstFieldOfContract a) < i ∧ i < i.succAbove (φsΛ.sndFieldOfContract a) ∧
      ((φsΛ.fstFieldOfContract a) < j) then
      𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs[φsΛ.sndFieldOfContract a])
    else
    if (φsΛ.fstFieldOfContract a) < j ∧ j < (φsΛ.sndFieldOfContract a) ∧
        ¬ i.succAbove (φsΛ.fstFieldOfContract a) < i then
      𝓢(𝓕 |>ₛ φs[j.1], 𝓕 |>ₛ φs[φsΛ.sndFieldOfContract a])
    else
      1

/-- Given a Wick contraction `φsΛ` the sign defined in the following way,
related to inserting a field `φ` at position `i` and contracting it with `j : φsΛ.uncontracted`.
- If `j < i`, for each field `φₐ` in `φⱼ₊₁…φᵢ₋₁` without a dual at position `< j`
  the sign `𝓢(φₐ, φᵢ)`.
- Else, for each field `φₐ` in `φᵢ…φⱼ₋₁` of `φs` without dual at position `< i` the sign
  `𝓢(φₐ, φⱼ)`. -/
def signInsertSomeCoef (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp) (φsΛ : WickContraction φs.length)
    (i : Fin φs.length.succ) (j : φsΛ.uncontracted) : ℂ :=
  let a : (φsΛ ↩Λ φ i (some j)).1 := congrLift (insertIdx_length_fin φ φs i).symm
    ⟨{i, i.succAbove j}, by simp [insertAndContractNat]⟩;
  𝓢(𝓕 |>ₛ (φs.insertIdx i φ)[(φsΛ ↩Λ φ i (some j)).sndFieldOfContract a],
    𝓕 |>ₛ ⟨(φs.insertIdx i φ).get, signFinset
    (φsΛ ↩Λ φ i (some j)) ((φsΛ ↩Λ φ i (some j)).fstFieldOfContract a)
    ((φsΛ ↩Λ φ i (some j)).sndFieldOfContract a)⟩)

/-- Given a Wick contraction `φsΛ` associated with a list of states `φs`
  and an `i : Fin φs.length.succ`, the change in sign of the contraction associated with
  inserting `φ` into `φs` at position `i` and contracting it with `j : c.uncontracted`. -/
def signInsertSome (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp) (φsΛ : WickContraction φs.length)
    (i : Fin φs.length.succ) (j : φsΛ.uncontracted) : ℂ :=
  signInsertSomeCoef φ φs φsΛ i j * signInsertSomeProd φ φs φsΛ i j

lemma sign_insert_some (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp) (φsΛ : WickContraction φs.length)
    (i : Fin φs.length.succ) (j : φsΛ.uncontracted) :
    (φsΛ ↩Λ φ i (some j)).sign = (φsΛ.signInsertSome φ φs i j) * φsΛ.sign := by
  rw [sign, signInsertSome, signInsertSomeProd, sign, mul_assoc, ← Finset.prod_mul_distrib]
  rw [insertAndContract_some_prod_contractions]
  congr
  funext a
  simp only [instCommGroup, Nat.succ_eq_add_one, insertAndContract_sndFieldOfContract,
    finCongr_apply, Fin.getElem_fin, Fin.val_cast, insertIdx_getElem_fin,
    insertAndContract_fstFieldOfContract, not_lt, ite_mul, one_mul]
  erw [signFinset_insertAndContract_some]
  split
  · rename_i h
    simp only [Nat.succ_eq_add_one, finCongr_apply]
    rw [ofFinset_insert]
    simp only [instCommGroup, Fin.getElem_fin, Fin.val_cast, List.getElem_insertIdx_self, map_mul]
    rw [stat_ofFinset_of_insertAndContractLiftFinset]
    simp only [exchangeSign_symm, instCommGroup.eq_1]
    simp
  · rename_i h
    split
    · rename_i h1
      simp only [Nat.succ_eq_add_one, finCongr_apply, h1, true_and]
      rw [if_pos]
      rw [ofFinset_erase]
      simp only [instCommGroup, Fin.getElem_fin, Fin.val_cast, insertIdx_getElem_fin, map_mul]
      rw [stat_ofFinset_of_insertAndContractLiftFinset]
      simp only [exchangeSign_symm, instCommGroup.eq_1]
      · rw [succAbove_mem_insertAndContractLiftFinset]
        simp only [signFinset, Finset.mem_filter, Finset.mem_univ, true_and]
        simp_all only [Nat.succ_eq_add_one, and_true, false_and, not_false_eq_true, not_lt,
          true_and]
        apply Or.inl
        simpa [uncontracted, -SetLike.coe_mem] using j.2
      · simp_all
    · rename_i h1
      rw [if_neg]
      rw [stat_ofFinset_of_insertAndContractLiftFinset]
      simp_all

lemma signInsertSomeProd_eq_one_if (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (j : φsΛ.uncontracted)
    (hφj : (𝓕 |>ₛ φ) = (𝓕 |>ₛ φs[j.1])) :
  φsΛ.signInsertSomeProd φ φs i j =
  ∏ (a : φsΛ.1),
    if (φsΛ.fstFieldOfContract a) < j
      ∧ (i.succAbove (φsΛ.fstFieldOfContract a) < i ∧ i < i.succAbove (φsΛ.sndFieldOfContract a)
      ∨ j < (φsΛ.sndFieldOfContract a) ∧ ¬ i.succAbove (φsΛ.fstFieldOfContract a) < i)
    then
      𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs[φsΛ.sndFieldOfContract a])
    else
      1 := by
  rw [signInsertSomeProd]
  congr
  funext a
  split
  · rename_i h
    simp only [instCommGroup.eq_1, Fin.getElem_fin, h, Nat.succ_eq_add_one, and_self,
      not_true_eq_false, and_false, or_false, ↓reduceIte]
  · rename_i h
    split
    · rename_i h1
      simp only [instCommGroup.eq_1, Fin.getElem_fin, h1, Nat.succ_eq_add_one, false_and,
        not_false_eq_true, and_self, or_true, ↓reduceIte]
      congr 1
      exact congrArg (⇑exchangeSign) (id (Eq.symm hφj))
    · rename_i h1
      simp only [Nat.succ_eq_add_one, not_lt, instCommGroup.eq_1, Fin.getElem_fin]
      rw [if_neg]
      simp_all only [Fin.getElem_fin, Nat.succ_eq_add_one, not_and, not_lt, not_le, not_or,
        implies_true, and_true]
      omega

lemma signInsertSomeProd_eq_prod_prod (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length)
    (i : Fin φs.length.succ) (j : φsΛ.uncontracted) (hφj : (𝓕 |>ₛ φ) = (𝓕 |>ₛ φs[j.1]))
    (hg : GradingCompliant φs φsΛ) :
  φsΛ.signInsertSomeProd φ φs i j =
  ∏ (a : φsΛ.1), ∏ (x : a.1), if x.1 < j
      ∧ (i.succAbove x.1 < i ∧
      i < i.succAbove ((φsΛ.getDual? x.1).get (getDual?_isSome_of_mem φsΛ a x))
      ∨ j < ((φsΛ.getDual? x.1).get (getDual?_isSome_of_mem φsΛ a x)) ∧ ¬ i.succAbove x < i)
    then
      𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs[x.1])
    else
      1 := by
  rw [signInsertSomeProd_eq_one_if]
  congr
  funext a
  rw [prod_finset_eq_mul_fst_snd]
  nth_rewrite 3 [if_neg]
  · simp only [Nat.succ_eq_add_one, not_lt, instCommGroup.eq_1, Fin.getElem_fin,
    fstFieldOfContract_getDual?, Option.get_some, mul_one]
    congr 1
    rw [hg a]
  · simp only [Nat.succ_eq_add_one, sndFieldOfContract_getDual?, Option.get_some, not_lt, not_and,
    not_or, not_le]
    intro h1
    have ha := fstFieldOfContract_lt_sndFieldOfContract φsΛ a
    apply And.intro
    · intro hi
      have hx := (Fin.succAbove_lt_succAbove_iff (p := i)).mpr ha
      omega
    · omega
  simp [hφj]

lemma signInsertSomeProd_eq_prod_fin (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length)
    (i : Fin φs.length.succ) (j : φsΛ.uncontracted) (hφj : (𝓕 |>ₛ φ) = (𝓕 |>ₛ φs[j.1]))
    (hg : GradingCompliant φs φsΛ) :
  φsΛ.signInsertSomeProd φ φs i j =
    ∏ (x : Fin φs.length),
      if h : (φsΛ.getDual? x).isSome then
          if x < j ∧ (i.succAbove x < i ∧ i < i.succAbove ((φsΛ.getDual? x).get h)
            ∨ j < ((φsΛ.getDual? x).get h) ∧ ¬ i.succAbove x < i)
          then 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs[x.1])
          else 1
      else 1 := by
  rw [signInsertSomeProd_eq_prod_prod]
  rw [Finset.prod_sigma']
  erw [← φsΛ.sigmaContractedEquiv.symm.prod_comp]
  let e2 : Fin φs.length ≃ {x // (φsΛ.getDual? x).isSome} ⊕ {x // ¬ (φsΛ.getDual? x).isSome} := by
    exact (Equiv.sumCompl fun a => (φsΛ.getDual? a).isSome = true).symm
  rw [← e2.symm.prod_comp]
  simp only [instCommGroup.eq_1, Fin.getElem_fin, Fintype.prod_sum_type]
  conv_rhs =>
    rhs
    enter [2, a]
    rw [dif_neg (by simpa [e2] using a.2)]
  conv_rhs =>
    lhs
    enter [2, a]
    rw [dif_pos (by simpa [e2] using a.2)]
  simp only [Nat.succ_eq_add_one, not_lt, Equiv.symm_symm, Equiv.sumCompl_apply_inl,
    Finset.prod_const_one, mul_one, e2]
  rfl
  simp only [hφj, Fin.getElem_fin]
  exact hg

lemma signInsertSomeProd_eq_finset (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length)
    (i : Fin φs.length.succ) (j : φsΛ.uncontracted) (hφj : (𝓕 |>ₛ φ) = (𝓕 |>ₛ φs[j.1]))
    (hg : GradingCompliant φs φsΛ) :
    φsΛ.signInsertSomeProd φ φs i j =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨φs.get, (Finset.univ.filter (fun x => (φsΛ.getDual? x).isSome ∧
      ∀ (h : (φsΛ.getDual? x).isSome),
      x < j ∧ (i.succAbove x < i ∧ i < i.succAbove ((φsΛ.getDual? x).get h)
      ∨ j < ((φsΛ.getDual? x).get h) ∧ ¬ i.succAbove x < i)))⟩) := by
  rw [signInsertSomeProd_eq_prod_fin]
  rw [ofFinset_eq_prod]
  rw [map_prod]
  congr
  funext x
  split
  · rename_i h
    simp only [Nat.succ_eq_add_one, not_lt, instCommGroup.eq_1, Finset.mem_filter, Finset.mem_univ,
      h, forall_true_left, true_and, Fin.getElem_fin]
    split
    · rename_i h1
      simp
    · rename_i h1
      simp
  · rename_i h
    simp [h]
  simp only [hφj, Fin.getElem_fin]
  exact hg

lemma signInsertSomeCoef_if (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp) (φsΛ : WickContraction φs.length)
    (i : Fin φs.length.succ) (j : φsΛ.uncontracted) (hφj : (𝓕 |>ₛ φ) = (𝓕 |>ₛ φs[j.1])) :
    φsΛ.signInsertSomeCoef φ φs i j =
    if i < i.succAbove j then
      𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨(φs.insertIdx i φ).get,
      (signFinset (φsΛ ↩Λ φ i (some j)) (finCongr (insertIdx_length_fin φ φs i).symm i)
      (finCongr (insertIdx_length_fin φ φs i).symm (i.succAbove j)))⟩)
    else
      𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨(φs.insertIdx i φ).get,
      signFinset (φsΛ ↩Λ φ i (some j))
      (finCongr (insertIdx_length_fin φ φs i).symm (i.succAbove j))
      (finCongr (insertIdx_length_fin φ φs i).symm i)⟩) := by
  simp only [signInsertSomeCoef, instCommGroup.eq_1, Nat.succ_eq_add_one,
    insertAndContract_sndFieldOfContract_some_incl, finCongr_apply, Fin.getElem_fin,
    insertAndContract_fstFieldOfContract_some_incl]
  split
  · simp [hφj]
  · simp [hφj]

lemma stat_signFinset_insert_some_self_fst
    (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp) (φsΛ : WickContraction φs.length)
    (i : Fin φs.length.succ) (j : φsΛ.uncontracted) :
  (𝓕 |>ₛ ⟨(φs.insertIdx i φ).get,
    (signFinset (φsΛ ↩Λ φ i (some j)) (finCongr (insertIdx_length_fin φ φs i).symm i)
      (finCongr (insertIdx_length_fin φ φs i).symm (i.succAbove j)))⟩) =
  𝓕 |>ₛ ⟨φs.get,
    (Finset.univ.filter (fun x => i < i.succAbove x ∧ x < j ∧ ((φsΛ.getDual? x = none) ∨
      ∀ (h : (φsΛ.getDual? x).isSome), i < i.succAbove ((φsΛ.getDual? x).get h))))⟩ := by
  rw [get_eq_insertIdx_succAbove φ _ i]
  rw [ofFinset_finset_map]
  swap
  refine
    (Equiv.comp_injective i.succAbove (finCongr (Eq.symm (insertIdx_length_fin φ φs i)))).mpr ?hi.a
  exact Fin.succAbove_right_injective
  congr
  ext x
  simp only [Nat.succ_eq_add_one, signFinset, finCongr_apply, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_map, Function.Embedding.coeFn_mk, Function.comp_apply]
  rcases insert_fin_eq_self φ i x with hx | hx
  · subst hx
    simp only [Nat.succ_eq_add_one, lt_self_iff_false, insertAndContract_some_getDual?_self_eq,
      reduceCtorEq, Option.isSome_some, Option.get_some, forall_const, false_or, and_self,
      false_and, false_iff, not_exists, not_and, and_imp]
    intro x hi hx h
    simp only [Fin.ext_iff, Fin.val_cast]
    simp only [Fin.val_eq_val]
    exact Fin.succAbove_ne i x
  · obtain ⟨x, hx⟩ := hx
    subst hx
    by_cases h : x = j.1
    · subst h
      simp only [Nat.succ_eq_add_one, lt_self_iff_false, insertAndContract_some_getDual?_some_eq,
        reduceCtorEq, Option.isSome_some, Option.get_some, imp_false, not_true_eq_false, or_self,
        and_self, and_false, false_iff, not_exists, not_and, and_imp]
      intro x hi hx h0
      simp only [Fin.ext_iff, Fin.val_cast]
      simp only [Fin.val_eq_val]
      rw [Function.Injective.eq_iff]
      omega
      exact Fin.succAbove_right_injective
    · simp only [Nat.succ_eq_add_one, ne_eq, h, not_false_eq_true,
        insertAndContract_some_succAbove_getDual?_eq_option, Option.map_eq_none_iff,
        Option.isSome_map]
      rw [Fin.lt_def, Fin.lt_def]
      simp only [Fin.val_cast, Fin.val_fin_lt]
      apply Iff.intro
      · intro h
        use x
        simp only [h, true_and, and_true]
        simp only [Option.get_map, Function.comp_apply] at h
        apply And.intro (Fin.succAbove_lt_succAbove_iff.mp h.2.1)
        have h2 := h.2.2
        rcases h2 with h2 | h2
        · simp [h2]
        · apply Or.inr
          intro h
          have h2 := h2 h
          simpa using h2
      · intro h
        obtain ⟨y, hy1, hy2⟩ := h
        simp only [Fin.ext_iff, Fin.val_cast] at hy2
        simp only [Fin.val_eq_val] at hy2
        rw [Function.Injective.eq_iff (Fin.succAbove_right_injective)] at hy2
        subst hy2
        simp only [hy1, true_and]
        apply And.intro
        · rw [@Fin.succAbove_lt_succAbove_iff]
          omega
        · have hy2 := hy1.2.2
          rcases hy2 with hy2 | hy2
          · simp [hy2]
          · apply Or.inr
            intro h
            have hy2 := hy2 h
            simpa [Option.get_map] using hy2

lemma stat_signFinset_insert_some_self_snd (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (j : φsΛ.uncontracted) :
    (𝓕 |>ₛ ⟨(φs.insertIdx i φ).get,
    (signFinset (φsΛ ↩Λ φ i (some j))
      (finCongr (insertIdx_length_fin φ φs i).symm (i.succAbove j))
      (finCongr (insertIdx_length_fin φ φs i).symm i))⟩) =
    𝓕 |>ₛ ⟨φs.get,
    (Finset.univ.filter (fun x => j < x ∧ i.succAbove x < i ∧ ((φsΛ.getDual? x = none) ∨
      ∀ (h : (φsΛ.getDual? x).isSome), j < ((φsΛ.getDual? x).get h))))⟩ := by
  rw [get_eq_insertIdx_succAbove φ _ i, ofFinset_finset_map]
  swap
  refine
    (Equiv.comp_injective i.succAbove (finCongr (Eq.symm (insertIdx_length_fin φ φs i)))).mpr ?hi.a
  exact Fin.succAbove_right_injective
  congr
  ext x
  simp only [Nat.succ_eq_add_one, signFinset, finCongr_apply, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_map, Function.Embedding.coeFn_mk, Function.comp_apply]
  rcases insert_fin_eq_self φ i x with hx | hx
  · subst hx
    simp only [Nat.succ_eq_add_one, lt_self_iff_false, insertAndContract_some_getDual?_self_eq,
      reduceCtorEq, Option.isSome_some, Option.get_some, imp_false, not_true_eq_false, or_self,
      and_self, and_false, false_iff, not_exists, not_and, and_imp]
    intro x hi hx h
    simp only [Fin.ext_iff, Fin.val_cast]
    simp only [Fin.val_eq_val]
    exact Fin.succAbove_ne i x
  · obtain ⟨x, hx⟩ := hx
    subst hx
    by_cases h : x = j.1
    · subst h
      simp only [Nat.succ_eq_add_one, lt_self_iff_false, insertAndContract_some_getDual?_some_eq,
        reduceCtorEq, Option.isSome_some, Option.get_some, forall_const, false_or, and_self,
        false_and, false_iff, not_exists, not_and, and_imp]
      intro x hi hx h0
      simp only [Fin.ext_iff, Fin.val_cast]
      simp only [Fin.val_eq_val]
      rw [Function.Injective.eq_iff]
      omega
      exact Fin.succAbove_right_injective
    · simp only [Nat.succ_eq_add_one, ne_eq, h, not_false_eq_true,
        insertAndContract_some_succAbove_getDual?_eq_option, Option.map_eq_none_iff,
        Option.isSome_map]
      rw [Fin.lt_def, Fin.lt_def]
      simp only [Fin.val_cast, Fin.val_fin_lt]
      apply Iff.intro
      · intro h
        use x
        simp only [h, true_and, and_true]
        simp only [Option.get_map, Function.comp_apply] at h
        apply And.intro (Fin.succAbove_lt_succAbove_iff.mp h.1)
        have h2 := h.2.2
        rcases h2 with h2 | h2
        · simp [h2]
        · apply Or.inr
          intro h
          have h2 := h2 h
          rw [Fin.lt_def] at h2
          simp only [Fin.val_cast, Fin.val_fin_lt] at h2
          exact Fin.succAbove_lt_succAbove_iff.mp h2
      · intro h
        obtain ⟨y, hy1, hy2⟩ := h
        simp only [Fin.ext_iff, Fin.val_cast] at hy2
        simp only [Fin.val_eq_val] at hy2
        rw [Function.Injective.eq_iff (Fin.succAbove_right_injective)] at hy2
        subst hy2
        simp only [hy1, true_and]
        apply And.intro
        · rw [@Fin.succAbove_lt_succAbove_iff]
          omega
        · have hy2 := hy1.2.2
          rcases hy2 with hy2 | hy2
          · simp [hy2]
          · apply Or.inr
            intro h
            have hy2 := hy2 h
            simp only [Fin.lt_def, Fin.val_cast, gt_iff_lt]
            simp only [Option.get_map, Function.comp_apply, Fin.val_cast, Fin.val_fin_lt]
            exact Fin.succAbove_lt_succAbove_iff.mpr hy2

lemma signInsertSomeCoef_eq_finset (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (j : φsΛ.uncontracted)
    (hφj : (𝓕 |>ₛ φ) = (𝓕 |>ₛ φs[j.1])) : φsΛ.signInsertSomeCoef φ φs i j =
    if i < i.succAbove j then
      𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨φs.get,
      (Finset.univ.filter (fun x => i < i.succAbove x ∧ x < j ∧ ((φsΛ.getDual? x = none) ∨
        ∀ (h : (φsΛ.getDual? x).isSome), i < i.succAbove ((φsΛ.getDual? x).get h))))⟩)
    else
      𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨φs.get,
        (Finset.univ.filter (fun x => j < x ∧ i.succAbove x < i ∧ ((φsΛ.getDual? x = none) ∨
        ∀ (h : (φsΛ.getDual? x).isSome), j < ((φsΛ.getDual? x).get h))))⟩) := by
  rw [signInsertSomeCoef_if, stat_signFinset_insert_some_self_snd,
    stat_signFinset_insert_some_self_fst]
  simp [hφj]

/--
The following two signs are equal for `i.succAbove k < i`. The sign `signInsertSome φ φs φsΛ i k`
which is constructed as follows:
1a. For each contracted pair `{a1, a2}` in `φsΛ` with `a1 < a2` the sign
  `𝓢(φ, φₐ₂)` if `a₁ < i ≤ a₂` and `a₁ < k`.
1b. For each contracted pair `{a1, a2}` in `φsΛ` with `a1 < a2` the sign
  `𝓢(φⱼ, φₐ₂)` if `a₁ < k < a₂` and `i < a₁`.
1c. For each field `φₐ` in `φₖ₊₁…φᵢ₋₁` without a dual at position `< k`
  the sign `𝓢(φₐ, φᵢ)`.
and the sign constructed as follows:
2a. For each uncontracted field `φₐ` in `φ₀…φₖ` in `φsΛ` the sign `𝓢(φ, φₐ)`
2b. For each field in `φₐ` in `φ₀…φᵢ₋₁` the sign `𝓢(φ, φₐ)`.

The outline of why this is true can be got by considering contributions of fields.
- `φₐ`, `i ≤ a`. No contributions.
- `φₖ`, `k -> 2a`, `k -> 2b`
- `φₐ`, `a ≤ k` uncontracted `a -> 2a`, `a -> 2b`.
- `φₐ`, `k < a < i` uncontracted `a -> 1c`, `a -> 2b`.

For contracted fields `{a₁, a₂}` in `φsΛ` with `a₁ < a₂` we have the following cases:
- `φₐ₁` `φₐ₂` `a₁ < a₂ < k < i`, `a₁ -> 2b`, `a₂ -> 2b`,
- `φₐ₁` `φₐ₂` `a₁ < k < a₂ < i`, `a₁ -> 2b`, `a₂ -> 2b`,
- `φₐ₁` `φₐ₂` `a₁ < k < i ≤ a₂`, `a₁ -> 2b`, `a₂ -> 1a`
- `φₐ₁` `φₐ₂` `k < a₁ < a₂ < i`, `a₁ -> 2b`, `a₂ -> 2b`, `a₁ -> 1c`, `a₂ -> 1c`
- `φₐ₁` `φₐ₂` `k < a₁ < i ≤ a₂ `,`a₁ -> 2b`, `a₁ -> 1c`
- `φₐ₁` `φₐ₂` `k < i ≤ a₁ < a₂ `, No contributions.
-/
lemma signInsertSome_mul_filter_contracted_of_lt (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (k : φsΛ.uncontracted)
    (hk : i.succAbove k < i) (hg : GradingCompliant φs φsΛ ∧ (𝓕 |>ₛ φ) = 𝓕 |>ₛ φs[k.1]) :
    signInsertSome φ φs φsΛ i k *
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨φs.get, φsΛ.uncontracted.filter (fun x => x ≤ ↑k)⟩)
    = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨φs.get, Finset.univ.filter (fun x => i.succAbove x < i)⟩) := by
  rw [signInsertSome, signInsertSomeProd_eq_finset (hφj := hg.2) (hg := hg.1),
    signInsertSomeCoef_eq_finset (hφj := hg.2), if_neg (by omega), ← map_mul, ← map_mul]
  congr 1
  rw [mul_eq_iff_eq_mul, ofFinset_union_disjoint]
  swap
  · /- Disjointness needed for `ofFinset_union_disjoint`. -/
    rw [Finset.disjoint_filter]
    intro j _ h
    simp only [Nat.succ_eq_add_one, not_lt, not_and, not_forall, not_or, not_le]
    intro h1
    use h1
    omega
  rw [ofFinset_union, ← mul_eq_one_iff, ofFinset_union]
  simp only [Nat.succ_eq_add_one, not_lt]
  apply stat_ofFinset_eq_one_of_gradingCompliant _ _ _ hg.1
  · /- The `c.getDual? i = none` case for `stat_ofFinset_eq_one_of_gradingCompliant`. -/
    intro j hn
    simp only [uncontracted, Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      hn, Option.isSome_none, Bool.false_eq_true, IsEmpty.forall_iff, or_self, and_true, or_false,
      true_and, and_self, Finset.mem_inter, not_and, not_lt, Classical.not_imp, not_le, and_imp]
    intro h
    rcases h with h | h
    · simp only [h, or_true, isEmpty_Prop, not_le, IsEmpty.forall_iff, and_self]
    · simp only [h, true_and]
      refine And.intro ?_ (And.intro ?_ h.2)
      · by_contra hkj
        simp only [not_lt] at hkj
        have h2 := h.2 hkj
        apply Fin.ne_succAbove i j
        have hij : i.succAbove j ≤ i.succAbove k.1 := Fin.succAbove_le_succAbove_iff.mpr hkj
        omega
      · have h1' := h.1
        rcases h1' with h1' | h1'
        · have hl := h.2 h1'
          have hij : i.succAbove j ≤ i.succAbove k.1 := Fin.succAbove_le_succAbove_iff.mpr h1'
          by_contra hn
          apply Fin.ne_succAbove i j
          omega
        · exact h1'
  · /- The `(c.getDual? i).isSome` case for `stat_ofFinset_eq_one_of_gradingCompliant`. -/
    intro j hj
    have hn : ¬ φsΛ.getDual? j = none := Option.isSome_iff_ne_none.mp hj
    simp only [uncontracted, Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      hn, hj, forall_true_left, false_or, true_and, and_false, false_and, Finset.mem_inter,
      not_false_eq_true, and_true, not_and, not_lt, getDual?_getDual?_get_get, reduceCtorEq,
      Option.isSome_some, Option.get_some, forall_const, and_imp]
    intro h1 h2
    have hijsucc' : i.succAbove ((φsΛ.getDual? j).get hj) ≠ i := Fin.succAbove_ne i _
    have hkneqj : ↑k ≠ j := by
      by_contra hkj
      have hk := k.prop
      simp only [uncontracted, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      simp_all
    have hkneqgetdual : k.1 ≠ (φsΛ.getDual? j).get hj := by
      by_contra hkj
      have hk := k.prop
      simp only [uncontracted, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      simp_all
    by_cases hik : ↑k < j
    · have hn : ¬ j < ↑k := by omega
      simp only [hik, true_and, hn, false_and, or_false, and_imp, and_true] at h1 h2 ⊢
      have hir : i.succAbove j < i := by
        rcases h1 with h1 | h1
        · simp [h1]
        · simp [h1]
      simp only [hir, true_and, or_true, forall_const] at h1 h2
      have hnkdual : ¬ ↑k < (φsΛ.getDual? j).get hj := by
        by_contra hn
        have h2 := h2 hn
        apply Fin.ne_succAbove i j
        omega
      simp only [hnkdual, IsEmpty.forall_iff, false_and, false_or, and_imp] at h2 ⊢
      have hnkdual : (φsΛ.getDual? j).get hj < ↑k := by omega
      have hi : i.succAbove ((φsΛ.getDual? j).get hj) < i.succAbove k := by
        rw [@Fin.succAbove_lt_succAbove_iff]
        omega
      omega
    · have ht : j < ↑k := by omega
      have ht' : i.succAbove j < i.succAbove k := by
        rw [@Fin.succAbove_lt_succAbove_iff]
        omega
      simp only [hik, false_and, ht, true_and, false_or, and_false, or_false, and_imp] at h1 h2 ⊢
      by_cases hik : i.succAbove j < i
      · simp_all only [Fin.getElem_fin, ne_eq, not_lt, true_and, or_true]
        have hn : ¬ i ≤ i.succAbove j := by omega
        simp_all only [and_false, or_false, imp_false, not_lt, Nat.succ_eq_add_one, not_le]
        apply And.intro
        · apply Or.inr
          omega
        · intro h1 h2 h3
          omega
      · simp_all only [Fin.getElem_fin, ne_eq, not_lt, false_and, false_or, or_false, and_self,
        or_true, imp_self]
        omega

/--
The following two signs are equal for `i < i.succAbove k`.
The sign `signInsertSome φ φs φsΛ i k` which is constructed
as follows:
1a. For each contracted pair `{a1, a2}` in `φsΛ` with `a1 < a2` the sign
  `𝓢(φ, φₐ₂)` if `a₁ < i ≤ a₂` and `a₁ < k`.
1b. For each contracted pair `{a1, a2}` in `φsΛ` with `a1 < a2` the sign
  `𝓢(φⱼ, φₐ₂)` if `a₁ < k < a₂` and `i < a₁`.
1c. For each field `φₐ` in `φᵢ…φₖ₋₁` of `φs` without dual at position `< i` the sign
  `𝓢(φₐ, φⱼ)`.
and the sign constructed as follows:
2a. For each uncontracted field `φₐ` in `φ₀…φₖ₋₁` in `φsΛ` the sign `𝓢(φ, φₐ)`
2b. For each field in `φₐ` in `φ₀…φᵢ₋₁` the sign `𝓢(φ, φₐ)`.

The outline of why this is true can be got by considering contributions of fields.
- `φₐ`, `k < a`. No contributions.
- `φₖ`, No Contributes
- `φₐ`, `a < i` uncontracted `a -> 2a`, `a -> 2b`.
- `φₐ`, `i ≤ a < k` uncontracted `a -> 1c`, `a -> 2a`.

For contracted fields `{a₁, a₂}` in `φsΛ` with `a₁ < a₂` we have the following cases:
- `φₐ₁` `φₐ₂` `a₁ < a₂ < i ≤ k`, `a₁ -> 2b`, `a₂ -> 2b`
- `φₐ₁` `φₐ₂` `a₁ < i ≤ a₂ < k`, `a₁ -> 2b`, `a₂ -> 1a`
- `φₐ₁` `φₐ₂` `a₁ < i ≤ k < a₂`, `a₁ -> 2b`, `a₂ -> 1a`
- `φₐ₁` `φₐ₂` `i ≤ a₁ < a₂ < k`, `a₂ -> 1c`, `a₁ -> 1c`
- `φₐ₁` `φₐ₂` `i ≤ a₁ < k < a₂ `, `a₁ -> 1c`, `a₁ -> 1b`
- `φₐ₁` `φₐ₂` `i ≤ k ≤ a₁ < a₂ `, No contributions
-/
lemma signInsertSome_mul_filter_contracted_of_not_lt (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (k : φsΛ.uncontracted)
    (hk : ¬ i.succAbove k < i) (hg : GradingCompliant φs φsΛ ∧ (𝓕 |>ₛ φ) = 𝓕 |>ₛ φs[k.1]) :
    signInsertSome φ φs φsΛ i k *
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨φs.get, φsΛ.uncontracted.filter (fun x => x < ↑k)⟩)
    = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨φs.get, Finset.univ.filter (fun x => i.succAbove x < i)⟩) := by
  have hik : i.succAbove ↑k ≠ i := Fin.succAbove_ne i ↑k
  rw [signInsertSome, signInsertSomeProd_eq_finset (hφj := hg.2) (hg := hg.1),
    signInsertSomeCoef_eq_finset (hφj := hg.2), if_pos (by omega), ← map_mul, ← map_mul]
  congr 1
  rw [mul_eq_iff_eq_mul, ofFinset_union, ofFinset_union]
  apply (mul_eq_one_iff _ _).mp
  rw [ofFinset_union]
  simp only [Nat.succ_eq_add_one, not_lt]
  apply stat_ofFinset_eq_one_of_gradingCompliant _ _ _ hg.1
  · /- The `c.getDual? i = none` case for `stat_ofFinset_eq_one_of_gradingCompliant`. -/
    intro j hj
    have hijsucc : i.succAbove j ≠ i := Fin.succAbove_ne i j
    simp only [uncontracted, Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      hj, Option.isSome_none, Bool.false_eq_true, IsEmpty.forall_iff, or_self, and_true, true_and,
      and_false, or_false, Finset.mem_inter, not_false_eq_true, and_self, not_and, not_lt,
      Classical.not_imp, not_le, and_imp]
    intro h
    have hij : i < i.succAbove j := by
      rcases h with h | h
      · exact h.1
      · rcases h.1 with h1 | h1
        · omega
        · have hik : i.succAbove k.1 ≤ i.succAbove j := by
            rw [Fin.succAbove_le_succAbove_iff]
            omega
          omega
    simp only [hij, true_and] at h ⊢
    omega
  · /- The `(c.getDual? i).isSome` case for `stat_ofFinset_eq_one_of_gradingCompliant`. -/
    intro j hj
    have hn : ¬ φsΛ.getDual? j = none := Option.isSome_iff_ne_none.mp hj
    have hijSuc : i.succAbove j ≠ i := Fin.succAbove_ne i j
    have hkneqj : ↑k ≠ j := by
      by_contra hkj
      have hk := k.prop
      simp only [uncontracted, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      simp_all
    have hkneqgetdual : k.1 ≠ (φsΛ.getDual? j).get hj := by
      by_contra hkj
      have hk := k.prop
      simp only [uncontracted, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      simp_all
    simp only [uncontracted, Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      hn, hj, forall_true_left, false_or, true_and, Finset.mem_inter, not_and, not_or, not_lt,
      not_le, and_imp, and_false, false_and, not_false_eq_true, and_true, getDual?_getDual?_get_get,
      reduceCtorEq, Option.isSome_some, Option.get_some, forall_const]
    by_cases hik : ↑k < j
    · have hikn : ¬ j < k.1 := by omega
      have hksucc : i.succAbove k.1 < i.succAbove j := by
        rw [Fin.succAbove_lt_succAbove_iff]
        omega
      have hkn : i < i.succAbove j := by omega
      have hl : ¬ i.succAbove j < i := by omega
      simp only [hkn, hikn, false_and, and_false, hl, false_or, or_self, IsEmpty.forall_iff,
        imp_false, not_lt, true_and, implies_true, and_true, forall_const, hik,
        imp_forall_iff_forall]
    · have hikn : j < k.1 := by omega
      have hksucc : i.succAbove j < i.succAbove k.1 := Fin.succAbove_lt_succAbove_iff.mpr hikn
      simp only [hikn, true_and, forall_const, hik, false_and, or_false, IsEmpty.forall_iff,
        and_true]
      by_cases hij: i < i.succAbove j
      · simp only [hij, true_and, forall_const, and_true, imp_forall_iff_forall]
        have hijn : ¬ i.succAbove j < i := by omega
        simp only [hijn, false_and, false_or, IsEmpty.forall_iff, imp_false, not_lt, true_and,
          or_false, and_imp]
        have hijle : i ≤ i.succAbove j := by omega
        simp only [hijle, and_true, implies_true, forall_const]
        intro h1 h2
        apply And.intro
        · rcases h1 with h1 | h1
          · apply Or.inl
            omega
          · apply Or.inl
            have hi : i.succAbove k.1 < i.succAbove ((φsΛ.getDual? j).get hj) :=
              Fin.succAbove_lt_succAbove_iff.mpr h1
            apply And.intro
            · apply Or.inr
              apply And.intro
              · omega
              · omega
            · omega
        · intro h3 h4
          omega
      · simp only [hij, false_and, false_or, IsEmpty.forall_iff, and_true, forall_const, and_false,
        or_self, implies_true]
        have hijn : i.succAbove j < i := by omega
        have hijn' : ¬ i ≤ i.succAbove j := by omega
        simp only [hijn, true_and, hijn', and_false, or_false, or_true, imp_false, not_lt,
          forall_const]
        exact fun h => lt_of_le_of_ne h (Fin.succAbove_ne i ((φsΛ.getDual? j).get hj))

/--
For a list `φs = φ₀…φₙ` of `𝓕.FieldOp`, a Wick contraction `φsΛ` of `φs`, an element `φ` of
  `𝓕.FieldOp`, a `i ≤ φs.length` and a `k` in `φsΛ.uncontracted` such that `k<i`,
the sign of `φsΛ ↩Λ φ i (some k)` is equal to the product of
- the sign associated with moving `φ` through the `φsΛ`-uncontracted `FieldOp` in `φ₀…φₖ`,
- the sign associated with moving `φ` through all `FieldOp` in `φ₀…φᵢ₋₁`,
- the sign of `φsΛ`.

The proof of this result involves a careful consideration of the contributions of different
`FieldOp` in `φs` to the sign of `φsΛ ↩Λ φ i (some k)`.
-/
lemma sign_insert_some_of_lt (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (k : φsΛ.uncontracted)
    (hk : i.succAbove k < i) (hg : GradingCompliant φs φsΛ ∧ (𝓕 |>ₛ φ) = 𝓕 |>ₛ φs[k.1]) :
    (φsΛ ↩Λ φ i (some k)).sign =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨φs.get, φsΛ.uncontracted.filter (fun x => x ≤ ↑k)⟩)
    * 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨φs.get, Finset.univ.filter (fun x => i.succAbove x < i)⟩)
    * φsΛ.sign := by
  rw [sign_insert_some,
    ← signInsertSome_mul_filter_contracted_of_lt φ φs φsΛ i k hk hg]
  rw [← mul_assoc]
  congr 1
  rw [mul_comm, ← mul_assoc]
  simp

/--
For a list `φs = φ₀…φₙ` of `𝓕.FieldOp`, a Wick contraction `φsΛ` of `φs`, an element `φ` of
  `𝓕.FieldOp`, a `i ≤ φs.length` and a `k` in `φsΛ.uncontracted` such that `i ≤ k`,
the sign of `φsΛ ↩Λ φ i (some k)` is equal to the product of
- the sign associated with moving `φ` through the `φsΛ`-uncontracted `FieldOp` in `φ₀…φₖ₋₁`,
- the sign associated with moving `φ` through all the `FieldOp` in `φ₀…φᵢ₋₁`,
- the sign of `φsΛ`.

The proof of this result involves a careful consideration of the contributions of different
`FieldOp` in `φs` to the sign of `φsΛ ↩Λ φ i (some k)`.
-/
lemma sign_insert_some_of_not_lt (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (k : φsΛ.uncontracted)
    (hk : ¬ i.succAbove k < i) (hg : GradingCompliant φs φsΛ ∧ (𝓕 |>ₛ φ) = 𝓕 |>ₛ φs[k.1]) :
    (φsΛ ↩Λ φ i (some k)).sign =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨φs.get, φsΛ.uncontracted.filter (fun x => x < ↑k)⟩)
    * 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨φs.get, Finset.univ.filter (fun x => i.succAbove x < i)⟩) *
    φsΛ.sign := by
  rw [sign_insert_some,
    ← signInsertSome_mul_filter_contracted_of_not_lt φ φs φsΛ i k hk hg]
  rw [← mul_assoc]
  congr 1
  rw [mul_comm, ← mul_assoc]
  simp

/--
For a list `φs = φ₀…φₙ` of `𝓕.FieldOp`, a Wick contraction `φsΛ` of `φs`, an element `φ` of
  `𝓕.FieldOp`, and a `k` in `φsΛ.uncontracted`,
the sign of `φsΛ ↩Λ φ 0 (some k)` is equal to the product of
- the sign associated with moving `φ` through the `φsΛ`-uncontracted `FieldOp` in `φ₀…φₖ₋₁`,
- the sign of `φsΛ`.

This is a direct corollary of `sign_insert_some_of_not_lt`.
-/
lemma sign_insert_some_zero (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (k : φsΛ.uncontracted)
    (hn : GradingCompliant φs φsΛ ∧ (𝓕|>ₛφ) = 𝓕|>ₛφs[k.1]) :
    (φsΛ ↩Λ φ 0 k).sign = 𝓢(𝓕|>ₛφ, 𝓕 |>ₛ ⟨φs.get, (φsΛ.uncontracted.filter (fun x => x < ↑k))⟩) *
    φsΛ.sign := by
  rw [sign_insert_some_of_not_lt]
  · simp
  · simp
  · exact hn

end WickContraction
