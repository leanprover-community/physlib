/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.QFT.PerturbationTheory.WickContraction.Join
/-!

# Time contractions

-/

@[expose] public section

open FieldSpecification
variable {𝓕 : FieldSpecification}

namespace WickContraction
variable {n : ℕ} (c : WickContraction n)
open PhysLean.List
open WickAlgebra

/-- The condition on a Wick contraction which is true iff and only if every contraction
  is between two fields of equal time. -/
def EqTimeOnly {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length) : Prop :=
  ∀ (i j), {i, j} ∈ φsΛ.1 → timeOrderRel φs[i] φs[j]
noncomputable section

instance {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length) :
    Decidable (EqTimeOnly φsΛ) :=
    inferInstanceAs (Decidable (∀ (i j), {i, j} ∈ φsΛ.1 → timeOrderRel φs[i] φs[j]))

namespace EqTimeOnly
variable {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length)

lemma timeOrderRel_of_eqTimeOnly_pair {i j : Fin φs.length} (h : {i, j} ∈ φsΛ.1)
    (hc : EqTimeOnly φsΛ) :
    timeOrderRel φs[i] φs[j] := by
  have h' := hc
  simp only [EqTimeOnly, Fin.getElem_fin] at h'
  exact h' i j h

lemma timeOrderRel_both_of_eqTimeOnly {i j : Fin φs.length} (h : {i, j} ∈ φsΛ.1)
    (hc : EqTimeOnly φsΛ) :
    timeOrderRel φs[i] φs[j] ∧ timeOrderRel φs[j] φs[i] := by
  apply And.intro
  · exact timeOrderRel_of_eqTimeOnly_pair φsΛ h hc
  · apply timeOrderRel_of_eqTimeOnly_pair φsΛ _ hc
    rw [@Finset.pair_comm]
    exact h

lemma eqTimeOnly_iff_forall_finset {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length) :
    φsΛ.EqTimeOnly ↔ ∀ (a : φsΛ.1),
      timeOrderRel (φs[φsΛ.fstFieldOfContract a]) (φs[φsΛ.sndFieldOfContract a])
      ∧ timeOrderRel (φs[φsΛ.sndFieldOfContract a]) (φs[φsΛ.fstFieldOfContract a]) := by
  apply Iff.intro
  · intro h a
    apply timeOrderRel_both_of_eqTimeOnly φsΛ _ h
    rw [← finset_eq_fstFieldOfContract_sndFieldOfContract]
    simp
  · intro h
    simp only [EqTimeOnly, Fin.getElem_fin]
    intro i j h1
    have h' := h ⟨{i, j}, h1⟩
    by_cases hij: i < j
    · have hi : φsΛ.fstFieldOfContract ⟨{i, j}, h1⟩ = i := by
        apply eq_fstFieldOfContract_of_mem _ _ i j
        · simp
        · simp
        · exact hij
      have hj : φsΛ.sndFieldOfContract ⟨{i, j}, h1⟩ = j := by
        apply eq_sndFieldOfContract_of_mem _ _ i j
        · simp
        · simp
        · exact hij
      simp_all
    · have hij : i ≠ j := by
        by_contra hij
        subst hij
        have h2 := φsΛ.2.1 {i, i} h1
        simp at h2
      have hj : φsΛ.fstFieldOfContract ⟨{i, j}, h1⟩ = j := by
        apply eq_fstFieldOfContract_of_mem _ _ j i
        · simp
        · simp
        · omega
      have hi : φsΛ.sndFieldOfContract ⟨{i, j}, h1⟩ = i := by
        apply eq_sndFieldOfContract_of_mem _ _ j i
        · simp
        · simp
        · omega
      simp_all

@[simp]
lemma empty_mem {φs : List 𝓕.FieldOp} : empty (n := φs.length).EqTimeOnly := by
  rw [eqTimeOnly_iff_forall_finset]
  simp [empty]

/-- Let `φs` be a list of `𝓕.FieldOp` and `φsΛ` a `WickContraction` of `φs` within
  which every contraction involves two `𝓕.FieldOp`s that have the same time, then
  `φsΛ.staticContract = φsΛ.timeContract`. -/
lemma staticContract_eq_timeContract_of_eqTimeOnly (h : φsΛ.EqTimeOnly) :
    φsΛ.staticContract = φsΛ.timeContract := by
  simp only [staticContract, timeContract]
  apply congrArg
  funext a
  ext
  simp only [List.get_eq_getElem]
  rw [timeContract_of_timeOrderRel]
  apply timeOrderRel_of_eqTimeOnly_pair φsΛ
  rw [← finset_eq_fstFieldOfContract_sndFieldOfContract]
  exact a.2
  exact h

lemma eqTimeOnly_congr {φs φs' : List 𝓕.FieldOp} (h : φs = φs') (φsΛ : WickContraction φs.length) :
    (congr (by simp [h]) φsΛ).EqTimeOnly (φs := φs') ↔ φsΛ.EqTimeOnly := by
  subst h
  simp

lemma quotContraction_eqTimeOnly {φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length}
    (h : φsΛ.EqTimeOnly) (S : Finset (Finset (Fin φs.length))) (ha : S ⊆ φsΛ.1) :
    (φsΛ.quotContraction S ha).EqTimeOnly := by
  rw [eqTimeOnly_iff_forall_finset]
  intro a
  simp only [Fin.getElem_fin]
  erw [subContraction_uncontractedList_get]
  erw [subContraction_uncontractedList_get]
  simp only [quotContraction_fstFieldOfContract_uncontractedListEmd, Fin.getElem_fin,
    quotContraction_sndFieldOfContract_uncontractedListEmd]
  rw [eqTimeOnly_iff_forall_finset] at h
  apply h

lemma exists_join_singleton_of_card_ge_zero {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length)
    (h : 0 < φsΛ.1.card) (h1 : φsΛ.EqTimeOnly) :
    ∃ (i j : Fin φs.length) (h : i < j) (φsucΛ : WickContraction [singleton h]ᵘᶜ.length),
    φsΛ = join (singleton h) φsucΛ ∧ (timeOrderRel φs[i] φs[j] ∧ timeOrderRel φs[j] φs[i])
    ∧ φsucΛ.EqTimeOnly ∧ φsucΛ.1.card + 1 = φsΛ.1.card := by
  obtain ⟨a, ha⟩ := exists_contraction_pair_of_card_ge_zero φsΛ h
  use φsΛ.fstFieldOfContract ⟨a, ha⟩
  use φsΛ.sndFieldOfContract ⟨a, ha⟩
  use φsΛ.fstFieldOfContract_lt_sndFieldOfContract ⟨a, ha⟩
  let φsucΛ :
    WickContraction [singleton (φsΛ.fstFieldOfContract_lt_sndFieldOfContract ⟨a, ha⟩)]ᵘᶜ.length :=
    congr (by simp [← subContraction_singleton_eq_singleton])
    (φsΛ.quotContraction {a} (by simpa using ha))
  use φsucΛ
  simp only [Fin.getElem_fin]
  apply And.intro
  · have h1 := join_congr (subContraction_singleton_eq_singleton _ ⟨a, ha⟩).symm (φsucΛ := φsucΛ)
    simp only [h1, congr_trans_apply, congr_refl, φsucΛ]
    rw [join_sub_quot]
  · apply And.intro
    · apply timeOrderRel_both_of_eqTimeOnly φsΛ _ h1
      rw [← finset_eq_fstFieldOfContract_sndFieldOfContract]
      simp [ha]
    apply And.intro
    · simp only [φsucΛ]
      rw [eqTimeOnly_congr (φs := [(φsΛ.subContraction {a} (by simpa using ha))]ᵘᶜ)]
      exact quotContraction_eqTimeOnly h1 _ _
      rw [← subContraction_singleton_eq_singleton]
    · simp only [card_congr, φsucΛ]
      have h1 := subContraction_card_plus_quotContraction_card_eq _ {a} (by simpa using ha)
      simp only [subContraction, Finset.card_singleton] at h1
      omega

lemma timeOrder_timeContract_mul_of_eqTimeOnly_mid_induction {φs : List 𝓕.FieldOp}
    (φsΛ : WickContraction φs.length)
    (hl : φsΛ.EqTimeOnly) (a b: 𝓕.WickAlgebra) : (n : ℕ) → (hn : φsΛ.1.card = n) →
    𝓣(a * φsΛ.timeContract.1 * b) = φsΛ.timeContract.1 * 𝓣(a * b)
  | 0, hn => by
    rw [@card_zero_iff_empty] at hn
    subst hn
    simp
  | Nat.succ n, hn => by
    obtain ⟨i, j, hij, φsucΛ, rfl, h2, h3, h4⟩ :=
      exists_join_singleton_of_card_ge_zero φsΛ (by simp [hn]) hl
    rw [join_timeContract]
    rw [singleton_timeContract]
    simp only [Fin.getElem_fin, MulMemClass.coe_mul]
    trans timeOrder (a * WickAlgebra.timeContract φs[↑i] φs[↑j] * (φsucΛ.timeContract.1 * b))
    simp only [mul_assoc, Fin.getElem_fin]
    rw [timeOrder_timeContract_eq_time_mid]
    have ih := timeOrder_timeContract_mul_of_eqTimeOnly_mid_induction φsucΛ h3 a b n (by omega)
    rw [← mul_assoc, ih]
    simp only [Fin.getElem_fin, mul_assoc]
    simp_all only [Nat.succ_eq_add_one, Fin.getElem_fin, add_left_inj]
    simp_all

lemma timeOrder_timeContract_mul_of_eqTimeOnly_mid {φs : List 𝓕.FieldOp}
    (φsΛ : WickContraction φs.length)
    (hl : φsΛ.EqTimeOnly) (a b : 𝓕.WickAlgebra) :
    𝓣(a * φsΛ.timeContract.1 * b) = φsΛ.timeContract.1 * 𝓣(a * b) := by
  exact timeOrder_timeContract_mul_of_eqTimeOnly_mid_induction φsΛ hl a b φsΛ.1.card rfl

/-- Let `φs` be a list of `𝓕.FieldOp`, `φsΛ` a `WickContraction` of `φs` within
  which every contraction involves two `𝓕.FieldOp`s that have the same time and
  `b` a general element in `𝓕.WickAlgebra`. Then
  `𝓣(φsΛ.timeContract.1 * b) = φsΛ.timeContract.1 * 𝓣(b)`.

  This follows from properties of orderings and the ideal defining `𝓕.WickAlgebra`. -/
lemma timeOrder_timeContract_mul_of_eqTimeOnly_left {φs : List 𝓕.FieldOp}
    (φsΛ : WickContraction φs.length)
    (hl : φsΛ.EqTimeOnly) (b : 𝓕.WickAlgebra) :
    𝓣(φsΛ.timeContract.1 * b) = φsΛ.timeContract.1 * 𝓣(b) := by
  trans 𝓣(1 * φsΛ.timeContract.1 * b)
  simp only [one_mul]
  rw [timeOrder_timeContract_mul_of_eqTimeOnly_mid φsΛ hl]
  simp

set_option maxHeartbeats 400000 in
lemma exists_join_singleton_of_not_eqTimeOnly {φs : List 𝓕.FieldOp}
    (φsΛ : WickContraction φs.length) (h1 : ¬ φsΛ.EqTimeOnly) :
    ∃ (i j : Fin φs.length) (h : i < j) (φsucΛ : WickContraction [singleton h]ᵘᶜ.length),
    φsΛ = join (singleton h) φsucΛ ∧ (¬ timeOrderRel φs[i] φs[j] ∨ ¬ timeOrderRel φs[j] φs[i]) := by
  rw [eqTimeOnly_iff_forall_finset] at h1
  simp only [Fin.getElem_fin, Subtype.forall, not_forall, not_and] at h1
  obtain ⟨a, ha, hr⟩ := h1
  use φsΛ.fstFieldOfContract ⟨a, ha⟩
  use φsΛ.sndFieldOfContract ⟨a, ha⟩
  use φsΛ.fstFieldOfContract_lt_sndFieldOfContract ⟨a, ha⟩
  let φsucΛ :
    WickContraction [singleton (φsΛ.fstFieldOfContract_lt_sndFieldOfContract ⟨a, ha⟩)]ᵘᶜ.length :=
    congr (by simp [← subContraction_singleton_eq_singleton])
      (φsΛ.quotContraction {a} (by simpa using ha))
  use φsucΛ
  simp only [Fin.getElem_fin]
  apply And.intro
  · have h1 := join_congr (subContraction_singleton_eq_singleton _ ⟨a, ha⟩).symm (φsucΛ := φsucΛ)
    simp only [h1, congr_trans_apply, congr_refl, φsucΛ]
    rw [join_sub_quot]
  · by_cases h1 : timeOrderRel φs[↑(φsΛ.fstFieldOfContract ⟨a, ha⟩)]
      φs[↑(φsΛ.sndFieldOfContract ⟨a, ha⟩)]
    · simp_all
    · simp_all

lemma timeOrder_timeContract_of_not_eqTimeOnly {φs : List 𝓕.FieldOp}
    (φsΛ : WickContraction φs.length)
    (hl : ¬ φsΛ.EqTimeOnly) : 𝓣(φsΛ.timeContract.1) = 0 := by
  obtain ⟨i, j, hij, φsucΛ, rfl, hr⟩ := exists_join_singleton_of_not_eqTimeOnly φsΛ hl
  rw [join_timeContract]
  rw [singleton_timeContract]
  simp only [Fin.getElem_fin, MulMemClass.coe_mul]
  rw [timeOrder_timeOrder_left]
  rw [timeOrder_timeContract_ne_time]
  simp only [zero_mul, map_zero]
  simp_all only [Fin.getElem_fin, not_and]
  intro h
  simp_all

/-- Let `φs` be a list of `𝓕.FieldOp` and `φsΛ` a `WickContraction` with
  at least one contraction between `𝓕.FieldOp` that do not have the same time. Then
  `𝓣(φsΛ.staticContract.1) = 0`. -/
lemma timeOrder_staticContract_of_not_mem {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length)
    (hl : ¬ φsΛ.EqTimeOnly) : 𝓣(φsΛ.staticContract.1) = 0 := by
  obtain ⟨i, j, hij, φsucΛ, rfl, hr⟩ := exists_join_singleton_of_not_eqTimeOnly φsΛ hl
  rw [join_staticContract]
  simp only [MulMemClass.coe_mul]
  rw [singleton_staticContract]
  rw [timeOrder_timeOrder_left]
  rw [timeOrder_superCommute_anPart_ofFieldOp_ne_time]
  simp only [zero_mul, map_zero]
  intro h
  simp_all

end EqTimeOnly

/-- The condition on a Wick contraction which is true if it has at least one contraction
  which is between two equal time fields. -/
def HaveEqTime {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length) : Prop :=
  ∃ (i j : Fin φs.length) (h : {i, j} ∈ φsΛ.1),
  timeOrderRel φs[i] φs[j] ∧ timeOrderRel φs[j] φs[i]

noncomputable instance {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length) :
    Decidable (HaveEqTime φsΛ) :=
  inferInstanceAs (Decidable (∃ (i j : Fin φs.length)
    (h : ({i, j} : Finset (Fin φs.length)) ∈ φsΛ.1),
    timeOrderRel φs[i] φs[j] ∧ timeOrderRel φs[j] φs[i]))

lemma haveEqTime_iff_finset {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length) :
    HaveEqTime φsΛ ↔ ∃ (a : Finset (Fin φs.length)) (h : a ∈ φsΛ.1),
      timeOrderRel φs[φsΛ.fstFieldOfContract ⟨a, h⟩] φs[φsΛ.sndFieldOfContract ⟨a, h⟩]
    ∧ timeOrderRel φs[φsΛ.sndFieldOfContract ⟨a, h⟩] φs[φsΛ.fstFieldOfContract ⟨a, h⟩] := by
  simp only [HaveEqTime, Fin.getElem_fin, exists_and_left, exists_prop]
  apply Iff.intro
  · intro h
    obtain ⟨i, j, hij, h1, h2⟩ := h
    use {i, j}, h1
    by_cases hij : i < j
    · have h1n := eq_fstFieldOfContract_of_mem φsΛ ⟨{i,j}, h1⟩ i j (by simp) (by simp) hij
      have h2n := eq_sndFieldOfContract_of_mem φsΛ ⟨{i,j}, h1⟩ i j (by simp) (by simp) hij
      simp only [h1n, h2n]
      simp_all only [true_and]
    · have hineqj : i ≠ j := by
        by_contra hineqj
        subst hineqj
        have h2 := φsΛ.2.1 {i, i} h1
        simp_all
      have hji : j < i := by omega
      have h1n := eq_fstFieldOfContract_of_mem φsΛ ⟨{i,j}, h1⟩ j i (by simp) (by simp) hji
      have h2n := eq_sndFieldOfContract_of_mem φsΛ ⟨{i,j}, h1⟩ j i (by simp) (by simp) hji
      simp only [h1n, h2n]
      simp_all
  · intro h
    obtain ⟨a, h1, h2, h3⟩ := h
    use φsΛ.fstFieldOfContract ⟨a, h1⟩
    use φsΛ.sndFieldOfContract ⟨a, h1⟩
    simp_all only [and_true, true_and]
    rw [← finset_eq_fstFieldOfContract_sndFieldOfContract]
    exact h1

@[simp]
lemma empty_not_haveEqTime {φs : List 𝓕.FieldOp} :
    ¬ HaveEqTime (empty : WickContraction φs.length) := by
  rw [haveEqTime_iff_finset]
  simp [empty]

/-- Given a Wick contraction the subset of contracted pairs between equal time fields. -/
def eqTimeContractSet {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length) :
    Finset (Finset (Fin φs.length)) :=
  Finset.univ.filter (fun a =>
    a ∈ φsΛ.1 ∧ ∀ (h : a ∈ φsΛ.1),
    timeOrderRel φs[φsΛ.fstFieldOfContract ⟨a, h⟩] φs[φsΛ.sndFieldOfContract ⟨a, h⟩]
    ∧ timeOrderRel φs[φsΛ.sndFieldOfContract ⟨a, h⟩] φs[φsΛ.fstFieldOfContract ⟨a, h⟩])

lemma eqTimeContractSet_subset {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length) :
    eqTimeContractSet φsΛ ⊆ φsΛ.1 := by
  simp only [eqTimeContractSet, Fin.getElem_fin]
  intro a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_imp]
  intro h _
  exact h

lemma mem_of_mem_eqTimeContractSet{φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length}
    {a : Finset (Fin φs.length)} (h : a ∈ eqTimeContractSet φsΛ) : a ∈ φsΛ.1 := by
  simp only [eqTimeContractSet, Fin.getElem_fin, Finset.mem_filter, Finset.mem_univ, true_and] at h
  exact h.1

lemma join_eqTimeContractSet {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) :
    eqTimeContractSet (join φsΛ φsucΛ) = φsΛ.eqTimeContractSet ∪
    φsucΛ.eqTimeContractSet.map (Finset.mapEmbedding uncontractedListEmd).toEmbedding := by
  ext a
  apply Iff.intro
  · intro h
    have hmem := mem_of_mem_eqTimeContractSet h
    have ht := joinLiftLeft_or_joinLiftRight_of_mem_join (φsucΛ := φsucΛ) _ hmem
    rcases ht with ht | ht
    · obtain ⟨b, rfl⟩ := ht
      simp only [Finset.le_eq_subset, Finset.mem_union, Finset.mem_map,
        RelEmbedding.coe_toEmbedding]
      left
      simp only [eqTimeContractSet, Fin.getElem_fin, Finset.mem_filter, Finset.mem_univ, true_and]
      apply And.intro (by simp [joinLiftLeft])
      intro h'
      simp only [eqTimeContractSet, Fin.getElem_fin, Finset.mem_filter, Finset.mem_univ,
        Finset.coe_mem, Subtype.coe_eta, join_fstFieldOfContract_joinLiftLeft,
        join_sndFieldOfContract_joinLift, forall_true_left, true_and] at h
      exact h
    · obtain ⟨b, rfl⟩ := ht
      simp only [Finset.le_eq_subset, Finset.mem_union, Finset.mem_map,
        RelEmbedding.coe_toEmbedding]
      right
      use b
      rw [Finset.mapEmbedding_apply]
      simp only [joinLiftRight, and_true]
      simpa [eqTimeContractSet] using h
  · intro h
    simp only [Finset.le_eq_subset, Finset.mem_union, Finset.mem_map,
      RelEmbedding.coe_toEmbedding] at h
    rcases h with h | h
    · simp only [eqTimeContractSet, Fin.getElem_fin, Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [eqTimeContractSet, Fin.getElem_fin, Finset.mem_filter, Finset.mem_univ,
        true_and] at h
      apply And.intro
      · simp [join, h.1]
      · intro h'
        have h2 := h.2 h.1
        exact h2
    · simp only [eqTimeContractSet, Fin.getElem_fin, Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [eqTimeContractSet, Fin.getElem_fin, Finset.mem_filter, Finset.mem_univ,
        true_and] at h
      obtain ⟨b, h1, h2, rfl⟩ := h
      apply And.intro
      · simp [join, h1]
      · intro h'
        have h2 := h1.2 h1.1
        have hj : ⟨(Finset.mapEmbedding uncontractedListEmd) b, h'⟩
          = joinLiftRight ⟨b, h1.1⟩ := by rfl
        simp only [hj, join_fstFieldOfContract_joinLiftRight, getElem_uncontractedListEmd,
          join_sndFieldOfContract_joinLiftRight]
        simpa using h2

lemma eqTimeContractSet_of_not_haveEqTime {φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length}
    (h : ¬ HaveEqTime φsΛ) : eqTimeContractSet φsΛ = ∅ := by
  ext a
  simp only [Finset.notMem_empty, iff_false]
  by_contra hn
  rw [haveEqTime_iff_finset] at h
  simp only [Fin.getElem_fin, not_exists, not_and] at h
  simp only [eqTimeContractSet, Fin.getElem_fin, Finset.mem_filter, Finset.mem_univ, true_and] at hn
  have h2 := hn.2 hn.1
  simp_all

lemma eqTimeContractSet_of_mem_eqTimeOnly {φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length}
    (h : φsΛ.EqTimeOnly) : eqTimeContractSet φsΛ = φsΛ.1 := by
  ext a
  simp only [eqTimeContractSet, Fin.getElem_fin, Finset.mem_filter, Finset.mem_univ, true_and,
    and_iff_left_iff_imp, imp_forall_iff_forall]
  rw [EqTimeOnly.eqTimeOnly_iff_forall_finset] at h
  exact fun h_1 => h ⟨a, h_1⟩

lemma subContraction_eqTimeContractSet_eqTimeOnly {φs : List 𝓕.FieldOp}
    (φsΛ : WickContraction φs.length) :
    (φsΛ.subContraction (eqTimeContractSet φsΛ) (eqTimeContractSet_subset φsΛ)).EqTimeOnly := by
  rw [EqTimeOnly.eqTimeOnly_iff_forall_finset]
  intro a
  have ha2 := a.2
  simp only [subContraction, eqTimeContractSet, Fin.getElem_fin, Finset.mem_filter, Finset.mem_univ,
    true_and] at ha2
  simp only [subContraction_fstFieldOfContract, Fin.getElem_fin, subContraction_sndFieldOfContract]
  exact ha2.2 ha2.1

lemma pair_mem_eqTimeContractSet_iff {φs : List 𝓕.FieldOp} {i j : Fin φs.length}
    (φsΛ : WickContraction φs.length) (h : {i, j} ∈ φsΛ.1) :
    {i, j} ∈ φsΛ.eqTimeContractSet ↔ timeOrderRel φs[i] φs[j] ∧ timeOrderRel φs[j] φs[i] := by
  simp only [eqTimeContractSet, Fin.getElem_fin, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hij : i < j
  · have h1 := eq_fstFieldOfContract_of_mem φsΛ ⟨{i,j}, h⟩ i j (by simp) (by simp) hij
    have h2 := eq_sndFieldOfContract_of_mem φsΛ ⟨{i,j}, h⟩ i j (by simp) (by simp) hij
    simp only [h1, h2]
    simp_all only [forall_true_left, true_and]
  · have hineqj : i ≠ j := by
      by_contra hineqj
      subst hineqj
      have h2 := φsΛ.2.1 {i, i} h
      simp_all
    have hji : j < i := by omega
    have h1 := eq_fstFieldOfContract_of_mem φsΛ ⟨{i,j}, h⟩ j i (by simp) (by simp) hji
    have h2 := eq_sndFieldOfContract_of_mem φsΛ ⟨{i,j}, h⟩ j i (by simp) (by simp) hji
    simp only [h1, h2]
    simp_all only [not_lt, ne_eq, forall_true_left, true_and]
    apply Iff.intro
    · intro a
      simp_all only [and_self]
    · intro a
      simp_all only [and_self]

lemma subContraction_eqTimeContractSet_not_empty_of_haveEqTime
    {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length) (h : HaveEqTime φsΛ) :
    φsΛ.subContraction (eqTimeContractSet φsΛ) (eqTimeContractSet_subset φsΛ) ≠ empty := by
  simp only [ne_eq]
  erw [Subtype.ext_iff]
  simp only [subContraction, empty]
  rw [Finset.eq_empty_iff_forall_notMem]
  simp only [HaveEqTime, Fin.getElem_fin, exists_and_left, exists_prop] at h
  obtain ⟨i, j, hij, h1, h2⟩ := h
  simp only [not_forall, Decidable.not_not]
  use {i, j}
  rw [pair_mem_eqTimeContractSet_iff]
  simp_all only [Fin.getElem_fin, and_self]
  exact h1

lemma quotContraction_eqTimeContractSet_not_haveEqTime {φs : List 𝓕.FieldOp}
    (φsΛ : WickContraction φs.length) :
    ¬ HaveEqTime (φsΛ.quotContraction (eqTimeContractSet φsΛ) (eqTimeContractSet_subset φsΛ)) := by
  rw [haveEqTime_iff_finset]
  simp only [Fin.getElem_fin, not_exists, not_and]
  intro a ha
  erw [subContraction_uncontractedList_get]
  erw [subContraction_uncontractedList_get]
  simp only [quotContraction_fstFieldOfContract_uncontractedListEmd, Fin.getElem_fin,
    quotContraction_sndFieldOfContract_uncontractedListEmd]
  simp only [quotContraction, Finset.mem_filter, Finset.mem_univ, true_and] at ha
  have hn' : Finset.map uncontractedListEmd a ∉
      (φsΛ.subContraction (eqTimeContractSet φsΛ) (eqTimeContractSet_subset φsΛ)).1 := by
    exact uncontractedListEmd_finset_not_mem a
  simp only [subContraction, eqTimeContractSet, Fin.getElem_fin, Finset.mem_filter, Finset.mem_univ,
    true_and, not_and, not_forall] at hn'
  have hn'' := hn' ha
  obtain ⟨h, h1⟩ := hn''
  simp_all

lemma join_haveEqTime_of_eqTimeOnly_nonEmpty {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length)
    (h1 : φsΛ.EqTimeOnly) (h2 : φsΛ ≠ empty)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) :
    HaveEqTime (join φsΛ φsucΛ) := by
  simp only [HaveEqTime, Fin.getElem_fin, join, Finset.le_eq_subset, Finset.mem_union,
    Finset.mem_map, RelEmbedding.coe_toEmbedding, exists_and_left, exists_prop]
  simp only [EqTimeOnly, Fin.getElem_fin] at h1
  obtain ⟨i, j, h⟩ := exists_pair_of_not_eq_empty _ h2
  use i, j
  simp_all only [ne_eq, true_or, true_and]
  apply h1 j i
  rw [Finset.pair_comm]
  exact h

lemma hasEqTimeEquiv_ext_sigma {φs : List 𝓕.FieldOp} {x1 x2 :
    Σ (φsΛ : {φsΛ : WickContraction φs.length // φsΛ.EqTimeOnly ∧ φsΛ ≠ empty}),
    {φssucΛ : WickContraction [φsΛ.1]ᵘᶜ.length // ¬ HaveEqTime φssucΛ}}
    (h1 : x1.1.1 = x2.1.1) (h2 : x1.2.1 = congr (by simp [h1]) x2.2.1) : x1 = x2 := by
  rcases x1 with ⟨⟨a1, b1⟩, ⟨c1, d1⟩⟩
  rcases x2 with ⟨b2, h2⟩
  simp only at h1
  subst h1
  simp only [ne_eq, congr_refl] at h2
  simp [h2]

/-- The equivalence which separates a Wick contraction which has an equal time contraction
into a non-empty contraction only between equal-time fields and a Wick contraction which
does not have equal time contractions. -/
def hasEqTimeEquiv (φs : List 𝓕.FieldOp) :
    {φsΛ : WickContraction φs.length // HaveEqTime φsΛ} ≃
    Σ (φsΛ : {φsΛ : WickContraction φs.length // φsΛ.EqTimeOnly ∧ φsΛ ≠ empty}),
    {φssucΛ : WickContraction [φsΛ.1]ᵘᶜ.length // ¬ HaveEqTime φssucΛ} where
  toFun φsΛ := ⟨⟨φsΛ.1.subContraction (eqTimeContractSet φsΛ.1) (eqTimeContractSet_subset φsΛ.1),
    subContraction_eqTimeContractSet_eqTimeOnly φsΛ.1,
    subContraction_eqTimeContractSet_not_empty_of_haveEqTime φsΛ.1 φsΛ.2⟩,
    ⟨φsΛ.1.quotContraction (eqTimeContractSet φsΛ.1) (eqTimeContractSet_subset φsΛ.1),
    quotContraction_eqTimeContractSet_not_haveEqTime φsΛ.1⟩⟩
  invFun φsΛ := ⟨join φsΛ.1.1 φsΛ.2.1,
    join_haveEqTime_of_eqTimeOnly_nonEmpty φsΛ.1.1 φsΛ.1.2.1 φsΛ.1.2.2 φsΛ.2⟩
  left_inv φsΛ := by
    match φsΛ with
    | ⟨φsΛ, h1, h2⟩ =>
      simp only [ne_eq, Subtype.mk.injEq]
      exact join_sub_quot φsΛ φsΛ.eqTimeContractSet (eqTimeContractSet_subset φsΛ)
  right_inv φsΛ' := by
    match φsΛ' with
    | ⟨⟨φsΛ, h1⟩, ⟨φsucΛ, h2⟩⟩ =>
      have hs : subContraction (φsΛ.join φsucΛ).eqTimeContractSet
        (eqTimeContractSet_subset (φsΛ.join φsucΛ)) = φsΛ := by
        apply Subtype.ext
        ext a
        simp only [subContraction]
        rw [join_eqTimeContractSet]
        rw [eqTimeContractSet_of_not_haveEqTime h2]
        simp only [Finset.le_eq_subset, ne_eq, Finset.map_empty, Finset.union_empty]
        rw [eqTimeContractSet_of_mem_eqTimeOnly h1.1]
      refine hasEqTimeEquiv_ext_sigma ?_ ?_
      · simp only [ne_eq]
        exact hs
      · simp only [ne_eq]
        apply Subtype.ext
        ext a
        simp only [quotContraction, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [mem_congr_iff]
        rw [mem_join_right_iff]
        simp only [ne_eq]
        rw [uncontractedListEmd_congr hs]
        rw [Finset.map_map]

lemma sum_haveEqTime (φs : List 𝓕.FieldOp)
    (f : WickContraction φs.length → M) [AddCommMonoid M]:
  ∑ (φsΛ : {φsΛ : WickContraction φs.length // HaveEqTime φsΛ}), f φsΛ =
  ∑ (φsΛ : {φsΛ : WickContraction φs.length // φsΛ.EqTimeOnly ∧ φsΛ ≠ empty}),
  ∑ (φssucΛ : {φssucΛ : WickContraction [φsΛ.1]ᵘᶜ.length // ¬ HaveEqTime φssucΛ}),
    f (join φsΛ.1 φssucΛ.1) := by
  rw [← (hasEqTimeEquiv φs).symm.sum_comp]
  erw [Finset.sum_sigma]
  rfl

end
end WickContraction
