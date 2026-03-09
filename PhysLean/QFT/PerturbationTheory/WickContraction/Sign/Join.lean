/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.QFT.PerturbationTheory.WickContraction.Join
/-!

# Sign associated with joining two Wick contractions

-/

@[expose] public section

open FieldSpecification
variable {𝓕 : FieldSpecification}

namespace WickContraction
variable {n : ℕ} (c : WickContraction n)
open PhysLean.List
open WickAlgebra

open FieldStatistic

lemma stat_signFinset_right {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (i j : Fin [φsΛ]ᵘᶜ.length) :
    (𝓕 |>ₛ ⟨[φsΛ]ᵘᶜ.get, φsucΛ.signFinset i j⟩) =
    (𝓕 |>ₛ ⟨φs.get, (φsucΛ.signFinset i j).map uncontractedListEmd⟩) := by
  simp only [ofFinset]
  congr 1
  rw [← fin_finset_sort_map_monotone]
  simp only [List.map_map, List.map_inj_left, Finset.mem_sort, List.get_eq_getElem,
    Function.comp_apply, getElem_uncontractedListEmd, implies_true]
  intro i j h
  exact uncontractedListEmd_strictMono h

lemma signFinset_right_map_uncontractedListEmd_eq_filter {φs : List 𝓕.FieldOp}
    (φsΛ : WickContraction φs.length) (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length)
    (i j : Fin [φsΛ]ᵘᶜ.length) : (φsucΛ.signFinset i j).map uncontractedListEmd =
    ((join φsΛ φsucΛ).signFinset (uncontractedListEmd i) (uncontractedListEmd j)).filter
    (fun c => c ∈ φsΛ.uncontracted) := by
  ext a
  simp only [Finset.mem_map, Finset.mem_filter]
  apply Iff.intro
  · intro h
    obtain ⟨a, ha, rfl⟩ := h
    apply And.intro
    · simp_all only [signFinset, Finset.mem_filter, Finset.mem_univ, true_and,
      join_getDual?_apply_uncontractedListEmb, Option.map_eq_none_iff, Option.isSome_map]
      apply And.intro
      · exact uncontractedListEmd_strictMono ha.1
      · apply And.intro
        · exact uncontractedListEmd_strictMono ha.2.1
        · have ha2 := ha.2.2
          simp_all only [and_true]
          rcases ha2 with ha2 | ha2
          · simp [ha2]
          · right
            intro h
            apply lt_of_lt_of_eq (uncontractedListEmd_strictMono (ha2 h))
            rw [Option.get_map]
    · exact uncontractedListEmd_mem_uncontracted a
  · intro h
    have h2 := h.2
    have h2' := uncontractedListEmd_surjective_mem_uncontracted a h.2
    obtain ⟨a, rfl⟩ := h2'
    use a
    simp_all only [signFinset, Finset.mem_filter, Finset.mem_univ,
      join_getDual?_apply_uncontractedListEmb, Option.map_eq_none_iff, Option.isSome_map, true_and,
      and_true]
    apply And.intro
    · have h1 := h.1
      rw [StrictMono.lt_iff_lt] at h1
      exact h1
      exact fun _ _ h => uncontractedListEmd_strictMono h
    · apply And.intro
      · have h1 := h.2.1
        rw [StrictMono.lt_iff_lt] at h1
        exact h1
        exact fun _ _ h => uncontractedListEmd_strictMono h
      · have h1 := h.2.2
        simp_all only [and_true]
        rcases h1 with h1 | h1
        · simp [h1]
        · right
          intro h
          have h1' := h1 h
          have hl : uncontractedListEmd i < uncontractedListEmd ((φsucΛ.getDual? a).get h) := by
            apply lt_of_lt_of_eq h1'
            simp [Option.get_map]
          rw [StrictMono.lt_iff_lt] at hl
          exact hl
          exact fun _ _ h => uncontractedListEmd_strictMono h

lemma sign_right_eq_prod_mul_prod {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) :
    φsucΛ.sign = (∏ a, 𝓢(𝓕|>ₛ [φsΛ]ᵘᶜ[φsucΛ.sndFieldOfContract a], 𝓕|>ₛ ⟨φs.get,
    ((join φsΛ φsucΛ).signFinset (uncontractedListEmd (φsucΛ.fstFieldOfContract a))
      (uncontractedListEmd (φsucΛ.sndFieldOfContract a))).filter
      (fun c => ¬ c ∈ φsΛ.uncontracted)⟩)) *
    (∏ a, 𝓢(𝓕|>ₛ [φsΛ]ᵘᶜ[φsucΛ.sndFieldOfContract a], 𝓕|>ₛ ⟨φs.get,
      ((join φsΛ φsucΛ).signFinset (uncontractedListEmd (φsucΛ.fstFieldOfContract a))
        (uncontractedListEmd (φsucΛ.sndFieldOfContract a)))⟩)) := by
  rw [← Finset.prod_mul_distrib, sign]
  congr
  funext a
  rw [← map_mul]
  congr
  rw [stat_signFinset_right, signFinset_right_map_uncontractedListEmd_eq_filter]
  rw [ofFinset_filter]

lemma join_singleton_signFinset_eq_filter {φs : List 𝓕.FieldOp}
    {i j : Fin φs.length} (h : i < j)
    (φsucΛ : WickContraction [singleton h]ᵘᶜ.length) :
    (join (singleton h) φsucΛ).signFinset i j =
    ((singleton h).signFinset i j).filter (fun c => ¬
    (((join (singleton h) φsucΛ).getDual? c).isSome ∧
    ((h1 : ((join (singleton h) φsucΛ).getDual? c).isSome) →
    (((join (singleton h) φsucΛ).getDual? c).get h1) < i))) := by
  ext a
  simp only [signFinset, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_forall, not_lt,
    and_assoc, and_congr_right_iff]
  intro h1 h2
  have h1 : (singleton h).getDual? a = none := by
    rw [singleton_getDual?_eq_none_iff_neq]
    omega
  simp only [h1, Option.isSome_none, Bool.false_eq_true, IsEmpty.forall_iff, or_self, true_and]
  apply Iff.intro
  · intro h1 h2
    rcases h1 with h1 | h1
    · simp only [h1, Option.isSome_none, Bool.false_eq_true, IsEmpty.exists_iff]
      have h2' : ¬ (((singleton h).join φsucΛ).getDual? a).isSome := by
        exact Option.not_isSome_iff_eq_none.mpr h1
      exact h2' h2
    use h2
    have h1 := h1 h2
    omega
  · intro h2
    by_cases h2' : (((singleton h).join φsucΛ).getDual? a).isSome = true
    · have h2 := h2 h2'
      obtain ⟨hb, h2⟩ := h2
      right
      intro hl
      apply lt_of_le_of_ne h2
      by_contra hn
      have hij : ((singleton h).join φsucΛ).getDual? i = j := by
        rw [@getDual?_eq_some_iff_mem]
        simp [join, singleton]
      simp only [hn, getDual?_getDual?_get_get, Option.some.injEq] at hij
      omega
    · simp only [Bool.not_eq_true] at h2'
      simp [h2']

lemma join_singleton_left_signFinset_eq_filter {φs : List 𝓕.FieldOp}
    {i j : Fin φs.length} (h : i < j)
    (φsucΛ : WickContraction [singleton h]ᵘᶜ.length) :
    (𝓕 |>ₛ ⟨φs.get, (singleton h).signFinset i j⟩)
    = (𝓕 |>ₛ ⟨φs.get, (join (singleton h) φsucΛ).signFinset i j⟩) *
      (𝓕 |>ₛ ⟨φs.get, ((singleton h).signFinset i j).filter (fun c =>
      (((join (singleton h) φsucΛ).getDual? c).isSome ∧
      ((h1 : ((join (singleton h) φsucΛ).getDual? c).isSome) →
      (((join (singleton h) φsucΛ).getDual? c).get h1) < i)))⟩) := by
  conv_rhs =>
    left
    rw [join_singleton_signFinset_eq_filter]
  rw [mul_comm]
  exact (ofFinset_filter_mul_neg 𝓕.fieldOpStatistic _ _ _).symm

/-- The difference in sign between `φsucΛ.sign` and the direct contribution of `φsucΛ` to
  `(join (singleton h) φsucΛ)`. -/
def joinSignRightExtra {φs : List 𝓕.FieldOp}
    {i j : Fin φs.length} (h : i < j)
    (φsucΛ : WickContraction [singleton h]ᵘᶜ.length) : ℂ :=
    ∏ a, 𝓢(𝓕|>ₛ [singleton h]ᵘᶜ[φsucΛ.sndFieldOfContract a], 𝓕|>ₛ ⟨φs.get,
    ((join (singleton h) φsucΛ).signFinset (uncontractedListEmd (φsucΛ.fstFieldOfContract a))
    (uncontractedListEmd (φsucΛ.sndFieldOfContract a))).filter
    (fun c => ¬ c ∈ (singleton h).uncontracted)⟩)

/-- The difference in sign between `(singleton h).sign` and the direct contribution of
  `(singleton h)` to `(join (singleton h) φsucΛ)`. -/
def joinSignLeftExtra {φs : List 𝓕.FieldOp}
    {i j : Fin φs.length} (h : i < j)
    (φsucΛ : WickContraction [singleton h]ᵘᶜ.length) : ℂ :=
    𝓢(𝓕 |>ₛ φs[j], (𝓕 |>ₛ ⟨φs.get, ((singleton h).signFinset i j).filter (fun c =>
      (((join (singleton h) φsucΛ).getDual? c).isSome ∧
      ((h1 : ((join (singleton h) φsucΛ).getDual? c).isSome) →
      (((join (singleton h) φsucΛ).getDual? c).get h1) < i)))⟩))

lemma join_singleton_sign_left {φs : List 𝓕.FieldOp}
    {i j : Fin φs.length} (h : i < j)
    (φsucΛ : WickContraction [singleton h]ᵘᶜ.length) :
    (singleton h).sign = 𝓢(𝓕 |>ₛ φs[j],
    (𝓕 |>ₛ ⟨φs.get, (join (singleton h) φsucΛ).signFinset i j⟩)) * (joinSignLeftExtra h φsucΛ) := by
  rw [singleton_sign_expand]
  rw [join_singleton_left_signFinset_eq_filter h φsucΛ]
  rw [map_mul]
  rfl

lemma join_singleton_sign_right {φs : List 𝓕.FieldOp}
    {i j : Fin φs.length} (h : i < j)
    (φsucΛ : WickContraction [singleton h]ᵘᶜ.length) :
    φsucΛ.sign =
    (joinSignRightExtra h φsucΛ) *
    (∏ a, 𝓢(𝓕|>ₛ [singleton h]ᵘᶜ[φsucΛ.sndFieldOfContract a], 𝓕|>ₛ ⟨φs.get,
      ((join (singleton h) φsucΛ).signFinset (uncontractedListEmd (φsucΛ.fstFieldOfContract a))
        (uncontractedListEmd (φsucΛ.sndFieldOfContract a)))⟩)) := by
  rw [sign_right_eq_prod_mul_prod]
  rfl

lemma joinSignRightExtra_eq_i_j_finset_eq_if {φs : List 𝓕.FieldOp}
    {i j : Fin φs.length} (h : i < j) (φsucΛ : WickContraction [singleton h]ᵘᶜ.length) :
    joinSignRightExtra h φsucΛ = ∏ a,
    𝓢((𝓕|>ₛ [singleton h]ᵘᶜ[φsucΛ.sndFieldOfContract a]),
    𝓕 |>ₛ ⟨φs.get, (if uncontractedListEmd (φsucΛ.fstFieldOfContract a) < j ∧
        j < uncontractedListEmd (φsucΛ.sndFieldOfContract a) ∧
        uncontractedListEmd (φsucΛ.fstFieldOfContract a) < i then {j} else ∅)
        ∪ (if uncontractedListEmd (φsucΛ.fstFieldOfContract a) < i ∧
        i < uncontractedListEmd (φsucΛ.sndFieldOfContract a) then {i} else ∅)⟩) := by
  rw [joinSignRightExtra]
  congr
  funext a
  congr
  rw [signFinset]
  rw [Finset.filter_comm]
  have h11 : (Finset.filter (fun c => c ∉ (singleton h).uncontracted) Finset.univ) = {i, j} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    rw [@mem_uncontracted_iff_not_contracted]
    simp only [singleton, Finset.mem_singleton, forall_eq, Finset.mem_insert, not_or, not_and,
      Decidable.not_not]
    omega
  rw [h11]
  ext x
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]
  have hjneqfst := singleton_uncontractedEmd_ne_right h (φsucΛ.fstFieldOfContract a)
  have hjneqsnd := singleton_uncontractedEmd_ne_right h (φsucΛ.sndFieldOfContract a)
  have hineqfst := singleton_uncontractedEmd_ne_left h (φsucΛ.fstFieldOfContract a)
  have hineqsnd := singleton_uncontractedEmd_ne_left h (φsucΛ.sndFieldOfContract a)
  by_cases hj1 : ¬ uncontractedListEmd (φsucΛ.fstFieldOfContract a) < j
  · simp only [hj1, false_and, ↓reduceIte, Finset.notMem_empty, false_or]
    have hi1 : ¬ uncontractedListEmd (φsucΛ.fstFieldOfContract a) < i := by omega
    simp only [hi1, false_and, ↓reduceIte, Finset.notMem_empty, iff_false, not_and, not_or,
      not_forall, not_lt]
    intro hxij h1 h2
    omega
  · have hj1 : uncontractedListEmd (φsucΛ.fstFieldOfContract a) < j := by
      omega
    by_cases hi1 : ¬ i < uncontractedListEmd (φsucΛ.sndFieldOfContract a)
    · simp only [hi1, and_false, ↓reduceIte, Finset.notMem_empty, or_false]
      have hj2 : ¬ j < uncontractedListEmd (φsucΛ.sndFieldOfContract a) := by omega
      simp only [hj2, false_and, and_false, ↓reduceIte, Finset.notMem_empty, iff_false, not_and,
        not_or, not_forall, not_lt]
      intro hxij h1 h2
      omega
    · have hi1 : i < uncontractedListEmd (φsucΛ.sndFieldOfContract a) := by
        omega
      simp only [hj1, true_and, hi1, and_true]
      by_cases hi2 : ¬ uncontractedListEmd (φsucΛ.fstFieldOfContract a) < i
      · simp only [hi2, and_false, ↓reduceIte, Finset.notMem_empty, or_self, iff_false, not_and,
        not_or, not_forall, not_lt]
        by_cases hj3 : ¬ j < uncontractedListEmd (φsucΛ.sndFieldOfContract a)
        · omega
        · have hj4 : j < uncontractedListEmd (φsucΛ.sndFieldOfContract a) := by omega
          intro h
          rcases h with h | h
          · subst h
            omega
          · subst h
            simp only [join_singleton_getDual?_right, reduceCtorEq, not_false_eq_true,
              Option.get_some, Option.isSome_some, exists_const, true_and]
            omega
      · have hi2 : uncontractedListEmd (φsucΛ.fstFieldOfContract a) < i := by omega
        simp only [hi2, and_true, ↓reduceIte, Finset.mem_singleton]
        by_cases hj3 : ¬ j < uncontractedListEmd (φsucΛ.sndFieldOfContract a)
        · simp only [hj3, ↓reduceIte, Finset.notMem_empty, false_or]
          apply Iff.intro
          · intro h
            omega
          · intro h
            subst h
            simp only [true_or, join_singleton_getDual?_left, reduceCtorEq, Option.isSome_some,
              Option.get_some, forall_const, false_or, true_and]
            omega
        · have hj3 : j < uncontractedListEmd (φsucΛ.sndFieldOfContract a) := by omega
          simp only [hj3, ↓reduceIte, Finset.mem_singleton]
          apply Iff.intro
          · intro h
            omega
          · intro h
            rcases h with h1 | h1
            · subst h1
              simp only [or_true, join_singleton_getDual?_right, reduceCtorEq, Option.isSome_some,
                Option.get_some, forall_const, false_or, true_and]
              omega
            · subst h1
              simp only [true_or, join_singleton_getDual?_left, reduceCtorEq, Option.isSome_some,
                Option.get_some, forall_const, false_or, true_and]
              omega

lemma joinSignLeftExtra_eq_joinSignRightExtra {φs : List 𝓕.FieldOp}
    {i j : Fin φs.length} (h : i < j) (hs : (𝓕 |>ₛ φs[i]) = (𝓕 |>ₛ φs[j]))
    (φsucΛ : WickContraction [singleton h]ᵘᶜ.length) :
    joinSignLeftExtra h φsucΛ = joinSignRightExtra h φsucΛ := by
  /- Simplifying joinSignLeftExtra. -/
  let e2 : Fin φs.length ≃ {x // (((singleton h).join φsucΛ).getDual? x).isSome} ⊕
    {x // ¬ (((singleton h).join φsucΛ).getDual? x).isSome} := by
    exact (Equiv.sumCompl fun a => (((singleton h).join φsucΛ).getDual? a).isSome = true).symm
  rw [joinSignLeftExtra, ofFinset_eq_prod, map_prod, ← e2.symm.prod_comp]
  simp only [Fin.getElem_fin, Fintype.prod_sum_type, instCommGroup]
  conv_lhs =>
    enter [2, 2, x]
    simp only [Equiv.symm_symm, Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr, e2]
    rw [if_neg (by
        simp only [Finset.mem_filter, mem_signFinset, not_and, not_forall, not_lt, and_imp]
        intro h1 h2
        have hx := x.2
        simp_all)]
  simp only [Finset.mem_filter, mem_signFinset, map_one, Finset.prod_const_one, mul_one]
  rw [← ((singleton h).join φsucΛ).sigmaContractedEquiv.prod_comp]
  rw [Fintype.prod_sigma]
  conv_lhs =>
    enter [2, a]
    rw [prod_finset_eq_mul_fst_snd]
    simp [e2, sigmaContractedEquiv]
  rw [prod_join, singleton_prod]
  simp only [join_fstFieldOfContract_joinLiftLeft, singleton_fstFieldOfContract,
    join_sndFieldOfContract_joinLift, singleton_sndFieldOfContract, lt_self_iff_false, and_false,
    ↓reduceIte, map_one, mul_one, join_fstFieldOfContract_joinLiftRight,
    join_sndFieldOfContract_joinLiftRight, getElem_uncontractedListEmd]
  rw [if_neg (by omega)]
  simp only [map_one, one_mul]
  /- Introducing joinSignRightExtra. -/
  rw [joinSignRightExtra_eq_i_j_finset_eq_if]
  congr
  funext a
  have hjneqsnd := singleton_uncontractedEmd_ne_right h (φsucΛ.sndFieldOfContract a)
  have hl : uncontractedListEmd (φsucΛ.fstFieldOfContract a) <
      uncontractedListEmd (φsucΛ.sndFieldOfContract a) := by
    apply uncontractedListEmd_strictMono
    exact fstFieldOfContract_lt_sndFieldOfContract φsucΛ a
  by_cases hj1 : ¬ uncontractedListEmd (φsucΛ.fstFieldOfContract a) < j
  · have hi1 : ¬ uncontractedListEmd (φsucΛ.fstFieldOfContract a) < i := by omega
    simp [hj1, hi1]
  · have hj1 : uncontractedListEmd (φsucΛ.fstFieldOfContract a) < j := by omega
    simp only [hj1, and_true, instCommGroup, Fin.getElem_fin, true_and]
    by_cases hi2 : ¬ i < uncontractedListEmd (φsucΛ.sndFieldOfContract a)
    · have hi1 : ¬ i < uncontractedListEmd (φsucΛ.fstFieldOfContract a) := by omega
      have hj2 : ¬ j < uncontractedListEmd (φsucΛ.sndFieldOfContract a) := by omega
      simp [hi2, hj2, hi1]
    · have hi2 : i < uncontractedListEmd (φsucΛ.sndFieldOfContract a) := by omega
      have hi2n : ¬ uncontractedListEmd (φsucΛ.sndFieldOfContract a) < i := by omega
      simp only [hi2n, and_false, ↓reduceIte, map_one, hi2, true_and, one_mul, and_true]
      by_cases hj2 : ¬ j < uncontractedListEmd (φsucΛ.sndFieldOfContract a)
      · simp only [hj2, false_and, ↓reduceIte, Finset.empty_union]
        have hj2 : uncontractedListEmd (φsucΛ.sndFieldOfContract a) < j:= by omega
        simp only [hj2, true_and]
        by_cases hi1 : ¬ uncontractedListEmd (φsucΛ.fstFieldOfContract a) < i
        · simp [hi1]
        · have hi1 : uncontractedListEmd (φsucΛ.fstFieldOfContract a) < i := by omega
          simp only [hi1, ↓reduceIte, ofFinset_singleton, List.get_eq_getElem]
          erw [hs]
          exact exchangeSign_symm (𝓕|>ₛφs[↑j]) (𝓕|>ₛ[singleton h]ᵘᶜ[↑(φsucΛ.sndFieldOfContract a)])
      · simp only [not_lt, not_le] at hj2
        simp only [hj2, true_and]
        by_cases hi1 : ¬ uncontractedListEmd (φsucΛ.fstFieldOfContract a) < i
        · simp [hi1]
        · have hi1 : uncontractedListEmd (φsucΛ.fstFieldOfContract a) < i := by omega
          simp only [hi1, and_true, ↓reduceIte]
          have hj2 : ¬ uncontractedListEmd (φsucΛ.sndFieldOfContract a) < j := by omega
          simp only [hj2, ↓reduceIte, map_one]
          rw [← ofFinset_union_disjoint]
          simp only [instCommGroup, ofFinset_singleton, List.get_eq_getElem]
          erw [hs]
          simp only [Fin.getElem_fin, mul_self, map_one]
          simp only [Finset.disjoint_singleton_right, Finset.mem_singleton]
          exact Fin.ne_of_lt h

lemma join_sign_singleton {φs : List 𝓕.FieldOp}
    {i j : Fin φs.length} (h : i < j) (hs : (𝓕 |>ₛ φs[i]) = (𝓕 |>ₛ φs[j]))
    (φsucΛ : WickContraction [singleton h]ᵘᶜ.length) :
    (join (singleton h) φsucΛ).sign = (singleton h).sign * φsucΛ.sign := by
  rw [join_singleton_sign_right, join_singleton_sign_left h φsucΛ]
  rw [joinSignLeftExtra_eq_joinSignRightExtra h hs φsucΛ]
  rw [← mul_assoc, mul_assoc _ _ (joinSignRightExtra h φsucΛ)]
  have h1 : (joinSignRightExtra h φsucΛ * joinSignRightExtra h φsucΛ) = 1 := by
    rw [← joinSignLeftExtra_eq_joinSignRightExtra h hs φsucΛ]
    simp [joinSignLeftExtra]
  simp only [instCommGroup, Fin.getElem_fin, h1, mul_one]
  rw [sign, prod_join]
  congr
  · rw [singleton_prod]
    simp
  · funext a
    simp

lemma join_sign_induction {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (hc : φsΛ.GradingCompliant) :
    (n : ℕ) → (hn : φsΛ.1.card = n) →
    (join φsΛ φsucΛ).sign = φsΛ.sign * φsucΛ.sign
  | 0, hn => by
    rw [@card_zero_iff_empty] at hn
    subst hn
    simp only [empty_join, sign_empty, one_mul]
    apply sign_congr
    simp
  | Nat.succ n, hn => by
    obtain ⟨i, j, hij, φsucΛ', rfl, h1, h2, h3⟩ :=
      exists_join_singleton_of_card_ge_zero φsΛ (by simp [hn]) hc
    rw [join_assoc, join_sign_singleton hij h1, join_sign_singleton hij h1]
    have hn : φsucΛ'.1.card = n := by
      omega
    rw [join_sign_induction φsucΛ' (congr (by simp [join_uncontractedListGet]) φsucΛ) h2
      n hn]
    rw [mul_assoc]
    simp only [mul_eq_mul_left_iff]
    left
    left
    apply sign_congr
    exact join_uncontractedListGet (singleton hij) φsucΛ'

/-- For a list `φs` of `𝓕.FieldOp`, a grading compliant Wick contraction `φsΛ` of `φs`,
  and a Wick contraction `φsucΛ` of `[φsΛ]ᵘᶜ`, the following relation holds
  `(join φsΛ φsucΛ).sign = φsΛ.sign * φsucΛ.sign`.

  In `φsΛ.sign` the sign is determined by starting with the contracted pair
  whose first element occurs at the left-most position. This lemma manifests that this
  choice does not matter, and that contracted pairs can be brought together in any order. -/
lemma join_sign {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (hc : φsΛ.GradingCompliant) :
    (join φsΛ φsucΛ).sign = φsΛ.sign * φsucΛ.sign :=
  join_sign_induction φsΛ φsucΛ hc (φsΛ).1.card rfl

/-- For a list `φs` of `𝓕.FieldOp`, a Wick contraction `φsΛ` of `φs`,
  and a Wick contraction `φsucΛ` of `[φsΛ]ᵘᶜ`,
  `(join φsΛ φsucΛ).sign • (join φsΛ φsucΛ).timeContract` is equal to the product of
  - `φsΛ.sign • φsΛ.timeContract` and
  - `φsucΛ.sign • φsucΛ.timeContract`. -/
lemma join_sign_timeContract {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) :
    (join φsΛ φsucΛ).sign • (join φsΛ φsucΛ).timeContract.1 =
    (φsΛ.sign • φsΛ.timeContract.1) * (φsucΛ.sign • φsucΛ.timeContract.1) := by
  rw [join_timeContract]
  by_cases h : φsΛ.GradingCompliant
  · rw [join_sign _ _ h]
    simp [smul_smul, mul_comm]
  · rw [timeContract_of_not_gradingCompliant _ _ h]
    simp

end WickContraction
