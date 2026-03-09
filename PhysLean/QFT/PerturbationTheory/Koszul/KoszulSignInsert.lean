/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module
public import PhysLean.QFT.PerturbationTheory.FieldStatistics.ExchangeSign
public import PhysLean.Mathematics.List
import all Mathlib.Data.List.Sort
/-!

# Koszul sign insert

-/

@[expose] public section

namespace Wick

open PhysLean.List
open FieldStatistic

variable {𝓕 : Type} (q : 𝓕 → FieldStatistic) (le : 𝓕 → 𝓕 → Prop) [DecidableRel le]

/-- Gives a factor of `-1` when inserting `a` into a list `List I` in the ordered position
  for each fermion-fermion cross. -/
def koszulSignInsert {𝓕 : Type} (q : 𝓕 → FieldStatistic) (le : 𝓕 → 𝓕 → Prop)
    [DecidableRel le] (φ : 𝓕) : List 𝓕 → ℂ
  | [] => 1
  | φ' :: φs => if le φ φ' then koszulSignInsert q le φ φs else
    if q φ = fermionic ∧ q φ' = fermionic then - koszulSignInsert q le φ φs else
      koszulSignInsert q le φ φs

/-- When inserting a boson the `koszulSignInsert` is always `1`. -/
lemma koszulSignInsert_boson (q : 𝓕 → FieldStatistic) (le : 𝓕 → 𝓕 → Prop) [DecidableRel le]
    (φ : 𝓕) (ha : q φ = bosonic) : (φs : List 𝓕) → koszulSignInsert q le φ φs = 1
  | [] => by
    simp [koszulSignInsert]
  | φ' :: φs => by
    simp only [koszulSignInsert]
    rw [koszulSignInsert_boson q le φ ha φs, ha]
    simp only [reduceCtorEq, false_and, ↓reduceIte, ite_self]

@[simp]
lemma koszulSignInsert_mul_self (φ : 𝓕) :
    (φs : List 𝓕) → koszulSignInsert q le φ φs * koszulSignInsert q le φ φs = 1
  | [] => by
    simp [koszulSignInsert]
  | φ' :: φs => by
    simp only [koszulSignInsert, mul_ite, ite_mul, neg_mul, mul_neg]
    by_cases hr : le φ φ'
    · simp only [hr, ↓reduceIte]
      rw [koszulSignInsert_mul_self]
    · simp only [hr, ↓reduceIte]
      by_cases hq : q φ = fermionic ∧ q φ' = fermionic
      · simp only [hq, and_self, ↓reduceIte, neg_neg]
        rw [koszulSignInsert_mul_self]
      · simp only [hq, ↓reduceIte]
        rw [koszulSignInsert_mul_self]

lemma koszulSignInsert_le_forall (φ : 𝓕) (φs : List 𝓕) (hi : ∀ φ', le φ φ') :
    koszulSignInsert q le φ φs = 1 := by
  induction φs with
  | nil => rfl
  | cons φ' φs ih =>
    simp only [koszulSignInsert]
    rw [ih]
    simp only [ite_eq_left_iff, ite_eq_right_iff, and_imp]
    intro h
    exact False.elim (h (hi φ'))

lemma koszulSignInsert_ge_forall_append (φs : List 𝓕) (φ' φ : 𝓕) (hi : ∀ φ'', le φ'' φ) :
    koszulSignInsert q le φ' φs = koszulSignInsert q le φ' (φs ++ [φ]) := by
  induction φs with
  | nil => simp [koszulSignInsert, hi]
  | cons φ'' φs ih =>
    simp only [koszulSignInsert, List.cons_append]
    by_cases hr : le φ' φ''
    · rw [if_pos hr, if_pos hr, ih]
    · rw [if_neg hr, if_neg hr, ih]

lemma koszulSignInsert_eq_filter (φ : 𝓕) : (φs : List 𝓕) →
    koszulSignInsert q le φ φs =
    koszulSignInsert q le φ (List.filter (fun i => decide (¬ le φ i)) φs)
  | [] => by
    simp [koszulSignInsert]
  | φ1 :: φs => by
    dsimp only [koszulSignInsert, Fin.isValue]
    simp only [List.filter, decide_not]
    by_cases h : le φ φ1
    · simp only [h, ↓reduceIte, decide_true, Bool.not_true]
      rw [koszulSignInsert_eq_filter]
      congr
      simp
    · simp only [h, ↓reduceIte, decide_false, Bool.not_false]
      dsimp only [Fin.isValue, koszulSignInsert]
      simp only [h, ↓reduceIte]
      rw [koszulSignInsert_eq_filter]
      congr
      · simp only [decide_not]
      · simp

lemma koszulSignInsert_eq_cons [Std.Total le] (φ : 𝓕) (φs : List 𝓕) :
    koszulSignInsert q le φ φs = koszulSignInsert q le φ (φ :: φs) := by
  simp only [koszulSignInsert, and_self]
  have h1 : le φ φ := by
    simpa only [or_self] using Std.Total.total (r := le) φ φ
  simp [h1]

lemma koszulSignInsert_eq_grade (φ : 𝓕) (φs : List 𝓕) :
    koszulSignInsert q le φ φs = if ofList q [φ] = fermionic ∧
    ofList q (List.filter (fun i => decide (¬ le φ i)) φs) = fermionic then -1 else 1 := by
  induction φs with
  | nil =>
    simp [koszulSignInsert]
  | cons φ1 φs ih =>
    rw [koszulSignInsert_eq_filter]
    by_cases hr1 : ¬ le φ φ1
    · rw [List.filter_cons_of_pos]
      · dsimp only [koszulSignInsert, Fin.isValue, decide_not]
        rw [if_neg hr1]
        dsimp only [Fin.isValue, ofList, ite_eq_right_iff, zero_ne_one, imp_false, decide_not]
        simp only [decide_not, ite_eq_right_iff, reduceCtorEq, imp_false]
        have ha (a b c : FieldStatistic) : (if a = fermionic ∧ b = fermionic then -if ¬a = bosonic ∧
          c = fermionic then -1 else (1 : ℂ)
          else if ¬a = bosonic ∧ c = fermionic then -1 else 1) =
          if ¬a = bosonic ∧ ¬b = c then -1 else 1 := by
          fin_cases a <;> fin_cases b <;> fin_cases c
          any_goals rfl
          simp
        rw [← ha (q φ) (q φ1) (ofList q (List.filter (fun a => !decide (le φ a)) φs))]
        congr
        · rw [koszulSignInsert_eq_filter] at ih
          simpa [ofList] using ih
        · rw [koszulSignInsert_eq_filter] at ih
          simpa [ofList] using ih
      · simp [hr1]
    · rw [List.filter_cons_of_neg]
      · simp only [decide_not]
        rw [koszulSignInsert_eq_filter] at ih
        simpa [ofList] using ih
      · simpa using hr1

lemma koszulSignInsert_eq_perm (φs φs' : List 𝓕) (φ : 𝓕) (h : φs.Perm φs') :
    koszulSignInsert q le φ φs = koszulSignInsert q le φ φs' := by
  rw [koszulSignInsert_eq_grade, koszulSignInsert_eq_grade]
  congr 1
  simp only [decide_not, eq_iff_iff, and_congr_right_iff]
  intro h'
  have hg : ofList q (List.filter (fun i => !decide (le φ i)) φs) =
      ofList q (List.filter (fun i => !decide (le φ i)) φs') := by
    apply ofList_perm
    exact List.Perm.filter (fun i => !decide (le φ i)) h
  rw [hg]

lemma koszulSignInsert_eq_sort (φs : List 𝓕) (φ : 𝓕) :
    koszulSignInsert q le φ φs = koszulSignInsert q le φ (List.insertionSort le φs) := by
  apply koszulSignInsert_eq_perm
  exact List.Perm.symm (List.perm_insertionSort le φs)

lemma koszulSignInsert_eq_exchangeSign_take [Std.Total le] [IsTrans 𝓕 le] (φ : 𝓕) (φs : List 𝓕) :
    koszulSignInsert q le φ φs = 𝓢(q φ, ofList q
    ((List.insertionSort le φs).take (orderedInsertPos le (List.insertionSort le φs) φ))) := by
  rw [koszulSignInsert_eq_cons, koszulSignInsert_eq_sort, koszulSignInsert_eq_filter,
    koszulSignInsert_eq_grade]
  have hx : (exchangeSign (q φ))
      (ofList q (List.take (↑(orderedInsertPos le (List.insertionSort le φs) φ))
      (List.insertionSort le φs))) = if FieldStatistic.ofList q [φ] = fermionic ∧
      FieldStatistic.ofList q (List.take (↑(orderedInsertPos le (List.insertionSort le φs) φ))
      (List.insertionSort le φs)) = fermionic then - 1 else 1 := by
    rw [exchangeSign_eq_if]
    simp
  rw [hx]
  congr
  simp only [List.filter_filter, Bool.and_self]
  rw [List.insertionSort_cons]
  nth_rewrite 1 [List.orderedInsert_eq_take_drop]
  rw [List.filter_append]
  have h1 : List.filter (fun a => decide ¬le φ a)
    (List.takeWhile (fun b => decide ¬le φ b) (List.insertionSort le φs))
    = (List.takeWhile (fun b => decide ¬le φ b) (List.insertionSort le φs)) := by
    induction φs with
    | nil => simp
    | cons r1 r ih =>
      simp only [decide_not, List.insertionSort, List.filter_eq_self, Bool.not_eq_eq_eq_not,
        Bool.not_true, decide_eq_false_iff_not]
      intro a ha
      have ha' := List.mem_takeWhile_imp ha
      simp_all
  rw [h1]
  rw [List.filter_cons]
  simp only [decide_not, (Std.Total.to_refl le).refl φ, not_true_eq_false, decide_false,
    Bool.false_eq_true, ↓reduceIte]
  rw [orderedInsertPos_take]
  simp only [decide_not, List.append_right_eq_self, List.filter_eq_nil_iff, Bool.not_eq_eq_eq_not,
    Bool.not_true, decide_eq_false_iff_not, Decidable.not_not]
  intro a ha
  refine List.Pairwise.rel_of_mem_take_of_mem_drop
    (i := (orderedInsertPos le (List.insertionSort le φs) φ).1 + 1)
    (List.pairwise_insertionSort le (φ :: φs)) ?_ ?_
  · simp only [List.insertionSort, List.foldr_cons, List.orderedInsert_eq_take_drop, decide_not]
    rw [List.take_append]
    rw [List.take_of_length_le]
    · simp [orderedInsertPos]
    · simp [orderedInsertPos]
  · simp only [List.insertionSort_cons, List.orderedInsert_eq_take_drop, decide_not]
    rw [List.drop_append, List.drop_of_length_le]
    · simpa [orderedInsertPos] using ha
    · simp [orderedInsertPos]

lemma koszulSignInsert_insertIdx (i j : 𝓕) (r : List 𝓕) (n : ℕ) (hn : n ≤ r.length) :
    koszulSignInsert q le j (List.insertIdx r n i) = koszulSignInsert q le j (i :: r) := by
  apply koszulSignInsert_eq_perm
  exact List.perm_insertIdx i r hn

/-- The difference in `koszulSignInsert` on inserting `r0` into `r` compared to
  into `r1 :: r` for any `r`. -/
def koszulSignCons (φ0 φ1 : 𝓕) : ℂ :=
  if le φ0 φ1 then 1 else
  if q φ0 = fermionic ∧ q φ1 = fermionic then -1 else 1

lemma koszulSignCons_eq_exchangeSign (φ0 φ1 : 𝓕) : koszulSignCons q le φ0 φ1 =
    if le φ0 φ1 then 1 else 𝓢(q φ0, q φ1) := by
  simp only [koszulSignCons]
  congr 1
  by_cases h0 : q φ0 = fermionic
  · by_cases h1 : q φ1 = fermionic
    · simp [h0, h1, exchangeSign]
    · have h1 : q φ1 = bosonic := (neq_fermionic_iff_eq_bosonic (q φ1)).mp h1
      simp [h0, h1]
  · have h0 : q φ0 = bosonic := (neq_fermionic_iff_eq_bosonic (q φ0)).mp h0
    by_cases h1 : q φ1 = fermionic
    · simp [h0, h1]
    · have h1 : q φ1 = bosonic := (neq_fermionic_iff_eq_bosonic (q φ1)).mp h1
      simp [h0, h1]

lemma koszulSignInsert_cons (r0 r1 : 𝓕) (r : List 𝓕) :
    koszulSignInsert q le r0 (r1 :: r) = (koszulSignCons q le r0 r1) *
    koszulSignInsert q le r0 r := by
  simp [koszulSignInsert, koszulSignCons]

lemma koszulSignInsert_of_le_mem (φ0 : 𝓕) : (φs : List 𝓕) → (h : ∀ b ∈ φs, le φ0 b) →
    koszulSignInsert q le φ0 φs = 1
  | [], _ => by
    simp [koszulSignInsert]
  | φ1 :: φs, h => by
    simp only [koszulSignInsert]
    rw [if_pos]
    · apply koszulSignInsert_of_le_mem
      · intro b hb
        exact h b (List.mem_cons_of_mem _ hb)
    · exact h φ1 List.mem_cons_self

lemma koszulSignInsert_eq_rel_eq_stat {ψ φ : 𝓕} [IsTrans 𝓕 le]
    (h1 : le φ ψ) (h2 : le ψ φ) (hq : q ψ = q φ) : (φs : List 𝓕) →
    koszulSignInsert q le φ φs = koszulSignInsert q le ψ φs
  | [] => by
    simp [koszulSignInsert]
  | φ' :: φs => by
    simp only [koszulSignInsert]
    simp_all only
    by_cases hr : le φ φ'
    · simp only [hr, ↓reduceIte]
      have h1' : le ψ φ' := by
        apply IsTrans.trans ψ φ φ' h2 hr
      simp only [h1', ↓reduceIte]
      exact koszulSignInsert_eq_rel_eq_stat h1 h2 hq φs
    · have hψφ' : ¬ le ψ φ' := by
        intro hψφ'
        apply hr
        apply IsTrans.trans φ ψ φ' h1 hψφ'
      simp only [hr, ↓reduceIte, hψφ']
      rw [koszulSignInsert_eq_rel_eq_stat h1 h2 hq φs]

lemma koszulSignInsert_eq_remove_same_stat_append {ψ φ φ' : 𝓕} [IsTrans 𝓕 le]
    (h1 : le φ ψ) (h2 : le ψ φ) (hq : q ψ = q φ) : (φs : List 𝓕) →
    koszulSignInsert q le φ' (φ :: ψ :: φs) = koszulSignInsert q le φ' φs := by
  intro φs
  simp_all only [koszulSignInsert, and_self, ite_true, ite_false, ite_self]
  by_cases hφ'φ : le φ' φ
  · have hφ'ψ : le φ' ψ := by
      apply IsTrans.trans φ' φ ψ hφ'φ h1
    simp [hφ'φ, hφ'ψ]
  · have hφ'ψ : ¬ le φ' ψ := by
      intro hφ'ψ
      apply hφ'φ
      apply IsTrans.trans φ' ψ φ hφ'ψ h2
    simp_all

end Wick
