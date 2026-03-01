/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QFT.PerturbationTheory.Koszul.KoszulSignInsert
import PhysLean.Mathematics.List.InsertionSort
/-!

# Koszul sign

-/

namespace Wick

open PhysLean.List
open FieldStatistic

variable {𝓕 : Type} (q : 𝓕 → FieldStatistic) (le : 𝓕 → 𝓕 → Prop) [DecidableRel le]

/-- Gives a factor of `- 1` for every fermion-fermion (`q` is `1`) crossing that occurs when sorting
  a list of based on `r`. -/
def koszulSign (q : 𝓕 → FieldStatistic) (le : 𝓕 → 𝓕 → Prop) [DecidableRel le] :
    List 𝓕 → ℂ
  | [] => 1
  | a :: l => koszulSignInsert q le a l * koszulSign q le l

@[simp]
lemma koszulSign_singleton (q : 𝓕 → FieldStatistic) (le : 𝓕 → 𝓕 → Prop) [DecidableRel le] (φ : 𝓕) :
    koszulSign q le [φ] = 1 := by
  simp [koszulSign, koszulSignInsert]

lemma koszulSign_mul_self (l : List 𝓕) : koszulSign q le l * koszulSign q le l = 1 := by
  induction l with
  | nil => simp [koszulSign]
  | cons a l ih =>
    simp only [koszulSign]
    trans (koszulSignInsert q le a l * koszulSignInsert q le a l) *
      (koszulSign q le l * koszulSign q le l)
    · ring
    · rw [ih, koszulSignInsert_mul_self, mul_one]

@[simp]
lemma koszulSign_freeMonoid_of (φ : 𝓕) : koszulSign q le (FreeMonoid.of φ) = 1 := by
  change koszulSign q le [φ] = 1
  simp only [koszulSign, mul_one]
  rfl

lemma koszulSignInsert_erase_boson {𝓕 : Type} (q : 𝓕 → FieldStatistic)
    (le : 𝓕 → 𝓕 → Prop) [DecidableRel le] (φ : 𝓕) :
    (φs : List 𝓕) → (n : Fin φs.length) → (heq : q (φs.get n) = bosonic) →
    koszulSignInsert q le φ (φs.eraseIdx n) = koszulSignInsert q le φ φs
  | [], _, _ => by
    simp
  | r1 :: r, ⟨0, h⟩, hr => by
    simp only [List.eraseIdx_zero, List.tail_cons]
    simp only [List.length_cons, Fin.zero_eta, List.get_eq_getElem, Fin.val_zero,
      List.getElem_cons_zero] at hr
    rw [koszulSignInsert]
    simp [hr]
  | r1 :: r, ⟨n + 1, h⟩, hr => by
    simp only [List.eraseIdx_cons_succ]
    rw [koszulSignInsert, koszulSignInsert]
    rw [koszulSignInsert_erase_boson q le φ r ⟨n, Nat.succ_lt_succ_iff.mp h⟩ hr]

lemma koszulSign_erase_boson {𝓕 : Type} (q : 𝓕 → FieldStatistic) (le : 𝓕 → 𝓕 → Prop)
    [DecidableRel le] :
    (φs : List 𝓕) → (n : Fin φs.length) → (heq : q (φs.get n) = bosonic) →
    koszulSign q le (φs.eraseIdx n) = koszulSign q le φs
  | [], _ => by
    simp
  | φ :: φs, ⟨0, h⟩ => by
    simp only [List.length_cons, Fin.zero_eta, List.get_eq_getElem, Fin.val_zero,
      List.getElem_cons_zero, List.eraseIdx_zero, List.tail_cons, koszulSign]
    intro h
    rw [koszulSignInsert_boson _ _ _ h]
    simp only [one_mul]
  | φ :: φs, ⟨n + 1, h⟩ => by
    simp only [List.length_cons, List.get_eq_getElem, List.getElem_cons_succ,
      List.eraseIdx_cons_succ]
    intro h'
    rw [koszulSign, koszulSign, koszulSign_erase_boson q le φs ⟨n, Nat.succ_lt_succ_iff.mp h⟩ h']
    congr 1
    rw [koszulSignInsert_erase_boson q le φ φs ⟨n, Nat.succ_lt_succ_iff.mp h⟩ h']

lemma koszulSign_insertIdx [Std.Total le] [IsTrans 𝓕 le] (φ : 𝓕) :
    (φs : List 𝓕) → (n : ℕ) → (hn : n ≤ φs.length) →
    koszulSign q le (List.insertIdx φs n φ) = 𝓢(q φ, ofList q (φs.take n)) * koszulSign q le φs *
      𝓢(q φ, ofList q ((List.insertionSort le (List.insertIdx φs n φ)).take
      (insertionSortEquiv le (List.insertIdx φs n φ) ⟨n, by
        rw [List.length_insertIdx]
        simp only [hn, ↓reduceIte]
        omega⟩)))
  | [], 0, h => by
    simp [koszulSign]
  | [], n + 1, h => by
    simp at h
  | φ1 :: φs, 0, h => by
    simp only [List.insertIdx_zero, List.insertionSort_cons, List.length_cons, Fin.zero_eta]
    rw [koszulSign]
    trans koszulSign q le (φ1 :: φs) * koszulSignInsert q le φ (φ1 :: φs)
    · ring
    simp only [insertionSortEquiv, List.length_cons, Nat.succ_eq_add_one, orderedInsertEquiv,
      PhysLean.Fin.equivCons_trans, Equiv.trans_apply, PhysLean.Fin.equivCons_zero]
    conv_rhs =>
      enter [2,2, 2, 2]
      rw [orderedInsert_eq_insertIdx_orderedInsertPos]
    conv_rhs =>
      rhs
      erw [← ofList_take_insert]
      change 𝓢(q φ, ofList q ((List.insertionSort le (φ1 :: φs)).take
        (↑(orderedInsertPos le ((List.insertionSort le (φ1 :: φs))) φ))))
      rw [← koszulSignInsert_eq_exchangeSign_take q le]
    rw [ofList_take_zero]
    simp
  | φ1 :: φs, n + 1, h => by
    conv_lhs =>
      rw [List.insertIdx_succ_cons]
      rw [koszulSign]
    rw [koszulSign_insertIdx _ _ _ (Nat.le_of_lt_succ h)]
    conv_rhs =>
      rhs
      simp only [List.insertIdx_succ_cons]
      simp only [List.insertionSort_cons, List.length_cons, insertionSortEquiv, Nat.succ_eq_add_one,
        Equiv.trans_apply, PhysLean.Fin.equivCons_succ]
      erw [orderedInsertEquiv_fin_succ]
      simp only [Fin.eta, Fin.val_cast]
      rhs
      simp [orderedInsert_eq_insertIdx_orderedInsertPos]
    conv_rhs =>
      lhs
      rw [ofList_take_succ_cons, map_mul, koszulSign]
    ring_nf
    conv_lhs =>
      lhs
      rw [mul_assoc, mul_comm]
    rw [mul_assoc]
    conv_rhs =>
      rw [mul_assoc, mul_assoc]
    congr 1
    let rs := (List.insertionSort le (List.insertIdx φs n φ))
    have hnsL : n < (List.insertIdx φs n φ).length := by
      rw [List.length_insertIdx]
      simp only [List.length_cons, add_le_add_iff_right] at h
      simp only [h, ↓reduceIte]
      omega
    let ni : Fin rs.length := (insertionSortEquiv le (List.insertIdx φs n φ))
      ⟨n, hnsL⟩
    let nro : Fin (rs.length + 1) :=
      ⟨↑(orderedInsertPos le rs φ1), orderedInsertPos_lt_length le rs φ1⟩
    rw [koszulSignInsert_insertIdx _ _ _ _ _ _ (Nat.le_of_lt_succ h), koszulSignInsert_cons]
    trans koszulSignInsert q le φ1 φs * (koszulSignCons q le φ1 φ *
      𝓢(q φ, ofList q (rs.take ni)))
    · simp only [rs, ni]
      ring
    trans koszulSignInsert q le φ1 φs * (𝓢(q φ, q φ1) *
          𝓢(q φ, ofList q ((List.insertIdx rs nro φ1).take (nro.succAbove ni))))
    swap
    · simp only [rs, nro, ni]
      ring
    congr 1
    simp only [Fin.succAbove]
    have hns : rs.get ni = φ := by
      simp only [rs]
      rw [← insertionSortEquiv_get]
      simp only [Function.comp_apply, Equiv.symm_apply_apply, List.get_eq_getElem, ni]
      simp_all only [List.length_cons, add_le_add_iff_right, List.getElem_insertIdx_self]
    have hc1 (hninro : ni.castSucc < nro) : ¬ le φ1 φ := by
      rw [← hns]
      exact lt_orderedInsertPos_rel le φ1 rs ni hninro
    have hc2 (hninro : ¬ ni.castSucc < nro) : le φ1 φ := by
      rw [← hns]
      refine gt_orderedInsertPos_rel le φ1 rs ?_ ni hninro
      exact List.pairwise_insertionSort le (List.insertIdx φs n φ)
    by_cases hn : ni.castSucc < nro
    · simp only [hn, ↓reduceIte, Fin.val_castSucc]
      rw [ofList_take_insertIdx_gt]
      swap
      · exact hn
      congr 1
      rw [koszulSignCons_eq_exchangeSign]
      simp only [hc1 hn, ↓reduceIte]
      rw [exchangeSign_symm]
    · simp only [hn, ↓reduceIte, Fin.val_succ]
      rw [ofList_take_insertIdx_le, map_mul, ← mul_assoc]
      · congr 1
        rw [exchangeSign_mul_self, koszulSignCons]
        simp only [hc2 hn, ↓reduceIte]
      · exact Nat.le_of_not_lt hn
      · exact Nat.le_of_lt_succ (orderedInsertPos_lt_length le rs φ1)

lemma insertIdx_eraseIdx {I : Type} : (n : ℕ) → (r : List I) → (hn : n < r.length) →
    List.insertIdx (r.eraseIdx n) n (r.get ⟨n, hn⟩) = r
  | n, [], hn => by
    simp at hn
  | 0, r0 :: r, hn => by
    simp
  | n + 1, r0 :: r, hn => by
    simp only [List.length_cons, List.get_eq_getElem, List.getElem_cons_succ,
      List.eraseIdx_cons_succ, List.insertIdx_succ_cons, List.cons.injEq, true_and]
    exact insertIdx_eraseIdx n r _

lemma koszulSign_eraseIdx [Std.Total le] [IsTrans 𝓕 le] (φs : List 𝓕) (n : Fin φs.length) :
    koszulSign q le (φs.eraseIdx n) = koszulSign q le φs * 𝓢(q (φs.get n), ofList q (φs.take n)) *
    𝓢(q (φs.get n), ofList q (List.take (↑(insertionSortEquiv le φs n))
    (List.insertionSort le φs))) := by
  let φs' := φs.eraseIdx ↑n
  have hφs : List.insertIdx φs' n (φs.get n) = φs := by
    exact insertIdx_eraseIdx n.1 φs n.prop
  conv_rhs =>
    lhs
    lhs
    rw [← hφs]
    rw [koszulSign_insertIdx q le (φs.get n) ((φs.eraseIdx ↑n)) n (by
      rw [List.length_eraseIdx]
      simp only [Fin.is_lt, ↓reduceIte]
      omega)]
    rhs
    enter [2, 2, 2]
    rw [hφs]
  conv_rhs =>
    enter [1, 1, 2, 2, 2, 1, 1]
    rw [insertionSortEquiv_congr _ _ hφs]
  simp only [instCommGroup.eq_1, List.get_eq_getElem]
  trans koszulSign q le (φs.eraseIdx ↑n) *
    (𝓢(q φs[↑n], ofList q ((φs.eraseIdx ↑n).take n)) * 𝓢(q φs[↑n], ofList q (List.take (↑n) φs))) *
    (𝓢(q φs[↑n], ofList q ((List.insertionSort le φs).take (↑((insertionSortEquiv le φs) n)))) *
    𝓢(q φs[↑n], ofList q (List.take (↑((insertionSortEquiv le φs) n)) (List.insertionSort le φs))))
  swap
  · simp only [Fin.getElem_fin]
    rw [Equiv.trans_apply, Equiv.trans_apply]
    simp only [instCommGroup.eq_1, Fin.castOrderIso,
      Equiv.coe_fn_mk, Fin.cast_mk, Fin.eta, Fin.val_cast]
    ring
  conv_rhs =>
    rhs
    rw [exchangeSign_mul_self]
  simp only [instCommGroup.eq_1, Fin.getElem_fin, mul_one]
  conv_rhs =>
    rhs
    rw [ofList_take_eraseIdx, exchangeSign_mul_self]
  simp

lemma koszulSign_eraseIdx_insertionSortMinPos [Std.Total le] [IsTrans 𝓕 le] (φ : 𝓕) (φs : List 𝓕) :
    koszulSign q le ((φ :: φs).eraseIdx (insertionSortMinPos le φ φs)) = koszulSign q le (φ :: φs)
    * 𝓢(q (insertionSortMin le φ φs), ofList q ((φ :: φs).take (insertionSortMinPos le φ φs))) := by
  rw [koszulSign_eraseIdx]
  conv_lhs =>
    rhs
    rhs
    lhs
    simp [insertionSortMinPos]
  erw [Equiv.apply_symm_apply]
  simp only [instCommGroup.eq_1, List.get_eq_getElem, List.length_cons, List.insertionSort,
    List.take_zero, ofList_empty, exchangeSign_bosonic, mul_one, mul_eq_mul_left_iff]
  apply Or.inl
  rfl

lemma koszulSign_swap_eq_rel_cons {ψ φ : 𝓕}
    (h1 : le φ ψ) (h2 : le ψ φ) (φs' : List 𝓕) :
    koszulSign q le (φ :: ψ :: φs') = koszulSign q le (ψ :: φ :: φs') := by
  simp only [Wick.koszulSign, ← mul_assoc, mul_eq_mul_right_iff]
  left
  rw [mul_comm]
  simp [Wick.koszulSignInsert, h1, h2]

lemma koszulSign_swap_eq_rel {ψ φ : 𝓕} (h1 : le φ ψ) (h2 : le ψ φ) : (φs φs' : List 𝓕) →
    koszulSign q le (φs ++ φ :: ψ :: φs') = koszulSign q le (φs ++ ψ :: φ :: φs')
  | [], φs' => by
    simp only [List.nil_append]
    exact koszulSign_swap_eq_rel_cons q le h1 h2 φs'
  | φ'' :: φs, φs' => by
    simp only [List.cons_append, koszulSign]
    rw [koszulSign_swap_eq_rel h1 h2]
    congr 1
    apply Wick.koszulSignInsert_eq_perm
    exact List.Perm.append_left φs (List.Perm.swap ψ φ φs')

lemma koszulSign_eq_rel_eq_stat_append {ψ φ : 𝓕} [IsTrans 𝓕 le]
    (h1 : le φ ψ) (h2 : le ψ φ) (hq : q ψ = q φ) : (φs : List 𝓕) →
    koszulSign q le (φ :: ψ :: φs) = koszulSign q le φs := by
  intro φs
  simp only [koszulSign, ← mul_assoc]
  trans 1 * koszulSign q le φs
  swap
  · simp only [one_mul]
  congr
  simp only [koszulSignInsert, ite_mul, neg_mul]
  simp_all only [and_self, ite_true]
  rw [koszulSignInsert_eq_rel_eq_stat q le h1 h2 hq]
  simp

lemma koszulSign_eq_rel_eq_stat {ψ φ : 𝓕} [IsTrans 𝓕 le]
    (h1 : le φ ψ) (h2 : le ψ φ) (hq : q ψ = q φ) : (φs' φs : List 𝓕) →
    koszulSign q le (φs' ++ φ :: ψ :: φs) = koszulSign q le (φs' ++ φs)
  | [], φs => by
    simp only [List.nil_append]
    exact koszulSign_eq_rel_eq_stat_append q le h1 h2 hq φs
  | φ'' :: φs', φs => by
    simp only [List.cons_append, koszulSign]
    rw [koszulSign_eq_rel_eq_stat h1 h2 hq φs' φs]
    simp only [mul_eq_mul_right_iff]
    left
    trans koszulSignInsert q le φ'' (φ :: ψ :: (φs' ++ φs))
    · apply koszulSignInsert_eq_perm
      exact (List.perm_cons_append_cons φ List.perm_middle.symm).symm
    · rw [koszulSignInsert_eq_remove_same_stat_append q le h1 h2 hq]

lemma koszulSign_of_sorted : (φs : List 𝓕)
    → (hs : List.Pairwise le φs) → koszulSign q le φs = 1
  | [], _ => by
    simp [koszulSign]
  | φ :: φs, h => by
    simp only [koszulSign]
    simp only [List.pairwise_cons] at h
    rw [koszulSign_of_sorted φs h.2]
    simp only [mul_one]
    exact koszulSignInsert_of_le_mem _ _ _ _ h.1

@[simp]
lemma koszulSign_of_insertionSort [Std.Total le] [IsTrans 𝓕 le] (φs : List 𝓕) :
    koszulSign q le (List.insertionSort le φs) = 1 := by
  apply koszulSign_of_sorted
  exact List.pairwise_insertionSort le φs

lemma koszulSign_of_append_eq_insertionSort_left [Std.Total le] [IsTrans 𝓕 le] :
    (φs φs' : List 𝓕) → koszulSign q le (φs ++ φs') =
    koszulSign q le (List.insertionSort le φs ++ φs') * koszulSign q le φs
  | φs, [] => by
    simp
  | φs, φ :: φs' => by
    have h1 : (φs ++ φ :: φs') = List.insertIdx (φs ++ φs') φs.length φ := by
      rw [insertIdx_length_fst_append]
    have h2 : (List.insertionSort le φs ++ φ :: φs') =
        List.insertIdx (List.insertionSort le φs ++ φs') (List.insertionSort le φs).length φ := by
      rw [insertIdx_length_fst_append]
    rw [h1, h2]
    rw [koszulSign_insertIdx _ _ _ _ _ (by simp)]
    simp only [instCommGroup.eq_1, List.take_left', List.length_insertionSort]
    rw [koszulSign_insertIdx _ _ _ _ _ (by simp)]
    simp only [mul_assoc, instCommGroup.eq_1, List.length_insertionSort, List.take_left',
      ofList_insertionSort, mul_eq_mul_left_iff]
    left
    rw [koszulSign_of_append_eq_insertionSort_left φs φs']
    simp only [mul_assoc, mul_eq_mul_left_iff]
    left
    simp only [mul_comm, mul_eq_mul_left_iff]
    left
    congr 3
    · have h2 : (List.insertionSort le φs ++ φ :: φs') =
          List.insertIdx (List.insertionSort le φs ++ φs') φs.length φ := by
        rw [← insertIdx_length_fst_append]
        simp
      rw [insertionSortEquiv_congr _ _ h2.symm]
      simp only [Equiv.trans_apply, RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply, Fin.cast_mk,
        Fin.val_cast]
      rw [insertionSortEquiv_insertionSort_append]
      simp only [finCongr_apply, Fin.val_cast]
      rw [insertionSortEquiv_congr _ _ h1.symm]
      simp
    · rw [insertIdx_length_fst_append]
      rw [show φs.length = (List.insertionSort le φs).length by simp]
      rw [insertIdx_length_fst_append]
      symm
      apply insertionSort_insertionSort_append

lemma koszulSign_of_append_eq_insertionSort [Std.Total le] [IsTrans 𝓕 le] : (φs'' φs φs' : List 𝓕) →
    koszulSign q le (φs'' ++ φs ++ φs') =
    koszulSign q le (φs'' ++ List.insertionSort le φs ++ φs') * koszulSign q le φs
  | [], φs, φs'=> by
    simp only [List.nil_append]
    exact koszulSign_of_append_eq_insertionSort_left q le φs φs'
  | φ'' :: φs'', φs, φs' => by
    simp only [List.cons_append, koszulSign]
    rw [koszulSign_of_append_eq_insertionSort φs'' φs φs', ← mul_assoc]
    congr 2
    apply koszulSignInsert_eq_perm
    refine (List.perm_append_right_iff φs').mpr ?_
    refine List.Perm.append_left φs'' ?_
    exact List.Perm.symm (List.perm_insertionSort le φs)

/-!

# koszulSign with permutations

-/

lemma koszulSign_perm_eq_append [IsTrans 𝓕 le] (φ : 𝓕) (φs φs' φs2 : List 𝓕)
    (hp : φs.Perm φs') : (h : ∀ φ' ∈ φs, le φ φ' ∧ le φ' φ) →
    koszulSign q le (φs ++ φs2) = koszulSign q le (φs' ++ φs2) := by
  let motive (φs φs' : List 𝓕) (hp : φs.Perm φs') : Prop :=
    (h : ∀ φ' ∈ φs, le φ φ' ∧ le φ' φ) →
    koszulSign q le (φs ++ φs2) = koszulSign q le (φs' ++ φs2)
  change motive φs φs' hp
  apply List.Perm.recOn
  · simp [motive]
  · intro x l1 l2 h ih hxφ
    simp_all only [List.mem_cons, or_true, and_self, implies_true, nonempty_prop, forall_const,
      forall_eq_or_imp, List.cons_append, motive]
    simp only [koszulSign, ih, mul_eq_mul_right_iff]
    left
    apply koszulSignInsert_eq_perm
    exact (List.perm_append_right_iff φs2).mpr h
  · intro x y l h
    simp_all only [List.mem_cons, forall_eq_or_imp, List.cons_append]
    apply Wick.koszulSign_swap_eq_rel_cons
    · exact IsTrans.trans y φ x h.1.2 h.2.1.1
    · exact IsTrans.trans x φ y h.2.1.2 h.1.1
  · intro l1 l2 l3 h1 h2 ih1 ih2 h
    simp_all only [and_self, implies_true, nonempty_prop, forall_const, motive]
    refine (ih2 ?_)
    intro φ' hφ
    refine h φ' ?_
    exact (List.Perm.mem_iff (id (List.Perm.symm h1))).mp hφ

lemma koszulSign_perm_eq [IsTrans 𝓕 le] (φ : 𝓕) : (φs1 φs φs' φs2 : List 𝓕) →
    (h : ∀ φ' ∈ φs, le φ φ' ∧ le φ' φ) → (hp : φs.Perm φs') →
    koszulSign q le (φs1 ++ φs ++ φs2) = koszulSign q le (φs1 ++ φs' ++ φs2)
  | [], φs, φs', φs2, h, hp => by
    simp only [List.nil_append]
    exact koszulSign_perm_eq_append q le φ φs φs' φs2 hp h
  | φ1 :: φs1, φs, φs', φs2, h, hp => by
    simp only [List.cons_append, koszulSign]
    have ih := koszulSign_perm_eq φ φs1 φs φs' φs2 h hp
    rw [ih]
    congr 1
    apply koszulSignInsert_eq_perm
    refine (List.perm_append_right_iff φs2).mpr ?_
    exact List.Perm.append_left φs1 hp

end Wick
