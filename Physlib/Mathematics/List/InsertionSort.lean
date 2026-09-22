/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module
public import Physlib.Mathematics.List
import all Physlib.Mathematics.List
/-!
# List lemmas

-/

@[expose] public section

namespace Physlib.List

open _root_.Physlib.Fin
open Physlib
variable {n : Nat}

lemma insertionSortMin_lt_length_succ {α : Type} (r : α → α → Prop) [DecidableRel r]
    (i : α) (l : List α) :
    insertionSortMinPos r i l < (insertionSortDropMinPos r i l).length.succ := by
  simp [insertionSortMinPos, insertionSortDropMinPos, eraseIdx_length']

/-- Given a list `i :: l` the left-most minimal position `a` of `i :: l` wrt `r`
  as an element of `Fin (insertionSortDropMinPos r i l).length.succ`. -/
def insertionSortMinPosFin {α : Type} (r : α → α → Prop) [DecidableRel r] (i : α) (l : List α) :
    Fin (insertionSortDropMinPos r i l).length.succ :=
  ⟨insertionSortMinPos r i l, insertionSortMin_lt_length_succ r i l⟩

lemma insertionSortMin_lt_mem_insertionSortDropMinPos {α : Type} (r : α → α → Prop) [DecidableRel r]
    [Std.Total r] [IsTrans α r] (a : α) (l : List α)
    (i : Fin (insertionSortDropMinPos r a l).length) :
    r (insertionSortMin r a l) ((insertionSortDropMinPos r a l)[i]) := by
  have hl1 := List.pairwise_insertionSort r (a :: l)
  rw [insertionSort_eq_insertionSortMin_cons r a l, List.pairwise_cons] at hl1
  exact hl1.1 _ (by simp)

lemma insertionSortMinPos_insertionSortEquiv {α : Type} (r : α → α → Prop) [DecidableRel r]
    (a : α) (l : List α) :
    insertionSortEquiv r (a ::l) (insertionSortMinPos r a l) =
    ⟨0, by simp [List.orderedInsert_length]⟩ := by
  rw [insertionSortMinPos]
  exact Equiv.apply_symm_apply (insertionSortEquiv r (a :: l)) ⟨0, _⟩

lemma insertionSortEquiv_gt_zero_of_ne_insertionSortMinPos {α : Type} (r : α → α → Prop)
    [DecidableRel r] (a : α) (l : List α) (k : Fin (a :: l).length)
    (hk : k ≠ insertionSortMinPos r a l) :
    ⟨0, by simp [List.orderedInsert_length]⟩ < insertionSortEquiv r (a :: l) k := by
  by_contra hn
  simp only [List.length_cons, not_lt] at hn
  refine hk ((Equiv.eq_symm_apply (insertionSortEquiv r (a :: l))).mpr ?_)
  simp_all only [List.length_cons, ne_eq, Fin.le_def, nonpos_iff_eq_zero]
  exact Fin.ext hn

set_option backward.isDefEq.respectTransparency false in
lemma insertionSortMin_lt_mem_insertionSortDropMinPos_of_lt {α : Type} (r : α → α → Prop)
    [DecidableRel r] (a : α) (l : List α)
    (i : Fin (insertionSortDropMinPos r a l).length)
    (h : (insertionSortMinPosFin r a l).succAbove i < insertionSortMinPosFin r a l) :
    ¬ r ((insertionSortDropMinPos r a l)[i]) (insertionSortMin r a l) := by
  simp only [Fin.getElem_fin, insertionSortMin, List.get_eq_getElem, List.length_cons]
  have h1 : (insertionSortDropMinPos r a l)[(i : ℕ)] =
    (a :: l).get (finCongr (eraseIdx_length_succ (a :: l) (insertionSortMinPos r a l))
    ((insertionSortMinPosFin r a l).succAbove i)) := by
    trans (insertionSortDropMinPos r a l).get i
    simp only [List.get_eq_getElem]
    simp only [insertionSortDropMinPos, List.length_cons, Nat.succ_eq_add_one, finCongr_apply]
    rw [eraseIdx_get]
    simp only [List.length_cons, Function.comp_apply, List.get_eq_getElem, Fin.val_cast]
    rfl
  rw [h1]
  simp only [List.length_cons, Nat.succ_eq_add_one, List.get_eq_getElem]
  apply insertionSortEquiv_order
  exact h
  simp only [List.length_cons, finCongr_apply]
  apply lt_of_eq_of_lt (insertionSortMinPos_insertionSortEquiv r a l)
  apply insertionSortEquiv_gt_zero_of_ne_insertionSortMinPos r a l
  simp only [List.length_cons, ne_eq, Fin.ext_iff, Fin.val_cast]
  have hl : (insertionSortMinPos r a l).val = (insertionSortMinPosFin r a l).val := by
    rfl
  simp only [hl, Nat.succ_eq_add_one, Fin.val_eq_val, ne_eq]
  exact Fin.succAbove_ne (insertionSortMinPosFin r a l) i

lemma insertionSort_insertionSort {α : Type} (r : α → α → Prop) [DecidableRel r]
    [Std.Total r] [IsTrans α r] (l1 : List α) :
    List.insertionSort r (List.insertionSort r l1) = List.insertionSort r l1 := by
  apply List.Pairwise.insertionSort_eq
  exact List.pairwise_insertionSort r l1

lemma orderedInsert_commute {α : Type} (r : α → α → Prop) [DecidableRel r]
    [Std.Total r] [IsTrans α r] (a b : α) (hr : ¬ r a b) : (l : List α) →
    List.orderedInsert r a (List.orderedInsert r b l) =
      List.orderedInsert r b (List.orderedInsert r a l)
  | [] => by
    have hrb : r b a := (Std.Total.total a b).resolve_left hr
    simp [hr, hrb]
  | c :: l => by
    have hrb : r b a := (Std.Total.total a b).resolve_left hr
    simp only [List.orderedInsert]
    by_cases h : r a c
    · simp only [h, ↓reduceIte, List.orderedInsert.eq_2, hrb]
      rw [ite_eq_left (IsTrans.trans (r := r) _ _ _ hrb h)]
      simp only [List.orderedInsert, hr, ↓reduceIte, h]
    · simp only [h, ↓reduceIte, List.orderedInsert.eq_2]
      by_cases hbc : r b c
      · simp [hbc, hr, h]
      · simp only [hbc, ↓reduceIte, List.orderedInsert.eq_2, h, List.cons.injEq, true_and]
        exact orderedInsert_commute r a b hr l

lemma insertionSort_orderedInsert_append {α : Type} (r : α → α → Prop) [DecidableRel r]
    [Std.Total r] [IsTrans α r] (a : α) : (l1 l2 : List α) →
    List.insertionSort r (List.orderedInsert r a l1 ++ l2) = List.insertionSort r (a :: l1 ++ l2)
  | [], l2 => by
    simp
  | b :: l1, l2 => by
    conv_lhs => simp
    by_cases h : r a b
    · simp [h]
    conv_lhs => simp [h]
    rw [insertionSort_orderedInsert_append r a l1 l2]
    simp only [List.cons_append, List.insertionSort_cons]
    rw [orderedInsert_commute r a b h]

lemma insertionSort_insertionSort_append {α : Type} (r : α → α → Prop) [DecidableRel r]
    [Std.Total r] [IsTrans α r] : (l1 l2 : List α) →
    List.insertionSort r (List.insertionSort r l1 ++ l2) = List.insertionSort r (l1 ++ l2)
  | [], l2 => by
    simp
  | a :: l1, l2 => by
    rw [List.insertionSort_cons, insertionSort_orderedInsert_append]
    simp only [List.cons_append, List.insertionSort_cons]
    rw [insertionSort_insertionSort_append r l1 l2]

lemma insertionSort_append_insertionSort_append {α : Type} (r : α → α → Prop) [DecidableRel r]
    [Std.Total r] [IsTrans α r] : (l1 l2 l3 : List α) →
    List.insertionSort r (l1 ++ List.insertionSort r l2 ++ l3) =
      List.insertionSort r (l1 ++ l2 ++ l3)
  | [], l2, l3 => by
    simpa using insertionSort_insertionSort_append r l2 l3
  | a :: l1, l2, l3 => by
    simp only [List.cons_append, List.insertionSort_cons]
    rw [insertionSort_append_insertionSort_append r l1 l2 l3]

@[simp]
lemma orderedInsert_length {α : Type} (r : α → α → Prop) [DecidableRel r] (a : α) (l : List α) :
    (List.orderedInsert r a l).length = (a :: l).length := by
  apply List.Perm.length_eq
  exact List.perm_orderedInsert r a l

lemma takeWhile_orderedInsert {α : Type} (r : α → α → Prop) [DecidableRel r]
    [Std.Total r] [IsTrans α r]
    (a b : α) (hr : ¬ r a b) : (l : List α) →
    (List.takeWhile (fun c => !decide (r a c)) (List.orderedInsert r b l)).length =
    (List.takeWhile (fun c => !decide (r a c)) l).length + 1
  | [] => by
    simp [hr]
  | c :: l => by
    simp only [List.orderedInsert]
    by_cases h : r b c
    · simp [h, hr]
    · simp only [h, ↓reduceIte]
      have hl : ¬ r a c :=
        fun hn => h (IsTrans.trans _ _ _ ((Std.Total.total a b).resolve_left hr) hn)
      simp only [hl, decide_false, Bool.not_false, List.takeWhile_cons_of_pos, List.length_cons,
        add_left_inj]
      exact takeWhile_orderedInsert r a b hr l

lemma takeWhile_orderedInsert' {α : Type} (r : α → α → Prop) [DecidableRel r]
    [Std.Total r] [IsTrans α r]
    (a b : α) (hr : ¬ r a b) : (l : List α) →
    (List.takeWhile (fun c => !decide (r b c)) (List.orderedInsert r a l)).length =
    (List.takeWhile (fun c => !decide (r b c)) l).length
  | [] => by
    simp [List.orderedInsert, (Std.Total.total a b).resolve_left hr]
  | c :: l => by
    have hrba : r b a := (Std.Total.total a b).resolve_left hr
    simp only [List.orderedInsert]
    by_cases h : r b c
    · by_cases hac : r a c <;> simp [h, hac, hrba]
    · by_cases hac : r a c
      · exact absurd (IsTrans.trans _ _ _ hrba hac) h
      · simp only [hac, ↓reduceIte, h, decide_false, Bool.not_false, List.takeWhile_cons_of_pos,
        List.length_cons, add_left_inj]
        exact takeWhile_orderedInsert' r a b hr l

set_option backward.isDefEq.respectTransparency false in
lemma insertionSortEquiv_commute {α : Type} (r : α → α → Prop) [DecidableRel r]
    [Std.Total r] [IsTrans α r] (a b : α) (hr : ¬ r a b) (n : ℕ) : (l : List α) →
    (hn : n + 2 < (a :: b :: l).length) →
    insertionSortEquiv r (a :: b :: l) ⟨n + 2, hn⟩ = (finCongr (by simp))
    (insertionSortEquiv r (b :: a :: l) ⟨n + 2, hn⟩) := by
  have hrba : r b a := (Std.Total.total a b).resolve_left hr
  intro l hn
  simp only [List.insertionSort, List.length_cons, insertionSortEquiv, Nat.succ_eq_add_one,
    equivCons_trans, Equiv.trans_apply, equivCons_succ, finCongr_apply]
  conv_lhs => erw [equivCons_succ]
  conv_rhs => erw [equivCons_succ]
  simp only [Equiv.toFun_as_coe]
  conv_lhs =>
    rhs
    rhs
    erw [orderedInsertEquiv_succ]
  conv_lhs => erw [orderedInsertEquiv_fin_succ]
  simp only [Fin.eta, Fin.val_cast]
  conv_rhs =>
    rhs
    rhs
    erw [orderedInsertEquiv_succ]
  conv_rhs => erw [orderedInsertEquiv_fin_succ]
  ext
  simp only [Fin.val_cast, Fin.eta, Fin.cast_cast]
  let a1 : Fin ((List.orderedInsert r b (List.insertionSort r l)).length + 1) :=
    ⟨↑(orderedInsertPos r (List.orderedInsert r b (List.insertionSort r l)) a),
      orderedInsertPos_lt_length r (List.orderedInsert r b (List.insertionSort r l)) a⟩
  let b1 : Fin ((List.insertionSort r l).length + 1) :=
    ⟨↑(orderedInsertPos r (List.insertionSort r l) b),
      orderedInsertPos_lt_length r (List.insertionSort r l) b⟩
  let a2 : Fin ((List.insertionSort r l).length + 1) :=
    ⟨↑(orderedInsertPos r (List.insertionSort r l) a),
      orderedInsertPos_lt_length r (List.insertionSort r l) a⟩
  let b2 : Fin ((List.orderedInsert r a (List.insertionSort r l)).length + 1) :=
    ⟨↑(orderedInsertPos r (List.orderedInsert r a (List.insertionSort r l)) b),
      orderedInsertPos_lt_length r (List.orderedInsert r a (List.insertionSort r l)) b⟩
  have ht : (List.takeWhile (fun c => !decide (r b c)) (List.insertionSort r l))
      = (List.takeWhile (fun c => !decide (r b c))
        ((List.takeWhile (fun c => !decide (r a c)) (List.insertionSort r l)))) := by
      rw [List.takeWhile_takeWhile]
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Bool.decide_and,
        decide_not]
      congr
      funext c
      simp only [Bool.eq_self_and, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
      intro hbc hac
      refine hbc ?_
      exact IsTrans.trans _ _ _ hrba hac
  have ha1 : b1.1 ≤ a2.1 := by
    simp only [orderedInsertPos, decide_not, b1]
    rw [ht]
    apply List.Sublist.length_le
    simp only [decide_not]
    exact List.takeWhile_sublist _
  have ha2 : a1.1 = a2.1 + 1 := by
    simp only [orderedInsertPos, decide_not, a1, a2]
    rw [takeWhile_orderedInsert]
    exact hr
  have hb : b1.1 = b2.1 := by
    simp only [orderedInsertPos, decide_not, b1, b2]
    rw [takeWhile_orderedInsert']
    exact hr
  let n := ((insertionSortEquiv r l) ⟨n, by simpa using hn⟩)
  change (a1.succAbove ⟨b1.succAbove n, _⟩).1 = (b2.succAbove ⟨a2.succAbove n, _⟩).1
  have hba : b2.1 ≤ a2.1 := hb ▸ ha1
  have val_succAbove {m : ℕ} (p : Fin (m + 1)) (i : Fin m) :
      (p.succAbove i).1 = if i.1 < p.1 then i.1 else i.1 + 1 := by
    rw [Fin.succAbove]
    split <;> simp_all [Fin.lt_def]
  simp only [val_succAbove, ha2, hb]
  split_ifs <;> omega

set_option backward.isDefEq.respectTransparency false in
lemma insertionSortEquiv_orderedInsert_append {α : Type} (r : α → α → Prop) [DecidableRel r]
    [Std.Total r] [IsTrans α r] (a a2 : α) : (l1 l2 : List α) →
    (insertionSortEquiv r (List.orderedInsert r a l1 ++ a2 :: l2) ⟨l1.length + 1, by
      simp⟩)
    = (finCongr (by
      simp only [List.cons_append, List.insertionSort_cons, orderedInsert_length, List.length_cons,
        List.length_insertionSort, List.length_append]
      omega))
      ((insertionSortEquiv r (a :: l1 ++ a2 :: l2)) ⟨l1.length + 1, by simp⟩)
  | [], l2 => by
    simp only [List.insertionSort, List.length_nil, zero_add, Fin.mk_one, List.cons_append,
      List.nil_append, List.foldr_cons, finCongr_refl, List.length_cons]
    rfl
  | b :: l1, l2 => by
    by_cases h : r a b
    · have h1 : (List.orderedInsert r a (b :: l1) ++ a2 :: l2) = (a :: b :: l1 ++ a2 :: l2) := by
        simp [h]
      rw [insertionSortEquiv_congr _ _ h1]
      simp
    · have h1 : (List.orderedInsert r a (b :: l1) ++ a2 :: l2) =
        (b :: List.orderedInsert r a (l1) ++ a2 :: l2) := by
        simp [h]
      rw [insertionSortEquiv_congr _ _ h1]
      simp only [List.cons_append, List.length_cons,
        Equiv.trans_apply, RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply, Fin.cast_mk,
        finCongr_apply]
      conv_lhs => simp [insertionSortEquiv]
      rw [insertionSortEquiv_orderedInsert_append r a]
      have hl : (List.insertionSort r (List.orderedInsert r a l1 ++ a2 :: l2)) =
        List.insertionSort r (a :: l1 ++ a2 :: l2) :=
        insertionSort_orderedInsert_append r a l1 (a2 :: l2)
      rw [orderedInsertEquiv_congr _ _ _ hl]
      conv_lhs =>
        enter [2, 1, 2, 1]
        simp [List.insertionSort_cons]
      simp only [List.insertionSort, List.foldr_cons, List.cons_append, List.length_cons,
        finCongr_apply, Equiv.trans_apply, RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply,
        Fin.cast_succ_eq, Fin.cast_cast, Fin.cast_eq_self]
      change Fin.cast _
        ((insertionSortEquiv r (b :: a :: (l1 ++ a2 :: l2))) ⟨l1.length + 2, by simp⟩) = _
      have hl : l1.length + 1 +1 = l1.length + 2 := by omega
      simp only [List.insertionSort, List.length_cons, hl]
      conv_rhs =>
        erw [insertionSortEquiv_commute _ _ _ h _ _]
      simp
      rfl

set_option backward.isDefEq.respectTransparency false in
lemma insertionSortEquiv_insertionSort_append {α : Type} (r : α → α → Prop) [DecidableRel r]
    [Std.Total r] [IsTrans α r] (a : α) : (l1 l2 : List α) →
    (insertionSortEquiv r (List.insertionSort r l1 ++ a :: l2) ⟨l1.length, by simp⟩)
    = finCongr (by simp) (insertionSortEquiv r (l1 ++ a :: l2) ⟨l1.length, by simp⟩)
  | [], l2 => by
    apply insertionSortEquiv_congr_apply
    simp
  | b :: l1, l2 => by
    simp only [List.insertionSort, List.length_cons, List.cons_append, finCongr_apply]
    have hl := insertionSortEquiv_orderedInsert_append r b a (List.insertionSort r l1) l2
    simp only [List.length_insertionSort, List.cons_append, List.length_cons,
      finCongr_apply] at hl
    erw [hl]
    have ih := insertionSortEquiv_insertionSort_append r a l1 l2
    simp only [insertionSortEquiv, Nat.succ_eq_add_one, List.insertionSort, Equiv.trans_apply,
      equivCons_succ]
    erw [ih]
    have hl : (List.insertionSort r (List.insertionSort r l1 ++ a :: l2)) =
        (List.insertionSort r (l1 ++ a :: l2)) := by
      exact insertionSort_insertionSort_append r l1 (a :: l2)
    erw [orderedInsertEquiv_congr _ _ _ hl]
    simp only [List.foldr_cons, finCongr_apply]
    rfl

/-!

## Insertion sort with equal fields

-/

lemma orderedInsert_filter_of_pos {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTrans α r] (a : α) (p : α → Prop) [DecidablePred p] (h : p a) : (l : List α) →
    (hl : l.Pairwise r) →
    List.filter p (List.orderedInsert r a l) = List.orderedInsert r a (List.filter p l)
  | [], hl => by
    simp only [List.orderedInsert, List.filter_nil, List.orderedInsert_nil, List.filter_eq_self,
      List.mem_singleton, decide_eq_true_eq, forall_eq]
    exact h
  | b :: l, hl => by
    simp only [List.orderedInsert]
    by_cases hpb : p b <;> by_cases hab : r a b
    · simp only [hab, ↓reduceIte, hpb, decide_true, List.filter_cons_of_pos,
      List.orderedInsert.eq_2]
      rw [List.filter_cons_of_pos (by simp [h])]
      rw [List.filter_cons_of_pos (by simp [hpb])]
    · simp only [hab, ↓reduceIte]
      rw [List.filter_cons_of_pos (by simp [hpb])]
      rw [List.filter_cons_of_pos (by simp [hpb])]
      simp only [List.orderedInsert, hab, ↓reduceIte, List.cons.injEq, true_and]
      simp only [List.pairwise_cons] at hl
      exact orderedInsert_filter_of_pos r a p h l hl.2
    · simp only [hab, ↓reduceIte]
      rw [List.filter_cons_of_pos (by simp [h]),
        List.filter_cons_of_neg (by simp [hpb])]
      rw [List.orderedInsert_eq_take_drop]
      have hl : List.takeWhile (fun b => decide ¬r a b)
          (List.filter (fun b => decide (p b)) l) = [] := by
        rw [List.takeWhile_eq_nil_iff]
        intro c hc
        simp only [List.get_eq_getElem, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true,
          decide_eq_false_iff_not] at hc
        apply hc
        apply IsTrans.trans a b _ hab
        simp only [List.pairwise_cons] at hl
        exact hl.1 _ (List.mem_filter.mp (List.getElem_mem c)).1
      rw [hl]
      simp only [decide_not, List.nil_append, List.cons.injEq, true_and]
      conv_lhs => rw [← List.takeWhile_append_dropWhile (p := fun b => decide ¬r a b)
        (l := List.filter (fun b => decide (p b)) l)]
      rw [hl]
      simp
    · simp only [hab, ↓reduceIte]
      rw [List.filter_cons_of_neg (by simp [hpb])]
      rw [List.filter_cons_of_neg (by simp [hpb])]
      simp only [List.pairwise_cons] at hl
      exact orderedInsert_filter_of_pos r a p h l hl.2

lemma orderedInsert_filter_of_neg {α : Type} (r : α → α → Prop) [DecidableRel r]
    (a : α) (p : α → Prop) [DecidablePred p] (h : ¬ p a) (l : List α) :
    List.filter p (List.orderedInsert r a l) = (List.filter p l) := by
  rw [List.orderedInsert_eq_take_drop]
  simp only [decide_not, List.filter_append]
  rw [List.filter_cons_of_neg (by simp [h]), ← List.filter_append, List.takeWhile_append_dropWhile]

lemma insertionSort_filter {α : Type} (r : α → α → Prop) [DecidableRel r] [Std.Total r]
    [IsTrans α r] (p : α → Prop) [DecidablePred p] : (l : List α) →
    List.insertionSort r (List.filter p l) =
    List.filter p (List.insertionSort r l)
  | [] => by simp
  | a :: l => by
    simp only [List.insertionSort_cons]
    by_cases h : p a
    · rw [orderedInsert_filter_of_pos r a p h _ (List.pairwise_insertionSort r l),
        List.filter_cons_of_pos (by simpa using h)]
      simp only [List.insertionSort_cons]
      rw [insertionSort_filter]
    · rw [orderedInsert_filter_of_neg r a p h, List.filter_cons_of_neg (by simpa using h),
        insertionSort_filter]

lemma takeWhile_sorted_eq_filter {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTrans α r] (a : α) : (l : List α) → (hl : l.Pairwise r) →
    List.takeWhile (fun c => ¬ r a c) l = List.filter (fun c => ¬ r a c) l
  | [], _ => by simp
  | b :: l, hl => by
    simp only [List.pairwise_cons] at hl
    by_cases hb : ¬ r a b
    · simp only [decide_not, hb, decide_false, Bool.not_false, List.takeWhile_cons_of_pos,
      List.filter_cons_of_pos, List.cons.injEq, true_and]
      simpa using takeWhile_sorted_eq_filter r a l hl.2
    · simp_all only [Decidable.not_not, decide_not, decide_true, Bool.not_true, Bool.false_eq_true,
      not_false_eq_true, List.takeWhile_cons_of_neg, List.filter_cons_of_neg, List.nil_eq,
      List.filter_eq_nil_iff, Bool.not_eq_eq_eq_not, decide_eq_false_iff_not]
      exact fun c hc => IsTrans.trans a b c hb (hl.1 c hc)

lemma dropWhile_sorted_eq_filter {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTrans α r] (a : α) : (l : List α) → (hl : l.Pairwise r) →
    List.dropWhile (fun c => ¬ r a c) l = List.filter (fun c => r a c) l
  | [], _ => by simp
  | b :: l, hl => by
    simp only [List.pairwise_cons] at hl
    by_cases hb : ¬ r a b
    · simp only [decide_not, hb, decide_false, Bool.not_false, List.dropWhile_cons_of_pos,
      Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg]
      simpa using dropWhile_sorted_eq_filter r a l hl.2
    · simp_all only [Decidable.not_not, decide_not, decide_true, Bool.not_true, Bool.false_eq_true,
      not_false_eq_true, List.dropWhile_cons_of_neg, List.filter_cons_of_pos, List.cons.injEq,
      true_and]
      symm
      rw [List.filter_eq_self]
      intro c hc
      simpa using IsTrans.trans a b c hb (hl.1 c hc)

lemma dropWhile_sorted_eq_filter_filter {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTrans α r] (a : α) :(l : List α) → (hl : l.Pairwise r) →
    List.filter (fun c => r a c) l =
    List.filter (fun c => r a c ∧ r c a) l ++ List.filter (fun c => r a c ∧ ¬ r c a) l
  | [], _ => by
    simp
  | b :: l, hl => by
    simp only [List.pairwise_cons] at hl
    by_cases hb : ¬ r a b
    · simp only [hb, decide_false, Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg,
      Bool.decide_and, Bool.false_and, decide_not]
      simpa using dropWhile_sorted_eq_filter_filter r a l hl.2
    · simp_all only [Decidable.not_not, decide_true, List.filter_cons_of_pos, Bool.decide_and,
      decide_not]
      by_cases hba : r b a
      · simp only [hba, decide_true, Bool.not_true, Bool.and_false, Bool.false_eq_true,
        not_false_eq_true, List.filter_cons_of_neg]
        rw [List.filter_cons_of_pos, dropWhile_sorted_eq_filter_filter]
        simp only [Bool.decide_and, decide_not, List.cons_append]
        exact hl.2
        simp_all
      · simp only [hba, decide_false, Bool.and_false, Bool.false_eq_true, not_false_eq_true,
        List.filter_cons_of_neg]
        have h1 : List.filter (fun c => decide (r a c) && decide (r c a)) l = [] := by
          rw [@List.filter_eq_nil_iff]
          intro c hc
          simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
          intro hac hca
          exact hba (IsTrans.trans b c a (hl.1 c hc) hca)
        rw [h1, dropWhile_sorted_eq_filter_filter]
        simp only [Bool.decide_and, h1, decide_not, List.nil_append]
        rw [List.filter_cons_of_pos]
        simp_all only [List.filter_eq_nil_iff, Bool.and_eq_true, decide_eq_true_eq, not_and,
          decide_true, decide_false, Bool.not_false, Bool.and_self]
        exact hl.2

lemma filter_rel_eq_insertionSort {α : Type} (r : α → α → Prop) [DecidableRel r]
    [Std.Total r] [IsTrans α r] (a : α) : (l : List α) →
    List.filter (fun c => r a c ∧ r c a) (l.insertionSort r) =
    List.filter (fun c => r a c ∧ r c a) l
  | [] => by simp
  | b :: l => by
    simp only [List.insertionSort_cons]
    by_cases h : r a b ∧ r b a
    · have hl := orderedInsert_filter_of_pos r b (fun c => r a c ∧ r c a) h
        (List.insertionSort r l) (List.pairwise_insertionSort r l)
      simp only [Bool.decide_and] at hl ⊢
      rw [hl]
      rw [List.orderedInsert_eq_take_drop]
      have ht : List.takeWhile (fun b_1 => decide ¬r b b_1)
        (List.filter (fun b => decide (r a b) && decide (r b a))
          (List.insertionSort r l)) = [] := by
        rw [List.takeWhile_eq_nil_iff]
        intro hl
        simp only [List.get_eq_getElem, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true,
          decide_eq_false_iff_not, Decidable.not_not]
        have hx := List.getElem_mem hl
        simp only [List.mem_filter, List.mem_insertionSort, Bool.and_eq_true,
          decide_eq_true_eq] at hx
        apply IsTrans.trans b a _ h.2
        simp_all
      rw [ht]
      simp only [decide_not, List.nil_append]
      rw [List.filter_cons_of_pos]
      simp only [List.cons.injEq, true_and]
      have ih := filter_rel_eq_insertionSort r a l
      simp only [Bool.decide_and] at ih
      rw [← ih]
      have htd := List.takeWhile_append_dropWhile (p := fun b_1 => decide ¬r b b_1)
        (l := List.filter (fun b => decide (r a b) && decide (r b a)) (List.insertionSort r l))
      simp only [decide_not] at htd
      conv_rhs => rw [← htd]
      simp only [List.self_eq_append_left, List.takeWhile_eq_nil_iff, List.get_eq_getElem,
        Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Decidable.not_not]
      intro hl
      have hx := List.getElem_mem hl
      simp only [List.mem_filter, List.mem_insertionSort, Bool.and_eq_true, decide_eq_true_eq] at hx
      apply IsTrans.trans b a _ h.2
      simp_all only [decide_not, List.takeWhile_eq_nil_iff, List.get_eq_getElem,
        Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Decidable.not_not,
        List.takeWhile_append_dropWhile]
      simp_all
    · have hl := orderedInsert_filter_of_neg r b (fun c => r a c ∧ r c a) h (List.insertionSort r l)
      simp only [Bool.decide_and] at hl ⊢
      rw [hl]
      rw [List.filter_cons_of_neg]
      have ih := filter_rel_eq_insertionSort r a l
      simp_all only [not_and, Bool.decide_and]
      simpa using h

lemma insertionSort_of_eq_list {α : Type} (r : α → α → Prop) [DecidableRel r]
    [Std.Total r] [IsTrans α r] (a : α) (l1 l l2 : List α)
    (h : ∀ b ∈ l, r a b ∧ r b a) :
    List.insertionSort r (l1 ++ l ++ l2) =
    (List.takeWhile (fun c => ¬ r a c) ((l1 ++ l2).insertionSort r))
    ++ (List.filter (fun c => r a c ∧ r c a) l1)
    ++ l
    ++ (List.filter (fun c => r a c ∧ r c a) l2)
    ++ (List.filter (fun c => r a c ∧ ¬ r c a) ((l1 ++ l2).insertionSort r)) := by
  have hlt : List.takeWhile (fun c => ¬ r a c) ((l1 ++ l ++ l2).insertionSort r)
      = List.takeWhile (fun c => ¬ r a c) ((l1 ++ l2).insertionSort r) := by
    rw [takeWhile_sorted_eq_filter, takeWhile_sorted_eq_filter]
    rw [← insertionSort_filter, ← insertionSort_filter]
    congr 1
    simp only [decide_not, List.append_assoc, List.filter_append, List.append_cancel_left_eq,
      List.append_left_eq_self, List.filter_eq_nil_iff, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not, Decidable.not_not]
    exact fun b hb => (h b hb).1
    exact List.pairwise_insertionSort r (l1 ++ l2)
    exact List.pairwise_insertionSort r (l1 ++ l ++ l2)
  conv_lhs => rw [← List.takeWhile_append_dropWhile (p := fun c => decide ¬ r a c)
    (l := (l1 ++ l ++ l2).insertionSort r), hlt]
  simp only [decide_not, Bool.decide_and, List.append_assoc, List.append_cancel_left_eq]
  have h1 := dropWhile_sorted_eq_filter r a (List.insertionSort r (l1 ++ (l ++ l2)))
  simp only [decide_not] at h1
  rw [h1, dropWhile_sorted_eq_filter_filter, filter_rel_eq_insertionSort]
  simp only [Bool.decide_and, List.filter_append, decide_not, List.append_assoc,
    List.append_cancel_left_eq]
  congr 1
  simp only [List.filter_eq_self, Bool.and_eq_true, decide_eq_true_eq]
  exact h
  congr 1
  have h1 := insertionSort_filter r (fun c => decide (r a c) && !decide (r c a)) (l1 ++ (l ++ l2))
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, Bool.decide_and, decide_not, List.filter_append] at h1
  rw [← h1]
  have h2 := insertionSort_filter r (fun c => decide (r a c) && !decide (r c a)) (l1 ++ l2)
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, Bool.decide_and, decide_not, List.filter_append] at h2
  rw [← h2]
  congr
  have hl : List.filter (fun b => decide (r a b) && !decide (r b a)) l = [] := by
    rw [@List.filter_eq_nil_iff]
    intro c hc
    simp_all
  rw [hl]
  simp only [List.nil_append]
  exact List.pairwise_insertionSort r (l1 ++ (l ++ l2))
  exact List.pairwise_insertionSort r (l1 ++ (l ++ l2))

lemma insertionSort_of_takeWhile_filter {α : Type} (r : α → α → Prop) [DecidableRel r]
    [Std.Total r] [IsTrans α r] (a : α) (l1 l2 : List α) :
    List.insertionSort r (l1 ++ l2) =
    (List.takeWhile (fun c => ¬ r a c) ((l1 ++ l2).insertionSort r))
    ++ (List.filter (fun c => r a c ∧ r c a) l1)
    ++ (List.filter (fun c => r a c ∧ r c a) l2)
    ++ (List.filter (fun c => r a c ∧ ¬ r c a) ((l1 ++ l2).insertionSort r)) := by
  simpa using insertionSort_of_eq_list r a l1 [] l2 (by simp)

end Physlib.List
