/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Mathematics.Fin
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.List.TakeWhile
/-!
# List lemmas

-/
namespace PhysLean.List

open Fin
open PhysLean
variable {n : Nat}

lemma takeWile_eraseIdx {I : Type} (P : I → Prop) [DecidablePred P] :
    (l : List I) → (i : ℕ) → (hi : ∀ (i j : Fin l.length), i < j → P (l.get j) → P (l.get i)) →
    List.takeWhile P (List.eraseIdx l i) = (List.takeWhile P l).eraseIdx i
  | [], _, h => by
    rfl
  | a :: [], 0, h => by
    simp only [List.takeWhile, List.eraseIdx_zero]
    split
    · rfl
    · rfl
  | a :: [], Nat.succ n, h => by
    simp only [Nat.succ_eq_add_one, List.eraseIdx_cons_succ, List.eraseIdx_nil]
    rw [List.eraseIdx_of_length_le]
    have h1 : (List.takeWhile P [a]).length ≤ [a].length :=
        List.Sublist.length_le (List.takeWhile_sublist _)
    simp only [List.length_singleton] at h1
    omega
  | a :: b :: l, 0, h => by
    simp only [List.takeWhile, List.eraseIdx_zero]
    by_cases hPb : P b
    · have hPa : P a := by
        simpa using h ⟨0, by simp⟩ ⟨1, by simp⟩ (by simp [Fin.lt_def]) (by simpa using hPb)
      simp [hPb, hPa]
    · simp only [hPb, decide_false]
      simp_all only [List.length_cons, List.get_eq_getElem, List.tail_cons, decide_false,
        Bool.false_eq_true, not_false_eq_true, List.takeWhile_cons_of_neg, List.nil_eq]
      split
      · rfl
      · rfl
  | a :: b :: l, Nat.succ n, h => by
    simp only [Nat.succ_eq_add_one, List.eraseIdx_cons_succ]
    by_cases hPa : P a
    · dsimp only [List.takeWhile]
      simp only [hPa, decide_true, List.eraseIdx_cons_succ, List.cons.injEq, true_and]
      rw [takeWile_eraseIdx]
      · rfl
      · intro i j hij hP
        simpa using h (Fin.succ i) (Fin.succ j) (by simpa using hij) (by simpa using hP)
    · simp [hPa]

lemma dropWile_eraseIdx {I : Type} (P : I → Prop) [DecidablePred P] :
    (l : List I) → (i : ℕ) → (hi : ∀ (i j : Fin l.length), i < j → P (l.get j) → P (l.get i)) →
    List.dropWhile P (List.eraseIdx l i) =
      if (List.takeWhile P l).length ≤ i then
        (List.dropWhile P l).eraseIdx (i - (List.takeWhile P l).length)
      else (List.dropWhile P l)
  | [], _, h => by
    simp
  | a :: [], 0, h => by
    simp only [List.eraseIdx_zero, nonpos_iff_eq_zero, List.length_eq_zero_iff,
      List.takeWhile_eq_nil_iff, List.length_singleton, zero_lt_one, Fin.zero_eta, Fin.isValue,
      List.get_eq_getElem, Fin.val_eq_zero, List.getElem_cons_zero, decide_eq_true_eq, forall_const,
      List.dropWhile, zero_le, Nat.sub_eq_zero_of_le, ite_not]
    simp_all only [List.length_cons, List.length_nil, List.get_eq_getElem, Fin.val_eq_zero,
      List.getElem_cons_zero, implies_true, List.tail_cons, List.dropWhile_nil, decide_true,
      decide_false, ite_self]
  | a :: [], Nat.succ n, h => by
    simp only [List.dropWhile, List.takeWhile, Nat.succ_eq_add_one]
    rw [List.eraseIdx_of_length_le]
    simp_all only [List.length_singleton, List.get_eq_getElem, Fin.val_eq_zero,
      List.getElem_cons_zero, implies_true]
    split
    next x heq =>
      simp_all only [decide_eq_true_eq, decide_true, List.dropWhile_cons_of_pos, List.dropWhile_nil,
        List.length_singleton, le_add_iff_nonneg_left, zero_le, ↓reduceIte,
        add_tsub_cancel_right, List.eraseIdx_nil]
    next x heq =>
      simp_all only [decide_eq_false_iff_not, decide_false, Bool.false_eq_true, not_false_eq_true,
        List.dropWhile_cons_of_neg, List.length_nil, le_add_iff_nonneg_left,
        zero_le, ↓reduceIte, tsub_zero, List.eraseIdx_cons_succ, List.eraseIdx_nil]
    exact Nat.le_add_left [a].length n
  | a :: b :: l, 0, h => by
    simp only [List.dropWhile, List.takeWhile, nonpos_iff_eq_zero, List.length_eq_zero_iff, zero_le,
      Nat.sub_eq_zero_of_le, List.eraseIdx_zero]
    by_cases hPb : P b
    · have hPa : P a := by
        simpa using h ⟨0, by simp⟩ ⟨1, by simp⟩ (by simp [Fin.lt_def]) (by simpa using hPb)
      simp [hPb, hPa]
    · simp only [List.tail_cons, hPb, decide_false, Bool.false_eq_true, not_false_eq_true,
      List.dropWhile_cons_of_neg]
      simp_all only [List.length_cons, List.get_eq_getElem]
      split
      next x heq =>
        simp_all only [decide_eq_true_eq, List.cons_ne_self, ↓reduceIte]
      next x heq => simp_all only [decide_eq_false_iff_not, ↓reduceIte, List.tail_cons]
  | a :: b :: l, Nat.succ n, h => by
    simp only [Nat.succ_eq_add_one, List.eraseIdx_cons_succ]
    by_cases hPb : P b
    · have hPa : P a := by
        simpa using h ⟨0, by simp⟩ ⟨1, by simp⟩ (by simp [Fin.lt_def]) (by simpa using hPb)
      simp only [List.dropWhile, hPa, decide_true, List.takeWhile, hPb, List.length_cons,
        add_le_add_iff_right, Nat.reduceSubDiff]
      rw [dropWile_eraseIdx]
      simp_all only [List.length_cons, List.get_eq_getElem, decide_true, List.takeWhile_cons_of_pos,
        List.dropWhile_cons_of_pos]
      intro i j hij hP
      simpa using h (Fin.succ i) (Fin.succ j) (by simpa using hij) (by simpa using hP)
    · simp only [List.dropWhile, List.takeWhile, hPb, decide_false]
      by_cases hPa : P a
      · rw [dropWile_eraseIdx]
        simp only [hPa, decide_true, hPb, decide_false, Bool.false_eq_true, not_false_eq_true,
          List.takeWhile_cons_of_neg, List.length_nil, zero_le, ↓reduceIte, List.dropWhile,
          tsub_zero, List.length_singleton, le_add_iff_nonneg_left, add_tsub_cancel_right]
        intro i j hij hP
        simpa using h (Fin.succ i) (Fin.succ j) (by simpa using hij) (by simpa using hP)
      · simp [hPa]

lemma insertionSort_length {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (l : List I) :
    (List.insertionSort le1 l).length = l.length :=
  List.Perm.length_eq (List.perm_insertionSort le1 l)

/-- The position `r0` ends up in `r` on adding it via `List.orderedInsert _ r0 r`. -/
def orderedInsertPos {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (r : List I) (r0 : I) :
    Fin (List.orderedInsert le1 r0 r).length :=
  ⟨(List.takeWhile (fun b => decide ¬ le1 r0 b) r).length, by
    rw [List.orderedInsert_length]
    have h1 : (List.takeWhile (fun b => decide ¬le1 r0 b) r).length ≤ r.length :=
      List.Sublist.length_le (List.takeWhile_sublist fun b => decide ¬le1 r0 b)
    omega⟩

lemma orderedInsertPos_lt_length {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (r : List I)
    (r0 : I) : orderedInsertPos le1 r r0 < (r0 :: r).length := by
  simp only [orderedInsertPos, List.length_cons]
  have h1 : (List.takeWhile (fun b => decide ¬le1 r0 b) r).length ≤ r.length :=
    List.Sublist.length_le (List.takeWhile_sublist fun b => decide ¬le1 r0 b)
  omega

@[simp]
lemma orderedInsert_get_orderedInsertPos {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r : List I) (r0 : I) :
    (List.orderedInsert le1 r0 r)[(orderedInsertPos le1 r r0).val] = r0 := by
  simp [List.orderedInsert_eq_take_drop, orderedInsertPos]

@[simp]
lemma orderedInsert_eraseIdx_orderedInsertPos {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r : List I) (r0 : I) :
    (List.orderedInsert le1 r0 r).eraseIdx ↑(orderedInsertPos le1 r r0) = r := by
  simp only [List.orderedInsert_eq_take_drop]
  rw [List.eraseIdx_append_of_length_le]
  · simp [orderedInsertPos]
  · rfl

lemma orderedInsertPos_cons {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r : List I) (r0 r1 : I) :
    (orderedInsertPos le1 (r1 ::r) r0).val =
    if le1 r0 r1 then ⟨0, by simp⟩ else (Fin.succ (orderedInsertPos le1 r r0)) := by
  simp only [List.orderedInsert.eq_2, orderedInsertPos, List.takeWhile, decide_not, Fin.zero_eta,
    Fin.succ_mk]
  by_cases h : le1 r0 r1
  · simp [h]
  · simp [h]

lemma orderedInsertPos_sigma {I : Type} {f : I → Type}
    (le1 : I → I → Prop) [DecidableRel le1] (l : List (Σ i, f i))
    (k : I) (a : f k) :
    (orderedInsertPos (fun (i j : Σ i, f i) => le1 i.1 j.1) l ⟨k, a⟩).1 =
    (orderedInsertPos le1 (List.map (fun (i : Σ i, f i) => i.1) l) k).1 := by
  simp only [orderedInsertPos, decide_not]
  induction l with
  | nil =>
    simp
  | cons a l ih =>
    simp only [List.takeWhile]
    obtain ⟨fst, snd⟩ := a
    simp_all only
    split
    next x heq => simp_all
    next x heq => simp_all

lemma orderedInsert_get_lt {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r : List I) (r0 : I) (i : ℕ)
    (hi : i < orderedInsertPos le1 r r0) :
    (List.orderedInsert le1 r0 r)[i] = r.get ⟨i, by
      simp only [orderedInsertPos] at hi
      have h1 : (List.takeWhile (fun b => decide ¬le1 r0 b) r).length ≤ r.length :=
        List.Sublist.length_le (List.takeWhile_sublist fun b => decide ¬le1 r0 b)
      omega⟩ := by
  simp only [orderedInsertPos, decide_not] at hi
  simp only [List.orderedInsert_eq_take_drop, decide_not, List.get_eq_getElem]
  rw [List.getElem_append]
  simp only [hi, ↓reduceDIte]
  rw [List.IsPrefix.getElem]
  exact List.takeWhile_prefix fun b => !decide (le1 r0 b)

lemma orderedInsertPos_take_orderedInsert {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r : List I) (r0 : I) :
    (List.take (orderedInsertPos le1 r r0) (List.orderedInsert le1 r0 r)) =
    List.takeWhile (fun b => decide ¬le1 r0 b) r := by
  simp [orderedInsertPos, List.orderedInsert_eq_take_drop]

lemma orderedInsertPos_take_eq_orderedInsert {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r : List I) (r0 : I) :
    List.take (orderedInsertPos le1 r r0) r =
    List.take (orderedInsertPos le1 r r0) (List.orderedInsert le1 r0 r) := by
  refine List.ext_get ?_ ?_
  · simp only [List.length_take, Fin.is_le', inf_of_le_left, inf_eq_left]
    exact Nat.le_of_lt_succ (orderedInsertPos_lt_length le1 r r0)
  · intro n h1 h2
    simp only [List.get_eq_getElem, List.getElem_take]
    rw [orderedInsert_get_lt le1 r r0 n]
    rfl
    simp only [List.length_take, lt_inf_iff] at h1
    exact h1.1

lemma orderedInsertPos_drop_eq_orderedInsert {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r : List I) (r0 : I) :
    List.drop (orderedInsertPos le1 r r0) r =
    List.drop (orderedInsertPos le1 r r0).succ (List.orderedInsert le1 r0 r) := by
  conv_rhs => simp [orderedInsertPos, List.orderedInsert_eq_take_drop]
  have hr : r = List.takeWhile (fun b => !decide (le1 r0 b)) r ++
      List.dropWhile (fun b => !decide (le1 r0 b)) r := by
    exact Eq.symm (List.takeWhile_append_dropWhile)
  conv_lhs =>
    rhs
    rw [hr]
  rw [List.drop_append]
  simp [orderedInsertPos]

lemma orderedInsertPos_take {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r : List I) (r0 : I) :
    List.take (orderedInsertPos le1 r r0) r = List.takeWhile (fun b => decide ¬le1 r0 b) r := by
  rw [orderedInsertPos_take_eq_orderedInsert,orderedInsertPos_take_orderedInsert]

lemma orderedInsertPos_drop {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r : List I) (r0 : I) :
    List.drop (orderedInsertPos le1 r r0) r = List.dropWhile (fun b => decide ¬le1 r0 b) r := by
  rw [orderedInsertPos_drop_eq_orderedInsert]
  simp [orderedInsertPos, List.orderedInsert_eq_take_drop]

lemma orderedInsertPos_succ_take_orderedInsert {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r : List I) (r0 : I) :
    (List.take (orderedInsertPos le1 r r0).succ (List.orderedInsert le1 r0 r)) =
    List.takeWhile (fun b => decide ¬le1 r0 b) r ++ [r0] := by
  simp [orderedInsertPos, List.orderedInsert_eq_take_drop, List.take_append]

lemma lt_orderedInsertPos_rel {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r0 : I) (r : List I) (n : Fin r.length)
    (hn : n.val < (orderedInsertPos le1 r r0).val) : ¬ le1 r0 (r.get n) := by
  have htake : r.get n ∈ List.take (orderedInsertPos le1 r r0) r := by
    rw [@List.mem_take_iff_getElem]
    use n
    simp only [List.get_eq_getElem, lt_inf_iff, Fin.is_lt, and_true, exists_prop]
    exact hn
  rw [orderedInsertPos_take] at htake
  simpa using List.mem_takeWhile_imp htake

lemma lt_orderedInsertPos_rel_fin {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r0 : I) (r : List I) (n : Fin (List.orderedInsert le1 r0 r).length)
    (hn : n < (orderedInsertPos le1 r r0)) : ¬ le1 r0 ((List.orderedInsert le1 r0 r).get n) := by
  have htake : (List.orderedInsert le1 r0 r).get n ∈ List.take (orderedInsertPos le1 r r0) r := by
    rw [orderedInsertPos_take_eq_orderedInsert, List.mem_take_iff_getElem]
    use n
    simp only [List.get_eq_getElem, Fin.is_le', inf_of_le_left, Fin.val_fin_lt, exists_prop,
      and_true]
    exact hn
  rw [orderedInsertPos_take] at htake
  simpa using List.mem_takeWhile_imp htake

lemma gt_orderedInsertPos_rel {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    [Std.Total le1] [IsTrans I le1] (r0 : I) (r : List I) (hs : List.Pairwise le1 r)
    (n : Fin r.length)
    (hn : ¬ n.val < (orderedInsertPos le1 r r0).val) : le1 r0 (r.get n) := by
  have hrsSorted : List.Pairwise le1 (List.orderedInsert le1 r0 r) :=
    List.Pairwise.orderedInsert r0 r hs
  apply List.Pairwise.rel_of_mem_take_of_mem_drop (i := (orderedInsertPos le1 r r0).succ) hrsSorted
  · rw [orderedInsertPos_succ_take_orderedInsert]
    simp
  · rw [← orderedInsertPos_drop_eq_orderedInsert]
    refine List.mem_drop_iff_getElem.mpr ?_
    use n - (orderedInsertPos le1 r r0).val
    have hn : ↑n - ↑(orderedInsertPos le1 r r0) + ↑(orderedInsertPos le1 r r0) < r.length := by
      omega
    use hn
    congr
    omega

lemma orderedInsert_eraseIdx_lt_orderedInsertPos {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r : List I) (r0 : I) (i : ℕ)
    (hi : i < orderedInsertPos le1 r r0)
    (hr : ∀ (i j : Fin r.length), i < j → ¬le1 r0 (r.get j) → ¬le1 r0 (r.get i)) :
    (List.orderedInsert le1 r0 r).eraseIdx i = List.orderedInsert le1 r0 (r.eraseIdx i) := by
  conv_lhs => simp only [List.orderedInsert_eq_take_drop]
  rw [List.eraseIdx_append_of_lt_length]
  · simp only [List.orderedInsert_eq_take_drop]
    congr 1
    · rw [takeWile_eraseIdx]
      exact hr
    · rw [dropWile_eraseIdx]
      simp only [orderedInsertPos, decide_not] at hi
      have hi' : ¬ (List.takeWhile (fun b => !decide (le1 r0 b)) r).length ≤ ↑i := by omega
      simp only [decide_not, hi', ↓reduceIte]
      exact fun i j a a_1 => hr i j a a_1
  · exact hi

lemma orderedInsert_eraseIdx_orderedInsertPos_le {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r : List I) (r0 : I) (i : ℕ)
    (hi : orderedInsertPos le1 r r0 ≤ i)
    (hr : ∀ (i j : Fin r.length), i < j → ¬le1 r0 (r.get j) → ¬le1 r0 (r.get i)) :
    (List.orderedInsert le1 r0 r).eraseIdx (Nat.succ i) =
    List.orderedInsert le1 r0 (r.eraseIdx i) := by
  conv_lhs => simp only [List.orderedInsert_eq_take_drop]
  rw [List.eraseIdx_append_of_length_le]
  · simp only [List.orderedInsert_eq_take_drop]
    congr 1
    · rw [takeWile_eraseIdx, List.eraseIdx_of_length_le]
      simp only [orderedInsertPos, decide_not] at hi
      simp only [decide_not]
      omega
      exact hr
    · simp only [Nat.succ_eq_add_one]
      have hn : (i + 1 - (List.takeWhile (fun b => (decide (¬ le1 r0 b))) r).length)
        = (i - (List.takeWhile (fun b => decide (¬ le1 r0 b)) r).length) + 1 := by
        simp only [orderedInsertPos] at hi
        omega
      rw [hn]
      simp only [List.eraseIdx_cons_succ, List.cons.injEq, true_and]
      rw [dropWile_eraseIdx, if_pos]
      · rw [orderedInsertPos] at hi
        omega
      · exact hr
  · simp only [orderedInsertPos] at hi
    omega

/-- The equivalence between `Fin (r0 :: r).length` and `Fin (List.orderedInsert le1 r0 r).length`
  according to where the elements map, i.e. `0` is taken to `orderedInsertPos le1 r r0`. -/
def orderedInsertEquiv {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (r : List I) (r0 : I) :
    Fin (r.length + 1) ≃ Fin (List.orderedInsert le1 r0 r).length := by
  let e2 : Fin (List.orderedInsert le1 r0 r).length ≃ Fin (r0 :: r).length :=
    (Fin.castOrderIso (List.orderedInsert_length le1 r r0)).toEquiv
  let e3 : Fin (r0 :: r).length ≃ Fin 1 ⊕ Fin (r).length := finExtractOne 0
  let e4 : Fin (r0 :: r).length ≃ Fin 1 ⊕ Fin (r).length :=
    finExtractOne ⟨orderedInsertPos le1 r r0, orderedInsertPos_lt_length le1 r r0⟩
  exact e3.trans (e4.symm.trans e2.symm)

@[simp]
lemma orderedInsertEquiv_zero {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (r : List I)
    (r0 : I) : orderedInsertEquiv le1 r r0 0 = orderedInsertPos le1 r r0 := by
  simp [orderedInsertEquiv]

lemma orderedInsertEquiv_succ {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (r : List I)
    (r0 : I) (n : ℕ) (hn : Nat.succ n < (r0 :: r).length) :
    orderedInsertEquiv le1 r r0 ⟨Nat.succ n, hn⟩ =
    Fin.cast (List.orderedInsert_length le1 r r0).symm
    ((Fin.succAbove ⟨(orderedInsertPos le1 r r0), orderedInsertPos_lt_length le1 r r0⟩)
    ⟨n, Nat.succ_lt_succ_iff.mp hn⟩) := by
  simp only [List.length_cons, orderedInsertEquiv, Nat.succ_eq_add_one, Equiv.trans_apply]
  match r with
  | [] =>
    simp [List.orderedInsert.eq_1]
  | r1 :: r =>
    simp only [List.orderedInsert.eq_2, List.length_cons]
    rw [finExtractOne_apply_neq]
    simp only [List.orderedInsert.eq_2, orderedInsertPos, decide_not, Nat.succ_eq_add_one,
      finExtractOne_symm_inr_apply]
    rfl
    exact ne_of_beq_false rfl

lemma orderedInsertEquiv_fin_succ {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (r : List I)
    (r0 : I) (n : Fin r.length) :
    orderedInsertEquiv le1 r r0 n.succ = Fin.cast (List.orderedInsert_length le1 r r0).symm
    ((Fin.succAbove ⟨(orderedInsertPos le1 r r0), orderedInsertPos_lt_length le1 r r0⟩)
      ⟨n, n.isLt⟩) := by
  simp only [orderedInsertEquiv, Equiv.trans_apply]
  match r with
  | [] =>
    simp [List.orderedInsert.eq_1]
  | r1 :: r =>
    simp only [List.orderedInsert.eq_2, List.length_cons, Fin.eta]
    rw [finExtractOne_apply_neq]
    simp only [orderedInsertPos, List.orderedInsert.eq_2, decide_not, Nat.succ_eq_add_one,
      finExtractOne_symm_inr_apply]
    rfl
    exact ne_of_beq_false rfl

lemma orderedInsertEquiv_monotone_fin_succ {I : Type}
    (le1 : I → I → Prop) [DecidableRel le1] (r : List I)
    (r0 : I) (n m : Fin r.length)
    (hx : orderedInsertEquiv le1 r r0 n.succ < orderedInsertEquiv le1 r r0 m.succ) :
    n < m := by
  rw [orderedInsertEquiv_fin_succ, orderedInsertEquiv_fin_succ, Fin.lt_def] at hx
  simp only [Fin.eta, Fin.val_cast, Fin.val_fin_lt] at hx
  rw [Fin.succAbove_lt_succAbove_iff] at hx
  exact hx

lemma orderedInsertEquiv_congr {α : Type} {r : α → α → Prop} [DecidableRel r] (a : α)
    (l l' : List α) (h : l = l') :
    orderedInsertEquiv r l a = (Fin.castOrderIso (by simp [h])).toEquiv.trans
    ((orderedInsertEquiv r l' a).trans (Fin.castOrderIso (by simp [h])).toEquiv) := by
  subst h
  rfl

lemma get_eq_orderedInsertEquiv {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (r : List I)
    (r0 : I) :
    (r0 :: r).get = (List.orderedInsert le1 r0 r).get ∘ (orderedInsertEquiv le1 r r0) := by
  funext x
  match x with
  | ⟨0, h⟩ =>
    simp
  | ⟨Nat.succ n, h⟩ =>
    simp only [List.length_cons, Nat.succ_eq_add_one, List.get_eq_getElem, List.getElem_cons_succ,
      Function.comp_apply]
    rw [orderedInsertEquiv_succ]
    simp only [Fin.succAbove, Fin.castSucc_mk, Fin.mk_lt_mk, Fin.succ_mk, Fin.val_cast]
    by_cases hn : n < ↑(orderedInsertPos le1 r r0)
    · simp [hn, orderedInsert_get_lt]
    · simp only [hn, ↓reduceIte, List.orderedInsert_eq_take_drop, decide_not]
      rw [List.getElem_append]
      have hn' : ¬ n + 1 < (List.takeWhile (fun b => !decide (le1 r0 b)) r).length := by
        simp only [orderedInsertPos, decide_not, not_lt] at hn
        omega
      simp only [hn', ↓reduceDIte]
      have hnn : n + 1 - (List.takeWhile (fun b => !decide (le1 r0 b)) r).length =
        (n - (List.takeWhile (fun b => !decide (le1 r0 b)) r).length) + 1 := by
        simp only [orderedInsertPos, decide_not, not_lt] at hn
        omega
      simp only [hnn, List.getElem_cons_succ]
      conv_rhs =>
        rw [List.IsSuffix.getElem (List.dropWhile_suffix fun b => !decide (le1 r0 b))]
      congr
      have hr : r.length = (List.takeWhile (fun b => !decide (le1 r0 b)) r).length +
          (List.dropWhile (fun b => !decide (le1 r0 b)) r).length := by
        rw [← List.length_append]
        congr
        exact Eq.symm (List.takeWhile_append_dropWhile)
      simp only [hr, add_tsub_cancel_right]
      omega

lemma orderedInsertEquiv_get {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (r : List I)
    (r0 : I) :
    (r0 :: r).get ∘ (orderedInsertEquiv le1 r r0).symm = (List.orderedInsert le1 r0 r).get := by
  rw [get_eq_orderedInsertEquiv le1]
  funext x
  simp

lemma orderedInsert_eraseIdx_orderedInsertEquiv_zero
    {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (r : List I) (r0 : I) :
    (List.orderedInsert le1 r0 r).eraseIdx (orderedInsertEquiv le1 r r0 ⟨0, by simp⟩) = r := by
  simp [orderedInsertEquiv]

lemma orderedInsert_eraseIdx_orderedInsertEquiv_succ
    {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (r : List I) (r0 : I) (n : ℕ)
    (hn : Nat.succ n < (r0 :: r).length)
    (hr : ∀ (i j : Fin r.length), i < j → ¬le1 r0 (r.get j) → ¬le1 r0 (r.get i)) :
    (List.orderedInsert le1 r0 r).eraseIdx (orderedInsertEquiv le1 r r0 ⟨Nat.succ n, hn⟩) =
    (List.orderedInsert le1 r0 (r.eraseIdx n)) := by
  induction r with
  | nil =>
    simp at hn
  | cons r1 r ih =>
    rw [orderedInsertEquiv_succ]
    simp only [List.length_cons, Fin.succAbove,
      Fin.castSucc_mk, Fin.mk_lt_mk, Fin.succ_mk, Fin.val_cast]
    by_cases hn' : n < (orderedInsertPos le1 (r1 :: r) r0)
    · simp only [hn', ↓reduceIte]
      rw [orderedInsert_eraseIdx_lt_orderedInsertPos le1 (r1 :: r) r0 n hn' hr]
    · simp only [hn', ↓reduceIte]
      rw [orderedInsert_eraseIdx_orderedInsertPos_le le1 (r1 :: r) r0 n _ hr]
      omega

lemma orderedInsert_eraseIdx_orderedInsertEquiv_fin_succ
    {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (r : List I) (r0 : I) (n : Fin r.length)
    (hr : ∀ (i j : Fin r.length), i < j → ¬le1 r0 (r.get j) → ¬le1 r0 (r.get i)) :
    (List.orderedInsert le1 r0 r).eraseIdx (orderedInsertEquiv le1 r r0 n.succ) =
    (List.orderedInsert le1 r0 (r.eraseIdx n)) := by
  have hn : n.succ = ⟨n.val + 1, by omega⟩ := by
    rw [Fin.ext_iff]
    rfl
  rw [hn]
  exact orderedInsert_eraseIdx_orderedInsertEquiv_succ le1 r r0 n.val _ hr

lemma orderedInsertEquiv_sigma {I : Type} {f : I → Type}
    (le1 : I → I → Prop) [DecidableRel le1] (l : List (Σ i, f i))
    (i : I) (a : f i) :
    (orderedInsertEquiv (fun i j => le1 i.fst j.fst) l ⟨i, a⟩) =
    (Fin.castOrderIso (by simp)).toEquiv.trans
    ((orderedInsertEquiv le1 (List.map (fun i => i.1) l) i).trans
    (Fin.castOrderIso (by simp [List.orderedInsert_length])).toEquiv) := by
  ext x
  match x with
  | ⟨0, h0⟩ =>
    simp only [Fin.zero_eta, Equiv.trans_apply, RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply,
      Fin.cast_zero, Fin.val_cast]
    rw [orderedInsertEquiv_zero, orderedInsertEquiv_zero]
    simp [orderedInsertPos_sigma]
  | ⟨Nat.succ n, h0⟩ =>
    simp only [Nat.succ_eq_add_one, Equiv.trans_apply, RelIso.coe_fn_toEquiv,
      Fin.castOrderIso_apply, Fin.cast_mk, Fin.val_cast]
    erw [orderedInsertEquiv_succ, orderedInsertEquiv_succ]
    simp only [orderedInsertPos_sigma, Fin.val_cast]
    rw [Fin.succAbove, Fin.succAbove]
    simp only [Fin.castSucc_mk, Fin.mk_lt_mk, Fin.succ_mk]
    split
    · rfl
    · rfl

set_option maxHeartbeats 350000
lemma orderedInsert_eq_insertIdx_orderedInsertPos {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r : List I) (r0 : I) :
    List.orderedInsert le1 r0 r = List.insertIdx r (orderedInsertPos le1 r r0).1 r0 := by
  apply List.ext_get
  · simp only [List.orderedInsert_length]
    rw [List.length_insertIdx]
    have h1 := orderedInsertPos_lt_length le1 r r0
    exact (if_pos (Nat.le_of_succ_le_succ h1)).symm
  intro n h1 h2
  obtain ⟨n', hn'⟩ := (orderedInsertEquiv le1 r r0).surjective ⟨n, h1⟩
  rw [← hn']
  have hn'' : n = ((orderedInsertEquiv le1 r r0) n').val := by rw [hn']
  subst hn''
  rw [← orderedInsertEquiv_get]
  simp only [List.length_cons, Function.comp_apply, Equiv.symm_apply_apply, List.get_eq_getElem]
  match n' with
  | ⟨0, h0⟩ =>
    simp only [List.getElem_cons_zero, Fin.zero_eta, orderedInsertEquiv_zero,
      List.getElem_insertIdx_self]
  | ⟨Nat.succ n', h0⟩ =>
    simp only [Nat.succ_eq_add_one, List.getElem_cons_succ]
    have hr := orderedInsertEquiv_succ le1 r r0 n' h0
    trans (List.insertIdx r (↑(orderedInsertPos le1 r r0)) r0).get
      ⟨↑((orderedInsertEquiv le1 r r0) ⟨n' +1, h0⟩), h2⟩
    swap
    · rfl
    rw [Fin.ext_iff] at hr
    have hx : (⟨↑((orderedInsertEquiv le1 r r0) ⟨n' +1, h0⟩), h2⟩ :
        Fin (List.insertIdx r (↑(orderedInsertPos le1 r r0)) r0).length) =
      ⟨((⟨↑(orderedInsertPos le1 r r0),
      orderedInsertPos_lt_length le1 r r0⟩ : Fin ((r).length + 1))).succAbove
      ⟨n', Nat.succ_lt_succ_iff.mp h0⟩, by
          erw [← hr]
          exact h2⟩ := by
      rw [Fin.ext_iff]
      simp only
      simpa using hr
    rw [hx]
    simp only [Fin.succAbove, Fin.castSucc_mk, Fin.mk_lt_mk, Fin.succ_mk, List.get_eq_getElem]
    by_cases hn' : n' < ↑(orderedInsertPos le1 r r0)
    · simp only [hn', ↓reduceIte]
      erw [List.getElem_insertIdx_of_lt]
      exact hn'
    · simp only [hn', ↓reduceIte]
      rw [List.getElem_insertIdx_of_gt]
      · rfl
      · omega

/-- The equivalence between `Fin l.length ≃ Fin (List.insertionSort r l).length` induced by the
  sorting algorithm. -/
def insertionSortEquiv {α : Type} (r : α → α → Prop) [DecidableRel r] : (l : List α) →
    Fin l.length ≃ Fin (List.insertionSort r l).length
  | [] => Equiv.refl _
  | a :: l =>
    (Fin.equivCons (insertionSortEquiv r l)).trans (orderedInsertEquiv r (List.insertionSort r l) a)

lemma insertionSortEquiv_get {α : Type} {r : α → α → Prop} [DecidableRel r] : (l : List α) →
    l.get ∘ (insertionSortEquiv r l).symm = (List.insertionSort r l).get
  | [] => by rfl
  | a :: l => by
    rw [insertionSortEquiv]
    change ((a :: l).get ∘ ((Fin.equivCons (insertionSortEquiv r l))).symm) ∘
      (orderedInsertEquiv r (List.insertionSort r l) a).symm = _
    have hl : (a :: l).get ∘ ((Fin.equivCons (insertionSortEquiv r l))).symm =
        (a :: List.insertionSort r l).get := by
      ext x
      match x with
      | ⟨0, h⟩ => rfl
      | ⟨Nat.succ x, h⟩ =>
        change _ = (List.insertionSort r l).get _
        rw [← insertionSortEquiv_get (r := r) l]
        rfl
    rw [hl, orderedInsertEquiv_get r (List.insertionSort r l) a]
    rfl

lemma insertionSortEquiv_congr {α : Type} {r : α → α → Prop} [DecidableRel r] (l l' : List α)
    (h : l = l') : insertionSortEquiv r l = (Fin.castOrderIso (by simp [h])).toEquiv.trans
      ((insertionSortEquiv r l').trans (Fin.castOrderIso (by simp [h])).toEquiv) := by
  subst h
  rfl

lemma insertionSortEquiv_congr_apply {α : Type} {r : α → α → Prop} [DecidableRel r] (l l' : List α)
    (h : l = l') (i : Fin l.length) :
    insertionSortEquiv r l i =
    Fin.cast (by simp [h])
    ((insertionSortEquiv r l') (Fin.cast (by simp [h]) i)) := by
  rw [insertionSortEquiv_congr l l' h]
  simp

lemma insertionSort_get_comp_insertionSortEquiv {α : Type} {r : α → α → Prop} [DecidableRel r]
    (l : List α) : (List.insertionSort r l).get ∘ (insertionSortEquiv r l) = l.get := by
  rw [← insertionSortEquiv_get]
  funext x
  simp

lemma insertionSort_eq_ofFn {α : Type} {r : α → α → Prop} [DecidableRel r] (l : List α) :
    List.insertionSort r l = List.ofFn (l.get ∘ (insertionSortEquiv r l).symm) := by
  rw [insertionSortEquiv_get (r := r)]
  exact (List.ofFn_get (List.insertionSort r l)).symm

lemma insertionSortEquiv_order {α : Type} {r : α → α → Prop} [DecidableRel r] :
    (l : List α) → (i : Fin l.length) → (j : Fin l.length) → (hij : i < j)
    → (hij' : insertionSortEquiv r l j < insertionSortEquiv r l i) →
    ¬ r l[i] l[j]
  | [], i, _, _, _ => Fin.elim0 i
  | a :: as, ⟨0, hi⟩, ⟨j + 1, hj⟩, hij, hij' => by
    simp only [List.length_cons, Fin.zero_eta, Fin.getElem_fin, Fin.val_zero,
      List.getElem_cons_zero, List.getElem_cons_succ]
    nth_rewrite 2 [insertionSortEquiv] at hij'
    simp only [List.length_cons, Nat.succ_eq_add_one, Fin.zero_eta,
      Equiv.trans_apply, equivCons_zero] at hij'
    have hx := orderedInsertEquiv_zero r (List.insertionSort r as) a
    simp only at hx
    convert lt_orderedInsertPos_rel_fin r a (List.insertionSort r as) _ hij'
    change _ = ((List.insertionSort r (a :: as))).get ((insertionSortEquiv r (a :: as)) ⟨j + 1, hj⟩)
    rw [← insertionSortEquiv_get]
    simp
  | a :: as, ⟨i + 1, hi⟩, ⟨j + 1, hj⟩, hij, hij' => by
    simp only [List.length_cons, insertionSortEquiv, Nat.succ_eq_add_one, Equiv.trans_apply,
      equivCons_succ] at hij'
    have h1 := orderedInsertEquiv_monotone_fin_succ _ _ _ _ _ hij'
    have h2 := insertionSortEquiv_order as ⟨i, Nat.succ_lt_succ_iff.mp hi⟩
      ⟨j, Nat.succ_lt_succ_iff.mp hj⟩ (by simpa using hij) h1
    simpa using h2

/-- Optional erase of an element in a list. For `none` returns the list, for `some i` returns
  the list with the `i`'th element erased. -/
def optionErase {I : Type} (l : List I) (i : Option (Fin l.length)) : List I :=
  match i with
  | none => l
  | some i => List.eraseIdx l i

lemma eraseIdx_length' {I : Type} (l : List I) (i : Fin l.length) :
    (List.eraseIdx l i).length = l.length - 1 := by
  simp [List.length_eraseIdx]

lemma eraseIdx_length {I : Type} (l : List I) (i : Fin l.length) :
    (List.eraseIdx l i).length + 1 = l.length := by
  simp only [List.length_eraseIdx, Fin.is_lt, ↓reduceIte]
  have hi := i.prop
  omega

lemma eraseIdx_length_succ {I : Type} (l : List I) (i : Fin l.length) :
    (List.eraseIdx l i).length.succ = l.length := by
  simp only [List.length_eraseIdx, Fin.is_lt, ↓reduceIte]
  have hi := i.prop
  omega

lemma eraseIdx_cons_length {I : Type} (a : I) (l : List I) (i : Fin (a :: l).length) :
    (List.eraseIdx (a :: l) i).length= l.length := by
  simp [List.length_eraseIdx]

lemma eraseIdx_get {I : Type} (l : List I) (i : Fin l.length) :
    (List.eraseIdx l i).get = l.get ∘ (Fin.cast (eraseIdx_length l i)) ∘
    (Fin.cast (eraseIdx_length l i).symm i).succAbove := by
  ext x
  simp only [Function.comp_apply, List.get_eq_getElem, List.getElem_eraseIdx]
  simp only [Fin.succAbove, Fin.val_cast]
  by_cases hi: x.castSucc < Fin.cast (Eq.symm (eraseIdx_length l i)) i
  · simp only [hi, ↓reduceIte, Fin.val_castSucc, dite_eq_left_iff, not_lt]
    intro h
    rw [Fin.lt_def] at hi
    simp_all only [Fin.val_castSucc, Fin.val_cast]
    omega
  · simp only [hi, ↓reduceIte, Fin.val_succ]
    rw [Fin.lt_def] at hi
    simp only [Fin.val_castSucc, Fin.val_cast, not_lt] at hi
    have hn : ¬ x.val < i.val := by omega
    simp [hn]

lemma eraseIdx_insertionSort {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    [Std.Total le1] [IsTrans I le1] :
    (n : ℕ) → (r : List I) → (hn : n < r.length) →
    (List.insertionSort le1 r).eraseIdx ↑((insertionSortEquiv le1 r) ⟨n, hn⟩)
    = List.insertionSort le1 (r.eraseIdx n)
  | 0, [], _ => by rfl
  | 0, (r0 :: r), hn => by
    simp only [List.insertionSort, List.foldr_cons, List.length_cons, insertionSortEquiv,
      Nat.succ_eq_add_one, Fin.zero_eta, Equiv.trans_apply, equivCons_zero, orderedInsertEquiv_zero,
      orderedInsert_eraseIdx_orderedInsertPos, List.eraseIdx_zero, List.tail_cons]
  | Nat.succ n, [], hn => by rfl
  | Nat.succ n, (r0 :: r), hn => by
    simp only [List.insertionSort, List.length_cons, insertionSortEquiv, Nat.succ_eq_add_one,
      Equiv.trans_apply, equivCons_succ]
    have hOr := orderedInsert_eraseIdx_orderedInsertEquiv_fin_succ le1
      (List.insertionSort le1 r) r0 ((insertionSortEquiv le1 r) ⟨n, by simpa using hn⟩)
    erw [hOr]
    congr
    refine eraseIdx_insertionSort le1 n r _
    intro i j hij hn
    have hx := List.Pairwise.rel_get_of_lt (R := le1) (l := (List.insertionSort le1 r))
      (List.pairwise_insertionSort le1 r) hij
    have ht (i j k : I) (hij : le1 i j) (hjk : ¬ le1 k j) : ¬ le1 k i := by
      intro hik
      have ht := IsTrans.trans (r := le1) k i j hik hij
      exact hjk ht
    exact ht ((List.insertionSort le1 r).get i) ((List.insertionSort le1 r).get j) r0 hx hn

lemma eraseIdx_insertionSort_fin {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    [Std.Total le1] [IsTrans I le1] (r : List I) (n : Fin r.length) :
    (List.insertionSort le1 r).eraseIdx ↑((PhysLean.List.insertionSortEquiv le1 r) n)
    = List.insertionSort le1 (r.eraseIdx n) :=
  eraseIdx_insertionSort le1 n.val r (Fin.prop n)

/-- Given a list `i :: l` the left-most minimal position `a` of `i :: l` wrt `r`.
  That is the first position
  of `l` such that for every element `(i :: l)[b]` before that position
  `r ((i :: l)[b]) ((i :: l)[a])` is not true. The use of `i :: l` here
  rather then just `l` is to ensure that such a position exists. . -/
def insertionSortMinPos {α : Type} (r : α → α → Prop) [DecidableRel r] (i : α) (l : List α) :
    Fin (i :: l).length := (insertionSortEquiv r (i :: l)).symm ⟨0, by
    rw [insertionSort_length]
    exact Nat.zero_lt_succ l.length⟩

/-- The element of `i :: l` at `insertionSortMinPos`. -/
def insertionSortMin {α : Type} (r : α → α → Prop) [DecidableRel r] (i : α) (l : List α) :
    α := (i :: l).get (insertionSortMinPos r i l)

lemma insertionSortMin_eq_insertionSort_head {α : Type} (r : α → α → Prop) [DecidableRel r]
    (i : α) (l : List α) :
    insertionSortMin r i l = (List.insertionSort r (i :: l)).head (by
    refine List.ne_nil_of_length_pos ?_
    rw [insertionSort_length]
    exact Nat.zero_lt_succ l.length) := by
  trans (List.insertionSort r (i :: l)).get (⟨0, by
    rw [insertionSort_length]; exact Nat.zero_lt_succ l.length⟩)
  · rw [← insertionSortEquiv_get]
    rfl
  · exact List.get_mk_zero
      (Eq.mpr (id (congrArg (fun _a => 0 < _a) (insertionSort_length r (i :: l))))
        (Nat.zero_lt_succ l.length))

/-- The list remaining after dropping the element at the position determined by
  `insertionSortMinPos`. -/
def insertionSortDropMinPos {α : Type} (r : α → α → Prop) [DecidableRel r] (i : α) (l : List α) :
    List α := (i :: l).eraseIdx (insertionSortMinPos r i l)

lemma insertionSort_eq_insertionSortMin_cons {α : Type} (r : α → α → Prop) [DecidableRel r]
    [Std.Total r] [IsTrans α r] (i : α) (l : List α) :
    List.insertionSort r (i :: l) =
    (insertionSortMin r i l) :: List.insertionSort r (insertionSortDropMinPos r i l) := by
  rw [insertionSortDropMinPos, ← eraseIdx_insertionSort_fin]
  conv_rhs =>
    rhs
    rhs
    rw [insertionSortMinPos, Equiv.apply_symm_apply]
  simp only [List.insertionSort, List.eraseIdx_zero]
  rw [insertionSortMin_eq_insertionSort_head]
  exact (List.cons_head_tail _).symm

/-- Optional erase of an element in a list, with addition for `none`. For `none` adds `a` to the
  front of the list, for `some i` removes the `i`th element of the list (does not add `a`).
  E.g. `optionEraseZ [0, 1, 2] 4 none = [4, 0, 1, 2]` and
  `optionEraseZ [0, 1, 2] 4 (some 1) = [0, 2]`. -/
def optionEraseZ {I : Type} (l : List I) (a : I) (i : Option (Fin l.length)) : List I :=
  match i with
  | none => a :: l
  | some i => List.eraseIdx l i

@[simp]
lemma optionEraseZ_some_length {I : Type} (l : List I) (a : I) (i : (Fin l.length)) :
    (optionEraseZ l a (some i)).length = l.length - 1 := by
  simp [optionEraseZ, List.length_eraseIdx]

lemma optionEraseZ_ext {I : Type} {l l' : List I} {a a' : I} {i : Option (Fin l.length)}
    {i' : Option (Fin l'.length)} (hl : l = l') (ha : a = a')
    (hi : Option.map (Fin.cast (by rw [hl])) i = i') :
    optionEraseZ l a i = optionEraseZ l' a' i' := by
  subst hl
  subst ha
  cases hi
  congr
  simp

lemma mem_take_finrange : (n m : ℕ) → (a : Fin n) → a ∈ List.take m (List.finRange n) ↔ a.val < m
  | 0, m, a => Fin.elim0 a
  | n+1, 0, a => by
    simp
  | n +1, m + 1, ⟨0, h⟩ => by
    simp [List.finRange_succ]
  | n +1, m + 1, ⟨i + 1, h⟩ => by
    simp only [List.finRange_succ, List.take_succ_cons, List.mem_cons, Fin.ext_iff, Fin.val_zero,
      AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, false_or, add_lt_add_iff_right]
    rw [← List.map_take, @List.mem_map]
    apply Iff.intro
    · intro h
      obtain ⟨a, ha⟩ := h
      rw [mem_take_finrange n m a, Fin.ext_iff] at ha
      simp_all only [Fin.val_succ, add_left_inj]
      omega
    · intro h1
      use ⟨i, Nat.succ_lt_succ_iff.mp h⟩
      simp only [Fin.succ_mk, and_true]
      rw [mem_take_finrange n m ⟨i, Nat.succ_lt_succ_iff.mp h⟩]
      exact h1

end PhysLean.List
