/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QFT.PerturbationTheory.WickContraction.ExtractEquiv
/-!

# List of uncontracted elements of a Wick contraction

-/

open FieldSpecification
variable {𝓕 : FieldSpecification}

namespace WickContraction
variable {n : ℕ} (c : WickContraction n)
open PhysLean.List
open PhysLean.Fin

/-!

## Some properties of lists of fin

-/

lemma fin_list_sorted_monotone_sorted {n m : ℕ} (l: List (Fin n)) (hl : l.Pairwise (· ≤ ·))
    (f : Fin n → Fin m) (hf : StrictMono f) : ((List.map f l)).Pairwise (· ≤ ·) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.pairwise_cons, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    apply And.intro
    · simp only [List.pairwise_cons] at hl
      intro b hb
      have hl1 := hl.1 b hb
      exact (StrictMono.le_iff_le hf).mpr hl1
    · simp only [List.pairwise_cons] at hl
      exact ih hl.2

lemma fin_list_sorted_succAboveEmb_sorted (l: List (Fin n)) (hl : l.Pairwise (· ≤ ·))
    (i : Fin n.succ) : ((List.map i.succAboveEmb l)).Pairwise (· ≤ ·) := by
  apply fin_list_sorted_monotone_sorted
  exact hl
  simp only [Fin.coe_succAboveEmb]
  exact Fin.strictMono_succAbove i

lemma fin_finset_sort_map_monotone {n m : ℕ} (a : Finset (Fin n)) (f : Fin n ↪ Fin m)
    (hf : StrictMono f) : (a.sort (· ≤ ·)).map f =
    ((a.map f).sort (· ≤ ·)) := by
  have h1 : ((a.sort (· ≤ ·)).map f).Pairwise (· ≤ ·) := by
    apply fin_list_sorted_monotone_sorted
    exact a.pairwise_sort (fun x1 x2 => x1 ≤ x2)
    exact hf
  have h2 : ((a.sort (· ≤ ·)).map f).Nodup := by
    refine (List.nodup_map_iff_inj_on ?_).mpr ?_
    exact a.sort_nodup (fun x1 x2 => x1 ≤ x2)
    intro a ha b hb hf
    exact f.2 hf
  have h3 : ((a.sort (· ≤ ·)).map f).toFinset = (a.map f) := by
    ext a
    simp
  rw [← h3]
  exact ((List.toFinset_sort (· ≤ ·) h2).mpr h1).symm

lemma fin_list_sorted_split :
    (l : List (Fin n)) → (hl : l.Pairwise (· ≤ ·)) → (i : ℕ) →
    l = l.filter (fun x => x.1 < i) ++ l.filter (fun x => i ≤ x.1)
  | [], _, _ => by simp
  | a :: l, hl, i => by
    simp only [List.pairwise_cons] at hl
    by_cases ha : a < i
    · conv_lhs => rw [fin_list_sorted_split l hl.2 i]
      rw [← List.cons_append]
      rw [List.filter_cons_of_pos, List.filter_cons_of_neg]
      simp only [decide_eq_true_eq, not_le, ha]
      simp [ha]
    · have hx : List.filter (fun x => decide (x.1 < i)) (a :: l) = [] := by
        simp only [ha, decide_false, Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg,
          List.filter_eq_nil_iff, decide_eq_true_eq, not_lt]
        intro b hb
        have hb' := hl.1 b hb
        omega
      simp only [hx, List.nil_append]
      rw [List.filter_cons_of_pos]
      simp only [List.cons.injEq, true_and]
      have hl' := fin_list_sorted_split l hl.2 i
      have hx : List.filter (fun x => decide (x.1 < i)) l = [] := by
        simp only [List.filter_eq_nil_iff, decide_eq_true_eq, not_lt]
        intro b hb
        have hb' := hl.1 b hb
        omega
      simp only [hx, List.nil_append] at hl'
      conv_lhs => rw [hl']
      simp only [decide_eq_true_eq]
      omega

lemma fin_list_sorted_indexOf_filter_le_mem :
    (l : List (Fin n)) → (hl : l.Pairwise (· ≤ ·)) → (i : Fin n) →
    (hl : i ∈ l) →
    List.idxOf i (List.filter (fun x => decide (↑i ≤ ↑x)) l) = 0
  | [], _, _, _ => by simp
  | a :: l, hl, i, hi => by
    simp only [List.pairwise_cons] at hl
    by_cases ha : i ≤ a
    · simp only [ha, decide_true, List.filter_cons_of_pos]
      have ha : a = i := by
        simp only [List.mem_cons] at hi
        rcases hi with hi | hi
        · subst hi
          rfl
        · have hl' := hl.1 i hi
          exact Fin.le_antisymm hl' ha
      subst ha
      simp
    · simp only [not_le] at ha
      rw [List.filter_cons_of_neg (by simpa using ha)]
      rw [fin_list_sorted_indexOf_filter_le_mem l hl.2]
      simp only [List.mem_cons] at hi
      rcases hi with hi | hi
      · omega
      · exact hi

lemma fin_list_sorted_indexOf_mem :
    (l : List (Fin n)) → (hl : l.Pairwise (· ≤ ·)) → (i : Fin n) →
    (hi : i ∈ l) →
    l.idxOf i = (l.filter (fun x => x.1 < i.1)).length := by
  intro l hl i hi
  conv_lhs => rw [fin_list_sorted_split l hl i]
  rw [List.idxOf_append_of_notMem]
  erw [fin_list_sorted_indexOf_filter_le_mem l hl i hi]
  · simp
  · simp

lemma orderedInsert_of_fin_list_sorted :
    (l : List (Fin n)) → (hl : l.Pairwise (· ≤ ·)) → (i : Fin n) →
    List.orderedInsert (· ≤ ·) i l = l.filter (fun x => x.1 < i.1) ++
    i :: l.filter (fun x => i.1 ≤ x.1)
  | [], _, _ => by simp
  | a :: l, hl, i => by
    simp only [List.pairwise_cons] at hl
    by_cases ha : i ≤ a
    · simp only [List.orderedInsert, ha, ↓reduceIte, Fin.val_fin_lt, decide_eq_true_eq, not_lt,
      List.filter_cons_of_neg, Fin.val_fin_le, decide_true, List.filter_cons_of_pos]
      have h1 : List.filter (fun x => decide (↑x < ↑i)) l = [] := by
        simp only [List.filter_eq_nil_iff, decide_eq_true_eq, not_lt]
        intro a ha
        have ha' := hl.1 a ha
        omega
      have hl : l = List.filter (fun x => decide (i ≤ x)) l := by
        conv_lhs => rw [fin_list_sorted_split l hl.2 i]
        simp [h1]
      simp [← hl, h1]
    · simp only [List.orderedInsert, ha, ↓reduceIte, Fin.val_fin_lt, Fin.val_fin_le, decide_false,
      Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg]
      rw [List.filter_cons_of_pos]
      rw [orderedInsert_of_fin_list_sorted l hl.2 i]
      simp only [Fin.val_fin_lt, Fin.val_fin_le, List.cons_append]
      simp only [decide_eq_true_eq]
      omega

lemma orderedInsert_eq_insertIdx_of_fin_list_sorted (l : List (Fin n)) (hl : l.Pairwise (· ≤ ·))
    (i : Fin n) :
    List.orderedInsert (· ≤ ·) i l = l.insertIdx (l.filter (fun x => x.1 < i.1)).length i := by
  let n : Fin l.length.succ := ⟨(List.filter (fun x => decide (x < i)) l).length, by
    have h1 := l.length_filter_le (fun x => x.1 < i.1)
    simp only [Fin.val_fin_lt] at h1
    omega⟩
  simp only [Fin.val_fin_lt]
  conv_rhs => rw [insertIdx_eq_take_drop _ _ n]
  rw [orderedInsert_of_fin_list_sorted]
  congr
  · conv_rhs =>
      rhs
      rw [fin_list_sorted_split l hl i]
    simp [n]
  · conv_rhs =>
      rhs
      rw [fin_list_sorted_split l hl i]
    simp [n]
  exact hl

/-!

## Uncontracted List

-/

/-- Given a Wick contraction `c`, the ordered list of elements of `Fin n` which are not contracted,
  i.e. do not appear anywhere in `c.1`. -/
def uncontractedList : List (Fin n) := List.filter (fun x => x ∈ c.uncontracted) (List.finRange n)

lemma uncontractedList_mem_iff (i : Fin n) :
    i ∈ c.uncontractedList ↔ i ∈ c.uncontracted := by
  simp [uncontractedList]

@[simp]
lemma uncontractedList_empty : (empty (n := n)).uncontractedList = List.finRange n := by
  simp [uncontractedList]

lemma nil_zero_uncontractedList : (empty (n := 0)).uncontractedList = [] := by
  simp [empty, uncontractedList]

lemma congr_uncontractedList {n m : ℕ} (h : n = m) (c : WickContraction n) :
    ((congr h) c).uncontractedList = List.map (finCongr h) c.uncontractedList := by
  subst h
  simp [congr]

lemma uncontractedList_get_mem_uncontracted (i : Fin c.uncontractedList.length) :
    c.uncontractedList.get i ∈ c.uncontracted := by
  rw [← uncontractedList_mem_iff]
  simp

lemma uncontractedList_sorted : List.Pairwise (· ≤ ·) c.uncontractedList := by
  rw [uncontractedList]
  apply List.Pairwise.filter
  rw [← List.ofFn_id]
  refine List.sortedLE_iff_pairwise.mp ?_
  exact Monotone.sortedLE_ofFn fun ⦃a b⦄ a => a

lemma uncontractedList_sorted_lt : List.Pairwise (· < ·) c.uncontractedList := by
  rw [uncontractedList]
  apply List.Pairwise.filter
  rw [← List.ofFn_id]
  exact List.pairwise_ofFn.mpr fun ⦃i j⦄ a => a

lemma uncontractedList_nodup : c.uncontractedList.Nodup := by
  rw [uncontractedList]
  refine List.Nodup.filter (fun x => decide (x ∈ c.uncontracted)) ?_
  exact List.nodup_finRange n

lemma uncontractedList_toFinset (c : WickContraction n) :
    c.uncontractedList.toFinset = c.uncontracted := by
  simp [uncontractedList]

lemma uncontractedList_eq_sort (c : WickContraction n) :
    c.uncontractedList = c.uncontracted.sort (· ≤ ·) := by
  symm
  rw [← uncontractedList_toFinset]
  refine (List.toFinset_sort (α := Fin n) (· ≤ ·) ?_).mpr ?_
  · exact uncontractedList_nodup c
  · exact uncontractedList_sorted c

lemma uncontractedList_length_eq_card (c : WickContraction n) :
    c.uncontractedList.length = c.uncontracted.card := by
  rw [uncontractedList_eq_sort]
  exact Finset.length_sort fun x1 x2 => x1 ≤ x2

lemma filter_uncontractedList (c : WickContraction n) (p : Fin n → Prop) [DecidablePred p] :
    (c.uncontractedList.filter p) = (c.uncontracted.filter p).sort (· ≤ ·) := by
  have h1 : (c.uncontractedList.filter p).Pairwise (· ≤ ·) := by
    apply List.Pairwise.filter
    exact uncontractedList_sorted c
  have h2 : (c.uncontractedList.filter p).Nodup := by
    refine List.Nodup.filter _ ?_
    exact uncontractedList_nodup c
  have h3 : (c.uncontractedList.filter p).toFinset = (c.uncontracted.filter p) := by
    ext a
    simp only [List.toFinset_filter, decide_eq_true_eq, Finset.mem_filter, List.mem_toFinset,
      and_congr_left_iff]
    rw [uncontractedList_mem_iff]
    simp
  have hx := (List.toFinset_sort (· ≤ ·) h2).mpr h1
  rw [← hx, h3]

/-!

## uncontractedIndexEquiv

-/

/-- The equivalence between the positions of `c.uncontractedList` i.e. elements of
  `Fin (c.uncontractedList).length` and the finite set `c.uncontracted` considered as a finite type.
-/
def uncontractedIndexEquiv (c : WickContraction n) :
    Fin (c.uncontractedList).length ≃ c.uncontracted where
  toFun i := ⟨c.uncontractedList.get i, c.uncontractedList_get_mem_uncontracted i⟩
  invFun i := ⟨List.idxOf i.1 c.uncontractedList,
    List.idxOf_lt_length_iff.mpr ((c.uncontractedList_mem_iff i.1).mpr i.2)⟩
  left_inv i := by
    ext
    exact List.get_idxOf (uncontractedList_nodup c) _
  right_inv i := by
    ext
    simp

@[simp]
lemma uncontractedList_getElem_uncontractedIndexEquiv_symm (k : c.uncontracted) :
    c.uncontractedList[(c.uncontractedIndexEquiv.symm k).val] = k := by
  simp [uncontractedIndexEquiv]

lemma uncontractedIndexEquiv_symm_eq_filter_length (k : c.uncontracted) :
    (c.uncontractedIndexEquiv.symm k).val =
    (List.filter (fun i => i < k.val) c.uncontractedList).length := by
  simp only [uncontractedIndexEquiv, List.get_eq_getElem, Equiv.coe_fn_symm_mk]
  rw [fin_list_sorted_indexOf_mem]
  · simp
  · exact uncontractedList_sorted c
  · rw [uncontractedList_mem_iff]
    exact k.2

lemma take_uncontractedIndexEquiv_symm (k : c.uncontracted) :
    c.uncontractedList.take (c.uncontractedIndexEquiv.symm k).val =
    c.uncontractedList.filter (fun i => i < k.val) := by
  have hl := fin_list_sorted_split c.uncontractedList (uncontractedList_sorted c) k.val
  conv_lhs =>
    rhs
    rw [hl]
  rw [uncontractedIndexEquiv_symm_eq_filter_length]
  simp
/-!

## Uncontracted List get

-/

/-- Given a Wick Contraction `φsΛ` of a list `φs` of `𝓕.FieldOp`. The list
  `φsΛ.uncontractedListGet` of `𝓕.FieldOp` is defined as the list `φs` with
  all contracted positions removed, leaving the uncontracted `𝓕.FieldOp`.

  The notation `[φsΛ]ᵘᶜ` is used for `φsΛ.uncontractedListGet`. -/
def uncontractedListGet {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length) :
    List 𝓕.FieldOp := φsΛ.uncontractedList.map φs.get

@[inherit_doc uncontractedListGet]
scoped[WickContraction] notation "[" φsΛ "]ᵘᶜ" => uncontractedListGet φsΛ

@[simp]
lemma uncontractedListGet_empty {φs : List 𝓕.FieldOp} :
    (empty (n := φs.length)).uncontractedListGet = φs := by
  simp [uncontractedListGet]

/-!

## uncontractedFieldOpEquiv

-/

/-- The equivalence between the type `Option c.uncontracted` for `WickContraction φs.length` and
  `Option (Fin (c.uncontractedList.map φs.get).length)`, that is optional positions of
  `c.uncontractedList.map φs.get` induced by `uncontractedIndexEquiv`. -/
def uncontractedFieldOpEquiv (φs : List 𝓕.FieldOp) (φsΛ : WickContraction φs.length) :
    Option φsΛ.uncontracted ≃ Option (Fin [φsΛ]ᵘᶜ.length) :=
  Equiv.optionCongr (φsΛ.uncontractedIndexEquiv.symm.trans
    (finCongr (by simp [uncontractedListGet])))

@[simp]
lemma uncontractedFieldOpEquiv_none (φs : List 𝓕.FieldOp) (φsΛ : WickContraction φs.length) :
    (uncontractedFieldOpEquiv φs φsΛ).toFun none = none := by
  simp [uncontractedFieldOpEquiv]

lemma uncontractedFieldOpEquiv_list_sum [AddCommMonoid α] (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (f : Option (Fin [φsΛ]ᵘᶜ.length) → α) :
    ∑ (i : Option (Fin [φsΛ]ᵘᶜ.length)), f i =
    ∑ (i : Option φsΛ.uncontracted), f (φsΛ.uncontractedFieldOpEquiv φs i) := by
  rw [(φsΛ.uncontractedFieldOpEquiv φs).sum_comp]

/-!

## uncontractedListEmd

-/

/-- The embedding of `Fin [φsΛ]ᵘᶜ.length` into `Fin φs.length`. -/
def uncontractedListEmd {φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length} :
    Fin [φsΛ]ᵘᶜ.length ↪ Fin φs.length := ((finCongr (by simp [uncontractedListGet])).trans
  φsΛ.uncontractedIndexEquiv).toEmbedding.trans
  (Function.Embedding.subtype fun x => x ∈ φsΛ.uncontracted)

lemma uncontractedListEmd_congr {φs : List 𝓕.FieldOp} {φsΛ φsΛ' : WickContraction φs.length}
    (h : φsΛ = φsΛ') : φsΛ.uncontractedListEmd =
    (finCongr (by simp [h])).toEmbedding.trans φsΛ'.uncontractedListEmd := by
  subst h
  rfl

lemma uncontractedListEmd_toFun_eq_get (φs : List 𝓕.FieldOp) (φsΛ : WickContraction φs.length) :
    (uncontractedListEmd (φsΛ := φsΛ)).toFun =
    φsΛ.uncontractedList.get ∘ (finCongr (by simp [uncontractedListGet])) := by
  rfl

lemma uncontractedListEmd_strictMono {φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length}
    {i j : Fin [φsΛ]ᵘᶜ.length} (h : i < j) : uncontractedListEmd i < uncontractedListEmd j := by
  simp only [uncontractedListEmd, uncontractedIndexEquiv, List.get_eq_getElem,
    Equiv.trans_toEmbedding, Function.Embedding.trans_apply, Equiv.coe_toEmbedding, finCongr_apply,
    Equiv.coe_fn_mk, Fin.val_cast, Function.Embedding.coe_subtype]
  apply List.SortedLT.strictMono_get
  exact φsΛ.uncontractedList_sorted_lt.sortedLT
  exact h

lemma uncontractedListEmd_mem_uncontracted {φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length}
    (i : Fin [φsΛ]ᵘᶜ.length) : uncontractedListEmd i ∈ φsΛ.uncontracted := by
  simp [uncontractedListEmd]

lemma uncontractedListEmd_surjective_mem_uncontracted {φs : List 𝓕.FieldOp}
    {φsΛ : WickContraction φs.length} (i : Fin φs.length) (hi : i ∈ φsΛ.uncontracted) :
    ∃ j, φsΛ.uncontractedListEmd j = i := by
  simp only [uncontractedListEmd, Equiv.trans_toEmbedding, Function.Embedding.trans_apply,
    Equiv.coe_toEmbedding, finCongr_apply, Function.Embedding.coe_subtype]
  have hj : ∃ j, φsΛ.uncontractedIndexEquiv j = ⟨i, hi⟩ := by
    exact φsΛ.uncontractedIndexEquiv.surjective ⟨i, hi⟩
  generalize_proofs h1
  obtain ⟨j, hj⟩ := hj
  have hj' : ∃ j', Fin.cast h1 j' = j := (finCongr h1).surjective j
  obtain ⟨j', rfl⟩ := (finCongr h1).surjective j
  use j'
  erw [hj]

@[simp]
lemma uncontractedListEmd_finset_disjoint_left {φs : List 𝓕.FieldOp}
    {φsΛ : WickContraction φs.length} (a : Finset (Fin [φsΛ]ᵘᶜ.length))
    (b : Finset (Fin φs.length)) (hb : b ∈ φsΛ.1) : Disjoint (a.map uncontractedListEmd) b := by
  rw [Finset.disjoint_left]
  intro x hx
  simp only [Finset.mem_map] at hx
  obtain ⟨x, hx, rfl⟩ := hx
  have h1 : uncontractedListEmd x ∈ φsΛ.uncontracted :=
    uncontractedListEmd_mem_uncontracted x
  rw [mem_uncontracted_iff_not_contracted] at h1
  exact h1 b hb

lemma uncontractedListEmd_finset_not_mem {φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length}
    (a : Finset (Fin [φsΛ]ᵘᶜ.length)) :
    a.map uncontractedListEmd ∉ φsΛ.1 := by
  by_contra hn
  have h1 := uncontractedListEmd_finset_disjoint_left a (a.map uncontractedListEmd) hn
  simp only [disjoint_self, Finset.bot_eq_empty, Finset.map_eq_empty] at h1
  have h2 := φsΛ.2.1 (a.map uncontractedListEmd) hn
  rw [h1] at h2
  simp at h2

@[simp]
lemma getElem_uncontractedListEmd {φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length}
    (k : Fin [φsΛ]ᵘᶜ.length) : φs[(uncontractedListEmd k).1] = [φsΛ]ᵘᶜ[k.1] := by
  simp only [uncontractedListGet, List.getElem_map, List.get_eq_getElem]
  rfl

@[simp]
lemma uncontractedListEmd_empty {φs : List 𝓕.FieldOp} :
    (empty (n := φs.length)).uncontractedListEmd = (finCongr (by simp)).toEmbedding := by
  ext x
  simp [uncontractedListEmd, uncontractedIndexEquiv]

/-!

## Uncontracted List for extractEquiv symm none

-/

lemma uncontractedList_succAboveEmb_sorted (c : WickContraction n) (i : Fin n.succ) :
    ((List.map i.succAboveEmb c.uncontractedList)).Pairwise (· ≤ ·) := by
  apply fin_list_sorted_succAboveEmb_sorted
  exact uncontractedList_sorted c

lemma uncontractedList_succAboveEmb_nodup (c : WickContraction n) (i : Fin n.succ) :
    ((List.map i.succAboveEmb c.uncontractedList)).Nodup := by
  refine List.Nodup.map ?_ ?_
  · exact Function.Embedding.injective i.succAboveEmb
  · exact uncontractedList_nodup c

lemma uncontractedList_succAbove_orderedInsert_nodup (c : WickContraction n) (i : Fin n.succ) :
    (List.orderedInsert (· ≤ ·) i (List.map i.succAboveEmb c.uncontractedList)).Nodup := by
  have h1 : (List.orderedInsert (· ≤ ·) i (List.map i.succAboveEmb c.uncontractedList)).Perm
    (i :: List.map i.succAboveEmb c.uncontractedList) := by
    exact List.perm_orderedInsert (fun x1 x2 => x1 ≤ x2) i _
  apply List.Perm.nodup h1.symm
  simp only [Nat.succ_eq_add_one, List.nodup_cons, List.mem_map, not_exists,
    not_and]
  apply And.intro
  · intro x _
    exact Fin.succAbove_ne i x
  · exact uncontractedList_succAboveEmb_nodup c i

lemma uncontractedList_succAbove_orderedInsert_sorted (c : WickContraction n) (i : Fin n.succ) :
    (List.orderedInsert (· ≤ ·) i
      (List.map i.succAboveEmb c.uncontractedList)).Pairwise (· ≤ ·) := by
  refine List.Pairwise.orderedInsert i (List.map (⇑i.succAboveEmb) c.uncontractedList) ?_
  exact uncontractedList_succAboveEmb_sorted c i

lemma uncontractedList_succAbove_orderedInsert_toFinset (c : WickContraction n) (i : Fin n.succ) :
    (List.orderedInsert (· ≤ ·) i (List.map i.succAboveEmb c.uncontractedList)).toFinset =
    (Insert.insert i (Finset.map i.succAboveEmb c.uncontracted)) := by
  ext a
  simp only [Nat.succ_eq_add_one, Fin.coe_succAboveEmb, List.mem_toFinset, List.mem_orderedInsert,
    List.mem_map, Finset.mem_insert, Finset.mem_map, Fin.succAboveEmb_apply]
  rw [← uncontractedList_toFinset]
  simp

lemma uncontractedList_succAbove_orderedInsert_eq_sort (c : WickContraction n) (i : Fin n.succ) :
    (List.orderedInsert (· ≤ ·) i (List.map i.succAboveEmb c.uncontractedList)) =
    (Insert.insert i (Finset.map i.succAboveEmb c.uncontracted)).sort (· ≤ ·) := by
  rw [← uncontractedList_succAbove_orderedInsert_toFinset]
  symm
  refine (List.toFinset_sort (α := Fin n.succ) (· ≤ ·) ?_).mpr ?_
  · exact uncontractedList_succAbove_orderedInsert_nodup c i
  · exact uncontractedList_succAbove_orderedInsert_sorted c i

lemma uncontractedList_extractEquiv_symm_none (c : WickContraction n) (i : Fin n.succ) :
    ((extractEquiv i).symm ⟨c, none⟩).uncontractedList =
    List.orderedInsert (· ≤ ·) i (List.map i.succAboveEmb c.uncontractedList) := by
  rw [uncontractedList_eq_sort, extractEquiv_symm_none_uncontracted]
  rw [uncontractedList_succAbove_orderedInsert_eq_sort]

/-!

## Uncontracted List for extractEquiv symm some

-/

lemma uncontractedList_succAboveEmb_eraseIdx_toFinset (c : WickContraction n) (i : Fin n.succ)
    (k : ℕ) (hk : k < c.uncontractedList.length) :
    ((List.map i.succAboveEmb c.uncontractedList).eraseIdx k).toFinset =
    (c.uncontracted.map i.succAboveEmb).erase (i.succAboveEmb c.uncontractedList[k]) := by
  ext a
  simp only [Fin.coe_succAboveEmb, List.mem_toFinset, Fin.succAboveEmb_apply, Finset.mem_erase,
    ne_eq, Finset.mem_map]
  rw [mem_eraseIdx_nodup _ _ _ (by simpa using hk)]
  simp_all only [List.mem_map, List.getElem_map, ne_eq]
  apply Iff.intro
  · intro a_1
    simp_all only [not_false_eq_true, true_and]
    obtain ⟨left, right⟩ := a_1
    obtain ⟨w, h⟩ := left
    obtain ⟨left, right_1⟩ := h
    subst right_1
    use w
    simp_all [uncontractedList]
  · intro a_1
    simp_all only [not_false_eq_true, and_true]
    obtain ⟨left, right⟩ := a_1
    obtain ⟨w, h⟩ := right
    obtain ⟨left_1, right⟩ := h
    subst right
    use w
    simp_all [uncontractedList]
  exact uncontractedList_succAboveEmb_nodup c i

lemma uncontractedList_succAboveEmb_eraseIdx_sorted (c : WickContraction n) (i : Fin n.succ)
    (k: ℕ) : ((List.map i.succAboveEmb c.uncontractedList).eraseIdx k).Pairwise (· ≤ ·) := by
  apply PhysLean.List.eraseIdx_sorted
  exact uncontractedList_succAboveEmb_sorted c i

lemma uncontractedList_succAboveEmb_eraseIdx_nodup (c : WickContraction n) (i : Fin n.succ) (k: ℕ) :
    ((List.map i.succAboveEmb c.uncontractedList).eraseIdx k).Nodup := by
  refine List.Nodup.eraseIdx k ?_
  exact uncontractedList_succAboveEmb_nodup c i

lemma uncontractedList_succAboveEmb_eraseIdx_eq_sort (c : WickContraction n) (i : Fin n.succ)
    (k : ℕ) (hk : k < c.uncontractedList.length) :
    ((List.map i.succAboveEmb c.uncontractedList).eraseIdx k) =
    ((c.uncontracted.map i.succAboveEmb).erase
    (i.succAboveEmb c.uncontractedList[k])).sort (· ≤ ·) := by
  rw [← uncontractedList_succAboveEmb_eraseIdx_toFinset]
  symm
  refine (List.toFinset_sort (α := Fin n.succ) (· ≤ ·) ?_).mpr ?_
  · exact uncontractedList_succAboveEmb_eraseIdx_nodup c i k
  · exact uncontractedList_succAboveEmb_eraseIdx_sorted c i k

lemma uncontractedList_extractEquiv_symm_some (c : WickContraction n) (i : Fin n.succ)
    (k : c.uncontracted) : ((extractEquiv i).symm ⟨c, some k⟩).uncontractedList =
    ((c.uncontractedList).map i.succAboveEmb).eraseIdx (c.uncontractedIndexEquiv.symm k) := by
  rw [uncontractedList_eq_sort]
  rw [uncontractedList_succAboveEmb_eraseIdx_eq_sort]
  swap
  simp only [Fin.is_lt]
  congr
  simp only [Nat.succ_eq_add_one, extractEquiv, Equiv.coe_fn_symm_mk,
    uncontractedList_getElem_uncontractedIndexEquiv_symm, Fin.succAboveEmb_apply]
  rw [insertAndContractNat_some_uncontracted]
  ext a
  simp

lemma uncontractedList_succAboveEmb_toFinset (c : WickContraction n) (i : Fin n.succ) :
    (List.map i.succAboveEmb c.uncontractedList).toFinset =
    (Finset.map i.succAboveEmb c.uncontracted) := by
  ext a
  simp only [Fin.coe_succAboveEmb, List.mem_toFinset, List.mem_map, Finset.mem_map,
    Fin.succAboveEmb_apply]
  rw [← c.uncontractedList_toFinset]
  simp

/-!

## uncontractedListOrderPos

-/

/-- Given a Wick contraction `c : WickContraction n` and a `Fin n.succ`, the number of elements
  of `c.uncontractedList` which are less than `i`.
  Suppose we want to insert into `c` at position `i`, then this is the position we would
  need to insert into `c.uncontractedList`. -/
def uncontractedListOrderPos (c : WickContraction n) (i : Fin n.succ) : ℕ :=
  (List.filter (fun x => x.1 < i.1) c.uncontractedList).length

@[simp]
lemma uncontractedListOrderPos_le_length (c : WickContraction n) (i : Fin n.succ) :
    c.uncontractedListOrderPos i ≤ c.uncontractedList.length := by
  simp only [uncontractedListOrderPos, Nat.succ_eq_add_one]
  have h1 := c.uncontractedList.length_filter_le (fun x => x.1 < i.1)
  omega

lemma take_uncontractedListOrderPos_eq_filter (c : WickContraction n) (i : Fin n.succ) :
    (c.uncontractedList.take (c.uncontractedListOrderPos i)) =
    c.uncontractedList.filter (fun x => x.1 < i.1) := by
  nth_rewrite 1 [fin_list_sorted_split c.uncontractedList _ i]
  simp only [uncontractedListOrderPos, Nat.succ_eq_add_one, List.take_left']
  exact uncontractedList_sorted c

lemma take_uncontractedListOrderPos_eq_filter_sort (c : WickContraction n) (i : Fin n.succ) :
    (c.uncontractedList.take (c.uncontractedListOrderPos i)) =
    (c.uncontracted.filter (fun x => x.1 < i.1)).sort (· ≤ ·) := by
  rw [take_uncontractedListOrderPos_eq_filter]
  have h1 : (c.uncontractedList.filter (fun x => x.1 < i.1)).Pairwise (· ≤ ·) := by
    apply List.Pairwise.filter
    exact uncontractedList_sorted c
  have h2 : (c.uncontractedList.filter (fun x => x.1 < i.1)).Nodup := by
    refine List.Nodup.filter _ ?_
    exact uncontractedList_nodup c
  have h3 : (c.uncontractedList.filter (fun x => x.1 < i.1)).toFinset =
    (c.uncontracted.filter (fun x => x.1 < i.1)) := by
    rw [uncontractedList_eq_sort]
    simp
  rw [← h3]
  exact ((List.toFinset_sort (α := Fin n) (· ≤ ·) h2).mpr h1).symm

lemma orderedInsert_succAboveEmb_uncontractedList_eq_insertIdx (c : WickContraction n)
    (i : Fin n.succ) :
    (List.orderedInsert (· ≤ ·) i (List.map i.succAboveEmb c.uncontractedList)) =
    (List.map i.succAboveEmb c.uncontractedList).insertIdx (uncontractedListOrderPos c i) i := by
  rw [orderedInsert_eq_insertIdx_of_fin_list_sorted]
  · congr 1
    simp only [Nat.succ_eq_add_one, Fin.val_fin_lt, Fin.coe_succAboveEmb, uncontractedListOrderPos]
    rw [List.filter_map]
    simp only [List.length_map]
    congr
    funext x
    simp only [Function.comp_apply, Fin.succAbove, decide_eq_decide]
    split
    · simp only [Fin.lt_def, Fin.val_castSucc]
    · rename_i h
      simp_all only [Fin.lt_def, Fin.val_castSucc, not_lt, Fin.val_succ]
      omega
  · exact uncontractedList_succAboveEmb_sorted c i

end WickContraction
