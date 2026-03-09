/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.QFT.PerturbationTheory.WickContraction.UncontractedList
/-!

# Inserting an element into a contraction based on a list

-/

@[expose] public section

open FieldSpecification
variable {𝓕 : FieldSpecification}

namespace WickContraction
variable {n : ℕ} (c : WickContraction n)
open PhysLean.List
open PhysLean.Fin

/-!

## Inserting an element into a list

-/

/-- Given a Wick contraction `φsΛ` for a list `φs` of `𝓕.FieldOp`,
  an element `φ` of `𝓕.FieldOp`, an `i ≤ φs.length` and a `k`
  in `Option φsΛ.uncontracted` i.e. is either `none` or
  some element of `φsΛ.uncontracted`, the new Wick contraction
  `φsΛ.insertAndContract φ i k` is defined by inserting `φ` into `φs` after
  the first `i`-elements and moving the values representing the contracted pairs in `φsΛ`
  accordingly.
  If `k` is not `none`, but rather `some k`, to this contraction is added the contraction
  of `φ` (at position `i`) with the new position of `k` after `φ` is added.

  In other words, `φsΛ.insertAndContract φ i k` is formed by adding `φ` to `φs` at position `i`,
  and contracting `φ` with the field originally at position `k` if `k` is not `none`.
  It is a Wick contraction of the list `φs.insertIdx φ i` corresponding to `φs` with `φ` inserted at
  position `i`.

  The notation `φsΛ ↩Λ φ i k` is used to denote `φsΛ.insertAndContract φ i k`. -/
def insertAndContract {φs : List 𝓕.FieldOp} (φ : 𝓕.FieldOp) (φsΛ : WickContraction φs.length)
    (i : Fin φs.length.succ) (k : Option φsΛ.uncontracted) :
    WickContraction (φs.insertIdx i φ).length :=
  congr (by simp) (φsΛ.insertAndContractNat i k)

@[inherit_doc insertAndContract]
scoped[WickContraction] notation φs "↩Λ" φ:max i:max j => insertAndContract φ φs i j

@[simp]
lemma insertAndContract_fstFieldOfContract (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (j : Option φsΛ.uncontracted)
    (a : φsΛ.1) : (φsΛ ↩Λ φ i j).fstFieldOfContract
    (congrLift (insertIdx_length_fin φ φs i).symm (insertLift i j a)) =
    finCongr (insertIdx_length_fin φ φs i).symm (i.succAbove (φsΛ.fstFieldOfContract a)) := by
  simp [insertAndContract]

@[simp]
lemma insertAndContract_sndFieldOfContract (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (j : Option (φsΛ.uncontracted))
    (a : φsΛ.1) : (φsΛ ↩Λ φ i j).sndFieldOfContract
    (congrLift (insertIdx_length_fin φ φs i).symm (insertLift i j a)) =
    finCongr (insertIdx_length_fin φ φs i).symm (i.succAbove (φsΛ.sndFieldOfContract a)) := by
  simp [insertAndContract]

@[simp]
lemma insertAndContract_fstFieldOfContract_some_incl (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (j : φsΛ.uncontracted) :
      (insertAndContract φ φsΛ i (some j)).fstFieldOfContract
      (congrLift (insertIdx_length_fin φ φs i).symm ⟨{i, i.succAbove j}, by
        simp [insertAndContractNat]⟩) =
      if i < i.succAbove j.1 then
      finCongr (insertIdx_length_fin φ φs i).symm i else
      finCongr (insertIdx_length_fin φ φs i).symm (i.succAbove j.1) := by
  split
  · rename_i h
    refine (insertAndContract φ φsΛ i (some j)).eq_fstFieldOfContract_of_mem
      (a := congrLift (insertIdx_length_fin φ φs i).symm ⟨{i, i.succAbove j}, by
        simp [insertAndContractNat]⟩)
      (i := finCongr (insertIdx_length_fin φ φs i).symm i) (j :=
        finCongr (insertIdx_length_fin φ φs i).symm (i.succAbove j)) ?_ ?_ ?_
    · simp [congrLift]
    · simp [congrLift]
    · rw [Fin.lt_def] at h ⊢
      simp_all
  · rename_i h
    refine (insertAndContract φ φsΛ i (some j)).eq_fstFieldOfContract_of_mem
      (a := congrLift (insertIdx_length_fin φ φs i).symm ⟨{i, i.succAbove j}, by
        simp [insertAndContractNat]⟩)
      (i := finCongr (insertIdx_length_fin φ φs i).symm (i.succAbove j))
      (j := finCongr (insertIdx_length_fin φ φs i).symm i) ?_ ?_ ?_
    · simp [congrLift]
    · simp [congrLift]
    · rw [Fin.lt_def] at h ⊢
      simp_all only [Nat.succ_eq_add_one, Fin.val_fin_lt, not_lt, finCongr_apply, Fin.val_cast]
      have hi : i.succAbove j ≠ i := Fin.succAbove_ne i j
      omega

/-!

## insertAndContract and getDual?

-/

@[simp]
lemma insertAndContract_none_getDual?_self (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) :
    (φsΛ ↩Λ φ i none).getDual? (Fin.cast (insertIdx_length_fin φ φs i).symm i) = none := by
  simp only [Nat.succ_eq_add_one, insertAndContract, getDual?_congr, finCongr_apply, Fin.cast_cast,
    Fin.cast_eq_self, Option.map_eq_none_iff]
  simp

lemma insertAndContract_isSome_getDual?_self (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (j : φsΛ.uncontracted) :
    ((φsΛ ↩Λ φ i (some j)).getDual?
    (Fin.cast (insertIdx_length_fin φ φs i).symm i)).isSome := by
  simp [insertAndContract, getDual?_congr]

lemma insertAndContract_some_getDual?_self_not_none (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (j : φsΛ.uncontracted) :
    ¬ ((φsΛ ↩Λ φ i (some j)).getDual?
    (Fin.cast (insertIdx_length_fin φ φs i).symm i)) = none := by
  simp [insertAndContract, getDual?_congr]

@[simp]
lemma insertAndContract_some_getDual?_self_eq (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (j : φsΛ.uncontracted) :
    ((φsΛ ↩Λ φ i (some j)).getDual? (Fin.cast (insertIdx_length_fin φ φs i).symm i))
    = some (Fin.cast (insertIdx_length_fin φ φs i).symm (i.succAbove j)) := by
  simp [insertAndContract, getDual?_congr]

@[simp]
lemma insertAndContract_some_getDual?_some_eq (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (j : φsΛ.uncontracted) :
    ((φsΛ ↩Λ φ i (some j)).getDual?
      (Fin.cast (insertIdx_length_fin φ φs i).symm (i.succAbove j)))
    = some (Fin.cast (insertIdx_length_fin φ φs i).symm i) := by
  rw [getDual?_eq_some_iff_mem]
  rw [@Finset.pair_comm]
  rw [← getDual?_eq_some_iff_mem]
  simp

@[simp]
lemma insertAndContract_none_succAbove_getDual?_eq_none_iff (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (j : Fin φs.length) :
    (φsΛ ↩Λ φ i none).getDual? (Fin.cast (insertIdx_length_fin φ φs i).symm
      (i.succAbove j)) = none ↔ φsΛ.getDual? j = none := by
  simp [insertAndContract, getDual?_congr]

@[simp]
lemma insertAndContract_some_succAbove_getDual?_eq_option (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (j : Fin φs.length)
    (k : φsΛ.uncontracted) (hkj : j ≠ k.1) :
    (φsΛ ↩Λ φ i (some k)).getDual? (Fin.cast (insertIdx_length_fin φ φs i).symm
    (i.succAbove j)) = Option.map (Fin.cast (insertIdx_length_fin φ φs i).symm ∘ i.succAbove)
    (φsΛ.getDual? j) := by
  simp only [Nat.succ_eq_add_one, insertAndContract, getDual?_congr, finCongr_apply, Fin.cast_cast,
    Fin.cast_eq_self, ne_eq, hkj, not_false_eq_true, insertAndContractNat_some_getDual?_of_neq,
    Option.map_map]
  rfl

@[simp]
lemma insertAndContract_none_succAbove_getDual?_isSome_iff (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (j : Fin φs.length) :
    ((φsΛ ↩Λ φ i none).getDual? (Fin.cast (insertIdx_length_fin φ φs i).symm
      (i.succAbove j))).isSome ↔ (φsΛ.getDual? j).isSome := by
  rw [← not_iff_not]
  simp

@[simp]
lemma insertAndContract_none_getDual?_get_eq (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (j : Fin φs.length)
    (h : ((φsΛ ↩Λ φ i none).getDual? (Fin.cast (insertIdx_length_fin φ φs i).symm
    (i.succAbove j))).isSome) :
    ((φsΛ ↩Λ φ i none).getDual? (Fin.cast (insertIdx_length_fin φ φs i).symm
    (i.succAbove j))).get h = Fin.cast (insertIdx_length_fin φ φs i).symm
    (i.succAbove ((φsΛ.getDual? j).get (by simpa using h))) := by
  simp [insertAndContract, getDual?_congr_get]

/-........................................... -/
@[simp]
lemma insertAndContract_sndFieldOfContract_some_incl (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (j : φsΛ.uncontracted) :
    (φsΛ ↩Λ φ i (some j)).sndFieldOfContract
    (congrLift (insertIdx_length_fin φ φs i).symm ⟨{i, i.succAbove j}, by
      simp [insertAndContractNat]⟩) =
    if i < i.succAbove j.1 then
    finCongr (insertIdx_length_fin φ φs i).symm (i.succAbove j.1) else
    finCongr (insertIdx_length_fin φ φs i).symm i := by
  split
  · rename_i h
    refine (φsΛ ↩Λ φ i (some j)).eq_sndFieldOfContract_of_mem
      (a := congrLift (insertIdx_length_fin φ φs i).symm ⟨{i, i.succAbove j}, by
        simp [insertAndContractNat]⟩)
      (i := finCongr (insertIdx_length_fin φ φs i).symm i) (j :=
        finCongr (insertIdx_length_fin φ φs i).symm (i.succAbove j)) ?_ ?_ ?_
    · simp [congrLift]
    · simp [congrLift]
    · rw [Fin.lt_def] at h ⊢
      simp_all
  · rename_i h
    refine (φsΛ ↩Λ φ i (some j)).eq_sndFieldOfContract_of_mem
      (a := congrLift (insertIdx_length_fin φ φs i).symm ⟨{i, i.succAbove j}, by
        simp [insertAndContractNat]⟩)
      (i := finCongr (insertIdx_length_fin φ φs i).symm (i.succAbove j))
      (j := finCongr (insertIdx_length_fin φ φs i).symm i) ?_ ?_ ?_
    · simp [congrLift]
    · simp [congrLift]
    · rw [Fin.lt_def] at h ⊢
      simp_all only [Nat.succ_eq_add_one, Fin.val_fin_lt, not_lt, finCongr_apply, Fin.val_cast]
      have hi : i.succAbove j ≠ i := Fin.succAbove_ne i j
      omega

lemma insertAndContract_none_prod_contractions (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ)
    (f : (φsΛ ↩Λ φ i none).1 → M) [CommMonoid M] :
    ∏ a, f a = ∏ (a : φsΛ.1), f (congrLift (insertIdx_length_fin φ φs i).symm
      (insertLift i none a)) := by
  let e1 := Equiv.ofBijective (φsΛ.insertLift i none) (insertLift_none_bijective i)
  let e2 := Equiv.ofBijective (congrLift (insertIdx_length_fin φ φs i).symm)
    ((φsΛ.insertAndContractNat i none).congrLift_bijective ((insertIdx_length_fin φ φs i).symm))
  erw [← e2.prod_comp]
  rw [← e1.prod_comp]
  rfl

lemma insertAndContract_some_prod_contractions (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (j : φsΛ.uncontracted)
    (f : (φsΛ ↩Λ φ i (some j)).1 → M) [CommMonoid M] :
    ∏ a, f a = f (congrLift (insertIdx_length_fin φ φs i).symm
      ⟨{i, i.succAbove j}, by simp [insertAndContractNat]⟩) *
    ∏ (a : φsΛ.1), f (congrLift (insertIdx_length_fin φ φs i).symm (insertLift i (some j) a)) := by
  let e2 := Equiv.ofBijective (congrLift (insertIdx_length_fin φ φs i).symm)
    ((φsΛ.insertAndContractNat i (some j)).congrLift_bijective ((insertIdx_length_fin φ φs i).symm))
  erw [← e2.prod_comp]
  let e1 := Equiv.ofBijective (φsΛ.insertLiftSome i j) (insertLiftSome_bijective i j)
  rw [← e1.prod_comp]
  rw [Fintype.prod_sum_type]
  simp only [Finset.univ_unique, PUnit.default_eq_unit, Nat.succ_eq_add_one, Finset.prod_singleton,
    Finset.univ_eq_attach]
  rfl

/-- Given a finite set of `Fin φs.length` the finite set of `(φs.insertIdx i φ).length`
  formed by mapping elements using `i.succAboveEmb` and `finCongr`. -/
def insertAndContractLiftFinset (φ : 𝓕.FieldOp) {φs : List 𝓕.FieldOp}
    (i : Fin φs.length.succ) (a : Finset (Fin φs.length)) :
    Finset (Fin (φs.insertIdx i φ).length) :=
    (a.map i.succAboveEmb).map (finCongr (insertIdx_length_fin φ φs i).symm).toEmbedding

@[simp]
lemma self_not_mem_insertAndContractLiftFinset (φ : 𝓕.FieldOp) {φs : List 𝓕.FieldOp}
    (i : Fin φs.length.succ) (a : Finset (Fin φs.length)) :
    Fin.cast (insertIdx_length_fin φ φs i).symm i ∉ insertAndContractLiftFinset φ i a := by
  simp only [Nat.succ_eq_add_one, insertAndContractLiftFinset, Finset.mem_map_equiv, finCongr_symm,
    finCongr_apply, Fin.cast_cast, Fin.cast_eq_self]
  simp only [Finset.mem_map, Fin.succAboveEmb_apply, not_exists, not_and]
  intro x
  exact fun a => Fin.succAbove_ne i x

lemma succAbove_mem_insertAndContractLiftFinset (φ : 𝓕.FieldOp) {φs : List 𝓕.FieldOp}
    (i : Fin φs.length.succ) (a : Finset (Fin φs.length)) (j : Fin φs.length) :
    Fin.cast (insertIdx_length_fin φ φs i).symm (i.succAbove j)
    ∈ insertAndContractLiftFinset φ i a ↔ j ∈ a := by
  simp only [insertAndContractLiftFinset, Finset.mem_map_equiv, finCongr_symm, finCongr_apply,
    Fin.cast_cast, Fin.cast_eq_self]
  simp only [Finset.mem_map, Fin.succAboveEmb_apply]
  apply Iff.intro
  · intro h
    obtain ⟨x, hx1, hx2⟩ := h
    rw [Function.Injective.eq_iff (Fin.succAbove_right_injective)] at hx2
    simp_all
  · intro h
    use j

lemma insert_fin_eq_self (φ : 𝓕.FieldOp) {φs : List 𝓕.FieldOp}
    (i : Fin φs.length.succ) (j : Fin (List.insertIdx φs i φ).length) :
    j = Fin.cast (insertIdx_length_fin φ φs i).symm i
    ∨ ∃ k, j = Fin.cast (insertIdx_length_fin φ φs i).symm (i.succAbove k) := by
  obtain ⟨k, hk⟩ := (finCongr (insertIdx_length_fin φ φs i).symm).surjective j
  subst hk
  by_cases hi : k = i
  · simp [hi]
  · simp only [Nat.succ_eq_add_one, ← Fin.exists_succAbove_eq_iff] at hi
    obtain ⟨z, hk⟩ := hi
    subst hk
    right
    use z
    rfl

/-- For a list `φs` of `𝓕.FieldOp`, a Wick contraction `φsΛ` of `φs`, an element `φ` of
  `𝓕.FieldOp` and a `i ≤ φs.length` then a sum over
  Wick contractions of `φs` with `φ` inserted at `i` is equal to the sum over Wick contractions
  `φsΛ` of just `φs` and the sum over optional uncontracted elements of the `φsΛ`.

  In other words,

  `∑ (φsΛ : WickContraction (φs.insertIdx i φ).length), f φsΛ`

  where `(φs.insertIdx i φ)` is `φs` with `φ` inserted at position `i`. is equal to

  `∑ (φsΛ : WickContraction φs.length), ∑ k, f (φsΛ ↩Λ φ i k) `.

  where the sum over `k` is over all `k` in `Option φsΛ.uncontracted`. -/
lemma insertLift_sum (φ : 𝓕.FieldOp) {φs : List 𝓕.FieldOp}
    (i : Fin φs.length.succ) [AddCommMonoid M] (f : WickContraction (φs.insertIdx i φ).length → M) :
    ∑ c, f c =
    ∑ (φsΛ : WickContraction φs.length), ∑ (k : Option φsΛ.uncontracted), f (φsΛ ↩Λ φ i k) := by
  rw [sum_extractEquiv_congr (finCongr (insertIdx_length_fin φ φs i).symm i) f
    (insertIdx_length_fin φ φs i)]
  rfl

/-!

## Uncontracted list

-/
lemma insertAndContract_uncontractedList_none_map (φ : 𝓕.FieldOp) {φs : List 𝓕.FieldOp}
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) :
    [φsΛ ↩Λ φ i none]ᵘᶜ = List.insertIdx [φsΛ]ᵘᶜ (φsΛ.uncontractedListOrderPos i) φ := by
  simp only [Nat.succ_eq_add_one, insertAndContract, uncontractedListGet]
  rw [congr_uncontractedList]
  erw [uncontractedList_extractEquiv_symm_none]
  rw [orderedInsert_succAboveEmb_uncontractedList_eq_insertIdx]
  rw [insertIdx_map, insertIdx_map]
  congr 1
  · simp
  · simp

@[simp]
lemma insertAndContract_uncontractedList_none_zero (φ : 𝓕.FieldOp) {φs : List 𝓕.FieldOp}
    (φsΛ : WickContraction φs.length) :
    [φsΛ ↩Λ φ 0 none]ᵘᶜ = φ :: [φsΛ]ᵘᶜ := by
  rw [insertAndContract_uncontractedList_none_map]
  simp [uncontractedListOrderPos]

open FieldStatistic in
lemma stat_ofFinset_of_insertAndContractLiftFinset (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (i : Fin φs.length.succ) (a : Finset (Fin φs.length)) :
    (𝓕 |>ₛ ⟨(φs.insertIdx i φ).get, insertAndContractLiftFinset φ i a⟩) = 𝓕 |>ₛ ⟨φs.get, a⟩ := by
  simp only [ofFinset, Nat.succ_eq_add_one]
  congr 1
  rw [get_eq_insertIdx_succAbove φ _ i, ← List.map_map, ← List.map_map]
  congr
  have h1 : (List.map (⇑(finCongr (insertIdx_length_fin φ φs i).symm))
      (List.map i.succAbove (a.sort (fun x1 x2 => x1 ≤ x2)))).Pairwise (· ≤ ·) := by
    simp only [Nat.succ_eq_add_one, List.map_map]
    refine
      fin_list_sorted_monotone_sorted (a.sort (fun x1 x2 => x1 ≤ x2)) ?hl
        (⇑(finCongr (Eq.symm (insertIdx_length_fin φ φs i))) ∘ i.succAbove) ?hf
    exact a.pairwise_sort (fun x1 x2 => x1 ≤ x2)
    refine StrictMono.comp (fun ⦃a b⦄ a => a) ?hf.hf
    exact Fin.strictMono_succAbove i
  have h2 : (List.map (⇑(finCongr (insertIdx_length_fin φ φs i).symm))
      (List.map i.succAbove (a.sort (fun x1 x2 => x1 ≤ x2)))).Nodup := by
    simp only [Nat.succ_eq_add_one, List.map_map]
    refine List.Nodup.map ?_ ?_
    apply (Equiv.comp_injective _ (finCongr _)).mpr
    exact Fin.succAbove_right_injective
    exact a.sort_nodup (fun x1 x2 => x1 ≤ x2)
  have h3 : (List.map (⇑(finCongr (insertIdx_length_fin φ φs i).symm))
      (List.map i.succAbove (a.sort (fun x1 x2 => x1 ≤ x2)))).toFinset
      = (insertAndContractLiftFinset φ i a) := by
    ext b
    simp only [Nat.succ_eq_add_one, List.map_map, List.mem_toFinset, List.mem_map, Finset.mem_sort,
      Function.comp_apply, finCongr_apply]
    rcases insert_fin_eq_self φ i b with hk | hk
    · subst hk
      simp only [Nat.succ_eq_add_one, self_not_mem_insertAndContractLiftFinset, iff_false,
        not_exists, not_and]
      intro x hx
      refine Fin.ne_of_val_ne ?h.inl.h
      simp only [Fin.val_cast, ne_eq]
      rw [Fin.val_eq_val]
      exact Fin.succAbove_ne i x
    · obtain ⟨k, hk⟩ := hk
      subst hk
      simp only [Nat.succ_eq_add_one]
      rw [succAbove_mem_insertAndContractLiftFinset]
      apply Iff.intro
      · intro h
        obtain ⟨x, hx⟩ := h
        simp only [Fin.ext_iff, Fin.val_cast] at hx
        rw [Fin.val_eq_val] at hx
        rw [Function.Injective.eq_iff] at hx
        rw [← hx.2]
        exact hx.1
        exact Fin.succAbove_right_injective
      · intro h
        use k
  rw [← h3]
  rw [(List.toFinset_sort (· ≤ ·) h2).mpr h1]

end WickContraction
