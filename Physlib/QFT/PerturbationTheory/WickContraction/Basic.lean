/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.PerturbationTheory.FieldSpecification.Basic
/-!

# Wick contractions

-/

@[expose] public section

open FieldSpecification

variable {𝓕 : FieldSpecification}

/--
Given a natural number `n`, which will correspond to the number of fields needing
contracting, a Wick contraction
is a finite set of pairs of `Fin n` (numbers `0`, ..., `n-1`), such that no
element of `Fin n` occurs in more than one pair. The pairs are the positions of fields we
'contract' together.
-/
def WickContraction (n : ℕ) : Type :=
  {f : Finset ((Finset (Fin n))) // (∀ a ∈ f, a.card = 2) ∧
    (∀ a ∈ f, ∀ b ∈ f, a = b ∨ Disjoint a b)}

namespace WickContraction
variable {n : ℕ} (c : WickContraction n)
open Physlib.List

/-- Wick contractions are decidable. -/
instance : DecidableEq (WickContraction n) := Subtype.instDecidableEq

/-- The contraction consisting of no contracted pairs. -/
def empty : WickContraction n := ⟨∅, by simp, by simp⟩

set_option backward.isDefEq.respectTransparency false in
lemma card_zero_iff_empty (c : WickContraction n) : c.1.card = 0 ↔ c = empty := by
  rw [Subtype.ext_iff, Finset.card_eq_zero, empty]

lemma exists_pair_of_not_eq_empty (c : WickContraction n) (h : c ≠ empty) :
    ∃ i j, {i, j} ∈ c.1 := by
  obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr fun hc => h (Subtype.ext hc)
  obtain ⟨i, j, -, rfl⟩ := Finset.card_eq_two.mp (c.2.1 a ha)
  exact ⟨i, j, ha⟩

/-- The equivalence between `WickContraction n` and `WickContraction m`
  derived from a propositional equality of `n` and `m`. -/
def congr : {n m : ℕ} → (h : n = m) → WickContraction n ≃ WickContraction m
  | n, .(n), rfl => Equiv.refl _

@[simp]
lemma congr_refl : c.congr rfl = c := rfl

@[simp]
lemma card_congr {n m : ℕ} (h : n = m) (c : WickContraction n) :
    (congr h c).1.card = c.1.card := by
  subst h
  simp

lemma congr_contractions {n m : ℕ} (h : n = m) (c : WickContraction n) :
    ((congr h) c).1 = Finset.map (Finset.mapEmbedding (finCongr h)).toEmbedding c.1 := by
  subst h
  ext a
  simp only [congr_refl, Finset.mem_map, RelEmbedding.coe_toEmbedding, finCongr_refl,
    Equiv.refl_toEmbedding]
  exact ⟨fun ha => ⟨a, ha, Finset.map_refl⟩,
    fun ⟨b, hb, hab⟩ => (Finset.map_refl.symm.trans hab) ▸ hb⟩

@[simp]
lemma congr_trans {n m o : ℕ} (h1 : n = m) (h2 : m = o) :
    (congr h1).trans (congr h2) = congr (h1.trans h2) := by
  subst h1 h2
  simp [congr]

@[simp]
lemma congr_trans_apply {n m o : ℕ} (h1 : n = m) (h2 : m = o) (c : WickContraction n) :
    (congr h2) ((congr h1) c) = congr (h1.trans h2) c := by
  subst h1 h2
  simp

lemma mem_congr_iff {n m : ℕ} (h : n = m) {c : WickContraction n } {a : Finset (Fin m)} :
    a ∈ (congr h c).1 ↔ Finset.map (finCongr h.symm).toEmbedding a ∈ c.1 := by
  subst h
  simp

/-- Given a contracted pair in `c : WickContraction n` the contracted pair
  in `congr h c`. -/
def congrLift {n m : ℕ} (h : n = m) {c : WickContraction n} (a : c.1) : (congr h c).1 :=
  ⟨a.1.map (finCongr h).toEmbedding, by aesop⟩

@[simp]
lemma congrLift_rfl {n : ℕ} {c : WickContraction n} :
    c.congrLift rfl = id := by
  funext a
  simp [congrLift]

lemma congrLift_injective {n m : ℕ} {c : WickContraction n} (h : n = m) :
    Function.Injective (c.congrLift h) := by
  subst h
  simpa using Function.injective_id

lemma congrLift_surjective {n m : ℕ} {c : WickContraction n} (h : n = m) :
    Function.Surjective (c.congrLift h) := by
  subst h
  simp [Function.surjective_id]

lemma congrLift_bijective {n m : ℕ} {c : WickContraction n} (h : n = m) :
    Function.Bijective (c.congrLift h) :=
  ⟨c.congrLift_injective h, c.congrLift_surjective h⟩

/-- Given a contracted pair in `c : WickContraction n` the contracted pair
  in `congr h c`. -/
def congrLiftInv {n m : ℕ} (h : n = m) {c : WickContraction n} (a : (congr h c).1) : c.1 :=
  ⟨a.1.map (finCongr h.symm).toEmbedding, by aesop⟩

set_option backward.isDefEq.respectTransparency false in
lemma congrLiftInv_rfl {n : ℕ} {c : WickContraction n} :
    c.congrLiftInv rfl = id := by
  funext a
  simp [congrLiftInv]

lemma eq_filter_mem_self : c.1 = Finset.filter (fun x => x ∈ c.1) Finset.univ :=
  (Finset.filter_univ_mem c.1).symm

/-- For a contraction `c : WickContraction n` and `i : Fin n` the `j` such that
  `{i, j}` is a contracted pair in `c`. If such an `j` does not exist, this returns `none`. -/
def getDual? (i : Fin n) : Option (Fin n) := Fin.find? (fun j => {i, j} ∈ c.1)

lemma getDual?_congr {n m : ℕ} (h : n = m) (c : WickContraction n) (i : Fin m) :
    (congr h c).getDual? i = Option.map (finCongr h) (c.getDual? (finCongr h.symm i)) := by
  subst h
  simp

lemma getDual?_congr_get {n m : ℕ} (h : n = m) (c : WickContraction n) (i : Fin m)
    (hg : ((congr h c).getDual? i).isSome) :
    ((congr h c).getDual? i).get hg =
    (finCongr h ((c.getDual? (finCongr h.symm i)).get (by simpa [getDual?_congr] using hg))) := by
  simpa only [getDual?_congr] using Option.get_map

lemma getDual?_eq_some_iff_mem (i j : Fin n) :
    c.getDual? i = some j ↔ {i, j} ∈ c.1 := by
  rw [getDual?, Fin.find?_eq_some_iff]
  refine ⟨fun h => by simpa using h.1, fun h => ⟨by simpa using h, fun k hkj => ?_⟩⟩
  simp only [decide_eq_false_iff_not]
  intro hk
  rcases c.2.2 _ h _ hk with heq | hdisj
  · have hkm : k = i ∨ k = j := by simpa using (Finset.ext_iff.mp heq k).mpr (by simp)
    rcases hkm with rfl | rfl
    · simpa using c.2.1 _ hk
    · omega
  · simpa using Finset.disjoint_left.mp hdisj (Finset.mem_insert_self i {j})

@[simp]
lemma getDual?_one_eq_none (c : WickContraction 1) (i : Fin 1) : c.getDual? i = none := by
  by_contra h
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp h
  rw [getDual?_eq_some_iff_mem] at ha
  simpa [show a = i by omega] using c.2.1 _ ha

@[simp]
lemma getDual?_get_self_mem (i : Fin n) (h : (c.getDual? i).isSome) :
    {(c.getDual? i).get h, i} ∈ c.1 := by
  rw [@Finset.pair_comm, ← getDual?_eq_some_iff_mem, Option.some_get]

@[simp]
lemma self_getDual?_get_mem (i : Fin n) (h : (c.getDual? i).isSome) :
    {i, (c.getDual? i).get h} ∈ c.1 := by
  rw [← getDual?_eq_some_iff_mem, Option.some_get]

lemma getDual?_eq_some_neq (i j : Fin n) (h : c.getDual? i = some j) :
    ¬ i = j := by
  rw [getDual?_eq_some_iff_mem] at h
  rintro rfl
  simpa using c.2.1 _ h

@[simp]
lemma self_ne_getDual?_get (i : Fin n) (h : (c.getDual? i).isSome) :
    ¬ i = (c.getDual? i).get h :=
  c.getDual?_eq_some_neq _ _ (Option.some_get h).symm

@[simp]
lemma getDual?_get_self_neq (i : Fin n) (h : (c.getDual? i).isSome) :
    ¬ (c.getDual? i).get h = i :=
  Ne.symm (c.self_ne_getDual?_get i h)

lemma getDual?_isSome_iff (i : Fin n) : (c.getDual? i).isSome ↔ ∃ (a : c.1), i ∈ a.1 := by
  simp only [Option.isSome_iff_exists, getDual?_eq_some_iff_mem]
  refine ⟨fun ⟨j, hj⟩ => ⟨⟨_, hj⟩, Finset.mem_insert_self ..⟩, fun ⟨a, ha⟩ => ?_⟩
  obtain ⟨x, y, -, hxy⟩ := Finset.card_eq_two.mp (c.2.1 a a.2)
  rw [hxy] at ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · exact ⟨y, hxy ▸ a.2⟩
  · rw [Finset.pair_comm] at hxy
    exact ⟨x, hxy ▸ a.2⟩

lemma getDual?_isSome_of_mem (a : c.1) (i : a.1) : (c.getDual? i).isSome :=
  (c.getDual?_isSome_iff i).mpr ⟨a, i.2⟩

@[simp]
lemma getDual?_getDual?_get_get (i : Fin n) (h : (c.getDual? i).isSome) :
    c.getDual? ((c.getDual? i).get h) = some i := by
  simp [getDual?_eq_some_iff_mem]

lemma getDual?_getDual?_get_isSome (i : Fin n) (h : (c.getDual? i).isSome) :
    (c.getDual? ((c.getDual? i).get h)).isSome := by
  simp

lemma getDual?_getDual?_get_not_none (i : Fin n) (h : (c.getDual? i).isSome) :
    ¬ (c.getDual? ((c.getDual? i).get h)) = none := by
  simp

/-!

## Extracting parts from a contraction.

-/

/-- The smallest of the two positions in a contracted pair given a Wick contraction. -/
def fstFieldOfContract (c : WickContraction n) (a : c.1) : Fin n :=
  (a.1.sort (· ≤ ·)).head (by
    have hx : (a.1.sort (fun x1 x2 => x1 ≤ x2)).length = a.1.card := Finset.length_sort ..
    by_contra hn
    simp only [hn, List.length_nil, c.2.1 a.1 a.2, OfNat.zero_ne_ofNat] at hx)

@[simp]
lemma fstFieldOfContract_congr {n m : ℕ} (h : n = m) (c : WickContraction n) (a : c.1) :
    (congr h c).fstFieldOfContract (c.congrLift h a) = (finCongr h) (c.fstFieldOfContract a) := by
  subst h
  simp [congr]

/-- The largest of the two positions in a contracted pair given a Wick contraction. -/
def sndFieldOfContract (c : WickContraction n) (a : c.1) : Fin n :=
  (a.1.sort (· ≤ ·)).tail.head (by
    have hx : (a.1.sort (fun x1 x2 => x1 ≤ x2)).length = a.1.card := Finset.length_sort ..
    by_contra hn
    have hn := congrArg List.length hn
    simp [c.2.1] at hn)

@[simp]
lemma sndFieldOfContract_congr {n m : ℕ} (h : n = m) (c : WickContraction n) (a : c.1) :
    (congr h c).sndFieldOfContract (c.congrLift h a) = (finCongr h) (c.sndFieldOfContract a) := by
  subst h
  simp [congr]

lemma finset_eq_fstFieldOfContract_sndFieldOfContract (c : WickContraction n) (a : c.1) :
    a.1 = {c.fstFieldOfContract a, c.sndFieldOfContract a} := by
  suffices h : ∀ x y : Fin n, x < y → a.1 = {x, y} →
      a.1 = {c.fstFieldOfContract a, c.sndFieldOfContract a} by
    obtain ⟨x, y, hxy, ha⟩ := Finset.card_eq_two.mp (c.2.1 a.1 a.2)
    rcases lt_or_gt_of_ne hxy with h' | h'
    · exact h x y h' ha
    · exact h y x h' (ha.trans (Finset.pair_comm x y))
  intro x y hxy ha
  have h1 : ∀ b ∈ ({y} : Finset (Fin n)), x ≤ b := by simp [hxy.le]
  have hs : a.1.sort (· ≤ ·) = [x, y] := by
    rw [ha, Finset.sort_insert _ h1 (by simp [hxy.ne]), Finset.sort_singleton]
  rw [ha]
  simp [fstFieldOfContract, sndFieldOfContract, hs]

lemma fstFieldOfContract_ne_sndFieldOfContract (c : WickContraction n) (a : c.1) :
    c.fstFieldOfContract a ≠ c.sndFieldOfContract a := by
  by_contra hn
  simpa [c.finset_eq_fstFieldOfContract_sndFieldOfContract a, hn] using c.2.1 a.1 a.2

lemma fstFieldOfContract_le_sndFieldOfContract (c : WickContraction n) (a : c.1) :
    c.fstFieldOfContract a ≤ c.sndFieldOfContract a :=
  (Finset.pairwise_sort ..).rel_head_tail (List.head_mem _)

lemma fstFieldOfContract_lt_sndFieldOfContract (c : WickContraction n) (a : c.1) :
    c.fstFieldOfContract a < c.sndFieldOfContract a :=
  lt_of_le_of_ne (c.fstFieldOfContract_le_sndFieldOfContract a)
    (c.fstFieldOfContract_ne_sndFieldOfContract a)

@[simp]
lemma fstFieldOfContract_mem (c : WickContraction n) (a : c.1) :
    c.fstFieldOfContract a ∈ a.1 := by
  simp [finset_eq_fstFieldOfContract_sndFieldOfContract]

lemma fstFieldOfContract_getDual?_isSome (c : WickContraction n) (a : c.1) :
    (c.getDual? (c.fstFieldOfContract a)).isSome :=
  (c.getDual?_isSome_iff _).mpr ⟨a, fstFieldOfContract_mem c a⟩

@[simp]
lemma fstFieldOfContract_getDual? (c : WickContraction n) (a : c.1) :
    c.getDual? (c.fstFieldOfContract a) = some (c.sndFieldOfContract a) := by
  simp [getDual?_eq_some_iff_mem, ← finset_eq_fstFieldOfContract_sndFieldOfContract]

@[simp]
lemma sndFieldOfContract_mem (c : WickContraction n) (a : c.1) :
    c.sndFieldOfContract a ∈ a.1 := by
  simp [finset_eq_fstFieldOfContract_sndFieldOfContract]

lemma sndFieldOfContract_getDual?_isSome (c : WickContraction n) (a : c.1) :
    (c.getDual? (c.sndFieldOfContract a)).isSome :=
  (c.getDual?_isSome_iff _).mpr ⟨a, sndFieldOfContract_mem c a⟩

@[simp]
lemma sndFieldOfContract_getDual? (c : WickContraction n) (a : c.1) :
    c.getDual? (c.sndFieldOfContract a) = some (c.fstFieldOfContract a) := by
  rw [getDual?_eq_some_iff_mem, Finset.pair_comm, ← finset_eq_fstFieldOfContract_sndFieldOfContract]
  exact a.2

lemma eq_fstFieldOfContract_of_mem (c : WickContraction n) (a : c.1) (i j : Fin n)
    (hi : i ∈ a.1) (hj : j ∈ a.1) (hij : i < j) :
    c.fstFieldOfContract a = i := by
  have hlt := fstFieldOfContract_lt_sndFieldOfContract c a
  rw [finset_eq_fstFieldOfContract_sndFieldOfContract] at hi hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> omega

lemma eq_sndFieldOfContract_of_mem (c : WickContraction n) (a : c.1) (i j : Fin n)
    (hi : i ∈ a.1) (hj : j ∈ a.1) (hij : i < j) :
    c.sndFieldOfContract a = j := by
  have hlt := fstFieldOfContract_lt_sndFieldOfContract c a
  rw [finset_eq_fstFieldOfContract_sndFieldOfContract] at hi hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> omega

/-- As a type, any pair of contractions is equivalent to `Fin 2`
  with `0` being associated with `c.fstFieldOfContract a` and `1` being associated with
  `c.sndFieldOfContract`. -/
def contractEquivFinTwo (c : WickContraction n) (a : c.1) :
    a ≃ Fin 2 where
  toFun i := if i = c.fstFieldOfContract a then 0 else 1
  invFun i :=
    match i with
    | 0 => ⟨c.fstFieldOfContract a, fstFieldOfContract_mem c a⟩
    | 1 => ⟨c.sndFieldOfContract a, sndFieldOfContract_mem c a⟩
  left_inv i := by
    simp only [Fin.isValue]
    have hi := i.2
    have ha := c.finset_eq_fstFieldOfContract_sndFieldOfContract a
    simp only [ha, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with hi | hi
    · rw [hi]
      simp only [↓reduceIte, Fin.isValue]
      exact Subtype.ext hi.symm
    · rw [hi, ite_eq_right]
      · exact Subtype.ext hi.symm
      · exact Ne.symm <| fstFieldOfContract_ne_sndFieldOfContract c a
  right_inv i := by
    fin_cases i
    · simp
    · simp only [Fin.isValue, Fin.mk_one, ite_eq_right_iff, zero_ne_one, imp_false]
      exact Ne.symm <| fstFieldOfContract_ne_sndFieldOfContract c a

lemma prod_finset_eq_mul_fst_snd (c : WickContraction n) (a : c.1)
    (f : a.1 → M) [CommMonoid M] :
    ∏ (x : a), f x = f (⟨c.fstFieldOfContract a, fstFieldOfContract_mem c a⟩)
    * f (⟨c.sndFieldOfContract a, sndFieldOfContract_mem c a⟩) := by
  rw [← (c.contractEquivFinTwo a).symm.prod_comp]
  simp [contractEquivFinTwo]

/-- For a field specification `𝓕`, `φs` a list of `𝓕.FieldOp` and a Wick contraction
  `φsΛ` of `φs`, the Wick contraction `φsΛ` is said to be `GradingCompliant` if
  for every pair in `φsΛ` the contracted fields are either both `fermionic` or both `bosonic`.
  In other words, in a `GradingCompliant` Wick contraction if
  no contracted pairs occur between `fermionic` and `bosonic` fields. -/
def GradingCompliant (φs : List 𝓕.FieldOp) (φsΛ : WickContraction φs.length) :=
  ∀ (a : φsΛ.1), (𝓕 |>ₛ φs[(φsΛ.fstFieldOfContract a).1]) = (𝓕 |>ₛ φs[(φsΛ.sndFieldOfContract a).1])

lemma gradingCompliant_congr {φs φs' : List 𝓕.FieldOp} (h : φs = φs')
    (φsΛ : WickContraction φs.length) :
    GradingCompliant φs φsΛ ↔ GradingCompliant φs' (congr (by simp [h]) φsΛ) := by
  subst h
  rfl

/-- An equivalence from the sigma type `(a : c.1) × a` to the subtype of `Fin n` consisting of
  those positions which are contracted. -/
def sigmaContractedEquiv : (a : c.1) × a ≃ {x : Fin n // (c.getDual? x).isSome} where
  toFun := fun x => ⟨x.2, getDual?_isSome_of_mem c x.fst x.snd⟩
  invFun := fun x => ⟨
    ⟨{x.1, (c.getDual? x.1).get x.2}, self_getDual?_get_mem c (↑x) x.prop⟩,
    ⟨x.1, by simp⟩⟩
  left_inv x := by
    have hxa (x1 x2 : (a : c.1) × a) (h1 : x1.1 = x2.1)
      (h2 : x1.2.val = x2.2.val) : x1 = x2 := by
      cases x1
      cases x2
      simp_all only [Sigma.mk.inj_iff, true_and]
      subst h1
      rename_i fst snd snd_1
      simp_all only [heq_eq_eq]
      obtain ⟨val, property⟩ := fst
      obtain ⟨val_2, property_2⟩ := snd
      subst h2
      simp_all only
    match x with
    | ⟨a, i⟩ =>
    apply hxa
    · have hc := c.2.2 a.1 a.2 {i.1, (c.getDual? ↑i).get (getDual?_isSome_of_mem c a i)}
        (self_getDual?_get_mem c (↑i) (getDual?_isSome_of_mem c a i))
      have hn : ¬ Disjoint a.1 {i.1, (c.getDual? ↑i).get (getDual?_isSome_of_mem c a i)} := by
        rw [Finset.disjoint_iff_inter_eq_empty, @Finset.eq_empty_iff_forall_notMem]
        simp only [Finset.coe_mem, Finset.inter_insert_of_mem, Finset.mem_insert, Finset.mem_inter,
          Finset.mem_singleton, not_or, not_and, not_forall, Decidable.not_not]
        exact ⟨i, fun x ↦ (x rfl).elim⟩
      simp_all only [or_false, disjoint_self, Finset.bot_eq_empty, Finset.insert_ne_empty,
        not_false_eq_true]
      exact Subtype.ext (id (Eq.symm hc))
    · simp
  right_inv := by
    intro x
    cases x
    rfl

end WickContraction
