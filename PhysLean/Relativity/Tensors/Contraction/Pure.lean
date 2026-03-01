/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.Basic
/-!

# Contractions on pure tensors

-/

open IndexNotation
open CategoryTheory
open MonoidalCategory

namespace TensorSpecies
open OverColor

variable {k : Type} [CommRing k] {C G : Type} [Group G] {S : TensorSpecies k C G}

namespace Tensor

/-!

## Pure.contrPCoeff

-/

namespace Pure

/-!

## dropPairEmb

-/

variable {n : ℕ} {c : Fin (n + 1 + 1) → C}

/-- The embedding of `Fin n` into `Fin (n + 1 + 1)` which leaves a hole
  at `i` and `j`. -/
def dropPairEmb (i j : Fin (n + 1 + 1)) (m : Fin n) : Fin (n + 1 + 1) :=
  if m.1 < i.1 ∧ m.1 < j.1 then
    ⟨m, by omega⟩
  else if m.1 + 1 < i.1 ∧ j.1 ≤ m.1 then
    ⟨m + 1, by omega⟩
  else if i.1 ≤ m.1 ∧ m.1 + 1 < j.1 then
    ⟨m + 1, by omega⟩
  else
    ⟨m + 2, by omega⟩

lemma dropPairEmb_self_apply (i : Fin (n + 1 + 1)) (m : Fin n) :
    dropPairEmb i i m = if m.1 < i.1 then ⟨m.1, by omega⟩ else ⟨m.1 + 2, by omega⟩ := by
  simp [dropPairEmb]
  by_cases hm : m.1 < i.1
  · simp_all
  · have hn : i.1 ≤ m.1 := by omega
    have hn2 : ¬ m.1 + 1 < i.1 := by omega
    simp [hm, hn, hn2]

lemma dropPairEmb_eq_succAbove_succAbove (i : Fin (n + 1 + 1)) (j : Fin (n + 1)) :
    dropPairEmb i (i.succAbove j) = i.succAbove ∘ j.succAbove := by
  ext m
  by_cases h : m.1 < i.1
  · simp [dropPairEmb, h, Fin.succAbove, Fin.lt_def]
    split_ifs
    all_goals
      simp_all
      try omega
  · simp [dropPairEmb, Fin.succAbove, Fin.lt_def]
    split_ifs
    all_goals
      simp_all
      try omega

lemma dropPairEmb_injective {n : ℕ}
    (i j : Fin (n + 1 + 1)) : Function.Injective (dropPairEmb i j) := by
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨j, rfl⟩
  · intro a b
    simp [dropPairEmb_self_apply]
    intro h
    split_ifs at h
    · simp_all [Fin.ext_iff]
    · simp_all [Fin.ext_iff]
      omega
    · simp_all [Fin.ext_iff]
      omega
    · simp_all [Fin.ext_iff]
  · rw [dropPairEmb_eq_succAbove_succAbove]
    apply Function.Injective.comp
    · exact Fin.succAbove_right_injective
    · exact Fin.succAbove_right_injective

@[simp]
lemma dropPairEmb_eq_iff_eq {n : ℕ}
    (i j : Fin (n + 1 + 1)) (m1 m2 : Fin n) :
    dropPairEmb i j m1 = dropPairEmb i j m2 ↔ m1 = m2 := by
  rw [(dropPairEmb_injective i j).eq_iff]

@[simp]
lemma dropPairEmb_leq_iff_leq {n : ℕ}
    (i j : Fin (n + 1 + 1)) (m1 m2 : Fin n) :
    dropPairEmb i j m1 ≤ dropPairEmb i j m2 ↔ m1 ≤ m2 := by
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨j, rfl⟩
  · simp [dropPairEmb_self_apply]
    split_ifs
    · simp_all
    · simp_all
      omega
    · simp_all
      omega
    · simp_all
  · rw [dropPairEmb_eq_succAbove_succAbove]
    simp only [Function.comp_apply]
    rw [Fin.succAbove_le_succAbove_iff]
    rw [Fin.succAbove_le_succAbove_iff]

@[simp]
lemma dropPairEmb_lt_iff_lt {n : ℕ}
    (i j : Fin (n + 1 + 1)) (m1 m2 : Fin n) :
    dropPairEmb i j m1 < dropPairEmb i j m2 ↔ m1 < m2 := by
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨j, rfl⟩
  · simp [dropPairEmb_self_apply]
    split_ifs
    · simp_all
    · simp_all
      omega
    · simp_all
      omega
    · simp_all
  · rw [dropPairEmb_eq_succAbove_succAbove]
    simp only [Function.comp_apply]
    rw [Fin.succAbove_lt_succAbove_iff]
    rw [Fin.succAbove_lt_succAbove_iff]

@[simp]
lemma dropPairEmb_monotone {n : ℕ} (i j : Fin (n + 1 + 1)) :
    Monotone (dropPairEmb i j) := by
  intro a b
  simp

lemma dropPairEmb_eq_orderEmbOfFin {n : ℕ}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j) :
    dropPairEmb i j = (Finset.orderEmbOfFin {i, j}ᶜ
    (by rw [Finset.card_compl]; simp [Finset.card_pair hij])) := by
  let dropPairEmb : Fin n ↪o Fin (n + 1 + 1) :=
  (Finset.orderEmbOfFin {i, j}ᶜ
  (by rw [Finset.card_compl]; simp [Finset.card_pair hij]))
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨j, rfl⟩
  · simp at hij
  rw [dropPairEmb_eq_succAbove_succAbove]
  symm
  let f : Fin n ↪o Fin (n + 1 + 1) :=
    ⟨⟨i.succAboveOrderEmb ∘ j.succAboveOrderEmb, by
      refine Function.Injective.comp ?_ ?_
      exact Fin.succAbove_right_injective
      exact Fin.succAbove_right_injective⟩, by
      simp only [Function.Embedding.coeFn_mk, Function.comp_apply, OrderEmbedding.le_iff_le,
        implies_true]⟩
  have hf : dropPairEmb = f := by
    rw [← OrderEmbedding.range_inj]
    simp only [Finset.range_orderEmbOfFin, Finset.coe_compl,
      RelEmbedding.coe_mk, Function.Embedding.coeFn_mk, dropPairEmb, f]
    change _ = Set.range (i.succAbove ∘ j.succAbove)
    rw [Set.range_comp]
    simp only [Fin.range_succAbove]
    ext a
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_image]
    apply Iff.intro
    · intro h
      have ha := Fin.eq_self_or_eq_succAbove i a
      simp_all [false_or]
      obtain ⟨a, rfl⟩ := ha
      use a
      simp_all only [and_true]
      rw [Fin.succAbove_right_injective.eq_iff] at h
      exact h.2
    · intro h
      obtain ⟨a, h1, rfl⟩ := h
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff,
        not_or]
      rw [Fin.succAbove_right_injective.eq_iff]
      simp_all only [not_false_eq_true, and_true]
      exact Fin.succAbove_ne i a
  ext a
  have hf' := congrFun (congrArg (fun x => x.toFun) hf) a
  simp only [Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding, Function.comp_apply,
    Fin.succAboveOrderEmb_apply, f] at hf'
  rw [hf']
  rfl

lemma dropPairEmb_symm (i j : Fin (n + 1 + 1)) :
    dropPairEmb i j = dropPairEmb j i := by
  by_cases hij : i = j
  · subst hij
    rfl
  rw [dropPairEmb_eq_orderEmbOfFin i j hij,
    dropPairEmb_eq_orderEmbOfFin j i (Ne.symm hij)]
  simp [Finset.pair_comm]

@[simp, nolint simpVarHead]
lemma permCond_dropPairEmb_symm {c : Fin (n + 1 + 1) → C} (i j : Fin (n + 1 + 1))
    (k : Fin n) : c (dropPairEmb i j k) = c (dropPairEmb j i k) := by
  rw [dropPairEmb_symm]

lemma dropPairEmb_apply_eq_orderIsoOfFin {i j : Fin (n + 1 + 1)} (hij : i ≠ j) (m : Fin n) :
    (dropPairEmb i j) m = (Finset.orderIsoOfFin {i, j}ᶜ
      (by rw [Finset.card_compl]; simp [Finset.card_pair hij])) m := by
  simp [dropPairEmb_eq_orderEmbOfFin i j hij]

@[simp]
lemma dropPairEmb_range {i j : Fin (n + 1 + 1)} (hij : i ≠ j) :
    Set.range (dropPairEmb i j) = {i, j}ᶜ := by
  rw [dropPairEmb_eq_orderEmbOfFin i j hij, Finset.range_orderEmbOfFin]
  simp only [Finset.compl_insert, Finset.coe_erase, Finset.coe_compl, Finset.coe_singleton]
  ext x : 1
  simp only [Set.mem_diff, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_insert_iff, not_or]
  apply Iff.intro
  · intro a
    simp_all only [not_false_eq_true, and_self]
  · intro a
    simp_all only [not_false_eq_true, and_self]

lemma dropPairEmb_image_compl {i j : Fin (n + 1 + 1)} (hij : i ≠ j)
    (X : Set (Fin n)) :
    (dropPairEmb i j) '' Xᶜ = ({i, j} ∪ dropPairEmb i j '' X)ᶜ := by
  rw [← compl_inj_iff, Function.Injective.compl_image_eq (dropPairEmb_injective i j)]
  simp only [compl_compl, dropPairEmb_range hij]
  exact Set.union_comm ((dropPairEmb i j) '' X) {i, j}

@[simp]
lemma fst_ne_dropPairEmb_pre (i j : Fin (n + 1 + 1)) (m : Fin n) :
    ¬ i = dropPairEmb i j m := by
  by_cases hij : i = j
  · subst hij
    simp [dropPairEmb_self_apply]
    by_cases hm : m.1 < i.1
    · simp [hm, Fin.ext_iff]
      omega
    · simp [hm, Fin.ext_iff]
      omega
  · by_contra hn
    have hi : i ∉ Set.range (dropPairEmb i j) := by
      simp [dropPairEmb_eq_orderEmbOfFin i j hij]
    nth_rewrite 2 [hn] at hi
    simp [- dropPairEmb_range] at hi

@[simp]
lemma dropPairEmb_ne_fst (i j : Fin (n + 1 + 1)) (m : Fin n) :
    ¬ dropPairEmb i j m = i := by
  apply Ne.symm
  simp

@[simp]
lemma snd_ne_dropPairEmb_pre (i j : Fin (n + 1 + 1)) (m : Fin n) :
    ¬ j = (dropPairEmb i j) m := by
  rw [dropPairEmb_symm]
  exact fst_ne_dropPairEmb_pre j i m

@[simp]
lemma dropPairEmb_ne_snd (i j : Fin (n + 1 + 1)) (m : Fin n) :
    ¬ dropPairEmb i j m = j := by
  apply Ne.symm
  simp

lemma dropPairEmb_succAbove {n : ℕ}
    (i : Fin (n + 1 + 1)) (j : Fin (n + 1)) :
    dropPairEmb i (i.succAbove j) =
    i.succAbove ∘ j.succAbove := by
  exact dropPairEmb_eq_succAbove_succAbove i j

lemma eq_or_exists_dropPairEmb
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j) (m : Fin (n + 1 + 1)) :
    m = i ∨ m = j ∨ ∃ m', m = dropPairEmb i j m' := by
  by_cases h : m = i
  · subst h
    simp
  · by_cases h' : m = j
    · subst h'
      simp
    · simp_all only [false_or]
      have h'' : m ∈ Set.range (dropPairEmb i j) := by
        simp_all [dropPairEmb_eq_orderEmbOfFin]
      rw [@Set.mem_range] at h''
      obtain ⟨m', rfl⟩ := h''
      exact ⟨m', rfl⟩

/-!

## dropPairEmbPre

-/

/-- The preimage of `m` under `dropPairEmb i j hij` given that `m` is not equal
  to `i` or `j`. -/
def dropPairEmbPre (i j : Fin (n + 1 + 1)) (hij : i ≠ j) (m : Fin (n + 1 + 1))
    (hm : m ≠ i ∧ m ≠ j) : Fin n :=
  if h1 : m.1 < i.1 ∧ m.1 < j.1 then
        ⟨m, by fin_omega⟩
      else if h2 : m.1 - 1 < i.1 ∧ j.1 ≤ m.1 then
        ⟨m - 1, by fin_omega⟩
      else if h3 : i.1 - 1 ≤ m.1 ∧ m.1 < j.1 then
        ⟨m - 1, by fin_omega⟩
      else
        ⟨m - 2, by fin_omega⟩

@[simp]
lemma dropPairEmb_dropPairEmbPre (i j : Fin (n + 1 + 1)) (hij : i ≠ j) (m : Fin (n + 1 + 1))
    (hm : m ≠ i ∧ m ≠ j) :
    dropPairEmb i j (dropPairEmbPre i j hij m hm) = m := by
  dsimp [dropPairEmb, dropPairEmbPre]
  split_ifs
  · rfl
  all_goals
    simp_all [Fin.ext_iff]
    try omega

lemma dropPairEmbPre_eq_orderIsoOfFin (i j : Fin (n + 1 + 1)) (hij : i ≠ j) (m : Fin (n + 1 + 1))
    (hm : m ≠ i ∧ m ≠ j) :
    dropPairEmbPre i j hij m hm =
    (Finset.orderIsoOfFin {i, j}ᶜ (by rw [Finset.card_compl]; simp [Finset.card_pair hij])).symm
    ⟨m, by simp [hm]⟩ := by
  apply dropPairEmb_injective i j
  conv_rhs => rw [dropPairEmb_apply_eq_orderIsoOfFin hij]
  simp

@[simp]
lemma dropPairEmbPre_injective (i j : Fin (n + 1 + 1)) (hij : i ≠ j)
    (m1 m2 : Fin (n + 1 + 1)) (hm1 : m1 ≠ i ∧ m1 ≠ j) (hm2 : m2 ≠ i ∧ m2 ≠ j) :
    dropPairEmbPre i j hij m1 hm1 = dropPairEmbPre i j hij m2 hm2 ↔ m1 = m2 := by
  rw [← Function.Injective.eq_iff (dropPairEmb_injective i j)]
  simp

lemma dropPairEmbPre_surjective (i j : Fin (n + 1 + 1)) (hij : i ≠ j)
    (m : Fin n) :
    ∃ m' : Fin (n + 1 + 1), ∃ (h : m' ≠ i ∧ m' ≠ j),
    dropPairEmbPre i j hij m' h = m := by
  use (dropPairEmb i j) m
  have h : (dropPairEmb i j) m ≠ i ∧ (dropPairEmb i j) m ≠ j := by
    simp [Ne.symm]
  use h
  apply (dropPairEmb_injective i j)
  simp

@[simp]
lemma dropPairEmbPre_dropPairEmb (i j : Fin (n + 1 + 1)) (hij : i ≠ j)
    (m : Fin n) :
    dropPairEmbPre i j hij (dropPairEmb i j m) (by simp) = m := by
  apply dropPairEmb_injective i j
  simp

/-!

## Commutativity of dropPairEmb

-/
lemma dropPairEmb_comm (i1 j1 : Fin (n + 1 + 1 + 1 + 1)) (i2 j2 : Fin (n + 1 + 1))
    (hij1 : i1 ≠ j1) (hij2 : i2 ≠ j2) :
    let i2' := (dropPairEmb i1 j1 i2);
    let j2' := (dropPairEmb i1 j1 j2);
    have hi2j2' : i2' ≠ j2' := by simp [i2', j2', hij2];
    let i1' := (dropPairEmbPre i2' j2' hi2j2' i1 (by simp [i2', j2']));
    let j1' := (dropPairEmbPre i2' j2' hi2j2' j1 (by simp [i2', j2']));
    dropPairEmb i1 j1 ∘ dropPairEmb i2 j2 =
    dropPairEmb i2' j2' ∘
    dropPairEmb i1' j1':= by
  intro i2' j2' hi2j2'
  let fl : Fin n ↪o Fin (n + 1 + 1 + 1 + 1) :=
    ⟨⟨dropPairEmb i1 j1 ∘ dropPairEmb i2 j2, by
      apply Function.Injective.comp
      exact dropPairEmb_injective i1 j1
      exact dropPairEmb_injective _ _⟩, by simp only [Function.Embedding.coeFn_mk,
        Function.comp_apply, dropPairEmb_leq_iff_leq, implies_true]⟩
  let fr : Fin n ↪o Fin (n + 1 + 1 + 1 + 1) :=
    ⟨⟨dropPairEmb i2' j2' ∘ dropPairEmb
      (dropPairEmbPre i2' j2' hi2j2' i1 (by simp [i2', j2']))
      (dropPairEmbPre i2' j2' hi2j2' j1 (by simp [i2', j2'])),
      by
      apply Function.Injective.comp
      exact dropPairEmb_injective _ _
      exact dropPairEmb_injective _ _⟩, by simp only [Function.Embedding.coeFn_mk,
        Function.comp_apply, dropPairEmb_leq_iff_leq, implies_true]⟩
  have h : fl = fr := by
    rw [← OrderEmbedding.range_inj]
    simp only [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk, Set.range_comp,
      dropPairEmb_range hij2, fl, fr, j2', i2']
    rw [dropPairEmb_range (by simp [hij1])]
    rw [dropPairEmb_image_compl, dropPairEmb_image_compl]
    congr 1
    rw [Set.image_pair, Set.image_pair]
    simp only [dropPairEmb_dropPairEmbPre, i2', j2']
    exact Set.union_comm {i1, j1} {(dropPairEmb i1 j1) i2, (dropPairEmb i1 j1) j2}
    simp [hij2]
    simp [hij1]
  ext1 a
  have h' := congrFun (congrArg (fun x => x.toFun) h) a
  dsimp [fl, fr] at h'
  exact h'

lemma dropPairEmb_comm_apply (i1 j1 : Fin (n + 1 + 1 + 1 + 1)) (i2 j2 : Fin (n + 1 + 1))
    (hij1 : i1 ≠ j1) (hij2 : i2 ≠ j2) (m : Fin n) :
    let i2' := (dropPairEmb i1 j1 i2);
    let j2' := (dropPairEmb i1 j1 j2);
    have hi2j2' : i2' ≠ j2' := by simp [i2', j2', hij2];
    let i1' := (dropPairEmbPre i2' j2' hi2j2' i1 (by simp [i2', j2']));
    let j1' := (dropPairEmbPre i2' j2' hi2j2' j1 (by simp [i2', j2']));
    dropPairEmb i2' j2'
    (dropPairEmb i1' j1' m) =
    dropPairEmb i1 j1 (dropPairEmb i2 j2 m) := by
  intro i2' j2' hi2j2' i1' j1'
  change _ = (dropPairEmb i1 j1 ∘ dropPairEmb i2 j2) m
  rw [dropPairEmb_comm i1 j1 i2 j2 hij1 hij2]
  rfl

lemma permCond_dropPairEmb_comm {n : ℕ} {c : Fin (n + 1 + 1 + 1 + 1) → C}
    (i1 j1 : Fin (n + 1 + 1 + 1 + 1)) (i2 j2 : Fin (n + 1 + 1))
    (hij1 : i1 ≠ j1) (hij2 : i2 ≠ j2) :
    let i2' := (dropPairEmb i1 j1 i2);
    let j2' := (dropPairEmb i1 j1 j2);
    have hi2j2' : i2' ≠ j2' := by simp [i2', j2', hij2];
    let i1' := (dropPairEmbPre i2' j2' hi2j2' i1 (by simp [i2', j2']));
    let j1' := (dropPairEmbPre i2' j2' hi2j2' j1 (by simp [i2', j2']));
    PermCond
      ((c ∘ dropPairEmb i2' j2') ∘ dropPairEmb i1' j1')
      ((c ∘ dropPairEmb i1 j1) ∘ dropPairEmb i2 j2)
      id := by
  apply And.intro (Function.bijective_id)
  simp only [id_eq, Function.comp_apply]
  intro i
  rw [dropPairEmb_comm_apply]
  · simp [hij1]
  · simp [hij2]

/-!

## dropPairOfMap

-/

/-- Given a bijection `Fin (n1 + 1 + 1) → Fin (n + 1 + 1))` and a pair `i j : Fin (n1 + 1 + 1)`,
  then `dropPairOfMap i j _ σ _ : Fin n1 → Fin n` corresponds to the induced bijection
  formed by dropping `i` and `j` in the source and their image in the target. -/
def dropPairOfMap {n n1 : ℕ} (i j : Fin (n1 + 1 + 1)) (hij : i ≠ j)
    (σ : Fin (n1 + 1 + 1) → Fin (n + 1 + 1)) (hσ : Function.Bijective σ)
    (m : Fin n1) : Fin n :=
  dropPairEmbPre (σ i) (σ j)
    (by simp [hσ.injective.eq_iff, hij])
    (σ (dropPairEmb i j m)) (by simp [hσ.injective.eq_iff, Ne.symm])

lemma dropPairOfMap_injective {n n1 : ℕ} (i j : Fin (n1 + 1 + 1)) (hij : i ≠ j)
    (σ : Fin (n1 + 1 + 1) → Fin (n + 1 + 1)) (hσ : Function.Bijective σ) :
    Function.Injective (dropPairOfMap i j hij σ hσ) := by
  intro m1 m2 h
  simpa [dropPairOfMap, hσ.injective.eq_iff] using h

lemma dropPairOfMap_surjective {n n1 : ℕ} (i j : Fin (n1 + 1 + 1)) (hij : i ≠ j)
    (σ : Fin (n1 + 1 + 1) → Fin (n + 1 + 1)) (hσ : Function.Bijective σ) :
    Function.Surjective (dropPairOfMap i j hij σ hσ) := by
  intro m
  simp only [dropPairOfMap]
  obtain ⟨m, hm, rfl⟩ := dropPairEmbPre_surjective (σ i) (σ j)
    (by simp [hσ.injective.eq_iff, hij]) m
  simp only [dropPairEmbPre_injective]
  obtain ⟨m', rfl⟩ := hσ.surjective m
  simp only [ne_eq, hσ.injective.eq_iff] at hm ⊢
  rcases eq_or_exists_dropPairEmb i j hij m' with rfl | rfl | ⟨m'', rfl⟩
  · simp_all
  · simp_all
  · exact ⟨m'', rfl⟩

lemma dropPairOfMap_bijective {n n1 : ℕ} (i j : Fin (n1 + 1 + 1)) (hij : i ≠ j)
    (σ : Fin (n1 + 1 + 1) → Fin (n + 1 + 1)) (hσ : Function.Bijective σ) :
    Function.Bijective (dropPairOfMap i j hij σ hσ) := by
  apply And.intro
  · apply dropPairOfMap_injective
  · apply dropPairOfMap_surjective

lemma permCond_dropPairOfMap {n n1 : ℕ} {c : Fin (n + 1 + 1) → C}
    {c1 : Fin (n1 + 1 + 1) → C}
    (i j : Fin (n1 + 1 + 1)) (hij : i ≠ j)
    (σ : Fin (n1 + 1 + 1) → Fin (n + 1 + 1)) (hσ : PermCond c c1 σ) :
    PermCond (c ∘ dropPairEmb (σ i) (σ j))
      (c1 ∘ dropPairEmb i j) (dropPairOfMap i j hij σ hσ.1) := by
  apply And.intro
  · exact dropPairOfMap_bijective i j hij σ hσ.left
  · intro m
    simp [dropPairOfMap, hσ.2]

@[simp]
lemma dropPairOfMap_id { n1 : ℕ} (i j : Fin (n1 + 1 + 1)) (hij : i ≠ j) :
    dropPairOfMap i j hij id (Function.bijective_id) = id := by
  ext1 m
  simp [dropPairOfMap]

/-!

## dropPair

-/

set_option linter.unusedVariables false in
/-- Given `i j : Fin (n + 1 + 1)`, `c : Fin (n + 1 + 1) → C` and a pure tensor `p : Pure S c`,
  `dropPair i j _ p` is the tensor formed by dropping the `i`th and `j`th parts of `p`. -/
@[nolint unusedArguments]
def dropPair (i j : Fin (n + 1 + 1)) (hij : i ≠ j) (p : Pure S c) :
    Pure S (c ∘ dropPairEmb i j) :=
    fun m => p (dropPairEmb i j m)

@[simp]
lemma dropPair_equivariant {n : ℕ} {c : Fin (n + 1 + 1) → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j) (p : Pure S c) (g : G) :
    dropPair i j hij (g • p) = g • dropPair i j hij p := by
  ext m
  simp only [dropPair, actionP_eq]
  rfl

lemma dropPair_symm (i j : Fin (n + 1 + 1)) (hij : i ≠ j)
    (p : Pure S c) : dropPair i j hij p =
    permP id (by simp) (dropPair j i hij.symm p) := by
  ext m
  simp only [Function.comp_apply, dropPair, permP, id_eq]
  refine (congr_right _ _ _ ?_).symm
  rw [dropPairEmb_symm]

lemma dropPair_comm {n : ℕ} {c : Fin (n + 1 + 1 + 1 + 1) → C}
    (i1 j1 : Fin (n + 1 + 1 + 1 + 1)) (i2 j2 : Fin (n + 1 + 1))
    (hij1 : i1 ≠ j1) (hij2 : i2 ≠ j2) (p : Pure S c) :
    let i2' := (dropPairEmb i1 j1 i2);
    let j2' := (dropPairEmb i1 j1 j2);
    have hi2j2' : i2' ≠ j2' := by simp [i2', j2', hij2];
    let i1' := (dropPairEmbPre i2' j2' hi2j2' i1 (by simp [i2', j2']));
    let j1' := (dropPairEmbPre i2' j2' hi2j2' j1 (by simp [i2', j2']));
    dropPair i2 j2 hij2 (dropPair i1 j1 hij1 p) =
    permP id (permCond_dropPairEmb_comm i1 j1 i2 j2 hij1 hij2)
    ((dropPair i1' j1' (by simp [i1', j1', hij1]) (dropPair i2' j2' hi2j2' p))) := by
  ext m
  simp only [Function.comp_apply, dropPair, permP, id_eq]
  apply (congr_right _ _ _ ?_).symm
  rw [dropPairEmb_comm_apply]
  · simp [hij1]
  · simp [hij2]

@[simp]
lemma dropPair_update_fst {n : ℕ} [inst : DecidableEq (Fin (n + 1 +1))] {c : Fin (n + 1 + 1) → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j) (p : Pure S c)
    (x : S.FD.obj (Discrete.mk (c i))) :
    dropPair i j hij (p.update i x) = dropPair i j hij p := by
  ext m
  simp only [Function.comp_apply, dropPair, update]
  rw [Function.update_of_ne]
  exact Ne.symm (fst_ne_dropPairEmb_pre i j m)

@[simp]
lemma dropPair_update_snd {n : ℕ} [inst : DecidableEq (Fin (n + 1 +1))] {c : Fin (n + 1 + 1) → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j) (p : Pure S c)
    (x : S.FD.obj (Discrete.mk (c j))) :
    dropPair i j hij (p.update j x) = dropPair i j hij p := by
  rw [dropPair_symm]
  simp only [dropPair_update_fst]
  conv_rhs => rw [dropPair_symm]

@[simp]
lemma dropPair_update_dropPairEmb {n : ℕ} [inst : DecidableEq (Fin (n + 1 +1))]
    {c : Fin (n + 1 + 1) → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j) (p : Pure S c)
    (m : Fin n)
    (x : S.FD.obj (Discrete.mk (c (dropPairEmb i j m)))) :
    dropPair i j hij (p.update (dropPairEmb i j m) x) =
    (dropPair i j hij p).update m x := by
  ext m'
  simp only [Function.comp_apply, dropPair, update]
  by_cases h : m' = m
  · subst h
    simp
  · rw [Function.update_of_ne, Function.update_of_ne]
    · rfl
    · simp [h]
    · simp [h]

TODO "63B7X" "Prove lemmas relating to the commutation rules of `dropPair` and `prodP`."

@[simp]
lemma dropPair_permP {n n1 : ℕ} {c : Fin (n + 1 + 1) → C}
    {c1 : Fin (n1 + 1 + 1) → C} (i j : Fin (n1 + 1 + 1)) (hij : i ≠ j)
    (σ : Fin (n1 + 1 + 1) → Fin (n + 1 + 1)) (hσ : PermCond c c1 σ) (p : Pure S c) :
    dropPair i j hij (permP σ hσ p) =
    permP (dropPairOfMap i j hij σ hσ.1) (permCond_dropPairOfMap i j hij σ hσ)
    (dropPair (σ i) (σ j) (by simp [hσ.1.injective.eq_iff, hij]) p) := by
  ext m
  simp only [Function.comp_apply, dropPair, permP, dropPairOfMap]
  apply congr_mid
  · simp
  · simp [hσ.2]
  · simp [hσ.2]

/-!

## Contraction coefficient

-/

/-- Given a pure tensor `p : Pure S c` and a `i j : Fin n`
  corresponding to dual colors in `c`, `contrPCoeff i j _ p` is the
  element of the underlying ring `k` formed by contracting `p i` and `p j`. -/
noncomputable def contrPCoeff {n : ℕ} {c : Fin n → C}
    (i j : Fin n) (hij : i ≠ j ∧ S.τ (c i) = c j) (p : Pure S c) : k :=
    (S.contr.app (Discrete.mk (c i))) (p i ⊗ₜ ((S.FD.map (eqToHom (by simp [hij]))) (p j)))

@[simp]
lemma contrPCoeff_permP {n n1 : ℕ} {c : Fin n → C}
    {c1 : Fin n1 → C} (i j : Fin n1) (hij : i ≠ j ∧ S.τ (c1 i) = c1 j)
    (σ : Fin n1 → Fin n) (hσ : PermCond c c1 σ) (p : Pure S c) :
    contrPCoeff i j hij (permP σ hσ p) =
    contrPCoeff (σ i) (σ j) (by simp [hσ.1.injective.eq_iff, hij, hσ.2]) p := by
  simp only [contrPCoeff, Monoidal.tensorUnit_obj, Equivalence.symm_inverse,
    Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
    Functor.comp_obj, Discrete.functor_obj_eq_as, Function.comp_apply, permP]
  conv_rhs => erw [S.contr_congr (c (σ i)) ((c1 i)) (by simp [hσ.2])]
  simp only [Monoidal.tensorUnit_obj, Equivalence.symm_inverse,
    Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
    Functor.comp_obj, Discrete.functor_obj_eq_as, Function.comp_apply]
  apply congrArg
  congr 1
  change ((S.FD.map (eqToHom _) ≫ S.FD.map (eqToHom _)).hom) _ =
    ((S.FD.map (eqToHom _) ≫ S.FD.map (eqToHom _)).hom) _
  rw [← Functor.map_comp, ← Functor.map_comp]
  simp

@[simp]
lemma contrPCoeff_update_dropPairEmb {n : ℕ} [inst : DecidableEq (Fin (n + 1 +1))]
    {c : Fin (n + 1 + 1) → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ S.τ (c i) = c j) (m : Fin n)
    (p : Pure S c) (x : S.FD.obj (Discrete.mk (c (dropPairEmb i j m)))) :
    contrPCoeff i j hij (p.update (dropPairEmb i j m) x) =
    contrPCoeff i j hij p := by
  simp only [contrPCoeff]
  congr
  · simp [update]
  · simp [update]

@[simp]
lemma contrPCoeff_update_fst_add {n : ℕ} [inst : DecidableEq (Fin n)] {c : Fin n → C}
    (i j : Fin n) (hij : i ≠ j ∧ S.τ (c i) = c j)
    (p : Pure S c) (x y : S.FD.obj (Discrete.mk (c i))) :
    contrPCoeff i j hij (p.update i (x + y)) =
    contrPCoeff i j hij (p.update i x) + contrPCoeff i j hij (p.update i y) := by
  change ((S.contr.app { as := c i })).hom.hom' _ = ((S.contr.app { as := c i })).hom.hom' _
    + ((S.contr.app { as := c i })).hom.hom' _
  simp [Function.update_of_ne (Ne.symm hij.1), update, TensorProduct.add_tmul, map_add]

@[simp]
lemma contrPCoeff_update_snd_add {n : ℕ} [inst : DecidableEq (Fin n)] {c : Fin n → C}
    (i j : Fin n) (hij : i ≠ j ∧ S.τ (c i) = c j)
    (p : Pure S c) (x y : S.FD.obj (Discrete.mk (c j))) :
    contrPCoeff i j hij (p.update j (x + y)) =
    contrPCoeff i j hij (p.update j x) + contrPCoeff i j hij (p.update j y) := by
  simp only [contrPCoeff, Monoidal.tensorUnit_obj, Equivalence.symm_inverse,
    Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
    Functor.comp_obj, Discrete.functor_obj_eq_as, Function.comp_apply, update, Function.update_self]
  change ((S.contr.app { as := c i })).hom.hom' _ = ((S.contr.app { as := c i })).hom.hom' _
    + ((S.contr.app { as := c i })).hom.hom' _
  rw [Function.update_of_ne hij.1, Function.update_of_ne hij.1,
    Function.update_of_ne hij.1]
  conv_lhs =>
    enter [2, 3]
    change ((S.FD.map (eqToHom _))).hom.hom' (x + y)
  simp only [Monoidal.tensorUnit_obj, map_add, TensorProduct.tmul_add]
  rfl

@[simp]
lemma contrPCoeff_update_fst_smul {n : ℕ} [inst : DecidableEq (Fin n)] {c : Fin n → C}
    (i j : Fin n) (hij : i ≠ j ∧ S.τ (c i) = c j)
    (p : Pure S c) (r : k) (x : S.FD.obj (Discrete.mk (c i))) :
    contrPCoeff i j hij (p.update i (r • x)) =
    r * contrPCoeff i j hij (p.update i x) := by
  simp only [contrPCoeff, Monoidal.tensorUnit_obj, Equivalence.symm_inverse,
    Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
    Functor.comp_obj, Discrete.functor_obj_eq_as, Function.comp_apply, update, Function.update_self,
    TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  change ((S.contr.app { as := c i })).hom.hom' _ = r * _
  simp only [Monoidal.tensorUnit_obj, map_smul, smul_eq_mul]
  congr 1
  change ((S.contr.app { as := c i })).hom.hom' _ = ((S.contr.app { as := c i })).hom.hom' _
  rw [Function.update_of_ne (Ne.symm hij.1), Function.update_of_ne (Ne.symm hij.1)]

@[simp]
lemma contrPCoeff_update_snd_smul {n : ℕ} [inst : DecidableEq (Fin n)] {c : Fin n → C}
    (i j : Fin n) (hij : i ≠ j ∧ S.τ (c i) = c j)
    (p : Pure S c) (r : k) (x : S.FD.obj (Discrete.mk (c j))) :
    contrPCoeff i j hij (p.update j (r • x)) =
    r * contrPCoeff i j hij (p.update j x) := by
  simp only [contrPCoeff, Monoidal.tensorUnit_obj, Equivalence.symm_inverse,
    Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
    Functor.comp_obj, Discrete.functor_obj_eq_as, Function.comp_apply, update, Function.update_self]
  change ((S.contr.app { as := c i })).hom.hom' _ = r * _
  rw [Function.update_of_ne hij.1, Function.update_of_ne hij.1]
  conv_lhs =>
    enter [2, 3]
    change ((S.FD.map (eqToHom _))).hom.hom' (r • _)
  simp only [Monoidal.tensorUnit_obj, map_smul, TensorProduct.tmul_smul, smul_eq_mul]
  rfl

lemma contrPCoeff_dropPair {n : ℕ} {c : Fin (n + 1 + 1) → C}
    (a b : Fin (n + 1 + 1)) (hab : a ≠ b)
    (i j : Fin n) (hij : i ≠ j ∧ S.τ (c (dropPairEmb a b i)) = (c (dropPairEmb a b j)))
    (p : Pure S c) : (p.dropPair a b hab).contrPCoeff i j hij =
    p.contrPCoeff (dropPairEmb a b i) (dropPairEmb a b j)
      (by simpa using hij) := by rfl

lemma contrPCoeff_symm {n : ℕ} {c : Fin n → C} {i j : Fin n} {hij : i ≠ j ∧ S.τ (c i) = c j}
    {p : Pure S c} :
    p.contrPCoeff i j hij = p.contrPCoeff j i ⟨hij.1.symm, by simp [← hij.2]⟩ := by
  rw [contrPCoeff, contrPCoeff]
  erw [S.contr_tmul_symm]
  rw [S.contr_congr (S.τ (c i)) (c j)]
  simp only [Monoidal.tensorUnit_obj, Equivalence.symm_inverse,
    Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
    Functor.comp_obj, Discrete.functor_obj_eq_as, Function.comp_apply]
  change _ = (ConcreteCategory.hom (S.contr.app { as := c j }).hom) _
  congr 2
  · change ((S.FD.map (eqToHom _) ≫ S.FD.map (eqToHom _)).hom) _ = _
    rw [← S.FD.map_comp]
    simp
  · change ((S.FD.map (eqToHom _) ≫ S.FD.map (eqToHom _)).hom) _ = _
    rw [← S.FD.map_comp]
    simp only [eqToHom_trans]
    rfl
  · simp [hij.2]

lemma contrPCoeff_mul_dropPair {n : ℕ} {c : Fin (n + 1 + 1 + 1 + 1) → C}
    (i1 j1 : Fin (n + 1 + 1 + 1 + 1)) (i2 j2 : Fin (n + 1 + 1))
    (hij1 : i1 ≠ j1 ∧ S.τ (c i1) = (c j1))
    (hij2 : i2 ≠ j2 ∧ S.τ (c (dropPairEmb i1 j1 i2)) = (c (dropPairEmb i1 j1 j2)))
    (p : Pure S c) :
    let i2' := (dropPairEmb i1 j1 i2);
    let j2' := (dropPairEmb i1 j1 j2);
    have hi2j2' : i2' ≠ j2' := by simp [i2', j2', hij2];
    let i1' := (dropPairEmbPre i2' j2' hi2j2' i1 (by simp [i2', j2']));
    let j1' := (dropPairEmbPre i2' j2' hi2j2' j1 (by simp [i2', j2']));
    (p.contrPCoeff i1 j1 hij1) * (dropPair i1 j1 hij1.1 p).contrPCoeff i2 j2 hij2 =
    (p.contrPCoeff i2' j2' (by simp [i2', j2', hij2])) *
    (dropPair i2' j2' (by simp [i2', j2', hij2]) p).contrPCoeff i1' j1'
      (by simp [i1', j1', hij1]) := by
  simp only [contrPCoeff_dropPair, dropPairEmb_dropPairEmbPre]
  rw [mul_comm]

@[simp]
lemma contrPCoeff_invariant {n : ℕ} {c : Fin n → C} {i j : Fin n}
    {hij : i ≠ j ∧ S.τ (c i) = c j} {p : Pure S c}
    (g : G) : (g • p).contrPCoeff i j hij = p.contrPCoeff i j hij := by
  calc (g • p).contrPCoeff i j hij
    _ = (S.contr.app (Discrete.mk (c i)))
          ((S.FD.obj _).ρ g (p i) ⊗ₜ ((S.FD.map (eqToHom (by simp [hij])))
          ((S.FD.obj _).ρ g (p j)))) := rfl
    _ = (S.contr.app (Discrete.mk (c i)))
          ((S.FD.obj _).ρ g (p i) ⊗ₜ (S.FD.obj _).ρ g ((S.FD.map (eqToHom (by simp [hij])))
          (p j))) := by
        congr 2
        simp only [Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
          Functor.comp_obj, Discrete.functor_obj_eq_as, Function.comp_apply,
          Action.FunctorCategoryEquivalence.functor_obj_obj]
        have h1 := (S.FD.map (eqToHom (by simp [hij] : { as := c j } =
          (Discrete.functor (Discrete.mk ∘ S.τ)).obj { as := c i }))).comm g
        have h2 := congrFun (congrArg (fun x => x.hom) h1) (p j)
        simp only [Discrete.functor_obj_eq_as, Function.comp_apply, ModuleCat.hom_comp, Rep.ρ_hom,
          LinearMap.coe_comp] at h2
        exact h2
  have h1 := (S.contr.app (Discrete.mk (c i))).comm g
  have h2 := congrFun (congrArg (fun x => x.hom) h1) ((p i) ⊗ₜ
    ((S.FD.map (eqToHom (by simp [hij]))) (p j)))
  simp only [Monoidal.tensorUnit_obj, ModuleCat.hom_comp, Rep.ρ_hom, Equivalence.symm_inverse,
    Action.functorCategoryEquivalence_functor, Functor.comp_obj, Discrete.functor_obj_eq_as,
    Function.comp_apply, Action.FunctorCategoryEquivalence.functor_obj_obj,
    LinearMap.coe_comp] at h2
  exact h2

/-!

## Contractions

-/

/-- For `c : Fin (n + 1 + 1) → C`, `i j : Fin (n + 1 + 1)` with dual color, and a pure tensor
  `p : Pure S c`, `contrP i j _ p` is the tensor (not pure due to the `n = 0` case)
  formed by contracting the `i`th index of `p`
  with the `j`th index. -/
noncomputable def contrP {n : ℕ} {c : Fin (n + 1 + 1) → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ S.τ (c i) = c j) (p : Pure S c) :
    S.Tensor (c ∘ dropPairEmb i j) :=
  (p.contrPCoeff i j hij) • (p.dropPair i j hij.1).toTensor

@[simp]
lemma contrP_update_add {n : ℕ} [inst : DecidableEq (Fin (n + 1 +1))] {c : Fin (n + 1 + 1) → C}
    (i j m : Fin (n + 1 + 1)) (hij : i ≠ j ∧ S.τ (c i) = c j)
    (p : Pure S c) (x y : S.FD.obj (Discrete.mk (c m))) :
    contrP i j hij (p.update m (x + y)) =
    contrP i j hij (p.update m x) + contrP i j hij (p.update m y) := by
  rcases eq_or_exists_dropPairEmb i j hij.1 m with rfl | rfl | ⟨m', rfl⟩
  · simp [contrP, add_smul]
  · simp [contrP, add_smul]
  · simp [contrP]

@[simp]
lemma contrP_update_smul {n : ℕ} [inst : DecidableEq (Fin (n + 1 +1))] {c : Fin (n + 1 + 1) → C}
    (i j m : Fin (n + 1 + 1)) (hij : i ≠ j ∧ S.τ (c i) = c j)
    (p : Pure S c) (r : k) (x : S.FD.obj (Discrete.mk (c m))) :
    contrP i j hij (p.update m (r • x)) =
    r • contrP i j hij (p.update m x) := by
  rcases eq_or_exists_dropPairEmb i j hij.1 m with rfl | rfl | ⟨m', rfl⟩
  · simp [contrP, smul_smul]
  · simp [contrP, smul_smul]
  · simp [contrP, smul_smul, mul_comm]

@[simp]
lemma contrP_equivariant {n : ℕ} {c : Fin (n + 1 + 1) → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ S.τ (c i) = c j) (p : Pure S c) (g : G) :
    contrP i j hij (g • p) = g • contrP i j hij p := by
  simp [contrP, contrPCoeff_invariant, dropPair_equivariant, actionT_pure]

lemma contrP_symm {n : ℕ} {c : Fin (n + 1 + 1) → C}
    {i j : Fin (n + 1 + 1)} {hij : i ≠ j ∧ S.τ (c i) = c j} {p : Pure S c} :
    contrP i j hij p = permT id (by simp)
    (contrP j i ⟨hij.1.symm, by simp [← hij.2]⟩ p) := by
  rw [contrP, contrPCoeff_symm, dropPair_symm]
  simp [contrP, permT_pure]

/-!

## contrP as a multilinear map

-/

/-- The multi-linear map formed by contracting a pair of indices of pure tensors. -/
noncomputable def contrPMultilinear {n : ℕ} {c : Fin (n + 1 + 1) → C}
    (i j : Fin (n + 1 + 1)) (hij : i ≠ j ∧ S.τ (c i) = c j) :
    MultilinearMap k (fun i => S.FD.obj (Discrete.mk (c i)))
      (S.Tensor (c ∘ dropPairEmb i j))where
  toFun p := contrP i j hij p
  map_update_add' p m x y := by
    change (update p m (x + y)).contrP i j hij = _
    simp only [contrP_update_add]
    rfl
  map_update_smul' p k r y := by
    change (update p k (r • y)).contrP i j hij = _
    rw [Pure.contrP_update_smul]
    rfl

end Pure

end Tensor

end TensorSpecies
