/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.QFT.PerturbationTheory.WickContraction.Singleton
/-!

# Join of contractions

-/

@[expose] public section

open FieldSpecification
variable {𝓕 : FieldSpecification}

namespace WickContraction
variable {n : ℕ} (c : WickContraction n)
open PhysLean.List
open WickAlgebra

/-- Given a list `φs` of `𝓕.FieldOp`, a Wick contraction `φsΛ` of `φs` and a Wick contraction
  `φsucΛ` of `[φsΛ]ᵘᶜ`, `join φsΛ φsucΛ` is defined as the Wick contraction of `φs` consisting of
  the contractions in `φsΛ` and those in `φsucΛ`.

  As an example, for `φs = [φ1, φ2, φ3, φ4]`,
  `φsΛ = {{0, 1}}` corresponding to the contraction of `φ1` and `φ2` in `φs` and
  `φsucΛ = {{0, 1}}`
  corresponding to the contraction of `φ3` and `φ4` in `[φsΛ]ᵘᶜ = [φ3, φ4]`, then
  `join φsΛ φsucΛ` is the contraction `{{0, 1}, {2, 3}}` of `φs`. -/
def join {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) : WickContraction φs.length :=
  ⟨φsΛ.1 ∪ φsucΛ.1.map (Finset.mapEmbedding uncontractedListEmd).toEmbedding, by
    intro a ha
    simp only [Finset.le_eq_subset, Finset.mem_union, Finset.mem_map,
      RelEmbedding.coe_toEmbedding] at ha
    rcases ha with ha | ha
    · exact φsΛ.2.1 a ha
    · obtain ⟨a, ha, rfl⟩ := ha
      rw [Finset.mapEmbedding_apply]
      simp only [Finset.card_map]
      exact φsucΛ.2.1 a ha, by
    intro a ha b hb
    simp only [Finset.le_eq_subset, Finset.mem_union, Finset.mem_map,
      RelEmbedding.coe_toEmbedding] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact φsΛ.2.2 a ha b hb
    · obtain ⟨b, hb, rfl⟩ := hb
      right
      symm
      rw [Finset.mapEmbedding_apply]
      apply uncontractedListEmd_finset_disjoint_left
      exact ha
    · obtain ⟨a, ha, rfl⟩ := ha
      right
      rw [Finset.mapEmbedding_apply]
      apply uncontractedListEmd_finset_disjoint_left
      exact hb
    · obtain ⟨a, ha, rfl⟩ := ha
      obtain ⟨b, hb, rfl⟩ := hb
      simp only [EmbeddingLike.apply_eq_iff_eq]
      rw [Finset.mapEmbedding_apply, Finset.mapEmbedding_apply]
      rw [Finset.disjoint_map]
      exact φsucΛ.2.2 a ha b hb⟩

lemma join_congr {φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} {φsΛ' : WickContraction φs.length}
    (h1 : φsΛ = φsΛ') :
    join φsΛ φsucΛ = join φsΛ' (congr (by simp [h1]) φsucΛ) := by
  subst h1
  rfl

/-- Given a contracting pair within `φsΛ` the corresponding contracting pair within
  `(join φsΛ φsucΛ)`. -/
def joinLiftLeft {φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} : φsΛ.1 → (join φsΛ φsucΛ).1 :=
  fun a => ⟨a, by simp [join]⟩

lemma jointLiftLeft_injective {φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} :
    Function.Injective (@joinLiftLeft _ _ φsΛ φsucΛ) := by
  intro a b h
  simp only [joinLiftLeft] at h
  rw [Subtype.mk_eq_mk] at h
  refine Subtype.ext h

/-- Given a contracting pair within `φsucΛ` the corresponding contracting pair within
  `(join φsΛ φsucΛ)`. -/
def joinLiftRight {φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} : φsucΛ.1 → (join φsΛ φsucΛ).1 :=
  fun a => ⟨a.1.map uncontractedListEmd, by
    simp only [join, Finset.le_eq_subset, Finset.mem_union, Finset.mem_map,
      RelEmbedding.coe_toEmbedding]
    right
    use a.1
    simp only [Finset.coe_mem, true_and]
    rfl⟩

lemma joinLiftRight_injective {φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} :
    Function.Injective (@joinLiftRight _ _ φsΛ φsucΛ) := by
  intro a b h
  simp only [joinLiftRight] at h
  rw [Subtype.mk_eq_mk] at h
  simp only [Finset.map_inj] at h
  refine Subtype.ext h

lemma jointLiftLeft_disjoint_joinLiftRight {φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} (a : φsΛ.1) (b : φsucΛ.1) :
    Disjoint (@joinLiftLeft _ _ _ φsucΛ a).1 (joinLiftRight b).1 := by
  simp only [joinLiftLeft, joinLiftRight]
  symm
  apply uncontractedListEmd_finset_disjoint_left
  exact a.2

lemma jointLiftLeft_ne_joinLiftRight {φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} (a : φsΛ.1) (b : φsucΛ.1) :
    joinLiftLeft a ≠ joinLiftRight b := by
  by_contra hn
  have h1 := jointLiftLeft_disjoint_joinLiftRight a b
  rw [hn] at h1
  simp only [disjoint_self, Finset.bot_eq_empty] at h1
  have hj := (join φsΛ φsucΛ).2.1 (joinLiftRight b).1 (joinLiftRight b).2
  rw [h1] at hj
  simp at hj

/-- The map from contracted pairs of `φsΛ` and `φsucΛ` to contracted pairs in
  `(join φsΛ φsucΛ)`. -/
def joinLift {φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} : φsΛ.1 ⊕ φsucΛ.1 → (join φsΛ φsucΛ).1 := fun a =>
  match a with
  | Sum.inl a => joinLiftLeft a
  | Sum.inr a => joinLiftRight a

lemma joinLift_injective {φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} : Function.Injective (@joinLift _ _ φsΛ φsucΛ) := by
  intro a b h
  match a, b with
  | Sum.inl a, Sum.inl b =>
    simp only [Sum.inl.injEq]
    exact jointLiftLeft_injective h
  | Sum.inr a, Sum.inr b =>
    simp only [Sum.inr.injEq]
    exact joinLiftRight_injective h
  | Sum.inl a, Sum.inr b =>
    simp only [joinLift] at h
    have h1 := jointLiftLeft_ne_joinLiftRight a b
    simp_all
  | Sum.inr a, Sum.inl b =>
    simp only [joinLift] at h
    have h1 := jointLiftLeft_ne_joinLiftRight b a
    simp_all

lemma joinLift_surjective {φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} : Function.Surjective (@joinLift _ _ φsΛ φsucΛ) := by
  intro a
  have ha2 := a.2
  simp only [join, Finset.le_eq_subset, Finset.mem_union, Finset.mem_map,
    RelEmbedding.coe_toEmbedding] at ha2
  rcases ha2 with ha2 | ⟨a2, ha3⟩
  · use Sum.inl ⟨a, ha2⟩
    simp [joinLift, joinLiftLeft]
  · rw [Finset.mapEmbedding_apply] at ha3
    use Sum.inr ⟨a2, ha3.1⟩
    simp only [joinLift, joinLiftRight]
    refine Subtype.ext ?_
    exact ha3.2

lemma joinLift_bijective {φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} : Function.Bijective (@joinLift _ _ φsΛ φsucΛ) := by
  apply And.intro
  · exact joinLift_injective
  · exact joinLift_surjective

lemma prod_join {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (f : (join φsΛ φsucΛ).1 → M) [CommMonoid M]:
      ∏ (a : (join φsΛ φsucΛ).1), f a = (∏ (a : φsΛ.1), f (joinLiftLeft a)) *
      ∏ (a : φsucΛ.1), f (joinLiftRight a) := by
  let e1 := Equiv.ofBijective (@joinLift _ _ φsΛ φsucΛ) joinLift_bijective
  rw [← e1.prod_comp]
  simp only [Fintype.prod_sum_type, Finset.univ_eq_attach]
  rfl

lemma joinLiftLeft_or_joinLiftRight_of_mem_join {φs : List 𝓕.FieldOp}
    (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) {a : Finset (Fin φs.length)}
    (ha : a ∈ (join φsΛ φsucΛ).1) :
    (∃ b, a = (joinLiftLeft (φsucΛ := φsucΛ) b).1) ∨
    (∃ b, a = (joinLiftRight (φsucΛ := φsucΛ) b).1) := by
  simp only [join, Finset.le_eq_subset, Finset.mem_union, Finset.mem_map,
    RelEmbedding.coe_toEmbedding] at ha
  rcases ha with ha | ⟨a, ha, rfl⟩
  · left
    use ⟨a, ha⟩
    rfl
  · right
    use ⟨a, ha⟩
    rfl

@[simp]
lemma join_fstFieldOfContract_joinLiftRight {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (a : φsucΛ.1) :
    (join φsΛ φsucΛ).fstFieldOfContract (joinLiftRight a) =
    uncontractedListEmd (φsucΛ.fstFieldOfContract a) := by
  apply eq_fstFieldOfContract_of_mem _ _ _ (uncontractedListEmd (φsucΛ.sndFieldOfContract a))
  · simp [joinLiftRight]
  · simp [joinLiftRight]
  · apply uncontractedListEmd_strictMono
    exact fstFieldOfContract_lt_sndFieldOfContract φsucΛ a

@[simp]
lemma join_sndFieldOfContract_joinLiftRight {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (a : φsucΛ.1) :
    (join φsΛ φsucΛ).sndFieldOfContract (joinLiftRight a) =
    uncontractedListEmd (φsucΛ.sndFieldOfContract a) := by
  apply eq_sndFieldOfContract_of_mem _ _ (uncontractedListEmd (φsucΛ.fstFieldOfContract a))
  · simp [joinLiftRight]
  · simp [joinLiftRight]
  · apply uncontractedListEmd_strictMono
    exact fstFieldOfContract_lt_sndFieldOfContract φsucΛ a

@[simp]
lemma join_fstFieldOfContract_joinLiftLeft {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (a : φsΛ.1) :
    (join φsΛ φsucΛ).fstFieldOfContract (joinLiftLeft a) =
    (φsΛ.fstFieldOfContract a) := by
  apply eq_fstFieldOfContract_of_mem _ _ _ (φsΛ.sndFieldOfContract a)
  · simp [joinLiftLeft]
  · simp [joinLiftLeft]
  · exact fstFieldOfContract_lt_sndFieldOfContract φsΛ a

@[simp]
lemma join_sndFieldOfContract_joinLift {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (a : φsΛ.1) :
    (join φsΛ φsucΛ).sndFieldOfContract (joinLiftLeft a) =
    (φsΛ.sndFieldOfContract a) := by
  apply eq_sndFieldOfContract_of_mem _ _ (φsΛ.fstFieldOfContract a) (φsΛ.sndFieldOfContract a)
  · simp [joinLiftLeft]
  · simp [joinLiftLeft]
  · exact fstFieldOfContract_lt_sndFieldOfContract φsΛ a

lemma mem_join_right_iff {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (a : Finset (Fin [φsΛ]ᵘᶜ.length)) :
    a ∈ φsucΛ.1 ↔ a.map uncontractedListEmd ∈ (join φsΛ φsucΛ).1 := by
  simp only [join, Finset.le_eq_subset, Finset.mem_union, Finset.mem_map,
    RelEmbedding.coe_toEmbedding]
  have h1' : ¬ Finset.map uncontractedListEmd a ∈ φsΛ.1 :=
    uncontractedListEmd_finset_not_mem a
  simp only [h1', false_or]
  apply Iff.intro
  · intro h
    use a
    simp only [h, true_and]
    rw [Finset.mapEmbedding_apply]
  · intro h
    obtain ⟨a, ha, h2⟩ := h
    rw [Finset.mapEmbedding_apply] at h2
    simp only [Finset.map_inj] at h2
    subst h2
    exact ha

lemma join_card {φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} :
    (join φsΛ φsucΛ).1.card = φsΛ.1.card + φsucΛ.1.card := by
  simp only [join, Finset.le_eq_subset]
  rw [Finset.card_union_of_disjoint]
  simp only [Finset.card_map]
  rw [@Finset.disjoint_left]
  intro a ha
  simp only [Finset.mem_map, RelEmbedding.coe_toEmbedding, not_exists, not_and]
  intro x hx
  by_contra hn
  have hdis : Disjoint (Finset.map uncontractedListEmd x) a := by
    exact uncontractedListEmd_finset_disjoint_left x a ha
  rw [Finset.mapEmbedding_apply] at hn
  rw [hn] at hdis
  simp only [disjoint_self, Finset.bot_eq_empty] at hdis
  have hcard := φsΛ.2.1 a ha
  simp_all

@[simp]
lemma empty_join {φs : List 𝓕.FieldOp} (φsΛ : WickContraction [empty (n := φs.length)]ᵘᶜ.length) :
    join empty φsΛ = congr (by simp) φsΛ := by
  apply Subtype.ext
  simp only [join, Finset.le_eq_subset, uncontractedListEmd_empty]
  ext a
  conv_lhs =>
    left
    left
    rw [empty]
  simp only [Finset.empty_union, Finset.mem_map, RelEmbedding.coe_toEmbedding]
  rw [mem_congr_iff]
  apply Iff.intro
  · intro h
    obtain ⟨a, ha, rfl⟩ := h
    rw [Finset.mapEmbedding_apply]
    rw [Finset.map_map]
    apply Set.mem_of_eq_of_mem _ ha
    trans Finset.map (Equiv.refl _).toEmbedding a
    rfl
    simp
  · intro h
    use Finset.map (finCongr (by simp)).toEmbedding a
    simp only [h, true_and]
    trans Finset.map (Equiv.refl _).toEmbedding a
    rw [Finset.mapEmbedding_apply, Finset.map_map]
    rfl
    simp

@[simp]
lemma join_empty {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length) :
    join φsΛ empty = φsΛ := by
  apply Subtype.ext
  ext a
  simp [join, empty]

lemma join_timeContract {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) :
    (join φsΛ φsucΛ).timeContract = φsΛ.timeContract * φsucΛ.timeContract := by
  simp only [timeContract, List.get_eq_getElem]
  rw [prod_join]
  congr 1
  congr
  funext a
  simp

lemma join_staticContract {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) :
    (join φsΛ φsucΛ).staticContract = φsΛ.staticContract * φsucΛ.staticContract := by
  simp only [staticContract, List.get_eq_getElem]
  rw [prod_join]
  congr 1
  congr
  funext a
  simp

lemma mem_join_uncontracted_of_mem_right_uncontracted {φs : List 𝓕.FieldOp}
    (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (i : Fin [φsΛ]ᵘᶜ.length)
    (ha : i ∈ φsucΛ.uncontracted) :
    uncontractedListEmd i ∈ (join φsΛ φsucΛ).uncontracted := by
  rw [mem_uncontracted_iff_not_contracted]
  intro p hp
  simp only [join, Finset.le_eq_subset, Finset.mem_union, Finset.mem_map,
    RelEmbedding.coe_toEmbedding] at hp
  rcases hp with hp | hp
  · have hi : uncontractedListEmd i ∈ φsΛ.uncontracted := by
      exact uncontractedListEmd_mem_uncontracted i
    rw [mem_uncontracted_iff_not_contracted] at hi
    exact hi p hp
  · obtain ⟨p, hp, rfl⟩ := hp
    rw [Finset.mapEmbedding_apply]
    simp only [Finset.mem_map']
    rw [mem_uncontracted_iff_not_contracted] at ha
    exact ha p hp

lemma exists_mem_left_uncontracted_of_mem_join_uncontracted {φs : List 𝓕.FieldOp}
    (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (i : Fin φs.length)
    (ha : i ∈ (join φsΛ φsucΛ).uncontracted) :
    i ∈ φsΛ.uncontracted := by
  rw [@mem_uncontracted_iff_not_contracted]
  rw [@mem_uncontracted_iff_not_contracted] at ha
  simp only [join, Finset.le_eq_subset, Finset.mem_union, Finset.mem_map,
    RelEmbedding.coe_toEmbedding] at ha
  intro p hp
  simp_all

lemma exists_mem_right_uncontracted_of_mem_join_uncontracted {φs : List 𝓕.FieldOp}
    (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (i : Fin φs.length)
    (hi : i ∈ (join φsΛ φsucΛ).uncontracted) :
    ∃ a, uncontractedListEmd a = i ∧ a ∈ φsucΛ.uncontracted := by
  have hi' := exists_mem_left_uncontracted_of_mem_join_uncontracted _ _ i hi
  obtain ⟨j, rfl⟩ := uncontractedListEmd_surjective_mem_uncontracted i hi'
  use j
  simp only [true_and]
  rw [mem_uncontracted_iff_not_contracted] at hi
  rw [mem_uncontracted_iff_not_contracted]
  intro p hp
  have hip := hi (p.map uncontractedListEmd) (by
    simp only [join, Finset.le_eq_subset, Finset.mem_union, Finset.mem_map,
      RelEmbedding.coe_toEmbedding]
    right
    use p
    simp only [hp, true_and]
    rw [Finset.mapEmbedding_apply])
  simpa using hip

lemma join_uncontractedList {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) :
    (join φsΛ φsucΛ).uncontractedList = List.map uncontractedListEmd φsucΛ.uncontractedList := by
  rw [uncontractedList_eq_sort]
  rw [uncontractedList_eq_sort]
  rw [fin_finset_sort_map_monotone]
  congr
  ext a
  simp only [Finset.mem_map]
  apply Iff.intro
  · intro h
    obtain ⟨a, rfl, ha⟩ := exists_mem_right_uncontracted_of_mem_join_uncontracted _ _ a h
    use a, ha
  · intro h
    obtain ⟨a, ha, rfl⟩ := h
    exact mem_join_uncontracted_of_mem_right_uncontracted φsΛ φsucΛ a ha
  · intro a b h
    exact uncontractedListEmd_strictMono h

lemma join_uncontractedList_get {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) :
    ((join φsΛ φsucΛ).uncontractedList).get =
    φsΛ.uncontractedListEmd ∘ (φsucΛ.uncontractedList).get ∘
        (Fin.cast (by rw [join_uncontractedList]; simp)) := by
  have h1 {n : ℕ} (l1 l2 : List (Fin n)) (h : l1 = l2) :
      l1.get = l2.get ∘ Fin.cast (by rw [h]) := by
    subst h
    rfl
  conv_lhs => rw [h1 _ _ (join_uncontractedList φsΛ φsucΛ)]
  ext i
  simp

lemma join_uncontractedListGet {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) :
    (join φsΛ φsucΛ).uncontractedListGet = φsucΛ.uncontractedListGet := by
  simp only [uncontractedListGet, join_uncontractedList, List.map_map, List.map_inj_left,
    Function.comp_apply, List.get_eq_getElem, List.getElem_map]
  intro a ha
  simp only [uncontractedListEmd, uncontractedIndexEquiv, List.get_eq_getElem,
    Equiv.trans_toEmbedding, Function.Embedding.trans_apply, Equiv.coe_toEmbedding, Equiv.coe_fn_mk,
    Function.Embedding.coe_subtype]
  rfl

lemma join_uncontractedListEmb {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) :
    (join φsΛ φsucΛ).uncontractedListEmd =
    ((finCongr (congrArg List.length (join_uncontractedListGet _ _))).toEmbedding.trans
      φsucΛ.uncontractedListEmd).trans φsΛ.uncontractedListEmd := by
  refine Function.Embedding.ext_iff.mpr (congrFun ?_)
  change uncontractedListEmd.toFun = _
  rw [uncontractedListEmd_toFun_eq_get]
  rw [join_uncontractedList_get]
  rfl

lemma join_assoc {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (φsucΛ' : WickContraction [φsΛ.join φsucΛ]ᵘᶜ.length) :
    join (join φsΛ φsucΛ) (φsucΛ') = join φsΛ (join φsucΛ (congr
      (congrArg List.length (join_uncontractedListGet _ _)) φsucΛ')) := by
  apply Subtype.ext
  ext a
  by_cases ha : a ∈ φsΛ.1
  · simp [ha, join]
  simp only [join, Finset.le_eq_subset, Finset.union_assoc, Finset.mem_union, ha, Finset.mem_map,
    RelEmbedding.coe_toEmbedding, false_or]
  apply Iff.intro
  · intro h
    rcases h with h | h
    · obtain ⟨a, ha', rfl⟩ := h
      use a
      simp [ha']
    · obtain ⟨a, ha', rfl⟩ := h
      let a' := congrLift (congrArg List.length (join_uncontractedListGet _ _)) ⟨a, ha'⟩
      let a'' := joinLiftRight a'
      use a''
      apply And.intro
      · right
        use a'
        apply And.intro
        · exact a'.2
        · simp only [joinLiftRight, a'']
          rfl
      · simp only [a'']
        rw [Finset.mapEmbedding_apply, Finset.mapEmbedding_apply]
        simp only [a', joinLiftRight, congrLift]
        rw [join_uncontractedListEmb]
        simp [Finset.map_map]
  · intro h
    obtain ⟨a, ha', rfl⟩ := h
    rcases ha' with ha' | ha'
    · left
      use a
    · obtain ⟨a, ha', rfl⟩ := ha'
      right
      let a' := congrLiftInv _ ⟨a, ha'⟩
      use a'
      simp only [Finset.coe_mem, true_and]
      simp only [a']
      rw [Finset.mapEmbedding_apply]
      rw [join_uncontractedListEmb]
      simp only [congrLiftInv, ← Finset.map_map]
      congr
      rw [Finset.map_map]
      change Finset.map (Equiv.refl _).toEmbedding a = _
      simp only [Equiv.refl_toEmbedding, Finset.map_refl]

lemma join_getDual?_apply_uncontractedListEmb_eq_none_iff {φs : List 𝓕.FieldOp}
    (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (i : Fin [φsΛ]ᵘᶜ.length) :
    (join φsΛ φsucΛ).getDual? (uncontractedListEmd i) = none
    ↔ φsucΛ.getDual? i = none := by
  rw [getDual?_eq_none_iff_mem_uncontracted, getDual?_eq_none_iff_mem_uncontracted]
  apply Iff.intro
  · intro h
    obtain ⟨a, ha', ha⟩ := exists_mem_right_uncontracted_of_mem_join_uncontracted _ _
      (uncontractedListEmd i) h
    simp only [EmbeddingLike.apply_eq_iff_eq] at ha'
    subst ha'
    exact ha
  · intro h
    exact mem_join_uncontracted_of_mem_right_uncontracted φsΛ φsucΛ i h

lemma join_getDual?_apply_uncontractedListEmb_isSome_iff {φs : List 𝓕.FieldOp}
    (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (i : Fin [φsΛ]ᵘᶜ.length) :
    ((join φsΛ φsucΛ).getDual? (uncontractedListEmd i)).isSome
    ↔ (φsucΛ.getDual? i).isSome := by
  rw [← Decidable.not_iff_not]
  simp [join_getDual?_apply_uncontractedListEmb_eq_none_iff]

lemma join_getDual?_apply_uncontractedListEmb_some {φs : List 𝓕.FieldOp}
    (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (i : Fin [φsΛ]ᵘᶜ.length)
    (hi :((join φsΛ φsucΛ).getDual? (uncontractedListEmd i)).isSome) :
    ((join φsΛ φsucΛ).getDual? (uncontractedListEmd i)) =
    some (uncontractedListEmd ((φsucΛ.getDual? i).get (by
    simpa [join_getDual?_apply_uncontractedListEmb_isSome_iff]using hi))) := by
  rw [getDual?_eq_some_iff_mem]
  simp only [join, Finset.le_eq_subset, Finset.mem_union, Finset.mem_map,
    RelEmbedding.coe_toEmbedding]
  right
  use {i, (φsucΛ.getDual? i).get (by
    simpa [join_getDual?_apply_uncontractedListEmb_isSome_iff] using hi)}
  simp only [self_getDual?_get_mem, true_and]
  rw [Finset.mapEmbedding_apply]
  simp

@[simp]
lemma join_getDual?_apply_uncontractedListEmb {φs : List 𝓕.FieldOp}
    (φsΛ : WickContraction φs.length) (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length)
    (i : Fin [φsΛ]ᵘᶜ.length) : ((join φsΛ φsucΛ).getDual? (uncontractedListEmd i)) =
    Option.map uncontractedListEmd (φsucΛ.getDual? i) := by
  by_cases h : (φsucΛ.getDual? i).isSome
  · rw [join_getDual?_apply_uncontractedListEmb_some]
    have h1 : (φsucΛ.getDual? i) = (φsucΛ.getDual? i).get (by simpa using h) :=
      Eq.symm (Option.some_get h)
    conv_rhs => rw [h1]
    simp only [Option.map_some]
    exact (join_getDual?_apply_uncontractedListEmb_isSome_iff φsΛ φsucΛ i).mpr h
  · simp only [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h
    rw [h]
    simp only [Option.map_none, join_getDual?_apply_uncontractedListEmb_eq_none_iff]
    exact h

/-!

## Subcontractions and quotient contractions

-/

section

variable {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length)

lemma join_sub_quot (S : Finset (Finset (Fin φs.length))) (ha : S ⊆ φsΛ.1) :
    join (subContraction S ha) (quotContraction S ha) = φsΛ := by
  apply Subtype.ext
  ext a
  simp only [join, Finset.le_eq_subset, Finset.mem_union, Finset.mem_map,
    RelEmbedding.coe_toEmbedding]
  apply Iff.intro
  · intro h
    rcases h with h | h
    · exact mem_of_mem_subContraction h
    · obtain ⟨a, ha, rfl⟩ := h
      apply mem_of_mem_quotContraction ha
  · intro h
    have h1 := mem_subContraction_or_quotContraction (S := S) (a := a) (hs := ha) h
    rcases h1 with h1 | h1
    · simp [h1]
    · right
      obtain ⟨a, rfl, ha⟩ := h1
      use a
      simp only [ha, true_and]
      rw [Finset.mapEmbedding_apply]

lemma subContraction_card_plus_quotContraction_card_eq (S : Finset (Finset (Fin φs.length)))
    (ha : S ⊆ φsΛ.1) :
    (subContraction S ha).1.card + (quotContraction S ha).1.card = φsΛ.1.card := by
  rw [← join_card]
  simp [join_sub_quot]

end
open FieldStatistic

@[simp]
lemma join_singleton_getDual?_left {φs : List 𝓕.FieldOp}
    {i j : Fin φs.length} (h : i < j)
    (φsucΛ : WickContraction [singleton h]ᵘᶜ.length) :
    (join (singleton h) φsucΛ).getDual? i = some j := by
  rw [@getDual?_eq_some_iff_mem]
  simp [singleton, join]

@[simp]
lemma join_singleton_getDual?_right {φs : List 𝓕.FieldOp}
    {i j : Fin φs.length} (h : i < j)
    (φsucΛ : WickContraction [singleton h]ᵘᶜ.length) :
    (join (singleton h) φsucΛ).getDual? j = some i := by
  rw [@getDual?_eq_some_iff_mem]
  simp only [join, singleton, Finset.le_eq_subset, Finset.mem_union, Finset.mem_singleton,
    Finset.mem_map, RelEmbedding.coe_toEmbedding]
  left
  exact Finset.pair_comm j i

lemma exists_contraction_pair_of_card_ge_zero {φs : List 𝓕.FieldOp}
    (φsΛ : WickContraction φs.length) (h : 0 < φsΛ.1.card) :
    ∃ a, a ∈ φsΛ.1 := by
  simpa using h

set_option maxHeartbeats 400000 in
lemma exists_join_singleton_of_card_ge_zero {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length)
    (h : 0 < φsΛ.1.card) (hc : φsΛ.GradingCompliant) :
    ∃ (i j : Fin φs.length) (h : i < j) (φsucΛ : WickContraction [singleton h]ᵘᶜ.length),
    φsΛ = join (singleton h) φsucΛ ∧ (𝓕 |>ₛ φs[i]) = (𝓕 |>ₛ φs[j])
    ∧ φsucΛ.GradingCompliant ∧ φsucΛ.1.card + 1 = φsΛ.1.card := by
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
  · apply And.intro (hc ⟨a, ha⟩)
    apply And.intro
    · simp only [φsucΛ]
      rw [gradingCompliant_congr (φs' := [(φsΛ.subContraction {a} (by simpa using ha))]ᵘᶜ)]
      simp only [congr_trans_apply, congr_refl]
      exact quotContraction_gradingCompliant hc
      rw [← subContraction_singleton_eq_singleton]
    · simp only [card_congr, φsucΛ]
      have h1 := subContraction_card_plus_quotContraction_card_eq _ {a} (by simpa using ha)
      simp only [subContraction, Finset.card_singleton] at h1
      omega

lemma join_not_gradingCompliant_of_left_not_gradingCompliant {φs : List 𝓕.FieldOp}
    (φsΛ : WickContraction φs.length) (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length)
    (hc : ¬ φsΛ.GradingCompliant) : ¬ (join φsΛ φsucΛ).GradingCompliant := by
  simp_all only [GradingCompliant, Subtype.forall, not_forall]
  obtain ⟨a, ha, ha2⟩ := hc
  use (joinLiftLeft (φsucΛ := φsucΛ) ⟨a, ha⟩).1
  use (joinLiftLeft (φsucΛ := φsucΛ) ⟨a, ha⟩).2
  simp only [Subtype.coe_eta, join_fstFieldOfContract_joinLiftLeft,
    join_sndFieldOfContract_joinLift]
  exact ha2

end WickContraction
