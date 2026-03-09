/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.QFT.PerturbationTheory.WickContraction.UncontractedList
/-!

# Sub contractions

-/

@[expose] public section

open FieldSpecification
variable {𝓕 : FieldSpecification}

namespace WickContraction
variable {n : ℕ} {φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length}
open PhysLean.List

/-- Given a Wick contraction `φsΛ`, and a subset of `φsΛ.1`, the Wick contraction
  consisting of contracted pairs within that subset. -/
def subContraction (S : Finset (Finset (Fin φs.length))) (ha : S ⊆ φsΛ.1) :
    WickContraction φs.length :=
  ⟨S, by
    intro i hi
    exact φsΛ.2.1 i (ha hi),
    by
    intro i hi j hj
    exact φsΛ.2.2 i (ha hi) j (ha hj)⟩

lemma mem_of_mem_subContraction {S : Finset (Finset (Fin φs.length))} {hs : S ⊆ φsΛ.1}
    {a : Finset (Fin φs.length)} (ha : a ∈ (φsΛ.subContraction S hs).1) : a ∈ φsΛ.1 := by
  exact hs ha

/-- Given a Wick contraction `φsΛ`, and a subset `S` of `φsΛ.1`, the Wick contraction
  on the uncontracted list `[φsΛ.subContraction S ha]ᵘᶜ`
  consisting of the remaining contracted pairs of `φsΛ` not in `S`. -/
def quotContraction (S : Finset (Finset (Fin φs.length))) (ha : S ⊆ φsΛ.1) :
    WickContraction [φsΛ.subContraction S ha]ᵘᶜ.length :=
  ⟨Finset.filter (fun a => Finset.map uncontractedListEmd a ∈ φsΛ.1) Finset.univ,
  by
    intro a ha'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha'
    simpa using φsΛ.2.1 (Finset.map uncontractedListEmd a) ha', by
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  by_cases hab : a = b
  · simp [hab]
  · simp only [hab, false_or]
    have hx := φsΛ.2.2 (Finset.map uncontractedListEmd a) ha (Finset.map uncontractedListEmd b) hb
    simp_all⟩

lemma mem_of_mem_quotContraction {S : Finset (Finset (Fin φs.length))} {hs : S ⊆ φsΛ.1}
    {a : Finset (Fin [φsΛ.subContraction S hs]ᵘᶜ.length)}
    (ha : a ∈ (quotContraction S hs).1) : Finset.map uncontractedListEmd a ∈ φsΛ.1 := by
  simp only [quotContraction, Finset.mem_filter, Finset.mem_univ, true_and] at ha
  exact ha

lemma mem_subContraction_or_quotContraction {S : Finset (Finset (Fin φs.length))} {hs : S ⊆ φsΛ.1}
    {a : Finset (Fin φs.length)} (ha : a ∈ φsΛ.1) :
    a ∈ (φsΛ.subContraction S hs).1 ∨
    ∃ a', Finset.map uncontractedListEmd a' = a ∧ a' ∈ (quotContraction S hs).1 := by
  by_cases h1 : a ∈ (φsΛ.subContraction S hs).1
  · simp [h1]
  simp only [h1, false_or]
  simp only [subContraction] at h1
  have h2 := φsΛ.2.1 a ha
  rw [@Finset.card_eq_two] at h2
  obtain ⟨i, j, hij, rfl⟩ := h2
  have hi : i ∈ (φsΛ.subContraction S hs).uncontracted := by
    rw [mem_uncontracted_iff_not_contracted]
    intro p hp
    have hp' : p ∈ φsΛ.1 := hs hp
    have hp2 := φsΛ.2.2 p hp' {i, j} ha
    simp only [subContraction] at hp
    rcases hp2 with hp2 | hp2
    · simp_all
    simp only [Finset.disjoint_insert_right, Finset.disjoint_singleton_right] at hp2
    exact hp2.1
  have hj : j ∈ (φsΛ.subContraction S hs).uncontracted := by
    rw [mem_uncontracted_iff_not_contracted]
    intro p hp
    have hp' : p ∈ φsΛ.1 := hs hp
    have hp2 := φsΛ.2.2 p hp' {i, j} ha
    simp only [subContraction] at hp
    rcases hp2 with hp2 | hp2
    · simp_all
    simp only [Finset.disjoint_insert_right, Finset.disjoint_singleton_right] at hp2
    exact hp2.2
  obtain ⟨i, rfl⟩ := uncontractedListEmd_surjective_mem_uncontracted i hi
  obtain ⟨j, rfl⟩ := uncontractedListEmd_surjective_mem_uncontracted j hj
  use {i, j}
  simp only [Finset.map_insert, Finset.map_singleton, quotContraction, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact ha

@[simp]
lemma subContraction_uncontractedList_get {S : Finset (Finset (Fin φs.length))} {hs : S ⊆ φsΛ.1}
    {a : Fin [subContraction S hs]ᵘᶜ.length} :
    [subContraction S hs]ᵘᶜ[a] = φs[uncontractedListEmd a] := by
  erw [← getElem_uncontractedListEmd]
  rfl

@[simp]
lemma subContraction_fstFieldOfContract {S : Finset (Finset (Fin φs.length))} {hs : S ⊆ φsΛ.1}
    (a : (subContraction S hs).1) :
    (subContraction S hs).fstFieldOfContract a =
    φsΛ.fstFieldOfContract ⟨a.1, mem_of_mem_subContraction a.2⟩:= by
  apply eq_fstFieldOfContract_of_mem _ _ _
    (φsΛ.sndFieldOfContract ⟨a.1, mem_of_mem_subContraction a.2⟩)
  · have ha := finset_eq_fstFieldOfContract_sndFieldOfContract _
      ⟨a.1, mem_of_mem_subContraction a.2⟩
    simp only at ha
    conv_lhs =>
      rw [ha]
    simp
  · have ha := finset_eq_fstFieldOfContract_sndFieldOfContract _
      ⟨a.1, mem_of_mem_subContraction a.2⟩
    simp only at ha
    conv_lhs =>
      rw [ha]
    simp
  · exact fstFieldOfContract_lt_sndFieldOfContract φsΛ ⟨↑a, mem_of_mem_subContraction a.property⟩

@[simp]
lemma subContraction_sndFieldOfContract {S : Finset (Finset (Fin φs.length))} {hs : S ⊆ φsΛ.1}
    (a : (subContraction S hs).1) :
    (subContraction S hs).sndFieldOfContract a =
    φsΛ.sndFieldOfContract ⟨a.1, mem_of_mem_subContraction a.2⟩:= by
  apply eq_sndFieldOfContract_of_mem _ _
    (φsΛ.fstFieldOfContract ⟨a.1, mem_of_mem_subContraction a.2⟩)
  · have ha := finset_eq_fstFieldOfContract_sndFieldOfContract _
      ⟨a.1, mem_of_mem_subContraction a.2⟩
    simp only at ha
    conv_lhs =>
      rw [ha]
    simp
  · have ha := finset_eq_fstFieldOfContract_sndFieldOfContract _
      ⟨a.1, mem_of_mem_subContraction a.2⟩
    simp only at ha
    conv_lhs =>
      rw [ha]
    simp
  · exact fstFieldOfContract_lt_sndFieldOfContract φsΛ ⟨↑a, mem_of_mem_subContraction a.property⟩

@[simp]
lemma quotContraction_fstFieldOfContract_uncontractedListEmd {S : Finset (Finset (Fin φs.length))}
    {hs : S ⊆ φsΛ.1} (a : (quotContraction S hs).1) :
    uncontractedListEmd ((quotContraction S hs).fstFieldOfContract a) =
    (φsΛ.fstFieldOfContract
    ⟨Finset.map uncontractedListEmd a.1, mem_of_mem_quotContraction a.2⟩) := by
  symm
  apply eq_fstFieldOfContract_of_mem _ _ _
    (uncontractedListEmd ((quotContraction S hs).sndFieldOfContract a))
  · simp only [Finset.mem_map', fstFieldOfContract_mem]
  · simp
  · apply uncontractedListEmd_strictMono
    exact fstFieldOfContract_lt_sndFieldOfContract (quotContraction S hs) a

@[simp]
lemma quotContraction_sndFieldOfContract_uncontractedListEmd {S : Finset (Finset (Fin φs.length))}
    {hs : S ⊆ φsΛ.1} (a : (quotContraction S hs).1) :
    uncontractedListEmd ((quotContraction S hs).sndFieldOfContract a) =
    (φsΛ.sndFieldOfContract
      ⟨Finset.map uncontractedListEmd a.1, mem_of_mem_quotContraction a.2⟩) := by
  symm
  apply eq_sndFieldOfContract_of_mem _ _
    (uncontractedListEmd ((quotContraction S hs).fstFieldOfContract a))
  · simp only [Finset.mem_map', fstFieldOfContract_mem]
  · simp
  · apply uncontractedListEmd_strictMono
    exact fstFieldOfContract_lt_sndFieldOfContract (quotContraction S hs) a

lemma quotContraction_gradingCompliant {S : Finset (Finset (Fin φs.length))} {hs : S ⊆ φsΛ.1}
    (hsΛ : φsΛ.GradingCompliant) :
    GradingCompliant [φsΛ.subContraction S hs]ᵘᶜ (quotContraction S hs) := by
  simp only [GradingCompliant, Subtype.forall]
  intro a ha
  erw [subContraction_uncontractedList_get]
  erw [subContraction_uncontractedList_get]
  simp only [quotContraction_fstFieldOfContract_uncontractedListEmd, Fin.getElem_fin,
    quotContraction_sndFieldOfContract_uncontractedListEmd]
  apply hsΛ

lemma mem_quotContraction_iff {S : Finset (Finset (Fin φs.length))} {hs : S ⊆ φsΛ.1}
    {a : Finset (Fin [φsΛ.subContraction S hs]ᵘᶜ.length)} :
    a ∈ (quotContraction S hs).1 ↔ a.map uncontractedListEmd ∈ φsΛ.1
    ∧ a.map uncontractedListEmd ∉ (subContraction S hs).1 := by
  apply Iff.intro
  · intro h
    apply And.intro
    · exact mem_of_mem_quotContraction h
    · exact uncontractedListEmd_finset_not_mem _
  · intro h
    have h2 := mem_subContraction_or_quotContraction (S := S) (hs := hs) h.1
    simp_all

end WickContraction
