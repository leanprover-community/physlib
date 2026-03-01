/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QFT.PerturbationTheory.WickContraction.Basic
/-!

# Uncontracted elements

-/
open FieldSpecification
variable {𝓕 : FieldSpecification}

namespace WickContraction
variable {n : ℕ} (c : WickContraction n)
open PhysLean.List

/-- For a Wick contraction `c`, `c.uncontracted` is defined as the finset of elements of `Fin n`
  which are not in any contracted pair. -/
def uncontracted : Finset (Fin n) := Finset.filter (fun i => c.getDual? i = none) (Finset.univ)

lemma congr_uncontracted {n m : ℕ} (c : WickContraction n) (h : n = m) :
    (c.congr h).uncontracted = Finset.map (finCongr h).toEmbedding c.uncontracted := by
  subst h
  simp

lemma getDual?_eq_none_iff_mem_uncontracted (i : Fin n) :
    c.getDual? i = none ↔ i ∈ c.uncontracted := by
  simp [uncontracted]

/-- The equivalence of `Option c.uncontracted` for two propositionally equal Wick contractions. -/
def uncontractedCongr {c c': WickContraction n} (h : c = c') :
    Option c.uncontracted ≃ Option c'.uncontracted :=
    Equiv.optionCongr (Equiv.subtypeEquivRight (by rw [h]; simp))

@[simp]
lemma uncontractedCongr_none {c c': WickContraction n} (h : c = c') :
    (uncontractedCongr h) none = none := by
  simp [uncontractedCongr]

@[simp]
lemma uncontractedCongr_some {c c': WickContraction n} (h : c = c') (i : c.uncontracted) :
    (uncontractedCongr h) (some i) = some (Equiv.subtypeEquivRight (by rw [h]; simp) i) := by
  simp [uncontractedCongr]

lemma mem_uncontracted_iff_not_contracted (i : Fin n) :
    i ∈ c.uncontracted ↔ ∀ p ∈ c.1, i ∉ p := by
  simp only [uncontracted, getDual?, Finset.mem_filter, Finset.mem_univ, true_and]
  apply Iff.intro
  · intro h p hp
    have hp := c.2.1 p hp
    rw [Finset.card_eq_two] at hp
    obtain ⟨a, b, ha, hb, hab⟩ := hp
    rw [Fin.find?_eq_none_iff] at h
    by_contra hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with hn | hn
    · subst hn
      simp at h
      exact h b hp
    · subst hn
      rw [Finset.pair_comm] at hp
      simp at h
      exact h a hp
  · intro h
    rw [Fin.find?_eq_none_iff]
    by_contra hn
    simp only [decide_eq_false_iff_not, not_forall, Decidable.not_not] at hn
    obtain ⟨j, hj⟩ := hn
    apply h {i, j} hj
    simp

lemma mem_uncontracted_empty (i : Fin n) : i ∈ empty.uncontracted := by
  rw [@mem_uncontracted_iff_not_contracted]
  intro p hp
  simp [empty] at hp

@[simp]
lemma getDual?_empty_eq_none (i : Fin n) : empty.getDual? i = none := by
  simpa [uncontracted] using mem_uncontracted_empty i

@[simp]
lemma uncontracted_empty {n : ℕ} : (@empty n).uncontracted = Finset.univ := by
  simp [uncontracted]

lemma uncontracted_card_le (c : WickContraction n) : c.uncontracted.card ≤ n := by
  simp only [uncontracted]
  apply le_of_le_of_eq (Finset.card_filter_le _ _)
  simp

lemma uncontracted_card_eq_iff (c : WickContraction n) :
    c.uncontracted.card = n ↔ c = empty := by
  apply Iff.intro
  · intro h
    have hc : c.uncontracted.card = (Finset.univ (α := Fin n)).card := by simpa using h
    simp only [uncontracted] at hc
    rw [Finset.card_filter_eq_iff] at hc
    by_contra hn
    have hc' := exists_pair_of_not_eq_empty c hn
    obtain ⟨i, j, hij⟩ := hc'
    have hci : c.getDual? i = some j := by
      rw [@getDual?_eq_some_iff_mem]
      exact hij
    simp_all
  · intro h
    subst h
    simp

end WickContraction
