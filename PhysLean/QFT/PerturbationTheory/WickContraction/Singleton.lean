/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QFT.PerturbationTheory.WickContraction.SubContraction
import PhysLean.QFT.PerturbationTheory.WickContraction.StaticContract
import PhysLean.QFT.PerturbationTheory.WickContraction.TimeContract
import PhysLean.QFT.PerturbationTheory.WickContraction.Sign.Basic
/-!

# Singleton of contractions

-/

open FieldSpecification
variable {𝓕 : FieldSpecification}

namespace WickContraction
variable {n : ℕ} (c : WickContraction n)
open PhysLean.List
open WickAlgebra
open FieldStatistic

/-- The Wick contraction formed from a single ordered pair. -/
def singleton {i j : Fin n} (hij : i < j) : WickContraction n :=
  ⟨{{i, j}}, by
    intro i hi
    simp only [Finset.mem_singleton] at hi
    subst hi
    rw [@Finset.card_eq_two]
    use i, j
    simp only [ne_eq, and_true]
    omega, by
    intro i hi j hj
    simp_all⟩

lemma mem_singleton {i j : Fin n} (hij : i < j) :
    {i, j} ∈ (singleton hij).1 := by
  simp [singleton]

lemma mem_singleton_iff {i j : Fin n} (hij : i < j) {a : Finset (Fin n)} :
    a ∈ (singleton hij).1 ↔ a = {i, j} := by
  simp [singleton]

lemma of_singleton_eq {i j : Fin n} (hij : i < j) (a : (singleton hij).1) :
    a = ⟨{i, j}, mem_singleton hij⟩ := by
  have ha2 := a.2
  rw [@mem_singleton_iff] at ha2
  exact Subtype.coe_eq_of_eq_mk ha2

lemma singleton_prod {φs : List 𝓕.FieldOp} {i j : Fin φs.length} (hij : i < j)
    (f : (singleton hij).1 → M) [CommMonoid M] :
    ∏ a, f a = f ⟨{i,j}, mem_singleton hij⟩:= by
  simp [singleton, of_singleton_eq]

@[simp]
lemma singleton_fstFieldOfContract {i j : Fin n} (hij : i < j) :
    (singleton hij).fstFieldOfContract ⟨{i, j}, mem_singleton hij⟩ = i := by
  refine eq_fstFieldOfContract_of_mem (singleton hij) ⟨{i, j}, mem_singleton hij⟩ i j ?_ ?_ ?_
  · simp
  · simp
  · exact hij

@[simp]
lemma singleton_sndFieldOfContract {i j : Fin n} (hij : i < j) :
    (singleton hij).sndFieldOfContract ⟨{i, j}, mem_singleton hij⟩ = j := by
  refine eq_sndFieldOfContract_of_mem (singleton hij) ⟨{i, j}, mem_singleton hij⟩ i j ?_ ?_ ?_
  · simp
  · simp
  · exact hij

lemma singleton_sign_expand {φs : List 𝓕.FieldOp} {i j : Fin φs.length} (hij : i < j) :
    (singleton hij).sign = 𝓢(𝓕 |>ₛ φs[j], 𝓕 |>ₛ ⟨φs.get, (singleton hij).signFinset i j⟩) := by
  rw [sign, singleton_prod]
  simp

lemma singleton_getDual?_eq_none_iff_neq {i j : Fin n} (hij : i < j) (a : Fin n) :
    (singleton hij).getDual? a = none ↔ (i ≠ a ∧ j ≠ a) := by
  rw [getDual?_eq_none_iff_mem_uncontracted]
  rw [mem_uncontracted_iff_not_contracted]
  simp only [singleton, Finset.mem_singleton, forall_eq, Finset.mem_insert, not_or, ne_eq]
  omega

lemma singleton_uncontractedEmd_ne_left {φs : List 𝓕.FieldOp} {i j : Fin φs.length} (hij : i < j)
    (a : Fin [singleton hij]ᵘᶜ.length) :
    (singleton hij).uncontractedListEmd a ≠ i := by
  by_contra hn
  have h1 : (singleton hij).uncontractedListEmd a ∈ (singleton hij).uncontracted := by
    simp [uncontractedListEmd]
  have h2 : i ∉ (singleton hij).uncontracted := by
    rw [mem_uncontracted_iff_not_contracted]
    simp [singleton]
  simp_all

lemma singleton_uncontractedEmd_ne_right {φs : List 𝓕.FieldOp} {i j : Fin φs.length} (hij : i < j)
    (a : Fin [singleton hij]ᵘᶜ.length) :
    (singleton hij).uncontractedListEmd a ≠ j := by
  by_contra hn
  have h1 : (singleton hij).uncontractedListEmd a ∈ (singleton hij).uncontracted := by
    simp [uncontractedListEmd]
  have h2 : j ∉ (singleton hij).uncontracted := by
    rw [mem_uncontracted_iff_not_contracted]
    simp [singleton]
  simp_all

@[simp]
lemma mem_signFinset {i j : Fin n} (hij : i < j) (a : Fin n) :
    a ∈ (singleton hij).signFinset i j ↔ i < a ∧ a < j := by
  simp only [signFinset, Finset.mem_filter, Finset.mem_univ, true_and, and_congr_right_iff,
    and_iff_left_iff_imp]
  intro h1 h2
  rw [@singleton_getDual?_eq_none_iff_neq]
  apply Or.inl
  omega

lemma subContraction_singleton_eq_singleton {φs : List 𝓕.FieldOp}
    (φsΛ : WickContraction φs.length)
    (a : φsΛ.1) : φsΛ.subContraction {a.1} (by simp) =
    singleton (φsΛ.fstFieldOfContract_lt_sndFieldOfContract a) := by
  apply Subtype.ext
  simp only [subContraction, singleton, Finset.singleton_inj]
  exact finset_eq_fstFieldOfContract_sndFieldOfContract φsΛ a

lemma singleton_timeContract {φs : List 𝓕.FieldOp} {i j : Fin φs.length} (hij : i < j) :
    (singleton hij).timeContract =
    ⟨WickAlgebra.timeContract φs[i] φs[j], timeContract_mem_center _ _⟩ := by
  rw [timeContract, singleton_prod]
  simp

lemma singleton_staticContract {φs : List 𝓕.FieldOp} {i j : Fin φs.length} (hij : i < j) :
    (singleton hij).staticContract.1 =
    [anPart φs[i], ofFieldOp φs[j]]ₛ := by
  rw [staticContract, singleton_prod]
  simp

end WickContraction
