/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QFT.PerturbationTheory.WickAlgebra.TimeContraction
import PhysLean.QFT.PerturbationTheory.WickContraction.InsertAndContract
/-!

# Time contractions

-/

open FieldSpecification
variable {𝓕 : FieldSpecification}

namespace WickContraction
variable {n : ℕ} (c : WickContraction n)
open PhysLean.List
open WickAlgebra

/-- For a list `φs` of `𝓕.FieldOp` and a Wick contraction `φsΛ` the
  element of the center of `𝓕.WickAlgebra`, `φsΛ.timeContract` is defined as the product
  of `timeContract φs[j] φs[k]` over contracted pairs `{j, k}` in `φsΛ`
  with `j < k`. -/
noncomputable def timeContract {φs : List 𝓕.FieldOp}
    (φsΛ : WickContraction φs.length) :
    Subalgebra.center ℂ 𝓕.WickAlgebra :=
  ∏ (a : φsΛ.1), ⟨WickAlgebra.timeContract
    (φs.get (φsΛ.fstFieldOfContract a)) (φs.get (φsΛ.sndFieldOfContract a)),
    timeContract_mem_center _ _⟩

/-- For a list `φs = φ₀…φₙ` of `𝓕.FieldOp`, a Wick contraction `φsΛ` of `φs`, an element `φ` of
  `𝓕.FieldOp`, and a `i ≤ φs.length` the following relation holds

  `(φsΛ ↩Λ φ i none).timeContract = φsΛ.timeContract`

  The proof of this result ultimately is a consequence of definitions. -/
@[simp]
lemma timeContract_insert_none (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) :
    (φsΛ ↩Λ φ i none).timeContract = φsΛ.timeContract := by
  rw [timeContract, insertAndContract_none_prod_contractions]
  congr
  ext a
  simp

/-- For a list `φs = φ₀…φₙ` of `𝓕.FieldOp`, a Wick contraction `φsΛ` of `φs`, an element `φ` of
  `𝓕.FieldOp`, a `i ≤ φs.length` and a `k` in `φsΛ.uncontracted`, then
  `(φsΛ ↩Λ φ i (some k)).timeContract` is equal to the product of
  - `timeContract φ φs[k]` if `i ≤ k` or `timeContract φs[k] φ` if `k < i`
  - `φsΛ.timeContract`.

  The proof of this result ultimately is a consequence of definitions. -/
lemma timeContract_insertAndContract_some
    (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (j : φsΛ.uncontracted) :
    (φsΛ ↩Λ φ i (some j)).timeContract =
    (if i < i.succAbove j then
      ⟨WickAlgebra.timeContract φ φs[j.1], timeContract_mem_center _ _⟩
    else ⟨WickAlgebra.timeContract φs[j.1] φ, timeContract_mem_center _ _⟩) *
    φsΛ.timeContract := by
  rw [timeContract, insertAndContract_some_prod_contractions]
  congr 1
  · simp only [Nat.succ_eq_add_one, insertAndContract_fstFieldOfContract_some_incl, finCongr_apply,
    List.get_eq_getElem, insertAndContract_sndFieldOfContract_some_incl, Fin.getElem_fin]
    split
    · simp
    · simp
  · congr
    ext a
    simp

@[simp]
lemma timeContract_empty (φs : List 𝓕.FieldOp) :
    (@empty φs.length).timeContract = 1 := by
  rw [timeContract, empty]
  simp

open FieldStatistic

/-- For a list `φs = φ₀…φₙ` of `𝓕.FieldOp`, a Wick contraction `φsΛ` of `φs`, an element `φ` of
  `𝓕.FieldOp`, a `i ≤ φs.length` and a `k` in `φsΛ.uncontracted` such that `i ≤ k`, with the
  condition that `φ` has greater or equal time to `φs[k]`, then
  `(φsΛ ↩Λ φ i (some k)).timeContract` is equal to the product of
  - `[anPart φ, φs[k]]ₛ`
  - `φsΛ.timeContract`
  - two copies of the exchange sign of `φ` with the uncontracted fields in `φ₀…φₖ₋₁`.
    These two exchange signs cancel each other out but are included for convenience.

  The proof of this result ultimately is a consequence of definitions and
  `timeContract_of_timeOrderRel`. -/
lemma timeContract_insert_some_of_lt
    (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (k : φsΛ.uncontracted)
    (ht : 𝓕.timeOrderRel φ φs[k.1]) (hik : i < i.succAbove k) :
    (φsΛ ↩Λ φ i (some k)).timeContract =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨φs.get, (φsΛ.uncontracted.filter (fun x => x < k))⟩)
    • (contractStateAtIndex φ [φsΛ]ᵘᶜ ((uncontractedFieldOpEquiv φs φsΛ) (some k)) *
      φsΛ.timeContract) := by
  rw [timeContract_insertAndContract_some]
  simp only [Nat.succ_eq_add_one, Fin.getElem_fin, ite_mul, instCommGroup.eq_1,
    contractStateAtIndex, uncontractedFieldOpEquiv, Equiv.optionCongr_apply,
    Equiv.coe_trans, Option.map_some, Function.comp_apply, finCongr_apply, Fin.val_cast,
    List.getElem_map, uncontractedList_getElem_uncontractedIndexEquiv_symm, List.get_eq_getElem,
    Algebra.smul_mul_assoc, uncontractedListGet]
  · simp only [hik, ↓reduceIte, MulMemClass.coe_mul]
    rw [timeContract_of_timeOrderRel]
    trans (1 : ℂ) • ((superCommute (anPart φ)) (ofFieldOp φs[k.1]) * ↑φsΛ.timeContract)
    · simp
    simp only [smul_smul]
    congr 1
    have h1 : ofList 𝓕.fieldOpStatistic (List.take (↑(φsΛ.uncontractedIndexEquiv.symm k))
        (List.map φs.get φsΛ.uncontractedList))
        = (𝓕 |>ₛ ⟨φs.get, (Finset.filter (fun x => x < k) φsΛ.uncontracted)⟩) := by
      simp only [ofFinset]
      congr
      rw [← List.map_take]
      congr
      rw [take_uncontractedIndexEquiv_symm]
      rw [filter_uncontractedList]
    rw [h1]
    simp only [exchangeSign_mul_self]
    · exact ht

/-- For a list `φs = φ₀…φₙ` of `𝓕.FieldOp`, a Wick contraction `φsΛ` of `φs`, an element `φ` of
  `𝓕.FieldOp`, a `i ≤ φs.length` and a `k` in `φsΛ.uncontracted` such that `k < i`, with the
  condition that `φs[k]` does not have time greater or equal to `φ`, then
  `(φsΛ ↩Λ φ i (some k)).timeContract` is equal to the product of
  - `[anPart φ, φs[k]]ₛ`
  - `φsΛ.timeContract`
  - the exchange sign of `φ` with the uncontracted fields in `φ₀…φₖ₋₁`.
  - the exchange sign of `φ` with the uncontracted fields in `φ₀…φₖ`.

  The proof of this result ultimately is a consequence of definitions and
  `timeContract_of_not_timeOrderRel_expand`. -/
lemma timeContract_insert_some_of_not_lt
    (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (k : φsΛ.uncontracted)
    (ht : ¬ 𝓕.timeOrderRel φs[k.1] φ) (hik : ¬ i < i.succAbove k) :
    (φsΛ ↩Λ φ i (some k)).timeContract =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨φs.get, (φsΛ.uncontracted.filter (fun x => x ≤ k))⟩)
    • (contractStateAtIndex φ [φsΛ]ᵘᶜ
      ((uncontractedFieldOpEquiv φs φsΛ) (some k)) * φsΛ.timeContract) := by
  rw [timeContract_insertAndContract_some]
  simp only [Nat.succ_eq_add_one, Fin.getElem_fin, ite_mul, instCommGroup.eq_1,
    contractStateAtIndex, uncontractedFieldOpEquiv, Equiv.optionCongr_apply,
    Equiv.coe_trans, Option.map_some, Function.comp_apply, finCongr_apply, Fin.val_cast,
    List.getElem_map, uncontractedList_getElem_uncontractedIndexEquiv_symm, List.get_eq_getElem,
    Algebra.smul_mul_assoc, uncontractedListGet]
  simp only [hik, ↓reduceIte, MulMemClass.coe_mul]
  rw [timeContract_of_not_timeOrderRel, timeContract_of_timeOrderRel]
  simp only [instCommGroup.eq_1, Algebra.smul_mul_assoc, smul_smul]
  congr
  have h1 : ofList 𝓕.fieldOpStatistic (List.take (↑(φsΛ.uncontractedIndexEquiv.symm k))
      (List.map φs.get φsΛ.uncontractedList))
      = (𝓕 |>ₛ ⟨φs.get, (Finset.filter (fun x => x < k) φsΛ.uncontracted)⟩) := by
    simp only [ofFinset]
    congr
    rw [← List.map_take]
    congr
    rw [take_uncontractedIndexEquiv_symm, filter_uncontractedList]
  rw [h1]
  trans 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨φs.get, {k.1}⟩)
  · rw [exchangeSign_symm, ofFinset_singleton]
    simp
  rw [← map_mul]
  congr
  rw [ofFinset_union]
  congr
  ext a
  simp only [Finset.mem_singleton, Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter,
    Finset.mem_inter, not_and, not_lt, and_imp]
  apply Iff.intro
  · intro h
    subst h
    simp
  · intro h
    have h1 := h.1
    rcases h1 with h1 | h1
    · have h2' := h.2 h1.1 h1.2 h1.1
      omega
    · have h2' := h.2 h1.1 (by omega) h1.1
      omega
  have ht := Std.Total.total (r := timeOrderRel) φs[k.1] φ
  simp_all only [Fin.getElem_fin, Nat.succ_eq_add_one, not_lt, false_or]
  exact ht

lemma timeContract_of_not_gradingCompliant (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (h : ¬ GradingCompliant φs φsΛ) :
    φsΛ.timeContract = 0 := by
  rw [timeContract]
  simp only [GradingCompliant, Subtype.forall, not_forall] at h
  obtain ⟨a, ha⟩ := h
  obtain ⟨ha, ha2⟩ := ha
  apply Finset.prod_eq_zero (i := ⟨a, ha⟩)
  simp only [Finset.univ_eq_attach, Finset.mem_attach]
  apply Subtype.ext
  simp only [List.get_eq_getElem, ZeroMemClass.coe_zero]
  rw [timeContract_zero_of_diff_grade]
  simp [ha2]

end WickContraction
