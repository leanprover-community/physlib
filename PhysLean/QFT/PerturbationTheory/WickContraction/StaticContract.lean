/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QFT.PerturbationTheory.WickContraction.InsertAndContract
import PhysLean.QFT.PerturbationTheory.WickAlgebra.NormalOrder.Lemmas
/-!

# Time contractions

-/

open FieldSpecification
variable {𝓕 : FieldSpecification}

namespace WickContraction
variable {n : ℕ} (c : WickContraction n)
open PhysLean.List
open WickAlgebra

/-- For a list `φs` of `𝓕.FieldOp` and a Wick contraction `φsΛ`, the
  element of the center of `𝓕.WickAlgebra`, `φsΛ.staticContract` is defined as the product
  of `[anPart φs[j], φs[k]]ₛ` over contracted pairs `{j, k}` in `φsΛ`
  with `j < k`. -/
noncomputable def staticContract {φs : List 𝓕.FieldOp}
    (φsΛ : WickContraction φs.length) :
    Subalgebra.center ℂ 𝓕.WickAlgebra :=
  ∏ (a : φsΛ.1), ⟨[anPart (φs.get (φsΛ.fstFieldOfContract a)),
    ofFieldOp (φs.get (φsΛ.sndFieldOfContract a))]ₛ,
      superCommute_anPart_ofFieldOp_mem_center _ _⟩

/-- For a list `φs = φ₀…φₙ` of `𝓕.FieldOp`, a Wick contraction `φsΛ` of `φs`, an element `φ` of
  `𝓕.FieldOp`, and a `i ≤ φs.length`, then the following relation holds:

  `(φsΛ ↩Λ φ i none).staticContract = φsΛ.staticContract`

  The proof of this result ultimately is a consequence of definitions.
-/
@[simp]
lemma staticContract_insert_none (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) :
    (φsΛ ↩Λ φ i none).staticContract = φsΛ.staticContract := by
  rw [staticContract, insertAndContract_none_prod_contractions]
  congr
  ext a
  simp

/--
  For a list `φs = φ₀…φₙ` of `𝓕.FieldOp`, a Wick contraction `φsΛ` of `φs`, an element `φ` of
  `𝓕.FieldOp`, a `i ≤ φs.length` and a `k` in `φsΛ.uncontracted`, then
  `(φsΛ ↩Λ φ i (some k)).staticContract` is equal to the product of
  - `[anPart φ, φs[k]]ₛ` if `i ≤ k` or `[anPart φs[k], φ]ₛ` if `k < i`
  - `φsΛ.staticContract`.

  The proof of this result ultimately is a consequence of definitions.
-/
lemma staticContract_insert_some
    (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (j : φsΛ.uncontracted) :
    (φsΛ ↩Λ φ i (some j)).staticContract =
    (if i < i.succAbove j then
      ⟨[anPart φ, ofFieldOp φs[j.1]]ₛ, superCommute_anPart_ofFieldOp_mem_center _ _⟩
    else ⟨[anPart φs[j.1], ofFieldOp φ]ₛ, superCommute_anPart_ofFieldOp_mem_center _ _⟩) *
    φsΛ.staticContract := by
  rw [staticContract, insertAndContract_some_prod_contractions]
  congr 1
  · simp only [Nat.succ_eq_add_one, insertAndContract_fstFieldOfContract_some_incl, finCongr_apply,
    List.get_eq_getElem, insertAndContract_sndFieldOfContract_some_incl, Fin.getElem_fin]
    split
    · simp
    · simp
  · congr
    ext a
    simp

open FieldStatistic

lemma staticContract_insert_some_of_lt
    (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (k : φsΛ.uncontracted)
    (hik : i < i.succAbove k) :
    (φsΛ ↩Λ φ i (some k)).staticContract =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨φs.get, (φsΛ.uncontracted.filter (fun x => x < k))⟩)
    • (contractStateAtIndex φ [φsΛ]ᵘᶜ ((uncontractedFieldOpEquiv φs φsΛ) (some k)) *
      φsΛ.staticContract) := by
  rw [staticContract_insert_some]
  simp only [Nat.succ_eq_add_one, Fin.getElem_fin, ite_mul, instCommGroup.eq_1,
    contractStateAtIndex, uncontractedFieldOpEquiv, Equiv.optionCongr_apply,
    Equiv.coe_trans, Option.map_some, Function.comp_apply, finCongr_apply, Fin.val_cast,
    List.getElem_map, uncontractedList_getElem_uncontractedIndexEquiv_symm, List.get_eq_getElem,
    Algebra.smul_mul_assoc, uncontractedListGet]
  · simp only [hik, ↓reduceIte, MulMemClass.coe_mul]
    trans (1 : ℂ) • ((superCommute (anPart φ)) (ofFieldOp φs[k.1]) * ↑φsΛ.staticContract)
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

lemma staticContract_of_not_gradingCompliant (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (h : ¬ GradingCompliant φs φsΛ) :
    φsΛ.staticContract = 0 := by
  rw [staticContract]
  simp only [GradingCompliant, Subtype.forall, not_forall] at h
  obtain ⟨a, ha⟩ := h
  obtain ⟨ha, ha2⟩ := ha
  apply Finset.prod_eq_zero (i := ⟨a, ha⟩)
  simp only [Finset.univ_eq_attach, Finset.mem_attach]
  apply Subtype.ext
  simp only [List.get_eq_getElem, ZeroMemClass.coe_zero]
  rw [superCommute_anPart_ofFieldOpF_diff_grade_zero]
  simp [ha2]

end WickContraction
