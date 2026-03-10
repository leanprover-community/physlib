/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.QFT.PerturbationTheory.WickContraction.Sign.InsertNone
public import PhysLean.QFT.PerturbationTheory.WickContraction.Sign.InsertSome
public import PhysLean.QFT.PerturbationTheory.WickContraction.TimeContract
public import PhysLean.QFT.PerturbationTheory.WickAlgebra.NormalOrder.WickContractions
/-!

# Wick term

-/

@[expose] public section

open FieldSpecification
variable {𝓕 : FieldSpecification}

namespace WickContraction
variable {n : ℕ} (c : WickContraction n)
open PhysLean.List
open WickAlgebra
open FieldStatistic
noncomputable section

/-- For a list `φs` of `𝓕.FieldOp`, and a Wick contraction `φsΛ` of `φs`, the element
  of `𝓕.WickAlgebra`, `φsΛ.wickTerm` is defined as

  `φsΛ.sign • φsΛ.timeContract * 𝓝([φsΛ]ᵘᶜ)`.

  This is a term which appears in the Wick's theorem. -/
def wickTerm {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length) : 𝓕.WickAlgebra :=
  φsΛ.sign • φsΛ.timeContract * 𝓝(ofFieldOpList [φsΛ]ᵘᶜ)

/-- For the empty list `[]` of `𝓕.FieldOp`, the `wickTerm` of the Wick contraction
  corresponding to the empty set `∅` (the only Wick contraction of `[]`) is `1`. -/
@[simp]
lemma wickTerm_empty_nil :
    wickTerm (empty (n := ([] : List 𝓕.FieldOp).length)) = 1 := by
  rw [wickTerm]
  simp [sign_empty]

/--
For a list `φs = φ₀…φₙ` of `𝓕.FieldOp`, a Wick contraction `φsΛ` of `φs`, an element `φ` of
  `𝓕.FieldOp`, and `i ≤ φs.length`, then `(φsΛ ↩Λ φ i none).wickTerm` is equal to

`𝓢(φ, φ₀…φᵢ₋₁) φsΛ.sign • φsΛ.timeContract * 𝓝(φ :: [φsΛ]ᵘᶜ)`

The proof of this result relies on
- `normalOrder_uncontracted_none` to rewrite normal orderings.
- `timeContract_insert_none` to rewrite the time contract.
- `sign_insert_none` to rewrite the sign.
-/
lemma wickTerm_insert_none (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (i : Fin φs.length.succ) (φsΛ : WickContraction φs.length) :
    (φsΛ ↩Λ φ i none).wickTerm =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨φs.get, (Finset.univ.filter (fun k => i.succAbove k < i))⟩)
    • (φsΛ.sign • φsΛ.timeContract * 𝓝(ofFieldOpList (φ :: [φsΛ]ᵘᶜ))) := by
  rw [wickTerm]
  by_cases hg : GradingCompliant φs φsΛ
  · rw [normalOrder_uncontracted_none, sign_insert_none _ _ _ _ hg]
    simp only [Nat.succ_eq_add_one, timeContract_insert_none, instCommGroup.eq_1,
      Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_smul]
    congr 1
    rw [← mul_assoc]
    congr 1
    rw [← map_mul]
    congr
    rw [ofFinset_union]
    congr
    ext a
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_inter, not_and, not_lt, and_imp]
    apply Iff.intro
    · intro ha
      have ha1 := ha.1
      rcases ha1 with ha1 | ha1
      · exact ha1.2
      · exact ha1.2
    · intro ha
      simp only [uncontracted, Finset.mem_filter, Finset.mem_univ, true_and, ha, and_true,
        forall_const]
      have hx : φsΛ.getDual? a = none ↔ ¬ (φsΛ.getDual? a).isSome := by
        simp
      rw [hx]
      simp only [Bool.not_eq_true, Bool.eq_false_or_eq_true_self, true_and]
      intro h1 h2
      simp_all
  · simp only [Nat.succ_eq_add_one, timeContract_insert_none, Algebra.smul_mul_assoc,
    instCommGroup.eq_1]
    rw [timeContract_of_not_gradingCompliant]
    simp only [ZeroMemClass.coe_zero, zero_mul, smul_zero]
    exact hg

/-- For a list `φs = φ₀…φₙ` of `𝓕.FieldOp`, a Wick contraction `φsΛ` of `φs`, an element `φ` of
  `𝓕.FieldOp`, `i ≤ φs.length` and a `k` in `φsΛ.uncontracted`,
  such that all `𝓕.FieldOp` in `φ₀…φᵢ₋₁` have time strictly less than `φ` and
  `φ` has a time greater than or equal to all `FieldOp` in `φ₀…φₙ`, then
  `(φsΛ ↩Λ φ i (some k)).staticWickTerm`
is equal to the product of
- the sign `𝓢(φ, φ₀…φᵢ₋₁) `
- the sign `φsΛ.sign`
- `φsΛ.timeContract`
- `s • [anPart φ, ofFieldOp φs[k]]ₛ` where `s` is the sign associated with moving `φ` through
  uncontracted fields in `φ₀…φₖ₋₁`
- the normal ordering `[φsΛ]ᵘᶜ` with the field corresponding to `k` removed.

The proof of this result relies on
- `timeContract_insert_some_of_not_lt`
  and `timeContract_insert_some_of_lt` to rewrite time
  contractions.
- `normalOrder_uncontracted_some` to rewrite normal orderings.
- `sign_insert_some_of_not_lt` and `sign_insert_some_of_lt` to rewrite signs.
-/
lemma wickTerm_insert_some (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (i : Fin φs.length.succ) (φsΛ : WickContraction φs.length) (k : φsΛ.uncontracted)
    (hlt : ∀ (k : Fin φs.length), timeOrderRel φ φs[k])
    (hn : ∀ (k : Fin φs.length), i.succAbove k < i → ¬ timeOrderRel φs[k] φ) :
    (φsΛ ↩Λ φ i (some k)).wickTerm =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨φs.get, (Finset.univ.filter (fun x => i.succAbove x < i))⟩)
    • (φsΛ.sign • (contractStateAtIndex φ [φsΛ]ᵘᶜ
      ((uncontractedFieldOpEquiv φs φsΛ) (some k)) * φsΛ.timeContract)
    * 𝓝(ofFieldOpList (optionEraseZ [φsΛ]ᵘᶜ φ (uncontractedFieldOpEquiv φs φsΛ k)))) := by
  rw [wickTerm]
  by_cases hg : GradingCompliant φs φsΛ ∧ (𝓕 |>ₛ φ) = (𝓕 |>ₛ φs[k.1])
  · by_cases hk : i.succAbove k < i
    · rw [WickContraction.timeContract_insert_some_of_not_lt]
      swap
      · exact hn _ hk
      · rw [normalOrder_uncontracted_some, sign_insert_some_of_lt φ φs φsΛ i k hk hg]
        simp only [instCommGroup.eq_1, smul_smul, Algebra.smul_mul_assoc]
        congr 1
        rw [mul_assoc, mul_assoc, mul_comm, mul_assoc, mul_assoc]
        simp
      · omega
    · have hik : i.succAbove ↑k ≠ i := Fin.succAbove_ne i ↑k
      rw [timeContract_insert_some_of_lt]
      swap
      · exact hlt _
      · rw [normalOrder_uncontracted_some]
        rw [sign_insert_some_of_not_lt φ φs φsΛ i k hk hg]
        simp only [instCommGroup.eq_1, smul_smul, Algebra.smul_mul_assoc]
        congr 1
        rw [mul_assoc, mul_assoc, mul_comm, mul_assoc, mul_assoc]
        simp
      · omega
  · rw [timeContract_insertAndContract_some]
    simp only [Fin.getElem_fin, not_and] at hg
    by_cases hg' : GradingCompliant φs φsΛ
    · have hg := hg hg'
      simp only [Nat.succ_eq_add_one, Fin.getElem_fin, ite_mul, Algebra.smul_mul_assoc,
        instCommGroup.eq_1, contractStateAtIndex, uncontractedFieldOpEquiv, Equiv.optionCongr_apply,
        Equiv.coe_trans, Option.map_some, Function.comp_apply, finCongr_apply, Fin.val_cast,
        List.getElem_map, uncontractedList_getElem_uncontractedIndexEquiv_symm, List.get_eq_getElem,
        uncontractedListGet]
      by_cases h1 : i < i.succAbove ↑k
      · simp only [h1, ↓reduceIte, MulMemClass.coe_mul]
        rw [timeContract_zero_of_diff_grade]
        simp only [zero_mul, smul_zero]
        rw [superCommute_anPart_ofFieldOpF_diff_grade_zero]
        simp only [zero_mul, smul_zero]
        exact hg
        exact hg
      · simp only [h1, ↓reduceIte, MulMemClass.coe_mul]
        rw [timeContract_zero_of_diff_grade]
        simp only [zero_mul, smul_zero]
        rw [superCommute_anPart_ofFieldOpF_diff_grade_zero]
        simp only [zero_mul, smul_zero]
        exact hg
        exact fun a => hg (id (Eq.symm a))
    · rw [timeContract_of_not_gradingCompliant]
      simp only [Nat.succ_eq_add_one, Fin.getElem_fin, mul_zero, ZeroMemClass.coe_zero, smul_zero,
        zero_mul, instCommGroup.eq_1]
      exact hg'

/--
For a list `φs = φ₀…φₙ` of `𝓕.FieldOp`, a Wick contraction `φsΛ` of `φs`, an element `φ` of
  `𝓕.FieldOp`, and `i ≤ φs.length`
  such that all `𝓕.FieldOp` in `φ₀…φᵢ₋₁` have time strictly less than `φ` and
  `φ` has a time greater than or equal to all `FieldOp` in `φ₀…φₙ`, then

`φ * φsΛ.wickTerm = 𝓢(φ, φ₀…φᵢ₋₁) • ∑ k, (φsΛ ↩Λ φ i k).wickTerm`

where the sum is over all `k` in `Option φsΛ.uncontracted`, so `k` is either `none` or `some k`.

The proof proceeds as follows:
- `ofFieldOp_mul_normalOrder_ofFieldOpList_eq_sum` is used to expand `φ 𝓝([φsΛ]ᵘᶜ)` as
  a sum over `k` in `Option φsΛ.uncontracted` of terms involving `[anPart φ, φs[k]]ₛ`.
- Then `wickTerm_insert_none` and `wickTerm_insert_some` are used to equate terms.
-/
lemma mul_wickTerm_eq_sum (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp) (i : Fin φs.length.succ)
    (φsΛ : WickContraction φs.length) (hlt : ∀ (k : Fin φs.length), timeOrderRel φ φs[k])
    (hn : ∀ (k : Fin φs.length), i.succAbove k < i → ¬timeOrderRel φs[k] φ) :
    ofFieldOp φ * φsΛ.wickTerm =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨φs.get, (Finset.univ.filter (fun x => i.succAbove x < i))⟩) •
    ∑ (k : Option φsΛ.uncontracted), (φsΛ ↩Λ φ i k).wickTerm := by
  trans (φsΛ.sign • φsΛ.timeContract) * ((ofFieldOp φ) * 𝓝(ofFieldOpList [φsΛ]ᵘᶜ))
  · have ht := Subalgebra.mem_center_iff.mp (Subalgebra.smul_mem (Subalgebra.center ℂ _)
      (WickContraction.timeContract φsΛ).2 (φsΛ.sign))
    rw [wickTerm]
    rw [← mul_assoc, ht, mul_assoc]
  rw [ofFieldOp_mul_normalOrder_ofFieldOpList_eq_sum, Finset.mul_sum,
    uncontractedFieldOpEquiv_list_sum, Finset.smul_sum]
  simp only [instCommGroup.eq_1, Nat.succ_eq_add_one]
  congr 1
  funext n
  match n with
  | none =>
    rw [wickTerm_insert_none]
    simp only [contractStateAtIndex, uncontractedFieldOpEquiv, Equiv.optionCongr_apply,
      Equiv.coe_trans, Option.map_none, one_mul, Algebra.smul_mul_assoc, instCommGroup.eq_1,
      smul_smul]
    congr 1
    rw [← mul_assoc, exchangeSign_mul_self]
    simp
  | some n =>
    rw [wickTerm_insert_some _ _ _ _ _
      (fun k => hlt k) (fun k a => hn k a)]
    simp only [uncontractedFieldOpEquiv, Equiv.optionCongr_apply, Equiv.coe_trans, Option.map_some,
      Function.comp_apply, finCongr_apply, Algebra.smul_mul_assoc, instCommGroup.eq_1, smul_smul]
    congr 1
    · rw [← mul_assoc, exchangeSign_mul_self]
      rw [one_mul]
    · rw [← mul_assoc]
      congr 1
      have ht := (WickContraction.timeContract φsΛ).prop
      rw [@Subalgebra.mem_center_iff] at ht
      rw [ht]

end
end WickContraction
