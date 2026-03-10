/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.QFT.PerturbationTheory.WickAlgebra.NormalOrder.WickContractions
public import PhysLean.QFT.PerturbationTheory.WickContraction.Sign.InsertNone
public import PhysLean.QFT.PerturbationTheory.WickContraction.Sign.InsertSome
public import PhysLean.QFT.PerturbationTheory.WickContraction.StaticContract
/-!

# Static Wick's terms

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
  of `𝓕.WickAlgebra`, `φsΛ.staticWickTerm` is defined as

  `φsΛ.sign • φsΛ.staticContract * 𝓝([φsΛ]ᵘᶜ)`.

  This is a term which appears in the static version Wick's theorem. -/
def staticWickTerm {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length) : 𝓕.WickAlgebra :=
  φsΛ.sign • φsΛ.staticContract * 𝓝(ofFieldOpList [φsΛ]ᵘᶜ)

/-- For the empty list `[]` of `𝓕.FieldOp`, the `staticWickTerm` of the Wick contraction
  corresponding to the empty set `∅` (the only Wick contraction of `[]`) is `1`. -/
@[simp]
lemma staticWickTerm_empty_nil :
    staticWickTerm (empty (n := ([] : List 𝓕.FieldOp).length)) = 1 := by
  rw [staticWickTerm, uncontractedListGet, nil_zero_uncontractedList]
  simp [sign, empty, staticContract]

/--
For a list `φs = φ₀…φₙ` of `𝓕.FieldOp`, a Wick contraction `φsΛ` of `φs`, and an element `φ` of
  `𝓕.FieldOp`, then `(φsΛ ↩Λ φ 0 none).staticWickTerm` is equal to

`φsΛ.sign • φsΛ.staticWickTerm * 𝓝(φ :: [φsΛ]ᵘᶜ)`

The proof of this result relies on
- `staticContract_insert_none` to rewrite the static contract.
- `sign_insert_none_zero` to rewrite the sign.
-/
lemma staticWickTerm_insert_zero_none (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) :
    (φsΛ ↩Λ φ 0 none).staticWickTerm =
    φsΛ.sign • φsΛ.staticContract * 𝓝(ofFieldOpList (φ :: [φsΛ]ᵘᶜ)) := by
  symm
  erw [staticWickTerm, sign_insert_none_zero]
  simp only [staticContract_insert_none, insertAndContract_uncontractedList_none_zero,
    Algebra.smul_mul_assoc]

/-- For a list `φs = φ₀…φₙ` of `𝓕.FieldOp`, a Wick contraction `φsΛ` of `φs`, an element `φ` of
  `𝓕.FieldOp`, and a `k` in `φsΛ.uncontracted`, `(φsΛ ↩Λ φ 0 (some k)).wickTerm` is equal
  to the product of
- the sign `𝓢(φ, φ₀…φᵢ₋₁) `
- the sign `φsΛ.sign`
- `φsΛ.staticContract`
- `s • [anPart φ, ofFieldOp φs[k]]ₛ` where `s` is the sign associated with moving `φ` through
  uncontracted fields in `φ₀…φₖ₋₁`
- the normal ordering of `[φsΛ]ᵘᶜ` with the field operator `φs[k]` removed.

The proof of this result ultimately relies on
- `staticContract_insert_some` to rewrite static contractions.
- `normalOrder_uncontracted_some` to rewrite normal orderings.
- `sign_insert_some_zero` to rewrite signs.
-/
lemma staticWickTerm_insert_zero_some (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (k : { x // x ∈ φsΛ.uncontracted }) :
    (φsΛ ↩Λ φ 0 k).staticWickTerm =
    sign φs φsΛ • (↑φsΛ.staticContract *
    (contractStateAtIndex φ [φsΛ]ᵘᶜ ((uncontractedFieldOpEquiv φs φsΛ) (some k)) *
    𝓝(ofFieldOpList (optionEraseZ [φsΛ]ᵘᶜ φ (uncontractedFieldOpEquiv φs φsΛ k))))) := by
  symm
  rw [staticWickTerm, normalOrder_uncontracted_some]
  simp only [← mul_assoc]
  rw [← smul_mul_assoc]
  congr 1
  rw [staticContract_insert_some_of_lt]
  swap
  · simp
  rw [smul_smul]
  by_cases hn : GradingCompliant φs φsΛ ∧ (𝓕|>ₛφ) = (𝓕|>ₛ φs[k.1])
  · congr 1
    swap
    · rw [Subalgebra.mem_center_iff.mp φsΛ.staticContract.2]
    · rw [sign_insert_some_zero _ _ _ _ hn, mul_comm, ← mul_assoc]
      simp
  · simp only [Fin.getElem_fin, not_and] at hn
    by_cases h0 : ¬ GradingCompliant φs φsΛ
    · rw [staticContract_of_not_gradingCompliant]
      simp only [ZeroMemClass.coe_zero, zero_mul, smul_zero, instCommGroup.eq_1, mul_zero]
      exact h0
    · simp_all only [not_not, instCommGroup.eq_1, forall_const]
      have h1 : contractStateAtIndex φ [φsΛ]ᵘᶜ (uncontractedFieldOpEquiv φs φsΛ k) = 0 := by
        simp only [contractStateAtIndex, uncontractedFieldOpEquiv, Equiv.optionCongr_apply,
          Equiv.coe_trans, Option.map_some, Function.comp_apply, finCongr_apply,
          instCommGroup.eq_1, Fin.val_cast, Fin.getElem_fin, smul_eq_zero]
        right
        simp only [uncontractedListGet, List.getElem_map,
          uncontractedList_getElem_uncontractedIndexEquiv_symm, List.get_eq_getElem]
        rw [superCommute_anPart_ofFieldOpF_diff_grade_zero]
        exact hn
      rw [h1]
      simp

/--
For a list `φs = φ₀…φₙ` of `𝓕.FieldOp`, a Wick contraction `φsΛ` of `φs`, the following relation
holds

`φ * φsΛ.staticWickTerm = ∑ k, (φsΛ ↩Λ φ 0 k).staticWickTerm`

where the sum is over all `k` in `Option φsΛ.uncontracted`, so `k` is either `none` or `some k`.

The proof proceeds as follows:
- `ofFieldOp_mul_normalOrder_ofFieldOpList_eq_sum` is used to expand `φ 𝓝([φsΛ]ᵘᶜ)` as
  a sum over `k` in `Option φsΛ.uncontracted` of terms involving `[anPart φ, φs[k]]ₛ`.
- Then `staticWickTerm_insert_zero_none` and `staticWickTerm_insert_zero_some` are
  used to equate terms.
-/
lemma mul_staticWickTerm_eq_sum (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) :
    ofFieldOp φ * φsΛ.staticWickTerm =
    ∑ (k : Option φsΛ.uncontracted), (φsΛ ↩Λ φ 0 k).staticWickTerm := by
  trans (φsΛ.sign • φsΛ.staticContract * (ofFieldOp φ * normalOrder (ofFieldOpList [φsΛ]ᵘᶜ)))
  · have ht := Subalgebra.mem_center_iff.mp (Subalgebra.smul_mem (Subalgebra.center ℂ _)
      (φsΛ.staticContract).2 φsΛ.sign)
    conv_rhs => rw [← mul_assoc, ← ht]
    simp [mul_assoc, staticWickTerm]
  rw [ofFieldOp_mul_normalOrder_ofFieldOpList_eq_sum]
  rw [Finset.mul_sum]
  rw [uncontractedFieldOpEquiv_list_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  match n with
  | none =>
    simp only [contractStateAtIndex, uncontractedFieldOpEquiv, Equiv.optionCongr_apply,
      Equiv.coe_trans, Option.map_none, one_mul, Algebra.smul_mul_assoc, Nat.succ_eq_add_one,
      Fin.val_zero, List.insertIdx_zero]
    rw [staticWickTerm_insert_zero_none]
    simp only [Algebra.smul_mul_assoc]
    rfl
  | some n =>
    simp only [Algebra.smul_mul_assoc, Nat.succ_eq_add_one, Fin.val_zero,
      List.insertIdx_zero]
    rw [staticWickTerm_insert_zero_some]

end
end WickContraction
