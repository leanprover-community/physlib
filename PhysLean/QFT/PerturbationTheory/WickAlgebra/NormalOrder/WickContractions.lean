/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QFT.PerturbationTheory.WickAlgebra.NormalOrder.Lemmas
import PhysLean.QFT.PerturbationTheory.WickContraction.InsertAndContract
/-!

# Normal ordering with relation to Wick contractions

-/

namespace FieldSpecification
open FieldOpFreeAlgebra
open PhysLean.List
open FieldStatistic
open WickContraction
namespace WickAlgebra
variable {𝓕 : FieldSpecification}

/-!

## Normal order of uncontracted terms within proto-algebra.

-/

/-- For a list `φs = φ₀…φₙ` of `𝓕.FieldOp`, a Wick contraction `φsΛ` of `φs`, an element `φ` of
  `𝓕.FieldOp`, and a `i ≤ φs.length`, then the following relation holds:

  `𝓝([φsΛ ↩Λ φ i none]ᵘᶜ) = s • 𝓝(φ :: [φsΛ]ᵘᶜ)`

  where `s` is the exchange sign for `φ` and the uncontracted fields in `φ₀…φᵢ₋₁`.

  The proof of this result ultimately is a consequence of `normalOrder_superCommute_eq_zero`.
-/
lemma normalOrder_uncontracted_none (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (i : Fin φs.length.succ) (φsΛ : WickContraction φs.length) :
    𝓝(ofFieldOpList [φsΛ ↩Λ φ i none]ᵘᶜ)
    = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨φs.get, φsΛ.uncontracted.filter (fun x => i.succAbove x < i)⟩) •
    𝓝(ofFieldOpList (φ :: [φsΛ]ᵘᶜ)) := by
  simp only [Nat.succ_eq_add_one, instCommGroup.eq_1]
  rw [ofFieldOpList_normalOrder_insert φ [φsΛ]ᵘᶜ
    ⟨(φsΛ.uncontractedListOrderPos i), by simp [uncontractedListGet]⟩,
    smul_smul]
  trans (1 : ℂ) • (𝓝(ofFieldOpList [φsΛ ↩Λ φ i none]ᵘᶜ))
  · simp
  congr 1
  simp only [instCommGroup.eq_1, uncontractedListGet]
  rw [← List.map_take, take_uncontractedListOrderPos_eq_filter]
  have h1 : (𝓕 |>ₛ List.map φs.get (List.filter (fun x => decide (↑x < i.1)) φsΛ.uncontractedList))
        = 𝓕 |>ₛ ⟨φs.get, (φsΛ.uncontracted.filter (fun x => x.val < i.1))⟩ := by
      simp only [Nat.succ_eq_add_one, ofFinset]
      congr
      rw [uncontractedList_eq_sort]
      have hdup : (List.filter (fun x => decide (x.1 < i.1))
          (φsΛ.uncontracted.sort (fun x1 x2 => x1 ≤ x2))).Nodup := by
        exact List.Nodup.filter _ (φsΛ.uncontracted.sort_nodup (fun x1 x2 => x1 ≤ x2))
      have hsort : (List.filter (fun x => decide (x.1 < i.1))
          (φsΛ.uncontracted.sort (fun x1 x2 => x1 ≤ x2))).Pairwise (· ≤ ·) := by
        exact List.Pairwise.filter _ (φsΛ.uncontracted.pairwise_sort (fun x1 x2 => x1 ≤ x2))
      rw [← (List.toFinset_sort (· ≤ ·) hdup).mpr hsort]
      congr
      ext a
      simp
  rw [h1]
  simp only [Nat.succ_eq_add_one]
  have h2 : (Finset.filter (fun x => x.1 < i.1) φsΛ.uncontracted) =
    (Finset.filter (fun x => i.succAbove x < i) φsΛ.uncontracted) := by
    ext a
    simp only [Nat.succ_eq_add_one, Finset.mem_filter, and_congr_right_iff]
    intro ha
    simp only [Fin.succAbove]
    split
    · apply Iff.intro
      · intro h
        omega
      · intro h
        rename_i h
        rw [Fin.lt_def] at h
        simp only [Fin.val_castSucc] at h
        omega
    · apply Iff.intro
      · intro h
        rename_i h'
        rw [Fin.lt_def]
        simp only [Fin.val_succ]
        rw [Fin.lt_def] at h'
        simp only [Fin.val_castSucc, not_lt] at h'
        omega
      · intro h
        rename_i h
        rw [Fin.lt_def] at h
        simp only [Fin.val_succ] at h
        omega
  rw [h2]
  simp only [exchangeSign_mul_self]
  congr
  simp only [Nat.succ_eq_add_one]
  rw [insertAndContract_uncontractedList_none_map]

/--
  For a list `φs = φ₀…φₙ` of `𝓕.FieldOp`, a Wick contraction `φsΛ` of `φs`, an element `φ` of
  `𝓕.FieldOp`, a `i ≤ φs.length` and a `k` in `φsΛ.uncontracted`, then
  `𝓝([φsΛ ↩Λ φ i (some k)]ᵘᶜ)` is equal to the normal ordering of `[φsΛ]ᵘᶜ` with the `𝓕.FieldOp`
  corresponding to `k` removed.

  The proof of this result ultimately is a consequence of definitions.
-/
lemma normalOrder_uncontracted_some (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (i : Fin φs.length.succ) (φsΛ : WickContraction φs.length) (k : φsΛ.uncontracted) :
    𝓝(ofFieldOpList [φsΛ ↩Λ φ i (some k)]ᵘᶜ)
    = 𝓝(ofFieldOpList (optionEraseZ [φsΛ]ᵘᶜ φ ((uncontractedFieldOpEquiv φs φsΛ) k))) := by
  simp only [Nat.succ_eq_add_one, insertAndContract, optionEraseZ, uncontractedFieldOpEquiv,
    Equiv.optionCongr_apply, Equiv.coe_trans, Option.map_some, Function.comp_apply, finCongr_apply,
    Fin.val_cast, uncontractedListGet]
  congr
  rw [congr_uncontractedList]
  erw [uncontractedList_extractEquiv_symm_some]
  simp only [Fin.coe_succAboveEmb, List.map_eraseIdx, List.map_map]
  congr 1
  conv_rhs => rw [get_eq_insertIdx_succAbove φ φs i]

end WickAlgebra
end FieldSpecification
