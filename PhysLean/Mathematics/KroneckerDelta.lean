/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Data.Finset.Disjoint
/-!

# Kronecker delta

This module defines the Kronecker delta.

-/

namespace KroneckerDelta

variable {α M : Type*} [DecidableEq α]

/-- The Kronecker delta function, `ite (i = j) 1 0`. -/
def kroneckerDelta (i j : α) : ℕ := if i = j then 1 else 0

@[inherit_doc]
notation "δ[" i "," j "]" => kroneckerDelta i j

@[simp]
lemma eq_one_of_same (i : α) : δ[i,i] = 1 := if_pos rfl

lemma eq_zero_of_ne {i j : α} (h : i ≠ j) : δ[i,j] = 0 := if_neg h

@[simp]
lemma eq_of_coe {p : α → Prop} (i j : Subtype p) : δ[(i : α),j] = δ[i,j] := by
  rcases eq_or_ne i j with (rfl | hne)
  · repeat rw [eq_one_of_same]
  · rw [eq_zero_of_ne hne, eq_zero_of_ne <| Subtype.coe_ne_coe.mpr hne]

lemma eq_zero_of_not {p : α → Prop} {i j : α} (hi : ¬p i) (hj : p j) : δ[i,j] = 0 := by
  dsimp [kroneckerDelta]
  rw [ite_cond_eq_false]
  apply eq_false'
  intro h
  rw [h] at hi
  exact hi hj

/-!
### Conditions for smul to vanish
-/

lemma smul_of_eq_zero [AddMonoid M] (i j : α) {f : α → α → M} (hf : f i i = 0) :
    δ[i,j] • f i j = 0 := by
  rcases eq_or_ne i j with (rfl | hne)
  · exact smul_eq_zero_of_right _ hf
  · exact smul_eq_zero_of_left (eq_zero_of_ne hne) _

lemma smul_eq_zero_iff [AddMonoid M] (i j : α) (f : α → α → M) :
    δ[i,j] • f i j = 0 ↔ i ≠ j ∨ f i i = 0 := by
  rcases eq_or_ne i j with (rfl | hne)
  · simp [one_nsmul]
  · simp [eq_zero_of_ne, hne]

lemma smul_eq_zero_iff' [AddMonoid M] (i : α) (f : α → α → M) :
    (∀ j : α, δ[i,j] • f i j = 0) ↔ f i i = 0 := by
  refine ⟨?_, fun hf j ↦ smul_of_eq_zero i j hf⟩
  intro h
  have hδf : δ[i,i] • f i i = 0 := h i
  rwa [eq_one_of_same, one_nsmul] at hδf

lemma smul_eq_zero_iff'' [AddMonoid M] (f : α → α → M) :
    (∀ i j : α, δ[i,j] • f i j = 0) ↔ ∀ i : α, f i i = 0 :=
  forall_congr' fun j ↦ smul_eq_zero_iff' j f

/-!
### Symmetrization
-/

lemma symm (i j : α) : δ[i,j] = δ[j,i] := ite_cond_congr <| Eq.propIntro Eq.symm Eq.symm

lemma smul_symm [AddMonoid M] (i j : α) (f : α → α → M) : δ[i,j] • f j i = δ[i,j] • f i j := by
  rcases eq_or_ne i j with (rfl | hne)
  · rfl
  · simp only [eq_zero_of_ne hne, zero_smul]

lemma symmetrize [AddMonoid M] (i j : α) (f : α → α → M) :
    δ[i,j] • (f i j + f j i) = (2 * δ[i,j]) • f i j := by
  rcases eq_or_ne i j with (rfl | hne)
  · simp [one_nsmul, two_nsmul]
  · simp [eq_zero_of_ne hne]

lemma symmetrize' [AddCommMonoid M] {K : Type*} [Semifield K] [CharZero K] [Module K M]
    (i j : α) (f : α → α → M) : δ[i,j] • (2 : K)⁻¹ • (f i j + f j i) = δ[i,j] • f i j := by
  rcases eq_or_ne i j with (rfl | hne)
  · simp only [eq_one_of_same, one_nsmul, ← two_smul K, smul_smul]
    rw [inv_mul_cancel₀ (OfNat.zero_ne_ofNat 2).symm, one_smul]
  · simp [eq_zero_of_ne hne]

@[simp]
lemma smul_sub_eq_zero [AddGroup M] (i j : α) (f : α → α → M) : δ[i,j] • (f i j - f j i) = 0 := by
  rcases eq_or_ne i j with (rfl | hne)
  · exact smul_eq_zero_of_right _ (sub_self <| f i i)
  · exact smul_eq_zero_of_left (eq_zero_of_ne hne) _

/-!
### Sums
-/

section Sums
open Finset

variable [AddCommMonoid M]

@[simp]
lemma sum_mul [Fintype α] (i j : α) : ∑ k : α, δ[i,k] * δ[k,j] = δ[i,j] := by
  dsimp [kroneckerDelta]
  simp

@[simp]
lemma sum_smul [Fintype α] (i : α) (f : α → M) : ∑ j : α, δ[i,j] • f j = f i := by
  dsimp [kroneckerDelta]
  simp [one_nsmul]

lemma sum_sum_smul_eq_zero [Fintype α] {f : α → α → M} (hf : ∀ i : α, f i i = 0) :
    ∑ i : α, ∑ j : α, δ[i,j] • f i j = 0 := by
  simp only [sum_smul, hf, sum_const_zero]

lemma finset_sum_smul (s : Finset α) (i : α) (f : α → M) :
    ∑ j ∈ s, δ[i,j] • f j = if i ∈ s then f i else 0 := by
  by_cases h : i ∈ s
  · simp only [h, ite_cond_eq_true]
    rw [← sum_coe_sort]
    trans ∑ j : s, δ[⟨i, h⟩,j] • f j
    · simp only [← eq_of_coe]
    exact sum_smul _ _
  · simp only [h, ↓reduceIte]
    rw [← sum_coe_sort]
    conv_lhs =>
      enter [2, j]
      rw [eq_zero_of_not h j.2, zero_smul]
    exact sum_const_zero

lemma finset_sum_sum_smul (s s' : Finset α) (f : α → α → M) :
    ∑ i ∈ s, ∑ j ∈ s', δ[(i : α),j] • f i j = ∑ i ∈ s ∩ s', f i i := by
  simp only [finset_sum_smul, Finset.sum_ite_mem]

lemma finset_sum_sum_smul_of_disjoint {s s' : Finset α} (h : Disjoint s s') (f : α → α → M) :
    ∑ i ∈ s, ∑ j ∈ s', δ[i,j] • f i j = 0 := by
  simp only [finset_sum_sum_smul]
  rw [disjoint_iff_inter_eq_empty.mp h, sum_empty]

lemma finset_sum_sum_smul_eq_zero {s s' : Finset α} {f : α → α → M}
    (hf : ∀ i ∈ s ∩ s', f i i = 0) : ∑ i ∈ s, ∑ j ∈ s', δ[i,j] • f i j = 0 := by
  simp only [finset_sum_sum_smul]
  rw [← sum_coe_sort]
  simp [hf]

end Sums

end KroneckerDelta
