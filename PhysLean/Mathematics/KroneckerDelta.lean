/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Data.Fintype.Card
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

lemma kroneckerDelta_self (i : α) : δ[i,i] = 1 := if_pos rfl

lemma kroneckerDelta_diff {i j : α} (h : i ≠ j) : δ[i,j] = 0 := if_neg h

/-!
### Conditions for nsmul to vanish
-/

lemma nsmul_of_eq_zero [AddMonoid M] (i j : α) {f : α → α → M} (hf : f i i = 0) :
    δ[i,j] • f i j = 0 := by
  rcases eq_or_ne i j with (rfl | hne)
  · exact smul_eq_zero_of_right _ hf
  · exact smul_eq_zero_of_left (kroneckerDelta_diff hne) _

lemma nsmul_eq_zero_iff [AddMonoid M] (i j : α) (f : α → α → M) :
    δ[i,j] • f i j = 0 ↔ i ≠ j ∨ f i i = 0 := by
  rcases eq_or_ne i j with (rfl | hne)
  · simp [kroneckerDelta_self, one_nsmul]
  · simp [kroneckerDelta_diff, hne]

lemma nsmul_eq_zero_iff' [AddMonoid M] (i : α) (f : α → α → M) :
    (∀ j : α, δ[i,j] • f i j = 0) ↔ f i i = 0 := by
  refine ⟨?_, fun hf j ↦ nsmul_of_eq_zero i j hf⟩
  intro h
  have hδf : δ[i,i] • f i i = 0 := h i
  rwa [kroneckerDelta_self, one_nsmul] at hδf

lemma nsmul_eq_zero_iff'' [AddMonoid M] (f : α → α → M) :
    (∀ i j : α, δ[i,j] • f i j = 0) ↔ ∀ i : α, f i i = 0 :=
  forall_congr' fun j ↦ nsmul_eq_zero_iff' j f

/-!
### Symmetrization
-/

lemma symm (i j : α) : δ[i,j] = δ[j,i] := ite_cond_congr <| Eq.propIntro Eq.symm Eq.symm

lemma nsmul_symm [AddMonoid M] (i j : α) (f : α → α → M) : δ[i,j] • f j i = δ[i,j] • f i j := by
  rcases eq_or_ne i j with (rfl | hne)
  · rfl
  · simp only [kroneckerDelta_diff hne, zero_nsmul]

lemma symmetrize [AddMonoid M] (i j : α) (f : α → α → M) :
    (2 * δ[i,j]) • f i j = δ[i,j] • (f i j + f j i) := by
  rcases eq_or_ne i j with (rfl | hne)
  · simp [kroneckerDelta_self, one_nsmul, two_nsmul]
  · simp [kroneckerDelta_diff hne]

lemma symmetrize' [AddCommMonoid M] {K : Type*} [Semifield K] [CharZero K] [Module K M]
    (i j : α) (f : α → α → M) : δ[i,j] • f i j = δ[i,j] • (2 : K)⁻¹ • (f i j + f j i) := by
  rcases eq_or_ne i j with (rfl | hne)
  · simp only [kroneckerDelta_self, one_nsmul, ← two_smul K, smul_smul]
    rw [inv_mul_cancel₀ (OfNat.zero_ne_ofNat 2).symm, one_smul]
  · simp [kroneckerDelta_diff hne]

@[simp]
lemma nsmul_sub_eq_zero [AddGroup M] (i j : α) (f : α → α → M) : δ[i,j] • (f i j - f j i) = 0 := by
  rcases eq_or_ne i j with (rfl | hne)
  · exact smul_eq_zero_of_right _ (sub_self <| f i i)
  · exact smul_eq_zero_of_left (kroneckerDelta_diff hne) _

/-!
### Sums
-/

section Sums
open Finset Fintype

variable [Fintype α] [AddCommMonoid M]

@[simp]
lemma sum_mul (i j : α) : ∑ k : α, δ[i,k] * δ[k,j] = δ[i,j] := by
  dsimp [kroneckerDelta]
  simp

@[simp]
lemma sum_nsmul (i : α) (f : α → M) : ∑ j : α, δ[i,j] • f j = f i := by
  dsimp [kroneckerDelta]
  simp [one_nsmul]

lemma sum_sum_nsmul_eq_zero {f : α → α → M} (hf : ∀ i : α, f i i = 0) :
    ∑ i : α, ∑ j : α, δ[i,j] • f i j = 0 := by
  simp only [sum_nsmul, hf, sum_const_zero]

end Sums

end KroneckerDelta
