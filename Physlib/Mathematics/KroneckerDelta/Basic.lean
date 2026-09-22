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
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
/-!

# Kronecker delta

## i. Overview

This module defines the Kronecker delta `kroneckerDelta i j` (notation `δ[i,j]`), equal to
`1` when `i = j` and `0` otherwise, together with its behaviour under scalar multiplication,
symmetrization, and finite sums. It also defines the `generalizedKroneckerDelta`, the
determinant of a matrix of Kronecker deltas.

## ii. Key results

- `kroneckerDelta` : the Kronecker delta on a type with decidable equality.
- `generalizedKroneckerDelta` : the determinant form `det (δ[μᵢ, νⱼ])`.

## iii. Table of contents

- A. The Kronecker delta
- B. Conditions for smul to vanish
- C. Symmetrization
- D. Sums
- E. The generalized Kronecker delta

## iv. References

* None.
-/

@[expose] public section

namespace KroneckerDelta

variable {α M : Type*} [DecidableEq α]

/-!

## A. The Kronecker delta

-/

/-- The Kronecker delta function, `ite (i = j) 1 0`. -/
def kroneckerDelta (i j : α) : ℕ := if i = j then 1 else 0

@[inherit_doc]
notation "δ[" i "," j "]" => kroneckerDelta i j

@[simp]
lemma eq_one_of_same (i : α) : δ[i,i] = 1 := ite_eq_left rfl

lemma eq_zero_of_ne {i j : α} (h : i ≠ j) : δ[i,j] = 0 := ite_eq_right h

@[simp]
lemma eq_of_coe {p : α → Prop} (i j : Subtype p) : δ[(i : α),j] = δ[i,j] := by
  rcases eq_or_ne i j with (rfl | hne)
  · repeat rw [eq_one_of_same]
  · rw [eq_zero_of_ne hne, eq_zero_of_ne <| Subtype.coe_ne_coe.mpr hne]

lemma eq_zero_of_not {p : α → Prop} {i j : α} (hi : ¬p i) (hj : p j) : δ[i,j] = 0 :=
  eq_zero_of_ne (fun h ↦ hi (h ▸ hj))

/-- The Kronecker delta is invariant under the component-index equivalence `finSumFinEquiv`. -/
lemma kroneckerDelta_finSumFinEquiv (a b : Fin 1 ⊕ Fin 3) :
    kroneckerDelta (finSumFinEquiv a) (finSumFinEquiv b) = kroneckerDelta a b := by
  simp only [kroneckerDelta, Equiv.apply_eq_iff_eq]

/-!

## B. Conditions for smul to vanish

-/

lemma smul_of_eq_zero [AddMonoid M] (i j : α) {f : α → α → M} (hf : f i i = 0) :
    δ[i,j] • f i j = 0 := by
  rcases eq_or_ne i j with (rfl | hne)
  · exact smul_eq_zero_of_right _ hf
  · exact smul_eq_zero_of_left (eq_zero_of_ne hne) _

lemma smul_eq_zero_iff [AddMonoid M] (i j : α) (f : α → α → M) :
    δ[i,j] • f i j = 0 ↔ i ≠ j ∨ f i i = 0 := by
  rcases eq_or_ne i j with (rfl | hne)
  · simp
  · simp [eq_zero_of_ne, hne]

lemma smul_eq_zero_iff' [AddMonoid M] (i : α) (f : α → α → M) :
    (∀ j : α, δ[i,j] • f i j = 0) ↔ f i i = 0 := by
  refine ⟨fun h ↦ ?_, fun hf j ↦ smul_of_eq_zero i j hf⟩
  simpa [one_nsmul] using h i

lemma smul_eq_zero_iff'' [AddMonoid M] (f : α → α → M) :
    (∀ i j : α, δ[i,j] • f i j = 0) ↔ ∀ i : α, f i i = 0 :=
  forall_congr' fun j ↦ smul_eq_zero_iff' j f

/-!

## C. Symmetrization

-/

lemma symm (i j : α) : δ[i,j] = δ[j,i] := ite_cond_congr <| Eq.propIntro Eq.symm Eq.symm

lemma smul_symm [AddMonoid M] (i j : α) (f : α → α → M) : δ[i,j] • f j i = δ[i,j] • f i j := by
  rcases eq_or_ne i j with (rfl | hne)
  · rfl
  · simp only [eq_zero_of_ne hne, zero_smul]

lemma symmetrize [AddMonoid M] (i j : α) (f : α → α → M) :
    δ[i,j] • (f i j + f j i) = (2 * δ[i,j]) • f i j := by
  rcases eq_or_ne i j with (rfl | hne)
  · simp [two_nsmul]
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

## D. Sums

-/

section Sums
open Finset

variable [AddCommMonoid M]

@[simp]
lemma sum_mul [Fintype α] (i j : α) : ∑ k : α, δ[i,k] * δ[k,j] = δ[i,j] := by
  simp [kroneckerDelta]

@[simp]
lemma sum_smul [Fintype α] (i : α) (f : α → M) : ∑ j : α, δ[i,j] • f j = f i := by
  simp [kroneckerDelta]

lemma sum_sum_smul_eq_zero [Fintype α] {f : α → α → M} (hf : ∀ i : α, f i i = 0) :
    ∑ i : α, ∑ j : α, δ[i,j] • f i j = 0 := by
  simp [sum_smul, hf, sum_const_zero]

lemma finset_sum_smul (s : Finset α) (i : α) (f : α → M) :
    ∑ j ∈ s, δ[i,j] • f j = if i ∈ s then f i else 0 := by
  simp [kroneckerDelta]

lemma finset_sum_sum_smul_eq_zero {s s' : Finset α} {f : α → α → M}
    (hf : ∀ i ∈ s ∩ s', f i i = 0) : ∑ i ∈ s, ∑ j ∈ s', δ[i,j] • f i j = 0 := by
  simp only [finset_sum_smul, Finset.sum_ite_mem]
  rw [← sum_coe_sort]
  simp [hf]

end Sums

/-!

## E. The generalized Kronecker delta

-/

section Generalized
open Matrix

/-- Integer-valued Kronecker entry via the existing `kroneckerDelta`. -/
local notation "δℤ" => (fun ρ σ => ((kroneckerDelta ρ σ : ℕ) : ℤ))

/-- Generalized Kronecker delta:
`δ^{μ₁...μₙ}_{ν₁...νₙ} = det (δ[μᵢ, νⱼ])`.

This is defined for any finite type `α` with decidable equality. -/
def generalizedKroneckerDelta {α ι : Type} [DecidableEq α]
    [DecidableEq ι] [Fintype ι]
    (μ : ι → α) (ν : ι → α) : ℤ :=
  Matrix.det (fun i j => δℤ (μ i) (ν j))

/-- Swapping two of the upper indices of the generalized Kronecker delta negates it.
This is one row transposition of the underlying determinant. -/
lemma generalizedKroneckerDelta_swap {α ι : Type} [DecidableEq α] [DecidableEq ι] [Fintype ι]
    (μ ν : ι → α) {i j : ι} (hij : i ≠ j) :
    generalizedKroneckerDelta (μ ∘ Equiv.swap i j) ν = - generalizedKroneckerDelta μ ν := by
  show (Matrix.submatrix (Matrix.of fun a b => ((kroneckerDelta (μ a) (ν b) : ℕ) : ℤ))
      (Equiv.swap i j) id).det
    = -(Matrix.of fun a b => ((kroneckerDelta (μ a) (ν b) : ℕ) : ℤ)).det
  rw [Matrix.det_permute, Equiv.Perm.sign_swap hij]
  simp

/-- Simultaneously reindexing the upper and lower slots of a generalized Kronecker delta by the
same permutation leaves it unchanged. -/
@[simp]
lemma generalizedKroneckerDelta_comp_perm {α ι : Type} [DecidableEq α] [DecidableEq ι]
    [Fintype ι] (μ ν : ι → α) (e : Equiv.Perm ι) :
    generalizedKroneckerDelta (μ ∘ e) (ν ∘ e) = generalizedKroneckerDelta μ ν := by
  show (Matrix.submatrix
      (Matrix.of fun i j => ((kroneckerDelta (μ i) (ν j) : ℕ) : ℤ)) e e).det =
    (Matrix.of fun i j => ((kroneckerDelta (μ i) (ν j) : ℕ) : ℤ)).det
  exact Matrix.det_submatrix_equiv_self e _

end Generalized

end KroneckerDelta
