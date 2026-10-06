/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Physlib.Relativity.PauliMatrices.Basic
/-!

# Three anticommuting matrices are the most `2 × 2` can hold

## i. Overview

A family `τ` of `2 × 2` complex matrices is anticommuting when `τ_a τ_b + τ_b τ_a = 2 δ_ab 1`:
each `τ_a` squares to `1` and two different ones anticommute. Conjugating `τ_a` by another
member reverses its sign, so every member is traceless, and the trace pairs the members with
each other and with `1` orthonormally. Together with `1` they are linearly independent in the
four dimensional space of `2 × 2` matrices, so such a family has at most three members. The
Pauli matrices `σ1, σ2, σ3` attain the bound: they are a maximal anticommuting family, one for
each axis of space.

## ii. Key results

- `IsAnticommuting` : the relation `τ_a τ_b + τ_b τ_a = 2 δ_ab 1`.
- `IsAnticommuting.trace_mul`, `IsAnticommuting.trace_eq_zero` : the trace pairing.
- `IsAnticommuting.linearIndependent` : the members together with `1` are independent.
- `IsAnticommuting.card_le_three` : an anticommuting family has at most three members.
- `isAnticommuting_pauliMatrix` : the Pauli matrices are anticommuting.
- `isGreatest_card_isAnticommuting` : the largest anticommuting family has three members.

## iii. Table of contents

- A. Anticommuting families
- B. At most three members
- C. The Pauli matrices attain the bound

## iv. References

* W. Pauli, *Zur Quantenmechanik des magnetischen Elektrons*, Z. Phys. 43 (1927) 601–623.

-/

@[expose] public section

namespace PauliMatrix

open Matrix

/-!

## A. Anticommuting families

-/

/-- A family of `2 × 2` matrices with `τ_a τ_b + τ_b τ_a = 2 δ_ab 1`. -/
def IsAnticommuting {ι : Type*} [DecidableEq ι] (τ : ι → Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  ∀ a b, τ a * τ b + τ b * τ a = (if a = b then 2 else 0 : ℂ) • 1

namespace IsAnticommuting

variable {ι : Type*} [DecidableEq ι] {τ : ι → Matrix (Fin 2) (Fin 2) ℂ} (hτ : IsAnticommuting τ)
include hτ

lemma mul_self (a : ι) : τ a * τ a = 1 := by
  have h := hτ a a
  rw [ite_eq_left rfl, ← two_smul ℂ (τ a * τ a)] at h
  exact smul_right_injective _ two_ne_zero (h.trans (by simp))

lemma mul_comm_of_ne {a b : ι} (h : a ≠ b) : τ b * τ a = -(τ a * τ b) := by
  have := hτ b a
  rw [ite_eq_right h.symm, zero_smul] at this
  exact eq_neg_of_add_eq_zero_left this

/-- The trace pairs the members orthogonally: `tr (τ_a τ_b) = 2 δ_ab`. -/
lemma trace_mul (a b : ι) : (τ a * τ b).trace = if a = b then 2 else 0 := by
  have h := congrArg trace (hτ a b)
  rw [trace_add, trace_mul_comm (τ b), trace_smul, trace_one, Fintype.card_fin] at h
  split_ifs at h ⊢ <;> push_cast at h <;> linear_combination h / 2

/-- In a family with at least two members, every member is traceless. -/
lemma trace_eq_zero {a b : ι} (hab : b ≠ a) : (τ a).trace = 0 := by
  have h : (τ b * τ a * τ b).trace = -(τ a).trace := by
    rw [hτ.mul_comm_of_ne hab.symm, neg_mul, mul_assoc, hτ.mul_self, mul_one, trace_neg]
  rw [mul_assoc, trace_mul_comm, mul_assoc, hτ.mul_self, mul_one] at h
  linear_combination h / 2

/-!

## B. At most three members

-/

/-- In a family with at least two members, the members together with `1` are linearly
independent. -/
lemma linearIndependent [Fintype ι] [Nontrivial ι] :
    LinearIndependent ℂ (fun o : Option ι => o.elim (1 : Matrix (Fin 2) (Fin 2) ℂ) τ) := by
  have htr (a : ι) : (τ a).trace = 0 := by
    obtain ⟨b, hb⟩ := exists_ne a
    exact hτ.trace_eq_zero hb
  let v : Option ι → Matrix (Fin 2) (Fin 2) ℂ := fun o => o.elim 1 τ
  have hpair (b x : Option ι) : (v b * v x).trace = if b = x then 2 else 0 := by
    cases b <;> cases x <;> simp [v, htr, hτ.trace_mul]
  refine Fintype.linearIndependent_iff.mpr fun c hc b => ?_
  have h := congrArg (fun M => (v b * M).trace) hc
  rw [Finset.mul_sum, trace_sum, mul_zero, trace_zero] at h
  change ∑ i, (v b * c i • v i).trace = 0 at h
  simp_rw [mul_smul_comm, trace_smul, hpair, smul_eq_mul, mul_ite, mul_zero] at h
  rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _)] at h
  simpa using h

/-- **An anticommuting family of `2 × 2` matrices has at most three members.** -/
theorem card_le_three [Fintype ι] : Fintype.card ι ≤ 3 := by
  by_contra hlt
  have : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have h := (hτ.linearIndependent (ι := ι)).fintype_card_le_finrank
  simp [Module.finrank_matrix] at h
  omega

end IsAnticommuting

/-!

## C. The Pauli matrices attain the bound

-/

/-- The Pauli matrices `σ1, σ2, σ3` are an anticommuting family. -/
lemma isAnticommuting_pauliMatrix : IsAnticommuting fun i : Fin 3 => pauliMatrix (Sum.inr i) :=
  fun i j => by
    rw [pauliMatrix_anticommutator, KroneckerDelta.kroneckerDelta]
    split_ifs <;> simp

/-- **The Pauli matrices are a maximal anticommuting family.** The largest anticommuting family
of `2 × 2` matrices has three members. -/
theorem isGreatest_card_isAnticommuting :
    IsGreatest {n : ℕ | ∃ τ : Fin n → Matrix (Fin 2) (Fin 2) ℂ, IsAnticommuting τ} 3 :=
  ⟨⟨_, isAnticommuting_pauliMatrix⟩, fun n ⟨_, hτ⟩ => by
    simpa using hτ.card_le_three⟩

end PauliMatrix
