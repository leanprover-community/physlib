/-
Copyright (c) 2026 Samyak Rai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samyak Rai
-/

module

public import Mathlib.Data.ZMod.Basic
public import Physlib.Relativity.PauliMatrices.Basic

/-!

# Pauli groups

The single-qubit Pauli group in its binary symplectic representation.

## i. Overview

The single-qubit Pauli group is a 16-element matrix group, consisting of the four Pauli
matrices, including the identity, each with four possible phase factors. A single-qubit Pauli
operator is recorded by a phase `p : ZMod 4`, contributing the factor `i^p`, and two bits
`x` and `z`: the operator carries an `X` when `x = 1` and a `Z` when `z = 1`, so it carries a
`Y` when both are `1`. This is the definition `PauliGroup.single`.

Two single-qubit Pauli operators commute exactly when their symplectic product, which does not
depend on the phases, is zero. This is recorded by `PauliGroup.symplecticSingle` and proved in
`PauliGroup.single_commute_iff`.

## ii. Key results

- `PauliGroup.single` : the single-qubit Pauli operator `i^p X^x Z^z` for phase `p` and bits
  `x` and `z`.
- `PauliGroup.symplecticSingle` : the symplectic product of two single-qubit Pauli operators.
- `PauliGroup.single_commute_iff` : two single-qubit Pauli operators commute if and only if
  their symplectic product is zero.

## iii. Table of contents

- A. The single-qubit Pauli operators
- B. The symplectic product

## iv. References

- [Pauli group, Wikipedia](https://en.wikipedia.org/wiki/Pauli_group)
- [Nielsen and Chuang, Quantum Computation and Quantum Information][nielsen_chuang_qci]

## A. The single-qubit Pauli operators

-/

@[expose] public section

open PauliMatrix
open KroneckerDelta

namespace PauliGroup

/-- The single-qubit Pauli operator `i^p X^x Z^z`, for phase `p` and bits `x` and `z`.
As `p : ZMod 4`, `x : ZMod 2` and `z : ZMod 2` range over their values, these are the
16 elements of the one-qubit Pauli group. -/
def single (p : ZMod 4) (x z : ZMod 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  Complex.I ^ p.val • (σ1 ^ x.val * σ3 ^ z.val)

/-!

## B. The symplectic product

-/

/-- The symplectic product of two elements `(x, z)` and `(x', z')` of `(ℤ/2ℤ)²`:
`(x, z) ⊙ (x', z') = z x' - x z'`.
The bits record the presence of an `X` and a `Z` factor, as in `PauliGroup.single`. -/
def symplecticSingle (x z x' z' : ZMod 2) : ZMod 2 :=
  z * x' - x * z'

/-- A generic criterion: if two matrices differ in a single entry after multiplication in the
two possible orders, they do not commute. -/
private lemma not_commute_of_entry_ne {A B : Matrix (Fin 2) (Fin 2) ℂ} {i j : Fin 2}
    (h : (A * B) i j ≠ (B * A) i j) : ¬ Commute A B := by
  intro hcomm
  rw [commute_iff_eq] at hcomm
  exact h (congrArg (fun M => M i j) hcomm)

private lemma iff_of_true {P Q : Prop} (hQ : Q) (hP : P) : P ↔ Q :=
  ⟨fun _ => hQ, fun _ => hP⟩

private lemma iff_of_false {P Q : Prop} (hQ : ¬ Q) (hP : ¬ P) : P ↔ Q :=
  ⟨fun h => (hP h).elim, fun h => (hQ h).elim⟩

/-- The symplectic product vanishes exactly when the corresponding Pauli matrices commute. -/
private lemma commute_pauli_iff (x z x' z' : ZMod 2) :
    Commute (σ1 ^ x.val * σ3 ^ z.val) (σ1 ^ x'.val * σ3 ^ z'.val) ↔
      symplecticSingle x z x' z' = 0 := by
  have hbits : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have hval0 : (0 : ZMod 2).val = 0 := rfl
  have hval1 : (1 : ZMod 2).val = 1 := rfl
  rcases hbits x with rfl | rfl <;>
    rcases hbits z with rfl | rfl <;>
    rcases hbits x' with rfl | rfl <;>
    rcases hbits z' with rfl | rfl <;>
    simp only [hval0, hval1, pow_zero, pow_one, one_mul, mul_one, symplecticSingle,
      mul_zero, sub_self, sub_zero] <;>
    first
      | exact iff_of_true (by decide) (Commute.refl _)
      | exact iff_of_true (by decide) (Commute.one_left _)
      | exact iff_of_true (by decide) (Commute.one_right _)
      | exact iff_of_false (by decide)
          (not_commute_of_entry_ne (A := σ1) (B := σ3) (i := 0) (j := 1)
            (by norm_num [pauliMatrix]))
      | exact iff_of_false (by decide)
          (fun h => (not_commute_of_entry_ne (A := σ3) (B := σ1) (i := 0) (j := 1)
            (by norm_num [pauliMatrix])) h)
      | exact iff_of_false (by decide)
          (not_commute_of_entry_ne (A := σ1) (B := σ1 * σ3) (i := 0) (j := 0)
            (by norm_num [pauliMatrix]))
      | exact iff_of_false (by decide)
          (fun h => (not_commute_of_entry_ne (A := σ1 * σ3) (B := σ1) (i := 0) (j := 0)
            (by norm_num [pauliMatrix])) h)
      | exact iff_of_false (by decide)
          (not_commute_of_entry_ne (A := σ3) (B := σ1 * σ3) (i := 0) (j := 1)
            (by norm_num [pauliMatrix]))
      | exact iff_of_false (by decide)
          (fun h => (not_commute_of_entry_ne (A := σ1 * σ3) (B := σ3) (i := 0) (j := 1)
            (by norm_num [pauliMatrix])) h)

/-- Phases do not affect commutation. -/
private lemma commute_single_iff (p q : ZMod 4) (x z x' z' : ZMod 2) :
    Commute (single p x z) (single q x' z') ↔
      Commute (σ1 ^ x.val * σ3 ^ z.val) (σ1 ^ x'.val * σ3 ^ z'.val) := by
  simp only [single]
  rw [Commute.smul_left_iff₀ (pow_ne_zero p.val Complex.I_ne_zero),
    Commute.smul_right_iff₀ (pow_ne_zero q.val Complex.I_ne_zero)]

/-- Two single-qubit Pauli operators commute if and only if their symplectic product is
zero. -/
lemma single_commute_iff (p q : ZMod 4) (x z x' z' : ZMod 2) :
    Commute (single p x z) (single q x' z') ↔ symplecticSingle x z x' z' = 0 := by
  rw [commute_single_iff, commute_pauli_iff]

end PauliGroup
