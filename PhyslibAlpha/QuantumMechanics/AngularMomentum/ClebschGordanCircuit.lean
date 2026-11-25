/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.QuantumMechanics.AngularMomentum.ClebschGordanCoefficients
public import QuantumInfo.States.Pure.Qubit

/-!

# A two-qubit circuit for the Clebsch–Gordan coefficients of two spins ½

The change of basis from the product basis to the coupled basis of two spins `1/2` as a
two-qubit circuit.

## i. Overview

A spin `1/2` is a qubit with `|↑⟩ = |0⟩` and `|↓⟩ = |1⟩`. The product basis of two spins is
indexed by `Qubit × Qubit`, in the order `|00⟩, |01⟩, |10⟩, |11⟩ = |↑↑⟩, |↑↓⟩, |↓↑⟩, |↓↓⟩`; the
first qubit is the first spin. The coupled basis is indexed by `Qubit × Qubit` as well, the
columns `(0,0), (0,1), (1,0), (1,1)` being the triplet states `|1, 1⟩, |1, 0⟩, |1, -1⟩` and the
singlet `|0, 0⟩`. The matrix `cgMatrix` of the change of basis has the Clebsch–Gordan
coefficients `cgCoefficient 1 1 k l a b` of `ClebschGordanCoefficients` as entries, with
Condon–Shortley phases.

It is the matrix of the circuit which first applies a Hadamard gate to the first qubit
controlled by the second (`CH21`), then the CNOT gate with the first qubit as control:
`CNOT * CH21 = cgMatrix` (`cnot_mul_CH21`). In particular `cgMatrix` is unitary
(`cgMatrix_mem_unitaryGroup`).

## ii. Key results

- `cgMatrix`: the Clebsch–Gordan matrix of two spins `1/2`.
- `CH21`: the controlled Hadamard gate with the second qubit as control.
- `cnot_mul_CH21`: the circuit `CNOT * CH21` is the Clebsch–Gordan matrix.
- `cgMatrix_mem_unitaryGroup`: the Clebsch–Gordan matrix is unitary.

## iii. Table of contents

- A. The Clebsch–Gordan matrix and the circuit

## iv. References

- The Clebsch–Gordan coefficients and their phase convention are those of
  `ClebschGordanCoefficients`; the gates are those of `QuantumInfo.States.Pure.Qubit`.

## A. The Clebsch–Gordan matrix and the circuit

-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Sl2

open Qubit

/-- The label `k` of the coupled state in column `q`: `0` for the triplet, `1` for the singlet
`q = (1, 1)`. -/
def cgK (q : Qubit × Qubit) : ℕ := if q = (1, 1) then 1 else 0

/-- The label `l = J - M` of the coupled state in column `q`: the columns `(0,0), (0,1), (1,0)`
are the triplet states with `M = 1, 0, -1`, the column `(1,1)` the singlet. -/
def cgL (q : Qubit × Qubit) : ℕ := ![![0, 1], ![2, 0]] q.1 q.2

/-- The Clebsch–Gordan matrix of two spins `1/2`: the entry in row `(a, b)` and column `q` is
`⟨½ m₁ ½ m₂ | J M⟩` with `m₁ = ½ - a`, `m₂ = ½ - b` and `J, M` given by `cgK q`, `cgL q`. -/
def cgMatrix : Matrix (Qubit × Qubit) (Qubit × Qubit) ℂ :=
  Matrix.of fun p q => (cgCoefficient 1 1 (cgK q) (cgL q) p.1 p.2 : ℂ)

/-- The Hadamard gate on the first qubit controlled by the second qubit. -/
def CH21 : Matrix (Qubit × Qubit) (Qubit × Qubit) ℂ :=
  Matrix.reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _) (C[H]).val

/-- The circuit `CH21` followed by `CNOT` is the Clebsch–Gordan matrix of two spins `1/2`. -/
lemma cnot_mul_CH21 : CNOT.val * CH21 = cgMatrix := by
  have h0 : ∀ {k l a b : ℕ}, k ≤ 1 → a + b ≠ k + l → cgCoefficient 1 1 k l a b = 0 :=
    fun hk h => cgCoefficient_eq_zero_of_ne (by norm_num) hk hk h
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [CH21, cgMatrix, cgK, cgL, CNOT, X, H, Matrix.mul_apply, Fintype.sum_prod_type,
      cgCoefficient_stretched, cgCoefficient_singlet_up, cgCoefficient_singlet_down,
      cgCoefficient_triplet_zero_up, cgCoefficient_triplet_zero_down,
      cgCoefficient_triplet_minus, h0, neg_div]

/-- `CH21` is unitary, as a reindexing of the unitary `C[H]`. -/
lemma CH21_mem_unitaryGroup : CH21 ∈ Matrix.unitaryGroup (Qubit × Qubit) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, CH21, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_reindex, ← Matrix.coe_reindexAlgEquiv ℂ ℂ, ← map_mul,
    ← Matrix.star_eq_conjTranspose, (C[H]).2.2, map_one]

/-- The Clebsch–Gordan matrix of two spins `1/2` is unitary. -/
lemma cgMatrix_mem_unitaryGroup : cgMatrix ∈ Matrix.unitaryGroup (Qubit × Qubit) ℂ := by
  rw [← cnot_mul_CH21]
  exact Submonoid.mul_mem _ CNOT.2 CH21_mem_unitaryGroup

end PhyslibAlpha.Sl2
