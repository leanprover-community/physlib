/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import Physlib.QuantumMechanics.HilbertSpaces.Qubit.Basic
public import Physlib.QuantumMechanics.HilbertSpaces.FiniteTarget.Operators
public import Physlib.Mathematics.ForMathlib.Unitary
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!

# Single-qubit gates

## i. Overview

The standard single-qubit gates as bounded operators on `Qubit`: the Pauli gates `X`, `Y`, `Z`,
the Hadamard gate and the phase gates `S` and `T`. Each gate is the image of its matrix in the
standard basis under `FiniteHilbertSpace.toOperator`. The relations between the gates are proved
on the matrices and transferred to the operators.

## ii. Key results

- `Qubit.pauliX`, `pauliY`, `pauliZ`, `hadamard`, `phaseS`, `phaseT` : the gates.
- `Qubit.pauliX_mul_self` and the other squares :
  `X² = Y² = Z² = H² = 1`, `S² = Z`, `T² = S`.
- `Qubit.pauliX_mul_pauliY` and the other anticommutators of the Pauli gates.
- `Qubit.hadamard_mul_pauliX`, `hadamard_mul_pauliZ` : `H X = Z H`, `H Z = X H`.
- `Qubit.isSelfAdjoint_pauliX` and the others : `X`, `Y`, `Z`, `H` are self-adjoint.
- `Qubit.pauliX_mem_unitary` and the others : all six gates are unitary.

## iii. Table of contents

- A. The gates
- B. Products of gates
- C. Self-adjointness and unitarity

## iv. References

* M. A. Nielsen, I. L. Chuang, *Quantum Computation and Quantum Information*, Section 4.2.

-/

@[expose] public section

namespace QuantumMechanics

namespace Qubit

open FiniteHilbertSpace Complex

/-!

## A. The gates

-/

/-- The Pauli `X` gate. -/
noncomputable def pauliX : 𝓑(Qubit) := toOperator !![0, 1; 1, 0]

/-- The Pauli `Y` gate. -/
noncomputable def pauliY : 𝓑(Qubit) := toOperator !![0, -I; I, 0]

/-- The Pauli `Z` gate. -/
noncomputable def pauliZ : 𝓑(Qubit) := toOperator !![1, 0; 0, -1]

/-- The Hadamard gate. -/
noncomputable def hadamard : 𝓑(Qubit) :=
  toOperator !![(Real.sqrt 2 : ℂ)⁻¹, (Real.sqrt 2 : ℂ)⁻¹;
    (Real.sqrt 2 : ℂ)⁻¹, -(Real.sqrt 2 : ℂ)⁻¹]

/-- The phase gate `S`. -/
noncomputable def phaseS : 𝓑(Qubit) := toOperator !![1, 0; 0, I]

/-- The phase gate `T`. -/
noncomputable def phaseT : 𝓑(Qubit) := toOperator !![1, 0; 0, exp (Real.pi / 4 * I)]

/-!

## B. Products of gates

-/

lemma pauliX_mul_self : pauliX * pauliX = 1 := by
  rw [pauliX, ← map_mul toOperator, ← map_one toOperator]
  congr 1; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

lemma pauliY_mul_self : pauliY * pauliY = 1 := by
  rw [pauliY, ← map_mul toOperator, ← map_one toOperator]
  congr 1; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

lemma pauliZ_mul_self : pauliZ * pauliZ = 1 := by
  rw [pauliZ, ← map_mul toOperator, ← map_one toOperator]
  congr 1; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

lemma hadamard_mul_self : hadamard * hadamard = 1 := by
  rw [hadamard, ← map_mul toOperator, ← map_one toOperator]
  congr 1; ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, ← mul_inv, ← ofReal_mul] <;> norm_num

lemma phaseS_mul_self : phaseS * phaseS = pauliZ := by
  rw [phaseS, pauliZ, ← map_mul toOperator]
  congr 1; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

lemma phaseT_mul_self : phaseT * phaseT = phaseS := by
  rw [phaseT, phaseS, ← map_mul toOperator]
  congr 1; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, ← exp_add]
  rw [show (Real.pi : ℂ) / 4 * I + Real.pi / 4 * I = Real.pi / 2 * I by ring,
    exp_pi_div_two_mul_I]

lemma pauliX_mul_pauliY : pauliX * pauliY = -(pauliY * pauliX) := by
  rw [pauliX, pauliY, ← map_mul toOperator, ← map_mul toOperator, ← map_neg toOperator]
  congr 1; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

lemma pauliZ_mul_pauliY : pauliZ * pauliY = -(pauliY * pauliZ) := by
  rw [pauliZ, pauliY, ← map_mul toOperator, ← map_mul toOperator, ← map_neg toOperator]
  congr 1; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

lemma pauliZ_mul_pauliX : pauliZ * pauliX = -(pauliX * pauliZ) := by
  rw [pauliZ, pauliX, ← map_mul toOperator, ← map_mul toOperator, ← map_neg toOperator]
  congr 1; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

lemma hadamard_mul_pauliX : hadamard * pauliX = pauliZ * hadamard := by
  rw [hadamard, pauliX, pauliZ, ← map_mul toOperator, ← map_mul toOperator]
  congr 1; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

lemma hadamard_mul_pauliZ : hadamard * pauliZ = pauliX * hadamard := by
  rw [hadamard, pauliZ, pauliX, ← map_mul toOperator, ← map_mul toOperator]
  congr 1; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

lemma pauliZ_mul_phaseS : pauliZ * phaseS = phaseS * pauliZ := by
  rw [pauliZ, phaseS, ← map_mul toOperator, ← map_mul toOperator]
  congr 1; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

lemma pauliZ_mul_phaseT : pauliZ * phaseT = phaseT * pauliZ := by
  rw [pauliZ, phaseT, ← map_mul toOperator, ← map_mul toOperator]
  congr 1; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

lemma phaseS_mul_phaseT : phaseS * phaseT = phaseT * phaseS := by
  rw [phaseS, phaseT, ← map_mul toOperator, ← map_mul toOperator]
  congr 1; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, mul_comm]

/-!

## C. Self-adjointness and unitarity

-/

lemma isSelfAdjoint_pauliX : IsSelfAdjoint pauliX :=
  IsSelfAdjoint.map toOperator (by ext i j; fin_cases i <;> fin_cases j <;> simp)

lemma isSelfAdjoint_pauliY : IsSelfAdjoint pauliY :=
  IsSelfAdjoint.map toOperator (by ext i j; fin_cases i <;> fin_cases j <;> simp)

lemma isSelfAdjoint_pauliZ : IsSelfAdjoint pauliZ :=
  IsSelfAdjoint.map toOperator (by ext i j; fin_cases i <;> fin_cases j <;> simp)

lemma isSelfAdjoint_hadamard : IsSelfAdjoint hadamard :=
  IsSelfAdjoint.map toOperator
    (by ext i j; fin_cases i <;> fin_cases j <;> simp [← ofReal_inv])

lemma pauliX_mem_unitary : pauliX ∈ unitary 𝓑(Qubit) :=
  isSelfAdjoint_pauliX.mem_unitary_of_mul_self pauliX_mul_self

lemma pauliY_mem_unitary : pauliY ∈ unitary 𝓑(Qubit) :=
  isSelfAdjoint_pauliY.mem_unitary_of_mul_self pauliY_mul_self

lemma pauliZ_mem_unitary : pauliZ ∈ unitary 𝓑(Qubit) :=
  isSelfAdjoint_pauliZ.mem_unitary_of_mul_self pauliZ_mul_self

lemma hadamard_mem_unitary : hadamard ∈ unitary 𝓑(Qubit) :=
  isSelfAdjoint_hadamard.mem_unitary_of_mul_self hadamard_mul_self

lemma phaseS_mem_unitary : phaseS ∈ unitary 𝓑(Qubit) :=
  Unitary.map_mem toOperator (by
    rw [Unitary.mem_iff, Matrix.star_eq_conjTranspose]
    constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply])

lemma phaseT_mem_unitary : phaseT ∈ unitary 𝓑(Qubit) :=
  Unitary.map_mem toOperator (by
    rw [Unitary.mem_iff, Matrix.star_eq_conjTranspose]
    constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Complex.mul_conj', Complex.conj_mul', Complex.norm_exp])

end Qubit

end QuantumMechanics
