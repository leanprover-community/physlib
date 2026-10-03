/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.Particles.QED.Fields
/-!
# Properties of the γ matrices

## i. Overview

The defining properties of the Dirac γ matrices of `Physlib.Particles.QED.Fields`, in
the chiral representation:

* the **Clifford algebra relation** `γ^μ γ^ν + γ^ν γ^μ = 2 η^{μν} 1`, which
  makes the Dirac operator a square root of the wave operator;
* the hermiticity properties `(γ⁰ γ^μ)† = γ⁰ γ^μ` and
  `(γ^μ)† = γ⁰ γ^μ γ⁰`, which make the Dirac Lagrangian hermitian;
* the factorisation `γ⁰ γ^μ` of the contraction matrices of the kinetic term.

This file contains no definitions, only theorems about the fields of
`Physlib.Particles.QED.Fields`.

## ii. Key results

- `JetAlgebra.gammaMatrix_mul_add_swap` : **the Clifford algebra relation**.
- `JetAlgebra.kineticGamma_eq_gammaMatrix_mul` : the contraction matrices of
  the kinetic term are `γ⁰ γ^μ`.
- `JetAlgebra.kineticGamma_conjTranspose` : the contraction matrices are
  self-adjoint.
- `JetAlgebra.gammaMatrix_conjTranspose` : `(γ^μ)† = γ⁰ γ^μ γ⁰`.

## iii. Table of contents

- A. The Pauli anticommutators
- B. The Clifford algebra relation
- C. Hermiticity

## iv. References

The γ matrices are defined in `Physlib.Particles.QED.Fields`; the Pauli matrices are
those of `Physlib.Relativity.PauliMatrices`.

-/

@[expose] public section

namespace QED

namespace JetAlgebra

open Matrix minkowskiMatrix
open scoped PauliMatrix

/-!

## A. The Pauli anticommutators

The two block identities behind the Clifford relation:
`σ^μ σ̄^ν + σ^ν σ̄^μ = 2 η^{μν} 1` and `σ̄^μ σ^ν + σ̄^ν σ^μ = 2 η^{μν} 1`,
with `σ̄^μ = η_{μμ} σ^μ` (no sum).  Both reduce to the anticommutation
relations of the Pauli matrices.

-/

lemma pauliMatrix_mul_smul_add_swap (μ ν : Fin 1 ⊕ Fin 3) :
    σ μ * (η ν ν • σ ν) + σ ν * (η μ μ • σ μ) =
      (2 * η μ ν) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  fin_cases μ <;> fin_cases ν <;>
    simp [PauliMatrix.pauliMatrix_mul_self, two_smul,
      PauliMatrix.pauliMatrix_inl_zero_eq_one]

lemma smul_pauliMatrix_mul_add_swap (μ ν : Fin 1 ⊕ Fin 3) :
    (η μ μ • σ μ) * σ ν + (η ν ν • σ ν) * σ μ =
      (2 * η μ ν) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  fin_cases μ <;> fin_cases ν <;>
    simp [PauliMatrix.pauliMatrix_mul_self, two_smul,
      PauliMatrix.pauliMatrix_inl_zero_eq_one]

/-!

## B. The Clifford algebra relation

-/

/-- **The Clifford algebra relation** of the Dirac γ matrices:
  `γ^μ γ^ν + γ^ν γ^μ = 2 η^{μν} 1`.  This is the algebraic identity that
  makes the Dirac operator a square root of the wave operator, and hence the
  Dirac equation relativistic. -/
theorem gammaMatrix_mul_add_swap (μ ν : Fin 1 ⊕ Fin 3) :
    gammaMatrix μ * gammaMatrix ν + gammaMatrix ν * gammaMatrix μ =
      (2 * η μ ν) • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ) := by
  rw [gammaMatrix, gammaMatrix, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_add,
    show ((2 * η μ ν) • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ)) =
      Matrix.fromBlocks ((2 * η μ ν) • 1) 0 0 ((2 * η μ ν) • 1) by
      rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, smul_zero]]
  congr 1
  · simpa using pauliMatrix_mul_smul_add_swap μ ν
  · simp
  · simp
  · simpa using smul_pauliMatrix_mul_add_swap μ ν

/-- The square of a γ matrix: `(γ^μ)² = η^{μμ} 1` (no sum). -/
theorem gammaMatrix_sq (μ : Fin 1 ⊕ Fin 3) :
    gammaMatrix μ * gammaMatrix μ =
      (η μ μ) • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ) := by
  rw [gammaMatrix, Matrix.fromBlocks_multiply,
    show ((η μ μ) • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ)) =
      Matrix.fromBlocks ((η μ μ) • 1) 0 0 ((η μ μ) • 1) by
      rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, smul_zero]]
  congr 1 <;> simp [PauliMatrix.pauliMatrix_mul_self]

/-- The γ matrices of distinct indices anticommute. -/
theorem gammaMatrix_anticommute {μ ν : Fin 1 ⊕ Fin 3} (h : μ ≠ ν) :
    gammaMatrix μ * gammaMatrix ν = -(gammaMatrix ν * gammaMatrix μ) := by
  have hc := gammaMatrix_mul_add_swap μ ν
  rw [off_diag_zero h] at hc
  simp only [mul_zero, zero_smul] at hc
  exact eq_neg_of_add_eq_zero_left hc

/-!

## C. Hermiticity

-/

/-- `γ⁰` in the chiral representation is the block off-diagonal identity. -/
theorem gammaMatrix_inl_zero :
    gammaMatrix (Sum.inl 0) = Matrix.fromBlocks 0 1 1 0 := by
  rw [gammaMatrix]
  simp [PauliMatrix.pauliMatrix_inl_zero_eq_one]

/-- The contraction matrices of the kinetic term are `γ⁰ γ^μ`. -/
theorem kineticGamma_eq_gammaMatrix_mul (μ : Fin 1 ⊕ Fin 3) :
    kineticGamma μ = gammaMatrix (Sum.inl 0) * gammaMatrix μ := by
  rw [kineticGamma, gammaMatrix, gammaMatrix, Matrix.fromBlocks_multiply]
  simp [PauliMatrix.pauliMatrix_inl_zero_eq_one]

/-- The contraction matrices `γ⁰ γ^μ` of the kinetic term are self-adjoint;
  this is what makes the Dirac kinetic term hermitian up to a total
  derivative. -/
theorem kineticGamma_conjTranspose (μ : Fin 1 ⊕ Fin 3) :
    (kineticGamma μ)ᴴ = kineticGamma μ := by
  fin_cases μ <;>
    simp [kineticGamma, Matrix.fromBlocks_conjTranspose,
      PauliMatrix.pauliMatrix_selfAdjoint]

/-- `γ⁰` is self-adjoint. -/
theorem gammaMatrix_zero_conjTranspose :
    (gammaMatrix (Sum.inl 0))ᴴ = gammaMatrix (Sum.inl 0) := by
  simp [gammaMatrix, Matrix.fromBlocks_conjTranspose,
    PauliMatrix.pauliMatrix_inl_zero_eq_one]

/-- The hermiticity relation of the γ matrices, `(γ^μ)† = γ⁰ γ^μ γ⁰`. -/
theorem gammaMatrix_conjTranspose (μ : Fin 1 ⊕ Fin 3) :
    (gammaMatrix μ)ᴴ =
      gammaMatrix (Sum.inl 0) * gammaMatrix μ * gammaMatrix (Sum.inl 0) := by
  fin_cases μ <;>
    simp [gammaMatrix, Matrix.fromBlocks_conjTranspose,
      Matrix.fromBlocks_multiply, PauliMatrix.pauliMatrix_selfAdjoint,
      PauliMatrix.pauliMatrix_inl_zero_eq_one]

end JetAlgebra

end QED
