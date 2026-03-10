/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
/-!

## Pauli matrices

The pauli matrices are defined ultimately through
- `pauliMatrix` which is a map `Fin 1 ⊕ Fin 3 → Matrix (Fin 2) (Fin 2) ℂ`.
  The notation `σ` can be used as short hand.

A tensorial structure is put on `Fin 1 ⊕ Fin 3 → Matrix (Fin 2) (Fin 2) ℂ` to allow the
use of index notation. We then define the following notation:

- `σ^^^` is the tensorial version of the Pauli matrices, which is a complex Lorentz tensor
  of type `ℂT[.up, .upL, .upR]`.

and the following abbreviations:
- `σ_^^` is the Pauli matrices as a complex Lorentz tensor of type `ℂT[.down, .upL, .upR]`.
- `σ___` is the Pauli matrices as a complex Lorentz tensor of type `ℂT[.down, .downR, .downL]`.
- `σ^__` is the Pauli matrices as a complex Lorentz tensor of type `ℂT[.up, .downR, .downL]`.

-/

@[expose] public section
open Matrix
open Complex
open TensorProduct

noncomputable section

namespace PauliMatrix

/-- The Pauli matrices. -/
def pauliMatrix : Fin 1 ⊕ Fin 3 → Matrix (Fin 2) (Fin 2) ℂ
  | Sum.inl 0 => 1
  | Sum.inr 0 => !![0, 1; 1, 0]
  | Sum.inr 1 => !![0, -I; I, 0]
  | Sum.inr 2 => !![1, 0; 0, -1]

@[inherit_doc pauliMatrix]
scoped[PauliMatrix] notation "σ" => pauliMatrix

/-- The 'Pauli matrix' corresponding to the identity `1`. -/
scoped[PauliMatrix] notation "σ0" => σ (Sum.inl 0)

/-- The Pauli matrix corresponding to the matrix `!![0, 1; 1, 0]`. -/
scoped[PauliMatrix] notation "σ1" => σ (Sum.inr 0)

/-- The Pauli matrix corresponding to the matrix `!![0, -I; I, 0]`. -/
scoped[PauliMatrix] notation "σ2" => σ (Sum.inr 1)

/-- The Pauli matrix corresponding to the matrix `!![1, 0; 0, -1]`. -/
scoped[PauliMatrix] notation "σ3" => σ (Sum.inr 2)

lemma pauliMatrix_inl_zero_eq_one : pauliMatrix (Sum.inl 0) = 1 := by
  dsimp [pauliMatrix]

/-!

## Matrix relations

-/

lemma pauliMatrix_selfAdjoint (μ : Fin 1 ⊕ Fin 3) :
    (σ μ)ᴴ = σ μ := by
  fin_cases μ
  all_goals
    dsimp [pauliMatrix]
    rw [eta_fin_two _ᴴ]
    simp
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp

/-! ### Inversions

Lemmas related to the inversions of the Pauli matrices.

-/

@[simp]
lemma pauliMatrix_mul_self (μ : Fin 1 ⊕ Fin 3) :
    (σ μ) * (σ μ) = 1 := by
  fin_cases μ
  all_goals
    dsimp [pauliMatrix]
    simp [one_fin_two]

instance pauliMatrixInvertiable (μ : Fin 1 ⊕ Fin 3) : Invertible (σ μ) := by
  use σ μ
  · simp
  · simp

lemma pauliMatrix_inv (μ : Fin 1 ⊕ Fin 3) :
    ⅟ (σ μ) = σ μ := by rfl

/-! ### Products

These lemmas try to put the terms in numerical order.
We skip `σ0` since it's just `1` anyway.
-/

@[simp] lemma σ2_mul_σ1 : σ2 * σ1 = -(σ1 * σ2) := by simp [pauliMatrix]
@[simp] lemma σ3_mul_σ1 : σ3 * σ1 = -(σ1 * σ3) := by simp [pauliMatrix]
@[simp] lemma σ3_mul_σ2 : σ3 * σ2 = -(σ2 * σ3) := by simp [pauliMatrix]

/-!

### Traces

-/

@[simp] lemma trace_σ1 : Matrix.trace σ1 = 0 := by simp [pauliMatrix]
@[simp] lemma trace_σ2 : Matrix.trace σ2 = 0 := by simp [pauliMatrix]
@[simp] lemma trace_σ3 : Matrix.trace σ3 = 0 := by simp [pauliMatrix]

/-- The trace of `σ0` multiplied by `σ0` is equal to `2`. -/
lemma σ0_σ0_trace : Matrix.trace (σ0 * σ0) = 2 := by simp

/-- The trace of `σ0` multiplied by `σ1` is equal to `0`. -/
lemma σ0_σ1_trace : Matrix.trace (σ0 * σ1) = 0 := by simp [pauliMatrix]

/-- The trace of `σ0` multiplied by `σ2` is equal to `0`. -/
lemma σ0_σ2_trace : Matrix.trace (σ0 * σ2) = 0 := by simp [pauliMatrix]

/-- The trace of `σ0` multiplied by `σ3` is equal to `0`. -/
lemma σ0_σ3_trace : Matrix.trace (σ0 * σ3) = 0 := by simp [pauliMatrix]

/-- The trace of `σ1` multiplied by `σ0` is equal to `0`. -/
lemma σ1_σ0_trace : Matrix.trace (σ1 * σ0) = 0 := by simp [pauliMatrix]

/-- The trace of `σ1` multiplied by `σ1` is equal to `2`. -/
lemma σ1_σ1_trace : Matrix.trace (σ1 * σ1) = 2 := by simp

/-- The trace of `σ1` multiplied by `σ2` is equal to `0`. -/
@[simp]
lemma σ1_σ2_trace : Matrix.trace (σ1 * σ2) = 0 := by
  simp [pauliMatrix]

/-- The trace of `σ1` multiplied by `σ3` is equal to `0`. -/
@[simp]
lemma σ1_σ3_trace : Matrix.trace (σ1 * σ3) = 0 := by
  simp [pauliMatrix]

/-- The trace of `σ2` multiplied by `σ0` is equal to `0`. -/
lemma σ2_σ0_trace : Matrix.trace (σ2 * σ0) = 0 := by simp [pauliMatrix]

/-- The trace of `σ2` multiplied by `σ1` is equal to `0`. -/
lemma σ2_σ1_trace : Matrix.trace (σ2 * σ1) = 0 := by
  simp [pauliMatrix]

/-- The trace of `σ2` multiplied by `σ2` is equal to `2`. -/
lemma σ2_σ2_trace : Matrix.trace (σ2 * σ2) = 2 := by simp

/-- The trace of `σ2` multiplied by `σ3` is equal to `0`. -/
@[simp]
lemma σ2_σ3_trace : Matrix.trace (σ2 * σ3) = 0 := by
  simp [pauliMatrix]

/-- The trace of `σ3` multiplied by `σ0` is equal to `0`. -/
lemma σ3_σ0_trace : Matrix.trace (σ3 * σ0) = 0 := by simp [pauliMatrix]

/-- The trace of `σ3` multiplied by `σ1` is equal to `0`. -/
lemma σ3_σ1_trace : Matrix.trace (σ3 * σ1) = 0 := by simp

/-- The trace of `σ3` multiplied by `σ2` is equal to `0`. -/
lemma σ3_σ2_trace : Matrix.trace (σ3 * σ2) = 0 := by simp

/-- The trace of `σ3` multiplied by `σ3` is equal to `2`. -/
lemma σ3_σ3_trace : Matrix.trace (σ3 * σ3) = 2 := by simp

/-!

### Commutation relations

Lemmas related to the commutation relations of the Pauli matrices.
-/

lemma σ1_σ2_commutator : σ1 * σ2 - σ2 * σ1 = (2 * I) • σ3 := by
  simp [pauliMatrix]
  ring_nf
  simp only [true_and, and_true]
  exact List.ofFn_inj.mp rfl

lemma σ1_σ3_commutator : σ1 * σ3 - σ3 * σ1 = - (2 * I) • σ2 := by
  simp [pauliMatrix]
  ring_nf
  simp only [I_sq, neg_mul, one_mul, neg_neg, true_and]
  exact List.ofFn_inj.mp rfl

lemma σ2_σ1_commutator : σ2 * σ1 - σ1 * σ2 = -(2 * I) • σ3 := by
  simp [pauliMatrix]
  ring_nf
  simp only [true_and, and_true]
  exact List.ofFn_inj.mp rfl

lemma σ2_σ3_commutator : σ2 * σ3 - σ3 * σ2 = (2 * I) • σ1 := by
  simp [pauliMatrix]
  ring_nf
  simp only [true_and]
  exact List.ofFn_inj.mp rfl

lemma σ3_σ1_commutator : σ3 * σ1 - σ1 * σ3 = (2 * I) • σ2 := by
  simp [pauliMatrix]
  ring_nf
  simp only [I_sq, neg_mul, one_mul, neg_neg, true_and]
  exact List.ofFn_inj.mp rfl

lemma σ3_σ2_commutator : σ3 * σ2 - σ2 * σ3 = -(2 * I) • σ1 := by
  simp [pauliMatrix]
  ring_nf
  simp only [true_and]
  exact List.ofFn_inj.mp rfl

end PauliMatrix
