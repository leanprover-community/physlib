/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Physlib.Mathematics.KroneckerDelta.Basic
public import Mathlib.LinearAlgebra.CrossProduct
/-!

## Pauli matrices

The pauli matrices are defined ultimately through
- `pauliMatrix` which is a map `Fin 1 ⊕ Fin 3 → Matrix (Fin 2) (Fin 2) ℂ`.
  The notation `σ` can be used as short hand.

A tensorial structure is put on `Fin 1 ⊕ Fin 3 → Matrix (Fin 2) (Fin 2) ℂ` to allow the
use of index notation.

-/

@[expose] public section

open Matrix
open Complex
open TensorProduct
open KroneckerDelta

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
lemma σ1_σ2_trace : Matrix.trace (σ1 * σ2) = 0 := by
  simp [pauliMatrix]

/-- The trace of `σ1` multiplied by `σ3` is equal to `0`. -/
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
lemma σ2_σ3_trace : Matrix.trace (σ2 * σ3) = 0 := by
  simp [pauliMatrix]

/-- The trace of `σ3` multiplied by `σ0` is equal to `0`. -/
lemma σ3_σ0_trace : Matrix.trace (σ3 * σ0) = 0 := by simp [pauliMatrix]

/-- The trace of `σ3` multiplied by `σ1` is equal to `0`. -/
lemma σ3_σ1_trace : Matrix.trace (σ3 * σ1) = 0 := by simp [pauliMatrix]

/-- The trace of `σ3` multiplied by `σ2` is equal to `0`. -/
lemma σ3_σ2_trace : Matrix.trace (σ3 * σ2) = 0 := by simp [pauliMatrix]

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

/-- Pauli matrices satisfy `{σᵢ, σⱼ} = 2 δᵢⱼ I`. -/
lemma pauliMatrix_anticommutator (i j : Fin 3) :
    pauliMatrix (Sum.inr i) * pauliMatrix (Sum.inr j) +
      pauliMatrix (Sum.inr j) * pauliMatrix (Sum.inr i) =
        ((2 * kroneckerDelta i j : ℕ) : ℂ) •
          (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  fin_cases i <;> fin_cases j <;>
    simp [kroneckerDelta, pauliMatrix] <;>
    ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num

/-- The matrix `a · σ` associated to a real three-vector `a`. -/
noncomputable def vectorMatrix (a : Fin 3 → ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ i : Fin 3, (a i : ℂ) • pauliMatrix (Sum.inr i)

/-- The anticommutator of two Pauli vectors is twice their Euclidean dot product
times the identity. -/
lemma vectorMatrix_anticommutator (a b : Fin 3 → ℝ) :
    vectorMatrix a * vectorMatrix b + vectorMatrix b * vectorMatrix a =
      ((2 * (a ⬝ᵥ b) : ℝ) : ℂ) •
        (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have h :
      vectorMatrix a * vectorMatrix b + vectorMatrix b * vectorMatrix a =
        ((a 0 : ℂ) * b 0) • (σ1 * σ1 + σ1 * σ1) +
          ((a 1 : ℂ) * b 1) • (σ2 * σ2 + σ2 * σ2) +
          ((a 2 : ℂ) * b 2) • (σ3 * σ3 + σ3 * σ3) +
          ((a 0 : ℂ) * b 1 + (a 1 : ℂ) * b 0) • (σ1 * σ2 + σ2 * σ1) +
          ((a 0 : ℂ) * b 2 + (a 2 : ℂ) * b 0) • (σ1 * σ3 + σ3 * σ1) +
          ((a 1 : ℂ) * b 2 + (a 2 : ℂ) * b 1) • (σ2 * σ3 + σ3 * σ2) := by
    simp only [vectorMatrix, Fin.sum_univ_three, add_mul, mul_add, Algebra.smul_mul_assoc,
      Algebra.mul_smul_comm]
    module
  rw [h]
  rw [pauliMatrix_anticommutator 0 0,
      pauliMatrix_anticommutator 1 1,
      pauliMatrix_anticommutator 2 2,
      pauliMatrix_anticommutator 0 1,
      pauliMatrix_anticommutator 0 2,
      pauliMatrix_anticommutator 1 2]
  norm_num [kroneckerDelta]
  simp only [dotProduct, Fin.sum_univ_three]
  push_cast
  module

/-- The commutator of two Pauli vectors is twice `i` times the Pauli vector
associated to their cross product. -/
lemma vectorMatrix_commutator (a b : Fin 3 → ℝ) :
    vectorMatrix a * vectorMatrix b - vectorMatrix b * vectorMatrix a =
      (2 * Complex.I) • vectorMatrix (a ⨯₃ b) := by
  have h :
      vectorMatrix a * vectorMatrix b - vectorMatrix b * vectorMatrix a =
        ((a 0 : ℂ) * b 1 - (a 1 : ℂ) * b 0) • (σ1 * σ2 - σ2 * σ1) +
          ((a 0 : ℂ) * b 2 - (a 2 : ℂ) * b 0) • (σ1 * σ3 - σ3 * σ1) +
          ((a 1 : ℂ) * b 2 - (a 2 : ℂ) * b 1) • (σ2 * σ3 - σ3 * σ2) := by
    simp only [vectorMatrix, Fin.sum_univ_three, add_mul, mul_add, Algebra.smul_mul_assoc,
      Algebra.mul_smul_comm]
    module
  rw [h]
  rw [σ1_σ2_commutator, σ1_σ3_commutator, σ2_σ3_commutator]
  simp only [vectorMatrix, Fin.sum_univ_three, cross_apply, Fin.isValue, neg_smul, smul_neg,
    Nat.succ_eq_add_one, Nat.reduceAdd, cons_val_zero, ofReal_sub, ofReal_mul, cons_val_one,
    cons_val, smul_add]
  module

/-- Product formula for Pauli vectors:
`(a · σ)(b · σ) = (a · b) I + i (a × b) · σ`. -/
lemma vectorMatrix_mul_vectorMatrix (a b : Fin 3 → ℝ) :
    vectorMatrix a * vectorMatrix b =
      ((a ⬝ᵥ b : ℝ) : ℂ) •
          (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        Complex.I • vectorMatrix (a ⨯₃ b) := by
  have hcomm := vectorMatrix_commutator a b
  have hanti := vectorMatrix_anticommutator a b
  refine smul_right_injective _ (two_ne_zero (α := ℂ)) ?_
  simp only
  have h2 : (2 : ℂ) • (vectorMatrix a * vectorMatrix b) =
      (vectorMatrix a * vectorMatrix b + vectorMatrix b * vectorMatrix a) +
        (vectorMatrix a * vectorMatrix b - vectorMatrix b * vectorMatrix a) := by
    rw [two_smul]; abel
  rw [h2, hanti, hcomm]
  module

/-- The square of `a · σ` is `|a|² I`. -/
lemma vectorMatrix_sq (a : Fin 3 → ℝ) :
    vectorMatrix a * vectorMatrix a =
      (∑ i : Fin 3, a i ^ 2 : ℝ) • 1 := by
  have hcross : a ⨯₃ a = 0 := by
    rw [cross_apply]
    ext i
    fin_cases i <;> simp <;> ring
  have hdot : a ⬝ᵥ a = ∑ i : Fin 3, a i ^ 2 := by simp [dotProduct, pow_two]
  rw [vectorMatrix_mul_vectorMatrix, hcross, hdot]
  simp only [vectorMatrix, Pi.zero_apply, Complex.ofReal_zero, zero_smul, Finset.sum_const_zero,
    smul_zero, add_zero]
  push_cast
  module

end PauliMatrix
