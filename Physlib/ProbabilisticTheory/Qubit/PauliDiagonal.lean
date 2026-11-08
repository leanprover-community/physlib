/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Physlib.Relativity.PauliMatrices.Basic

/-!
# Unital qubit maps that are diagonal in the Pauli basis

## i. Overview

A unital map of `M₂(ℂ)` that is diagonal in the Pauli basis fixes `1` and multiplies `σᵢ` by a
real number `lᵢ`. On the Bloch ball it acts as `r ↦ diag(l₀, l₁, l₂) r`. Every such map is a
signed mixture of the four Pauli conjugations,
`X ↦ ∑ μ, q μ • (σ μ * X * σ μ)`,
with weights `q₀ = (1 + l₀ + l₁ + l₂) / 4` and `qᵢ = (1 + lᵢ − lⱼ − lₖ) / 4`. The weights sum to
`1`. When they are nonnegative, `l` lies in the tetrahedron with vertices `(1, 1, 1)`,
`(1, −1, −1)`, `(−1, 1, −1)`, `(−1, −1, 1)`, and the map is a Pauli channel: it sends positive
semidefinite matrices to positive semidefinite matrices.

## ii. Key results

- `PauliMatrix.pauliDiagonal` : the map with Pauli eigenvalues `l`.
- `PauliMatrix.pauliDiagonal_one` : it is unital.
- `PauliMatrix.pauliDiagonal_pauli` : it multiplies `σᵢ` by `lᵢ`.
- `PauliMatrix.sum_pauliWeight` : the weights sum to `1`.
- `PauliMatrix.pauliDiagonal_posSemidef` : with nonnegative weights it preserves positive
  semidefinite matrices.

## iii. Table of contents

- A. The weights
- B. The map
- C. Positivity on the tetrahedron

## iv. References

* M. B. Ruskai, S. Szarek, E. Werner, *An analysis of completely-positive trace-preserving maps
  on `M₂`*, Linear Algebra Appl. 347 (2002), arXiv:quant-ph/0101003.

-/

@[expose] public section

open Matrix
open scoped ComplexOrder

noncomputable section

namespace PauliMatrix

/-!

## A. The weights

-/

/-- The weight of the conjugation by `σ μ` in the map with Pauli eigenvalues `l`. -/
def pauliWeight (l : Fin 3 → ℝ) : Fin 1 ⊕ Fin 3 → ℝ
  | Sum.inl _ => (1 + l 0 + l 1 + l 2) / 4
  | Sum.inr 0 => (1 + l 0 - l 1 - l 2) / 4
  | Sum.inr 1 => (1 - l 0 + l 1 - l 2) / 4
  | Sum.inr 2 => (1 - l 0 - l 1 + l 2) / 4

/-- **The weights sum to `1`.** -/
lemma sum_pauliWeight (l : Fin 3 → ℝ) : ∑ μ, pauliWeight l μ = 1 := by
  simp [Fintype.sum_sum_type, Fin.sum_univ_succ, pauliWeight]
  ring

/-!

## B. The map

-/

/-- The unital map of `M₂(ℂ)` with Pauli eigenvalues `l`: `X ↦ ∑ μ, q μ • (σ μ * X * σ μ)`. -/
def pauliDiagonal (l : Fin 3 → ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun X := ∑ μ, pauliWeight l μ • (σ μ * X * σ μ)
  map_add' X Y := by simp [mul_add, add_mul, smul_add, Finset.sum_add_distrib]
  map_smul' c X := by simp [Finset.smul_sum, smul_comm c]

lemma pauliDiagonal_apply (l : Fin 3 → ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    pauliDiagonal l X = ∑ μ, pauliWeight l μ • (σ μ * X * σ μ) := rfl

/-- **The map is unital.** -/
lemma pauliDiagonal_one (l : Fin 3 → ℝ) : pauliDiagonal l 1 = 1 := by
  simp only [pauliDiagonal_apply, mul_one, pauliMatrix_mul_self, ← Finset.sum_smul,
    sum_pauliWeight, one_smul]

/-- **The map multiplies `σᵢ` by `lᵢ`.** -/
lemma pauliDiagonal_pauli (l : Fin 3 → ℝ) (i : Fin 3) :
    pauliDiagonal l (σ (Sum.inr i)) = (l i : ℂ) • σ (Sum.inr i) := by
  rw [pauliDiagonal_apply]
  ext a b
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [Fintype.sum_sum_type, Fin.sum_univ_succ, pauliWeight, pauliMatrix,
      Complex.ext_iff] <;> ring_nf

/-!

## C. Positivity on the tetrahedron

-/

/-- **On the tetrahedron the map preserves positive semidefinite matrices**: when every weight
is nonnegative, the map is a mixture of conjugations by the Pauli matrices. -/
lemma pauliDiagonal_posSemidef (l : Fin 3 → ℝ) (hq : ∀ μ, 0 ≤ pauliWeight l μ)
    {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : X.PosSemidef) : (pauliDiagonal l X).PosSemidef := by
  refine posSemidef_sum _ fun μ _ => PosSemidef.smul ?_ (hq μ)
  simpa [pauliMatrix_selfAdjoint] using hX.mul_mul_conjTranspose_same (σ μ)

end PauliMatrix
