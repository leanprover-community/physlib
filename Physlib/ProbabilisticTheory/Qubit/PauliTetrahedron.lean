/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Data.Matrix.Composition
public import Physlib.ProbabilisticTheory.Qubit.PauliDiagonal

/-!
# The completely positive Pauli-diagonal qubit maps form a tetrahedron

## i. Overview

The unital map `pauliDiagonal l` of `M₂(ℂ)` is `X ↦ ∑ μ, q μ • (σ μ * X * σ μ)` with weights
`q = pauliWeight l`. It is completely positive, in the sense of `CompletelyPositiveMap`, exactly
when every weight is nonnegative, that is, when `l` lies in the tetrahedron with vertices
`(1, 1, 1)`, `(1, −1, −1)`, `(−1, 1, −1)`, `(−1, −1, 1)`.

* **Sufficiency.** Applied entrywise to a block matrix `M`, the map is
  `∑ μ, star (S μ) * M * S μ` with `S μ` block diagonal with entries `√(q μ) • σ μ`. Conjugates of
  a nonnegative element are nonnegative.
* **Necessity.** The block matrix `(Eᵢⱼ)ᵢⱼ` of matrix units is `star N * N`, hence nonnegative.
  Its image is the Choi matrix `(Φ Eᵢⱼ)ᵢⱼ`. Flattened to a `4 × 4` matrix by `compRingEquiv`, a
  star ring isomorphism, it is positive semidefinite, and at the vector `w μ (i, a) = σ μ a i` it
  takes the value `4 q μ`.

## ii. Key results

- `PauliMatrix.pauliChannel` : with nonnegative weights, the map as a completely positive map.
- `PauliMatrix.pauliWeight_nonneg_of_cp` : if the map is completely positive, every weight is
  nonnegative.
- `PauliMatrix.exists_cp_iff` : the map is completely positive if and only if every weight is
  nonnegative.

## iii. Table of contents

- A. Sufficiency
- B. The Choi matrix
- C. The tetrahedron

## iv. References

* M. B. Ruskai, S. Szarek, E. Werner, *An analysis of completely-positive trace-preserving maps
  on `M₂`*, Linear Algebra Appl. 347 (2002), Section 2, arXiv:quant-ph/0101003.

-/

@[expose] public section

open Matrix CStarMatrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator CStarAlgebra

noncomputable section

namespace PauliMatrix

/-!

## A. Sufficiency

-/

/-- The block diagonal matrix with `c` on the diagonal. -/
def blockDiag (k : ℕ) (c : Matrix (Fin 2) (Fin 2) ℂ) :
    CStarMatrix (Fin k) (Fin k) (Matrix (Fin 2) (Fin 2) ℂ) :=
  ofMatrixStarAlgEquiv (diagonal fun _ => c)

lemma cstar_sum_apply {ι : Type*} {k : ℕ} (s : Finset ι)
    (N : ι → CStarMatrix (Fin k) (Fin k) (Matrix (Fin 2) (Fin 2) ℂ)) (i j : Fin k) :
    (∑ μ ∈ s, N μ) i j = ∑ μ ∈ s, N μ i j := by
  rw [← ofMatrixStarAlgEquiv.apply_symm_apply (∑ μ ∈ s, N μ), map_sum]
  exact Matrix.sum_apply i j s _

lemma star_blockDiag_mul_mul {k : ℕ} (c : Matrix (Fin 2) (Fin 2) ℂ)
    (M : CStarMatrix (Fin k) (Fin k) (Matrix (Fin 2) (Fin 2) ℂ)) (i j : Fin k) :
    (star (blockDiag k c) * M * blockDiag k c) i j = cᴴ * M i j * c := by
  rw [blockDiag, ← ofMatrixStarAlgEquiv.apply_symm_apply M, ← map_star, ← map_mul, ← map_mul]
  change (star (diagonal fun _ => c) * ofMatrixStarAlgEquiv.symm M * diagonal fun _ => c :
    Matrix (Fin k) (Fin k) (Matrix (Fin 2) (Fin 2) ℂ)) i j = _
  rw [Matrix.star_eq_conjTranspose, diagonal_conjTranspose, mul_diagonal, diagonal_mul]
  rfl

lemma sqrt_smul_pauli (q : ℝ) (hq : 0 ≤ q) (μ : Fin 1 ⊕ Fin 3) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    ((Real.sqrt q : ℂ) • σ μ)ᴴ * X * ((Real.sqrt q : ℂ) • σ μ) = q • (σ μ * X * σ μ) := by
  rw [conjTranspose_smul, pauliMatrix_selfAdjoint, Complex.star_def, Complex.conj_ofReal]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, Real.mul_self_sqrt hq, Complex.coe_smul]

/-- **With nonnegative weights the map is completely positive.** -/
def pauliChannel (l : Fin 3 → ℝ) (hq : ∀ μ, 0 ≤ pauliWeight l μ) :
    Matrix (Fin 2) (Fin 2) ℂ →CP Matrix (Fin 2) (Fin 2) ℂ where
  toLinearMap := pauliDiagonal l
  map_cstarMatrix_nonneg' k M hM := by
    have h : M.map (pauliDiagonal l) = ∑ μ, star (blockDiag k ((Real.sqrt (pauliWeight l μ) : ℂ) •
        σ μ)) * M * blockDiag k ((Real.sqrt (pauliWeight l μ) : ℂ) • σ μ) := by
      refine CStarMatrix.ext fun i j => ?_
      rw [cstar_sum_apply]
      simp only [star_blockDiag_mul_mul, sqrt_smul_pauli _ (hq _)]
      rfl
    rw [h]
    exact Finset.sum_nonneg fun μ _ => star_left_conjugate_nonneg hM _

/-!

## B. The Choi matrix

-/

/-- Flattening a `2 × 2` block matrix of `2 × 2` matrices, as a star ring homomorphism. -/
def flatten : CStarMatrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) ℂ) →⋆ₙ+*
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ where
  __ := ((ofMatrixRingEquiv (n := Fin 2) (A := Matrix (Fin 2) (Fin 2) ℂ)).symm.trans
    (compRingEquiv (Fin 2) (Fin 2) ℂ)).toNonUnitalRingHom
  map_star' M := by
    ext ⟨i, a⟩ ⟨j, b⟩
    rfl

lemma flatten_apply (M : CStarMatrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) ℂ))
    (i a j b : Fin 2) : flatten M (i, a) (j, b) = M i j a b := rfl

/-- The block matrix of matrix units, `(Eᵢⱼ)ᵢⱼ`. -/
def unitBlock : CStarMatrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) ℂ) :=
  ofMatrixStarAlgEquiv (Matrix.of fun i j => single i j 1)

lemma unitBlock_map_apply (f : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (i j : Fin 2) : unitBlock.map f i j = f (single i j 1) := rfl

lemma unitBlock_nonneg : 0 ≤ unitBlock := by
  let N : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) ℂ) :=
    Matrix.of fun i j => if i = 0 then single 0 j 1 else 0
  have h : (Matrix.of fun i j => single i j 1 : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) ℂ))
      = star N * N := by
    ext i j a b
    fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
      simp [N, Matrix.mul_apply, single_apply, Matrix.star_eq_conjTranspose]
  rw [unitBlock, h, map_mul, map_star]
  exact star_mul_self_nonneg _

/-- The vector of `σ μ`: `w μ (i, a) = σ μ a i`. -/
def pauliVec (μ : Fin 1 ⊕ Fin 3) : Fin 2 × Fin 2 → ℂ := fun p => σ μ p.2 p.1

lemma pauliVec_choi (l : Fin 3 → ℝ) (μ : Fin 1 ⊕ Fin 3) :
    star (pauliVec μ) ⬝ᵥ (flatten (unitBlock.map (pauliDiagonal l)) *ᵥ pauliVec μ) =
      ((4 * pauliWeight l μ : ℝ) : ℂ) := by
  simp only [dotProduct, mulVec, Fintype.sum_prod_type, flatten_apply, unitBlock_map_apply]
  fin_cases μ <;>
    simp [pauliVec, pauliDiagonal_apply, Fintype.sum_sum_type,
      Fin.sum_univ_succ, pauliWeight, pauliMatrix, Matrix.mul_apply, single_apply, vecMul,
      dotProduct, Complex.ext_iff] <;> ring_nf

/-- **If the map is completely positive, every weight is nonnegative.** -/
lemma pauliWeight_nonneg_of_cp (l : Fin 3 → ℝ)
    (Φ : Matrix (Fin 2) (Fin 2) ℂ →CP Matrix (Fin 2) (Fin 2) ℂ) (hΦ : ⇑Φ = pauliDiagonal l)
    (μ : Fin 1 ⊕ Fin 3) : 0 ≤ pauliWeight l μ := by
  have hC : 0 ≤ unitBlock.map (pauliDiagonal l) := by
    rw [← hΦ]
    exact Φ.map_cstarMatrix_nonneg _ unitBlock_nonneg
  have hF := nonneg_iff_posSemidef.mp (flatten.map_le_map_of_map_star hC)
  have hv := hF.dotProduct_mulVec_nonneg (pauliVec μ)
  rw [pauliVec_choi, Complex.zero_le_real] at hv
  linarith

/-!

## C. The tetrahedron

-/

/-- **The tetrahedron**: the map is completely positive if and only if every weight is
nonnegative. -/
lemma exists_cp_iff (l : Fin 3 → ℝ) :
    (∃ Φ : Matrix (Fin 2) (Fin 2) ℂ →CP Matrix (Fin 2) (Fin 2) ℂ, ⇑Φ = pauliDiagonal l) ↔
      ∀ μ, 0 ≤ pauliWeight l μ :=
  ⟨fun ⟨Φ, hΦ⟩ => pauliWeight_nonneg_of_cp l Φ hΦ, fun hq => ⟨pauliChannel l hq, rfl⟩⟩

end PauliMatrix
