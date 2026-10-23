/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Physlib.ProbabilisticTheory.Channel.Basic
public import Physlib.ProbabilisticTheory.Qubit.PauliDiagonal

/-!
# The positive unital qubit maps diagonal in the Pauli basis form a cube

## i. Overview

The unital map `pauliDiagonal l` of `M₂(ℂ)` multiplies `σᵢ` by `lᵢ`. It sends positive
semidefinite matrices to positive semidefinite matrices exactly when `|lᵢ| ≤ 1` for every `i`.

* **Sufficiency.** The map is affine in each `lᵢ`, so on the cube it is a mixture, with
  nonnegative weights, of the maps at the eight corners `l ∈ {±1}³`. At the four corners with
  `l₀ l₁ l₂ = 1` it is a conjugation by a Pauli matrix. At the other four it is such a
  conjugation after the transpose, which multiplies `σ₁` by `−1` and fixes the others. Both keep
  positive semidefinite matrices positive semidefinite.
* **Necessity.** The matrix `1 + c σᵢ`, with `c = ±1`, is positive semidefinite, and the map
  sends it to `1 + c lᵢ σᵢ`. Evaluating at the eigenvector of `σᵢ` with eigenvalue `−1` gives
  `1 − c lᵢ ≥ 0`.

On the cube the map is a unital positive linear map in the sense of
`UnitalPositiveLinearMap`, for the order on matrices given by positive semidefiniteness.

## ii. Key results

- `PauliMatrix.pauliDiagonal_transpose` : composing with the transpose reverses `l₁`.
- `PauliMatrix.pauliDiagonal_posSemidef_iff` : the map preserves positive semidefinite matrices
  if and only if `|lᵢ| ≤ 1` for every `i`.
- `PauliMatrix.pauliCube` : on the cube, the map as a unital positive linear map.

## iii. Table of contents

- A. Affine dependence on one eigenvalue
- B. The transpose
- C. The corners of the cube
- D. The cube

## iv. References

* M. B. Ruskai, S. Szarek, E. Werner, *An analysis of completely-positive trace-preserving maps
  on `M₂`*, Linear Algebra Appl. 347 (2002), Section 2, arXiv:quant-ph/0101003.

-/

@[expose] public section

open Matrix
open scoped ComplexOrder

noncomputable section

namespace PauliMatrix

/-- The map with Pauli eigenvalues `l` preserves positive semidefinite matrices. -/
def PreservesPosSemidef (l : Fin 3 → ℝ) : Prop :=
  ∀ X : Matrix (Fin 2) (Fin 2) ℂ, X.PosSemidef → (pauliDiagonal l X).PosSemidef

/-!

## A. Affine dependence on one eigenvalue

-/

lemma pauliWeight_affine (l : Fin 3 → ℝ) (i : Fin 3) (μ : Fin 1 ⊕ Fin 3) :
    pauliWeight l μ = (1 + l i) / 2 * pauliWeight (Function.update l i 1) μ +
      (1 - l i) / 2 * pauliWeight (Function.update l i (-1)) μ := by
  fin_cases i <;> fin_cases μ <;> simp [pauliWeight, Function.update] <;> ring

/-- **The map is affine in each eigenvalue.** -/
lemma pauliDiagonal_affine (l : Fin 3 → ℝ) (i : Fin 3) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    pauliDiagonal l X = ((1 + l i) / 2) • pauliDiagonal (Function.update l i 1) X +
      ((1 - l i) / 2) • pauliDiagonal (Function.update l i (-1)) X := by
  simp only [pauliDiagonal_apply, Finset.smul_sum, ← Finset.sum_add_distrib, smul_smul,
    ← add_smul, ← pauliWeight_affine]

lemma PreservesPosSemidef.of_update {l : Fin 3 → ℝ} (i : Fin 3) (hl : |l i| ≤ 1)
    (h₁ : PreservesPosSemidef (Function.update l i 1))
    (h₂ : PreservesPosSemidef (Function.update l i (-1))) : PreservesPosSemidef l := by
  intro X hX
  rw [pauliDiagonal_affine l i]
  obtain ⟨hlo, hhi⟩ := abs_le.mp hl
  exact ((h₁ X hX).smul (by linarith)).add ((h₂ X hX).smul (by linarith))

/-!

## B. The transpose

-/

/-- Reverse the eigenvalue of `σ₁`. -/
def flipY (l : Fin 3 → ℝ) : Fin 3 → ℝ := Function.update l 1 (-l 1)

/-- **Composing with the transpose reverses the eigenvalue of `σ₁`.** -/
lemma pauliDiagonal_transpose (l : Fin 3 → ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    pauliDiagonal l Xᵀ = pauliDiagonal (flipY l) X := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [pauliDiagonal_apply, Fintype.sum_sum_type, Fin.sum_univ_succ, pauliWeight, flipY,
      Function.update, pauliMatrix, mul_apply, vecMul, dotProduct] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

lemma PreservesPosSemidef.of_flipY {l : Fin 3 → ℝ} (h : PreservesPosSemidef (flipY l)) :
    PreservesPosSemidef l := by
  intro X hX
  have hl : flipY (flipY l) = l := by
    funext j; fin_cases j <;> simp [flipY, Function.update]
  rw [← hl, ← pauliDiagonal_transpose]
  exact h _ hX.transpose

/-!

## C. The corners of the cube

-/

lemma PreservesPosSemidef.of_weights {l : Fin 3 → ℝ} (hq : ∀ μ, 0 ≤ pauliWeight l μ) :
    PreservesPosSemidef l :=
  fun _ hX => pauliDiagonal_posSemidef l hq hX

/-!

## D. The cube

-/

/-- **Inside the cube the map preserves positive semidefinite matrices.** -/
lemma PreservesPosSemidef.of_abs_le {l : Fin 3 → ℝ} (hl : ∀ i, |l i| ≤ 1) :
    PreservesPosSemidef l := by
  refine .of_update 0 (hl 0) ?_ ?_ <;>
  refine .of_update 1 (by simpa [Function.update] using hl 1) ?_ ?_ <;>
  refine .of_update 2 (by simpa [Function.update] using hl 2) ?_ ?_ <;>
  first
  | (refine .of_weights fun μ => ?_
     fin_cases μ <;> norm_num [pauliWeight, Function.update]; done)
  | (refine .of_flipY (.of_weights fun μ => ?_)
     fin_cases μ <;> norm_num [pauliWeight, flipY, Function.update])

lemma one_add_smul_posSemidef (i : Fin 3) {c : ℝ} (hc : c = 1 ∨ c = -1) :
    (1 + (c : ℂ) • σ (Sum.inr i)).PosSemidef := by
  have h : 1 + (c : ℂ) • σ (Sum.inr i) = (1 / 2 : ℝ) •
      ((1 + (c : ℂ) • σ (Sum.inr i)) * (1 + (c : ℂ) • σ (Sum.inr i))ᴴ) := by
    rcases hc with rfl | rfl <;> ext a b <;> fin_cases i <;> fin_cases a <;> fin_cases b <;>
      simp [pauliMatrix, mul_apply, Fin.sum_univ_two] <;> ring_nf
  rw [h]
  exact (posSemidef_self_mul_conjTranspose _).smul (by norm_num)

/-- An eigenvector of `σᵢ` with eigenvalue `−1`. -/
def minusVec : Fin 3 → Fin 2 → ℂ
  | 0 => ![1, -1]
  | 1 => ![1, -Complex.I]
  | 2 => ![0, 1]

lemma minusVec_dotProduct (i : Fin 3) (t : ℝ) :
    star (minusVec i) ⬝ᵥ ((1 + (t : ℂ) • σ (Sum.inr i)) *ᵥ minusVec i) =
      (((if i = 2 then 1 else 2) * (1 - t) : ℝ) : ℂ) := by
  fin_cases i <;>
    simp [minusVec, pauliMatrix, dotProduct, mulVec, Fin.sum_univ_two, Complex.ext_iff] <;> ring

/-- **Outside the cube the map does not preserve positive semidefinite matrices.** -/
lemma PreservesPosSemidef.abs_le {l : Fin 3 → ℝ} (h : PreservesPosSemidef l) (i : Fin 3) :
    |l i| ≤ 1 := by
  have key : ∀ c : ℝ, (c = 1 ∨ c = -1) → 0 ≤ 1 - c * l i := by
    intro c hc
    have hP := h _ (one_add_smul_posSemidef i hc)
    rw [map_add, map_smul, pauliDiagonal_one, pauliDiagonal_pauli, smul_smul,
      ← Complex.ofReal_mul] at hP
    have hv := hP.dotProduct_mulVec_nonneg (minusVec i)
    rw [minusVec_dotProduct, Complex.zero_le_real] at hv
    split_ifs at hv <;> nlinarith
  have h₁ := key 1 (Or.inl rfl)
  have h₂ := key (-1) (Or.inr rfl)
  exact _root_.abs_le.mpr ⟨by linarith, by linarith⟩

/-- **The cube**: the map preserves positive semidefinite matrices if and only if
`|lᵢ| ≤ 1` for every `i`. -/
lemma pauliDiagonal_posSemidef_iff (l : Fin 3 → ℝ) :
    PreservesPosSemidef l ↔ ∀ i, |l i| ≤ 1 :=
  ⟨fun h => h.abs_le, .of_abs_le⟩

open scoped MatrixOrder in
/-- On the cube, the map as a unital positive linear map. -/
def pauliCube (l : Fin 3 → ℝ) (hl : ∀ i, |l i| ≤ 1) :
    Matrix (Fin 2) (Fin 2) ℂ →ₚ₁[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  .ofLinearMap (pauliDiagonal l)
    (fun X hX => nonneg_iff_posSemidef.mpr
      (PreservesPosSemidef.of_abs_le hl X (nonneg_iff_posSemidef.mp hX)))
    (pauliDiagonal_one l)

end PauliMatrix
