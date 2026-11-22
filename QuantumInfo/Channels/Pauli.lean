/-
Copyright (c) 2026 Mehardeep Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mehardeep Singh
-/
module

public import QuantumInfo.Channels.CPTP
public import QuantumInfo.States.Pure.Qubit

/-!

# Qubit Pauli channels

Qubit Pauli channels, their Bell-basis Choi diagonalization, and the Fujiwara–Algoet complete
positivity characterization.

## i. Overview

A qubit Pauli map `MatrixMap.pauliMap lx ly lz` is a trace-preserving, unital linear map on
`2 × 2` complex matrices that scales the three Pauli operators `X`, `Y`, `Z` by real parameters
`lx`, `ly`, `lz` respectively. In the Kraus-like Pauli representation, it is the affine combination
of conjugation by `1`, `X`, `Y`, and `Z` with real coefficients
`(1 + lx + ly + lz) / 4`, `(1 + lx - ly - lz) / 4`, `(1 - lx + ly - lz) / 4`, and
`(1 - lx - ly + lz) / 4`.

By Choi's theorem (`MatrixMap.choi_PSD_iff_CP_map`), complete positivity is equivalent to positive
semidefiniteness of the `4 × 4` Choi matrix. Factorizing the Choi matrix through the unnormalized
Bell basis matrix (`MatrixMap.choi_pauliMap_eq_bellBasis`) and using orthogonality of the Bell
columns (`MatrixMap.pauliBellMatrix_conjTranspose_mul_self`) diagonalizes the Choi matrix with
entries `1 + lx + ly + lz`, `1 + lx - ly - lz`, `1 - lx + ly - lz`, and `1 - lx - ly + lz`. This
yields the Fujiwara–Algoet theorem: a qubit Pauli map is completely positive if and only if these
four tetrahedron inequalities hold.

## ii. Key results

- `MatrixMap.pauliMap` : the trace-preserving unital qubit Pauli map with Pauli eigenvalues
  `lx`, `ly`, `lz`.
- `MatrixMap.pauliMap_X`, `MatrixMap.pauliMap_Y`, `MatrixMap.pauliMap_Z` : action on the Pauli
  operators.
- `MatrixMap.pauliMap_comp` : composition of Pauli maps multiplies their eigenvalues componentwise.
- `MatrixMap.pauliMap_isCompletelyPositive_iff` : the Fujiwara–Algoet theorem characterizing
  complete positivity of a qubit Pauli map via the four tetrahedron inequalities.
- `CPTPMap.pauliChannel` : the bundled `CPTPMap Qubit Qubit` constructed from any valid
  Fujiwara–Algoet triple `(lx, ly, lz)`.

## iii. Table of contents

- A. Qubit Pauli maps
- B. Basic properties
- C. Bell-basis diagonalization and the Fujiwara–Algoet theorem
- D. Bundled Pauli quantum channels

## iv. References

* A. Fujiwara and P. Algoet, One-to-one parametrization of quantum channels, Phys. Rev. A 59,
  3290–3294 (1999). [ref: fujiwara_algoet_1999]
* M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum Information, Cambridge
  University Press (2010). [ref: nielsen_chuang_qci]

-/

@[expose] public section

open scoped Matrix ComplexOrder

namespace MatrixMap

noncomputable section

/-!

## A. Qubit Pauli maps

-/

/-- The trace-preserving unital qubit Pauli map scaling `X`, `Y`, `Z` by real parameters
`lx`, `ly`, `lz`. -/
def pauliMap (lx ly lz : ℝ) : MatrixMap Qubit Qubit ℂ where
  toFun A :=
    (((1 + lx + ly + lz) / 4 : ℝ) : ℂ) • A +
    (((1 + lx - ly - lz) / 4 : ℝ) : ℂ) • (Qubit.X.val * A * Qubit.X.val) +
    (((1 - lx + ly - lz) / 4 : ℝ) : ℂ) • (Qubit.Y.val * A * Qubit.Y.val) +
    (((1 - lx - ly + lz) / 4 : ℝ) : ℂ) • (Qubit.Z.val * A * Qubit.Z.val)
  map_add' A B := by
    simp only [Matrix.mul_add, Matrix.add_mul, smul_add]
    abel
  map_smul' c A := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_add, RingHom.id_apply, smul_comm c]

/-- Entry `(0, 0)` of `pauliMap lx ly lz A`. -/
lemma pauliMap_apply_00 (lx ly lz : ℝ) (A : Matrix Qubit Qubit ℂ) :
    pauliMap lx ly lz A 0 0 =
      ((1 + lz : ℝ) : ℂ) / 2 * A 0 0 + ((1 - lz : ℝ) : ℂ) / 2 * A 1 1 := by
  simp only [pauliMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.add_apply, Matrix.smul_apply,
    Matrix.mul_apply, Fin.sum_univ_two, Qubit.X, Qubit.Y, Qubit.Z, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    smul_eq_mul]
  push_cast
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (-(1 - (lx : ℂ) + (ly : ℂ) - (lz : ℂ)) / 4 * A 1 1) * hI

/-- Entry `(0, 1)` of `pauliMap lx ly lz A`. -/
lemma pauliMap_apply_01 (lx ly lz : ℝ) (A : Matrix Qubit Qubit ℂ) :
    pauliMap lx ly lz A 0 1 =
      ((lx + ly : ℝ) : ℂ) / 2 * A 0 1 + ((lx - ly : ℝ) : ℂ) / 2 * A 1 0 := by
  simp only [pauliMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.add_apply, Matrix.smul_apply,
    Matrix.mul_apply, Fin.sum_univ_two, Qubit.X, Qubit.Y, Qubit.Z, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    smul_eq_mul]
  push_cast
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination ((1 - (lx : ℂ) + (ly : ℂ) - (lz : ℂ)) / 4 * A 1 0) * hI

/-- Entry `(1, 0)` of `pauliMap lx ly lz A`. -/
lemma pauliMap_apply_10 (lx ly lz : ℝ) (A : Matrix Qubit Qubit ℂ) :
    pauliMap lx ly lz A 1 0 =
      ((lx - ly : ℝ) : ℂ) / 2 * A 0 1 + ((lx + ly : ℝ) : ℂ) / 2 * A 1 0 := by
  simp only [pauliMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.add_apply, Matrix.smul_apply,
    Matrix.mul_apply, Fin.sum_univ_two, Qubit.X, Qubit.Y, Qubit.Z, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    smul_eq_mul]
  push_cast
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination ((1 - (lx : ℂ) + (ly : ℂ) - (lz : ℂ)) / 4 * A 0 1) * hI

/-- Entry `(1, 1)` of `pauliMap lx ly lz A`. -/
lemma pauliMap_apply_11 (lx ly lz : ℝ) (A : Matrix Qubit Qubit ℂ) :
    pauliMap lx ly lz A 1 1 =
      ((1 - lz : ℝ) : ℂ) / 2 * A 0 0 + ((1 + lz : ℝ) : ℂ) / 2 * A 1 1 := by
  simp only [pauliMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.add_apply, Matrix.smul_apply,
    Matrix.mul_apply, Fin.sum_univ_two, Qubit.X, Qubit.Y, Qubit.Z, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    smul_eq_mul]
  push_cast
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (-(1 - (lx : ℂ) + (ly : ℂ) - (lz : ℂ)) / 4 * A 0 0) * hI

/-- Evaluating `pauliMap` on the identity matrix gives the identity matrix. -/
@[simp]
lemma pauliMap_one (lx ly lz : ℝ) : pauliMap lx ly lz 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, pauliMap_apply_00, pauliMap_apply_01, pauliMap_apply_10,
      pauliMap_apply_11, Matrix.one_apply, ↓reduceIte, Fin.zero_ne_one, one_ne_zero] <;>
    push_cast <;> ring

/-- Evaluating `pauliMap` on `Qubit.X` scales it by `lx`. -/
@[simp]
lemma pauliMap_X (lx ly lz : ℝ) :
    pauliMap lx ly lz Qubit.X.val = (lx : ℂ) • Qubit.X.val := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, pauliMap_apply_00, pauliMap_apply_01, pauliMap_apply_10,
      pauliMap_apply_11, Qubit.X, Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, smul_eq_mul] <;>
    push_cast <;> ring

/-- Evaluating `pauliMap` on `Qubit.Y` scales it by `ly`. -/
@[simp]
lemma pauliMap_Y (lx ly lz : ℝ) :
    pauliMap lx ly lz Qubit.Y.val = (ly : ℂ) • Qubit.Y.val := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, pauliMap_apply_00, pauliMap_apply_01, pauliMap_apply_10,
      pauliMap_apply_11, Qubit.Y, Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, smul_eq_mul] <;>
    push_cast <;> ring

/-- Evaluating `pauliMap` on `Qubit.Z` scales it by `lz`. -/
@[simp]
lemma pauliMap_Z (lx ly lz : ℝ) :
    pauliMap lx ly lz Qubit.Z.val = (lz : ℂ) • Qubit.Z.val := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, pauliMap_apply_00, pauliMap_apply_01, pauliMap_apply_10,
      pauliMap_apply_11, Qubit.Z, Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, smul_eq_mul] <;>
    push_cast <;> ring

/-!

## B. Basic properties

-/

/-- Every qubit Pauli map is unital. -/
lemma pauliMap_unital (lx ly lz : ℝ) : (pauliMap lx ly lz).Unital :=
  pauliMap_one lx ly lz

/-- Every qubit Pauli map is trace-preserving. -/
lemma pauliMap_isTracePreserving (lx ly lz : ℝ) : (pauliMap lx ly lz).IsTracePreserving := by
  intro A
  simp only [Matrix.trace_fin_two, pauliMap_apply_00, pauliMap_apply_11]
  push_cast
  ring

/-- The Pauli map with eigenvalues `(1, 1, 1)` is the identity map. -/
@[simp]
lemma pauliMap_id : pauliMap 1 1 1 = MatrixMap.id Qubit ℂ := by
  ext A i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, pauliMap_apply_00, pauliMap_apply_01, pauliMap_apply_10,
      pauliMap_apply_11, MatrixMap.id, LinearMap.id_apply] <;>
    push_cast <;> ring

/-- Composition of two qubit Pauli maps multiplies their Pauli eigenvalues componentwise. -/
lemma pauliMap_comp (lx₁ ly₁ lz₁ lx₂ ly₂ lz₂ : ℝ) :
    (pauliMap lx₁ ly₁ lz₁) ∘ₗ (pauliMap lx₂ ly₂ lz₂) =
      pauliMap (lx₁ * lx₂) (ly₁ * ly₂) (lz₁ * lz₂) := by
  ext A i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, LinearMap.comp_apply, pauliMap_apply_00,
      pauliMap_apply_01, pauliMap_apply_10, pauliMap_apply_11] <;>
    push_cast <;> ring

/-!

## C. Bell-basis diagonalization and the Fujiwara–Algoet theorem

-/

/-- Unnormalized Bell basis matrix on `Qubit × Qubit`, with columns
`|00⟩ + |11⟩`, `|01⟩ + |10⟩`, `|01⟩ - |10⟩`, and `|00⟩ - |11⟩`. -/
def pauliBellMatrix : Matrix (Qubit × Qubit) (Fin 4) ℂ :=
  Matrix.of fun p k =>
    match p, k with
    | (0, 0), 0 => 1 | (1, 1), 0 => 1
    | (0, 1), 1 => 1 | (1, 0), 1 => 1
    | (0, 1), 2 => 1 | (1, 0), 2 => -1
    | (0, 0), 3 => 1 | (1, 1), 3 => -1
    | _, _ => 0

/-- The diagonal eigenvalues of the Choi matrix of `pauliMap` in the unnormalized Bell basis. -/
def pauliChoiEigenvals (lx ly lz : ℝ) : Fin 4 → ℂ :=
  ![((1 + lx + ly + lz : ℝ) : ℂ), ((1 + lx - ly - lz : ℝ) : ℂ),
    ((1 - lx + ly - lz : ℝ) : ℂ), ((1 - lx - ly + lz : ℝ) : ℂ)]

/-- The columns of `pauliBellMatrix` are orthogonal with squared norm `2`. -/
lemma pauliBellMatrix_conjTranspose_mul_self :
    pauliBellMatrixᴴ * pauliBellMatrix = (2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliBellMatrix, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two] <;>
    norm_num

/-- The Choi matrix of `pauliMap` is congruent to `Matrix.diagonal (pauliChoiEigenvals lx ly lz)`
via `(1 / 2 : ℂ) • pauliBellMatrix`. -/
lemma choi_pauliMap_eq_bellBasis (lx ly lz : ℝ) :
    (pauliMap lx ly lz).choi_matrix =
      ((1 / 2 : ℂ) • pauliBellMatrix) * Matrix.diagonal (pauliChoiEigenvals lx ly lz) *
        ((1 / 2 : ℂ) • pauliBellMatrix)ᴴ := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp only [Fin.zero_eta, Fin.mk_one, choi_matrix, pauliMap_apply_00, pauliMap_apply_01,
      pauliMap_apply_10, pauliMap_apply_11, Matrix.single, Matrix.of_apply, Matrix.mul_apply,
      Matrix.smul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply, Fin.sum_univ_four,
      pauliBellMatrix, pauliChoiEigenvals, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, smul_eq_mul] <;>
    norm_num <;> ring

/-- Conjugating the Choi matrix of `pauliMap` by `pauliBellMatrix` yields the diagonal matrix of
the four Fujiwara–Algoet expressions. -/
lemma pauliBellMatrix_conjTranspose_mul_choi (lx ly lz : ℝ) :
    pauliBellMatrixᴴ * (pauliMap lx ly lz).choi_matrix * pauliBellMatrix =
      Matrix.diagonal (pauliChoiEigenvals lx ly lz) := by
  rw [choi_pauliMap_eq_bellBasis]
  simp only [Matrix.conjTranspose_smul, star_div₀, star_one, star_ofNat, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc pauliBellMatrixᴴ pauliBellMatrix,
    pauliBellMatrix_conjTranspose_mul_self, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
    Matrix.mul_one, smul_smul, smul_smul, smul_smul]
  norm_num

/-- The Fujiwara–Algoet theorem: a qubit Pauli map `pauliMap lx ly lz` is completely positive
if and only if its Pauli eigenvalues satisfy the four tetrahedron inequalities
`0 ≤ 1 + lx + ly + lz`, `0 ≤ 1 + lx - ly - lz`, `0 ≤ 1 - lx + ly - lz`, and
`0 ≤ 1 - lx - ly + lz`. -/
theorem pauliMap_isCompletelyPositive_iff (lx ly lz : ℝ) :
    (pauliMap lx ly lz).IsCompletelyPositive ↔
      0 ≤ 1 + lx + ly + lz ∧ 0 ≤ 1 + lx - ly - lz ∧
      0 ≤ 1 - lx + ly - lz ∧ 0 ≤ 1 - lx - ly + lz := by
  rw [choi_PSD_iff_CP_map]
  constructor
  · intro hPSD
    have hdiag : (Matrix.diagonal (pauliChoiEigenvals lx ly lz)).PosSemidef := by
      rw [← pauliBellMatrix_conjTranspose_mul_choi]
      exact hPSD.conjTranspose_mul_mul_same pauliBellMatrix
    rw [Matrix.posSemidef_diagonal_iff] at hdiag
    exact ⟨Complex.zero_le_real.mp (hdiag 0), Complex.zero_le_real.mp (hdiag 1),
      Complex.zero_le_real.mp (hdiag 2), Complex.zero_le_real.mp (hdiag 3)⟩
  · rintro ⟨h₀, h₁, h₂, h₃⟩
    have hdiag : (Matrix.diagonal (pauliChoiEigenvals lx ly lz)).PosSemidef := by
      rw [Matrix.posSemidef_diagonal_iff]
      intro k
      fin_cases k
      · exact Complex.zero_le_real.mpr h₀
      · exact Complex.zero_le_real.mpr h₁
      · exact Complex.zero_le_real.mpr h₂
      · exact Complex.zero_le_real.mpr h₃
    rw [choi_pauliMap_eq_bellBasis]
    exact hdiag.mul_mul_conjTranspose_same ((1 / 2 : ℂ) • pauliBellMatrix)

end

end MatrixMap

/-!

## D. Bundled Pauli quantum channels

-/

namespace CPTPMap

noncomputable section

/-- The bundled completely positive trace-preserving qubit Pauli channel associated with any
triple `(lx, ly, lz)` satisfying the Fujiwara–Algoet tetrahedron inequalities. -/
def pauliChannel (lx ly lz : ℝ)
    (h₀ : 0 ≤ 1 + lx + ly + lz) (h₁ : 0 ≤ 1 + lx - ly - lz)
    (h₂ : 0 ≤ 1 - lx + ly - lz) (h₃ : 0 ≤ 1 - lx - ly + lz) :
    CPTPMap Qubit Qubit where
  toLinearMap := MatrixMap.pauliMap lx ly lz
  cp := (MatrixMap.pauliMap_isCompletelyPositive_iff lx ly lz).mpr ⟨h₀, h₁, h₂, h₃⟩
  TP := MatrixMap.pauliMap_isTracePreserving lx ly lz

/-- The underlying linear map of `pauliChannel` is `MatrixMap.pauliMap`. -/
@[simp]
lemma pauliChannel_map (lx ly lz : ℝ)
    (h₀ : 0 ≤ 1 + lx + ly + lz) (h₁ : 0 ≤ 1 + lx - ly - lz)
    (h₂ : 0 ≤ 1 - lx + ly - lz) (h₃ : 0 ≤ 1 - lx - ly + lz) :
    (pauliChannel lx ly lz h₀ h₁ h₂ h₃).map = MatrixMap.pauliMap lx ly lz := rfl

/-- Every qubit Pauli channel is unital. -/
lemma pauliChannel_unital (lx ly lz : ℝ)
    (h₀ : 0 ≤ 1 + lx + ly + lz) (h₁ : 0 ≤ 1 + lx - ly - lz)
    (h₂ : 0 ≤ 1 - lx + ly - lz) (h₃ : 0 ≤ 1 - lx - ly + lz) :
    (pauliChannel lx ly lz h₀ h₁ h₂ h₃).map.Unital :=
  MatrixMap.pauliMap_unital lx ly lz

end

end CPTPMap
