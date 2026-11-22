/-
Copyright (c) 2026 Mehardeep Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mehardeep Singh
-/
module

public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
public import Physlib.ProbabilisticTheory.CStarAlgebra.Channel
public import Physlib.Relativity.PauliMatrices.Basic

/-!

# Qubit Pauli channels

Qubit Pauli maps on the `2 × 2` matrix C⋆-algebra, their Fujiwara–Algoet complete positivity
characterization, and the induced observable channels.

## i. Overview

On the qubit C⋆-algebra `CStarMatrix (Fin 2) (Fin 2) ℂ`, conjugation by each of the four Pauli
matrices `σ0, σ1, σ2, σ3` from `Physlib.Relativity.PauliMatrices.Basic` is a unital star-algebra
automorphism and therefore completely positive in Mathlib's `CompletelyPositiveMap` sense. A qubit
Pauli map `ProbabilisticTheory.pauliMap lx ly lz` is the affine combination of these four Pauli
conjugations with real coefficients `(1 + lx + ly + lz) / 4`, `(1 + lx - ly - lz) / 4`,
`(1 - lx + ly - lz) / 4`, and `(1 - lx - ly + lz) / 4`; it is unital, trace-preserving, and
scales `σ1`, `σ2`, `σ3` by `lx`, `ly`, `lz` respectively.

We prove the Fujiwara–Algoet theorem (`ProbabilisticTheory.pauliMap_isCompletelyPositive_iff`):
`pauliMap lx ly lz` is completely positive on `CStarMatrix (Fin 2) (Fin 2) ℂ` if and only if the
four tetrahedron inequalities hold (`0 ≤ 1 + lx + ly + lz`, `0 ≤ 1 + lx - ly - lz`,
`0 ≤ 1 - lx + ly - lz`, `0 ≤ 1 - lx - ly + lz`). Sufficiency follows directly from complete
positivity of star-algebra homomorphisms, and necessity follows by applying the `2 × 2` block
extension to the maximally entangled matrix unit block and conjugating by four Bell witnesses.
Every valid triple induces both a `CompletelyPositiveMap` and a `Channel` between qubit
observables via `Channel.ofComplex`.

## ii. Key results

- `ProbabilisticTheory.pauliConj` : conjugation by a Pauli matrix as a unital `ℂ`-star-algebra
  homomorphism on `CStarMatrix (Fin 2) (Fin 2) ℂ`.
- `ProbabilisticTheory.pauliMap` : the unital trace-preserving qubit Pauli map scaling `σ1`,
  `σ2`, `σ3` by `lx`, `ly`, `lz`.
- `ProbabilisticTheory.pauliMap_comp` : composition multiplies Pauli eigenvalues componentwise.
- `ProbabilisticTheory.pauliMap_isCompletelyPositive_iff` : the Fujiwara–Algoet theorem
  characterizing complete positivity of `pauliMap lx ly lz`.
- `ProbabilisticTheory.pauliCPMap`, `ProbabilisticTheory.pauliChannel` : the bundled
  `CompletelyPositiveMap` and `Channel` on `ofCStarAlgebra (CStarMatrix (Fin 2) (Fin 2) ℂ)`.

## iii. Table of contents

- A. Pauli conjugations and qubit Pauli maps
- B. Basic algebraic properties
- C. The Fujiwara–Algoet complete positivity theorem
- D. Bundled completely positive maps and observable channels

## iv. References

* A. Fujiwara and P. Algoet, One-to-one parametrization of quantum channels, Phys. Rev. A 59,
  3290–3294 (1999). [ref: fujiwara_algoet_1999]
* M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum Information, Cambridge
  University Press (2010). [ref: nielsen_chuang_qci]

-/

@[expose] public section

open scoped CStarAlgebra ComplexOrder PauliMatrix

namespace ProbabilisticTheory

noncomputable section

/-- The `2 × 2` complex matrix C⋆-algebra of a single qubit. -/
abbrev QubitAlgebra : Type := CStarMatrix (Fin 2) (Fin 2) ℂ

/-!

## A. Pauli conjugations and qubit Pauli maps

-/

/-- The Pauli matrix `σ μ` viewed as an element of `QubitAlgebra`. -/
def pauliCStar (μ : Fin 1 ⊕ Fin 3) : QubitAlgebra :=
  CStarMatrix.ofMatrix (PauliMatrix.pauliMatrix μ)

/-- Every Pauli matrix is self-adjoint in `QubitAlgebra`. -/
@[simp]
lemma pauliCStar_star (μ : Fin 1 ⊕ Fin 3) : star (pauliCStar μ) = pauliCStar μ :=
  PauliMatrix.pauliMatrix_selfAdjoint μ

/-- Every Pauli matrix squares to the identity in `QubitAlgebra`. -/
@[simp]
lemma pauliCStar_mul_self (μ : Fin 1 ⊕ Fin 3) : pauliCStar μ * pauliCStar μ = 1 :=
  PauliMatrix.pauliMatrix_mul_self μ

/-- Conjugation `A ↦ σ μ * A * σ μ` by a Pauli matrix as a unital star-algebra homomorphism on
`QubitAlgebra`. -/
def pauliConj (μ : Fin 1 ⊕ Fin 3) : QubitAlgebra →⋆ₐ[ℂ] QubitAlgebra where
  toFun A := pauliCStar μ * A * pauliCStar μ
  map_one' := by rw [mul_one, pauliCStar_mul_self]
  map_mul' A B := by
    calc pauliCStar μ * (A * B) * pauliCStar μ
        = pauliCStar μ * A * (pauliCStar μ * pauliCStar μ) * B * pauliCStar μ := by
          simp only [pauliCStar_mul_self, mul_one, mul_assoc]
      _ = (pauliCStar μ * A * pauliCStar μ) * (pauliCStar μ * B * pauliCStar μ) := by
          simp only [mul_assoc]
  map_zero' := by simp only [mul_zero, zero_mul]
  map_add' A B := by simp only [mul_add, add_mul]
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one,
      pauliCStar_mul_self]
  map_star' A := by simp only [star_mul, pauliCStar_star, mul_assoc]

/-- The unital, trace-preserving qubit Pauli map on `QubitAlgebra` scaling the Pauli operators
`σ1`, `σ2`, `σ3` by real parameters `lx`, `ly`, `lz`. -/
def pauliMap (lx ly lz : ℝ) : QubitAlgebra →ₗ[ℂ] QubitAlgebra :=
  (((1 + lx + ly + lz) / 4 : ℝ) : ℂ) • (pauliConj (Sum.inl 0)).toLinearMap +
  (((1 + lx - ly - lz) / 4 : ℝ) : ℂ) • (pauliConj (Sum.inr 0)).toLinearMap +
  (((1 - lx + ly - lz) / 4 : ℝ) : ℂ) • (pauliConj (Sum.inr 1)).toLinearMap +
  (((1 - lx - ly + lz) / 4 : ℝ) : ℂ) • (pauliConj (Sum.inr 2)).toLinearMap

/-- Entry `(0, 0)` of `pauliMap lx ly lz A`. -/
lemma pauliMap_apply_00 (lx ly lz : ℝ) (A : QubitAlgebra) :
    pauliMap lx ly lz A 0 0 =
      ((1 + lz : ℝ) : ℂ) / 2 * A 0 0 + ((1 - lz : ℝ) : ℂ) / 2 * A 1 1 := by
  simp only [pauliMap, pauliConj, pauliCStar, PauliMatrix.pauliMatrix, LinearMap.add_apply,
    LinearMap.smul_apply, AlgHom.toLinearMap_apply, AlgHom.coe_mk, RingHom.coe_mk,
    MonoidHom.coe_mk, OneHom.coe_mk, CStarMatrix.add_apply, CStarMatrix.smul_apply,
    CStarMatrix.mul_apply, CStarMatrix.ofMatrix_apply, Matrix.one_apply, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Fin.sum_univ_two, Fin.isValue, smul_eq_mul, ↓reduceIte, Fin.zero_ne_one, one_ne_zero]
  push_cast
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (-(1 - (lx : ℂ) + (ly : ℂ) - (lz : ℂ)) / 4 * A 1 1) * hI

/-- Entry `(0, 1)` of `pauliMap lx ly lz A`. -/
lemma pauliMap_apply_01 (lx ly lz : ℝ) (A : QubitAlgebra) :
    pauliMap lx ly lz A 0 1 =
      ((lx + ly : ℝ) : ℂ) / 2 * A 0 1 + ((lx - ly : ℝ) : ℂ) / 2 * A 1 0 := by
  simp only [pauliMap, pauliConj, pauliCStar, PauliMatrix.pauliMatrix, LinearMap.add_apply,
    LinearMap.smul_apply, AlgHom.toLinearMap_apply, AlgHom.coe_mk, RingHom.coe_mk,
    MonoidHom.coe_mk, OneHom.coe_mk, CStarMatrix.add_apply, CStarMatrix.smul_apply,
    CStarMatrix.mul_apply, CStarMatrix.ofMatrix_apply, Matrix.one_apply, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Fin.sum_univ_two, Fin.isValue, smul_eq_mul, ↓reduceIte, Fin.zero_ne_one]
  push_cast
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination ((1 - (lx : ℂ) + (ly : ℂ) - (lz : ℂ)) / 4 * A 1 0) * hI

/-- Entry `(1, 0)` of `pauliMap lx ly lz A`. -/
lemma pauliMap_apply_10 (lx ly lz : ℝ) (A : QubitAlgebra) :
    pauliMap lx ly lz A 1 0 =
      ((lx - ly : ℝ) : ℂ) / 2 * A 0 1 + ((lx + ly : ℝ) : ℂ) / 2 * A 1 0 := by
  simp only [pauliMap, pauliConj, pauliCStar, PauliMatrix.pauliMatrix, LinearMap.add_apply,
    LinearMap.smul_apply, AlgHom.toLinearMap_apply, AlgHom.coe_mk, RingHom.coe_mk,
    MonoidHom.coe_mk, OneHom.coe_mk, CStarMatrix.add_apply, CStarMatrix.smul_apply,
    CStarMatrix.mul_apply, CStarMatrix.ofMatrix_apply, Matrix.one_apply, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Fin.sum_univ_two, Fin.isValue, smul_eq_mul, ↓reduceIte, one_ne_zero]
  push_cast
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination ((1 - (lx : ℂ) + (ly : ℂ) - (lz : ℂ)) / 4 * A 0 1) * hI

/-- Entry `(1, 1)` of `pauliMap lx ly lz A`. -/
lemma pauliMap_apply_11 (lx ly lz : ℝ) (A : QubitAlgebra) :
    pauliMap lx ly lz A 1 1 =
      ((1 - lz : ℝ) : ℂ) / 2 * A 0 0 + ((1 + lz : ℝ) : ℂ) / 2 * A 1 1 := by
  simp only [pauliMap, pauliConj, pauliCStar, PauliMatrix.pauliMatrix, LinearMap.add_apply,
    LinearMap.smul_apply, AlgHom.toLinearMap_apply, AlgHom.coe_mk, RingHom.coe_mk,
    MonoidHom.coe_mk, OneHom.coe_mk, CStarMatrix.add_apply, CStarMatrix.smul_apply,
    CStarMatrix.mul_apply, CStarMatrix.ofMatrix_apply, Matrix.one_apply, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Fin.sum_univ_two, Fin.isValue, smul_eq_mul, ↓reduceIte, Fin.zero_ne_one, one_ne_zero]
  push_cast
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (-(1 - (lx : ℂ) + (ly : ℂ) - (lz : ℂ)) / 4 * A 0 0) * hI

/-!

## B. Basic algebraic properties

-/

/-- Every qubit Pauli map is unital (`pauliMap lx ly lz 1 = 1`). -/
@[simp]
lemma pauliMap_one (lx ly lz : ℝ) : pauliMap lx ly lz 1 = 1 := by
  apply CStarMatrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, pauliMap_apply_00, pauliMap_apply_01, pauliMap_apply_10,
      pauliMap_apply_11, CStarMatrix.one_apply, ↓reduceIte, Fin.zero_ne_one, one_ne_zero] <;>
    push_cast <;> ring

/-- Evaluating `pauliMap` on `σ1` scales it by `lx`. -/
@[simp]
lemma pauliMap_sigma1 (lx ly lz : ℝ) :
    pauliMap lx ly lz (pauliCStar (Sum.inr 0)) = (lx : ℂ) • pauliCStar (Sum.inr 0) := by
  apply CStarMatrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, pauliMap_apply_00, pauliMap_apply_01, pauliMap_apply_10,
      pauliMap_apply_11, pauliCStar, PauliMatrix.pauliMatrix, CStarMatrix.smul_apply,
      CStarMatrix.ofMatrix_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, smul_eq_mul] <;>
    push_cast <;> ring

/-- Evaluating `pauliMap` on `σ2` scales it by `ly`. -/
@[simp]
lemma pauliMap_sigma2 (lx ly lz : ℝ) :
    pauliMap lx ly lz (pauliCStar (Sum.inr 1)) = (ly : ℂ) • pauliCStar (Sum.inr 1) := by
  apply CStarMatrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, pauliMap_apply_00, pauliMap_apply_01, pauliMap_apply_10,
      pauliMap_apply_11, pauliCStar, PauliMatrix.pauliMatrix, CStarMatrix.smul_apply,
      CStarMatrix.ofMatrix_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, smul_eq_mul] <;>
    push_cast <;> ring

/-- Evaluating `pauliMap` on `σ3` scales it by `lz`. -/
@[simp]
lemma pauliMap_sigma3 (lx ly lz : ℝ) :
    pauliMap lx ly lz (pauliCStar (Sum.inr 2)) = (lz : ℂ) • pauliCStar (Sum.inr 2) := by
  apply CStarMatrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, pauliMap_apply_00, pauliMap_apply_01, pauliMap_apply_10,
      pauliMap_apply_11, pauliCStar, PauliMatrix.pauliMatrix, CStarMatrix.smul_apply,
      CStarMatrix.ofMatrix_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, smul_eq_mul] <;>
    push_cast <;> ring

/-- Every qubit Pauli map preserves the matrix trace. -/
lemma pauliMap_trace (lx ly lz : ℝ) (A : QubitAlgebra) :
    (CStarMatrix.ofMatrix.symm (pauliMap lx ly lz A)).trace =
      (CStarMatrix.ofMatrix.symm A).trace := by
  simp only [Matrix.trace_fin_two, CStarMatrix.ofMatrix_symm_apply, pauliMap_apply_00,
    pauliMap_apply_11]
  push_cast
  ring

/-- The Pauli map with eigenvalues `(1, 1, 1)` is the identity map. -/
@[simp]
lemma pauliMap_id : pauliMap 1 1 1 = LinearMap.id := by
  ext A i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, pauliMap_apply_00, pauliMap_apply_01, pauliMap_apply_10,
      pauliMap_apply_11, LinearMap.id_apply] <;>
    push_cast <;> ring

/-- Composition of two qubit Pauli maps multiplies their Pauli eigenvalues componentwise. -/
lemma pauliMap_comp (lx₁ ly₁ lz₁ lx₂ ly₂ lz₂ : ℝ) :
    (pauliMap lx₁ ly₁ lz₁).comp (pauliMap lx₂ ly₂ lz₂) =
      pauliMap (lx₁ * lx₂) (ly₁ * ly₂) (lz₁ * lz₂) := by
  ext A i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, LinearMap.comp_apply, pauliMap_apply_00,
      pauliMap_apply_01, pauliMap_apply_10, pauliMap_apply_11] <;>
    push_cast <;> ring

/-!

## C. The Fujiwara–Algoet complete positivity theorem

-/

/-- Matrix unit `|i⟩⟨j|` in `QubitAlgebra`. -/
def qubitMatrixUnit (i j : Fin 2) : QubitAlgebra :=
  CStarMatrix.ofMatrix (Matrix.single i j (1 : ℂ))

/-- The `2 × 2` maximally entangled Choi input matrix `(i, j) ↦ |i⟩⟨j|` over `QubitAlgebra`. -/
def pauliChoiInput : CStarMatrix (Fin 2) (Fin 2) QubitAlgebra :=
  CStarMatrix.ofMatrix (Matrix.of fun i j => qubitMatrixUnit i j)

/-- Square-root factor `V` with `star V * V = pauliChoiInput`. -/
def pauliChoiFactor : CStarMatrix (Fin 2) (Fin 2) QubitAlgebra :=
  CStarMatrix.ofMatrix (Matrix.of fun i j => if i = 0 then qubitMatrixUnit 0 j else 0)

/-- The Choi input matrix is positive because
`pauliChoiInput = star pauliChoiFactor * pauliChoiFactor`. -/
lemma pauliChoiInput_nonneg : (0 : CStarMatrix (Fin 2) (Fin 2) QubitAlgebra) ≤ pauliChoiInput := by
  have h : star pauliChoiFactor * pauliChoiFactor = pauliChoiInput := by
    apply CStarMatrix.ext
    intro i j
    apply CStarMatrix.ext
    intro a b
    fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
      simp [pauliChoiFactor, pauliChoiInput, qubitMatrixUnit, CStarMatrix.mul_apply,
        CStarMatrix.star_apply, Matrix.single]
  rw [← h]
  exact star_mul_self_nonneg pauliChoiFactor

/-- Rank-one projection `|00⟩⟨00|` in `CStarMatrix (Fin 2) (Fin 2) QubitAlgebra`. -/
def pauliBellProj : CStarMatrix (Fin 2) (Fin 2) QubitAlgebra :=
  CStarMatrix.ofMatrix (Matrix.single 0 0 (qubitMatrixUnit 0 0))

/-- `pauliBellProj` is nonnegative because it is a self-adjoint idempotent. -/
lemma pauliBellProj_nonneg : (0 : CStarMatrix (Fin 2) (Fin 2) QubitAlgebra) ≤ pauliBellProj := by
  have h : star pauliBellProj * pauliBellProj = pauliBellProj := by
    apply CStarMatrix.ext
    intro i j
    apply CStarMatrix.ext
    intro a b
    fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
      simp [pauliBellProj, qubitMatrixUnit, CStarMatrix.mul_apply, CStarMatrix.star_apply,
        Matrix.single]
  rw [← h]
  exact star_mul_self_nonneg pauliBellProj

/-- A real multiple of `pauliBellProj` is nonnegative only if the scalar is nonnegative. -/
lemma nonneg_of_smul_pauliBellProj_nonneg {c : ℝ}
    (hc : (0 : CStarMatrix (Fin 2) (Fin 2) QubitAlgebra) ≤ c • pauliBellProj) : 0 ≤ c := by
  by_contra hlt
  push Not at hlt
  have hneg : (0 : CStarMatrix (Fin 2) (Fin 2) QubitAlgebra) ≤ (-c) • pauliBellProj :=
    smul_nonneg (neg_nonneg.mpr hlt.le) pauliBellProj_nonneg
  rw [neg_smul, Left.nonneg_neg_iff] at hneg
  have hzero : c • pauliBellProj = 0 := le_antisymm hneg hc
  have h00 : (c • pauliBellProj) 0 0 0 0 = (0 : ℂ) := by
    rw [hzero]
    rfl
  simp [pauliBellProj, qubitMatrixUnit, CStarMatrix.smul_apply, Matrix.single,
    Complex.real_smul] at h00
  linarith

/-- The four Bell witness operators in `CStarMatrix (Fin 2) (Fin 2) QubitAlgebra` extracting the
four Fujiwara–Algoet eigenvalues of `pauliChoiInput.map (pauliMap lx ly lz)`. -/
def pauliBellWitness (k : Fin 4) : CStarMatrix (Fin 2) (Fin 2) QubitAlgebra :=
  CStarMatrix.ofMatrix <| Matrix.of fun i j =>
    if j ≠ 0 then 0
    else match k, i with
    | 0, 0 => qubitMatrixUnit 0 0
    | 0, 1 => qubitMatrixUnit 1 0
    | 1, 0 => qubitMatrixUnit 1 0
    | 1, 1 => qubitMatrixUnit 0 0
    | 2, 0 => qubitMatrixUnit 1 0
    | 2, 1 => -qubitMatrixUnit 0 0
    | 3, 0 => qubitMatrixUnit 0 0
    | 3, 1 => -qubitMatrixUnit 1 0

/-- Conjugating `pauliChoiInput.map (pauliMap lx ly lz)` by the `k`-th Bell witness isolates the
`k`-th Fujiwara–Algoet expression times `pauliBellProj`. -/
lemma pauliBellWitness_conj_choi (lx ly lz : ℝ) (k : Fin 4) :
    star (pauliBellWitness k) * pauliChoiInput.map (pauliMap lx ly lz) * pauliBellWitness k =
      (![1 + lx + ly + lz, 1 + lx - ly - lz, 1 - lx + ly - lz, 1 - lx - ly + lz] k : ℝ) •
        pauliBellProj := by
  apply CStarMatrix.ext
  intro i j
  apply CStarMatrix.ext
  intro a b
  fin_cases k <;> fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [pauliBellWitness, pauliChoiInput, pauliBellProj, qubitMatrixUnit,
      pauliMap_apply_00, pauliMap_apply_01, pauliMap_apply_10, pauliMap_apply_11,
      CStarMatrix.mul_apply, CStarMatrix.star_apply, CStarMatrix.map_apply,
      Matrix.single, Fin.sum_univ_two, Complex.real_smul]
  all_goals ring

/-- Entrywise application of `pauliMap` decomposes as a real linear combination of the four
completely positive Pauli conjugations. -/
lemma map_pauliMap_eq_sum {k : ℕ} (lx ly lz : ℝ)
    (M : CStarMatrix (Fin k) (Fin k) QubitAlgebra) :
    M.map (pauliMap lx ly lz) =
      ((1 + lx + ly + lz) / 4 : ℝ) • M.map (pauliConj (Sum.inl 0)) +
      ((1 + lx - ly - lz) / 4 : ℝ) • M.map (pauliConj (Sum.inr 0)) +
      ((1 - lx + ly - lz) / 4 : ℝ) • M.map (pauliConj (Sum.inr 1)) +
      ((1 - lx - ly + lz) / 4 : ℝ) • M.map (pauliConj (Sum.inr 2)) := by
  apply CStarMatrix.ext
  intro i j
  simp only [CStarMatrix.map_apply, CStarMatrix.add_apply, CStarMatrix.smul_apply, pauliMap,
    LinearMap.add_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply, StarAlgHom.coe_toAlgHom,
    Complex.coe_smul]
  rfl

/-- The Fujiwara–Algoet theorem: a qubit Pauli map `pauliMap lx ly lz` is completely positive
on `QubitAlgebra` if and only if its Pauli eigenvalues satisfy the four tetrahedron inequalities
`0 ≤ 1 + lx + ly + lz`, `0 ≤ 1 + lx - ly - lz`, `0 ≤ 1 - lx + ly - lz`, and
`0 ≤ 1 - lx - ly + lz`. -/
theorem pauliMap_isCompletelyPositive_iff (lx ly lz : ℝ) :
    (∀ (k : ℕ) (M : CStarMatrix (Fin k) (Fin k) QubitAlgebra),
      0 ≤ M → 0 ≤ M.map (pauliMap lx ly lz)) ↔
      0 ≤ 1 + lx + ly + lz ∧ 0 ≤ 1 + lx - ly - lz ∧
      0 ≤ 1 - lx + ly - lz ∧ 0 ≤ 1 - lx - ly + lz := by
  constructor
  · intro hCP
    have hChoi : 0 ≤ pauliChoiInput.map (pauliMap lx ly lz) :=
      hCP 2 pauliChoiInput pauliChoiInput_nonneg
    have hkey (k : Fin 4) :
        0 ≤ ![1 + lx + ly + lz, 1 + lx - ly - lz, 1 - lx + ly - lz, 1 - lx - ly + lz] k := by
      have hconj := star_left_conjugate_nonneg hChoi (pauliBellWitness k)
      rw [pauliBellWitness_conj_choi] at hconj
      exact nonneg_of_smul_pauliBellProj_nonneg hconj
    exact ⟨hkey 0, hkey 1, hkey 2, hkey 3⟩
  · rintro ⟨h₀, h₁, h₂, h₃⟩ k M hM
    rw [map_pauliMap_eq_sum]
    have hc (μ : Fin 1 ⊕ Fin 3) : 0 ≤ M.map (pauliConj μ) :=
      CompletelyPositiveMapClass.map_cstarMatrix_nonneg' (pauliConj μ) k M hM
    exact add_nonneg
      (add_nonneg
        (add_nonneg (smul_nonneg (by linarith) (hc (Sum.inl 0)))
          (smul_nonneg (by linarith) (hc (Sum.inr 0))))
        (smul_nonneg (by linarith) (hc (Sum.inr 1))))
      (smul_nonneg (by linarith) (hc (Sum.inr 2)))

/-!

## D. Bundled completely positive maps and observable channels

-/

/-- The qubit Pauli map bundled as a Mathlib `CompletelyPositiveMap` whenever `(lx, ly, lz)`
satisfies the Fujiwara–Algoet tetrahedron inequalities. -/
def pauliCPMap (lx ly lz : ℝ)
    (h₀ : 0 ≤ 1 + lx + ly + lz) (h₁ : 0 ≤ 1 + lx - ly - lz)
    (h₂ : 0 ≤ 1 - lx + ly - lz) (h₃ : 0 ≤ 1 - lx - ly + lz) :
    QubitAlgebra →CP QubitAlgebra where
  toLinearMap := pauliMap lx ly lz
  map_cstarMatrix_nonneg' :=
    (pauliMap_isCompletelyPositive_iff lx ly lz).mpr ⟨h₀, h₁, h₂, h₃⟩

/-- The qubit Pauli channel bundled as a `Channel` on the observables of `QubitAlgebra`. -/
def pauliChannel (lx ly lz : ℝ)
    (h₀ : 0 ≤ 1 + lx + ly + lz) (h₁ : 0 ≤ 1 + lx - ly - lz)
    (h₂ : 0 ≤ 1 - lx + ly - lz) (h₃ : 0 ≤ 1 - lx - ly + lz) :
    Channel (ofCStarAlgebra QubitAlgebra) (ofCStarAlgebra QubitAlgebra) :=
  Channel.ofComplex (PositiveLinearMap.ofClass (pauliCPMap lx ly lz h₀ h₁ h₂ h₃))
    (pauliMap_one lx ly lz)

/-- Extending `pauliChannel` back to all operators recovers `pauliMap`. -/
@[simp]
lemma pauliChannel_extend_apply (lx ly lz : ℝ)
    (h₀ : 0 ≤ 1 + lx + ly + lz) (h₁ : 0 ≤ 1 + lx - ly - lz)
    (h₂ : 0 ≤ 1 - lx + ly - lz) (h₃ : 0 ≤ 1 - lx - ly + lz) (A : QubitAlgebra) :
    (pauliChannel lx ly lz h₀ h₁ h₂ h₃).extend A = pauliMap lx ly lz A := by
  have heq := Channel.extend_ofComplex
    (PositiveLinearMap.ofClass (pauliCPMap lx ly lz h₀ h₁ h₂ h₃)) (pauliMap_one lx ly lz)
  exact DFunLike.congr_fun heq A

end

end ProbabilisticTheory
