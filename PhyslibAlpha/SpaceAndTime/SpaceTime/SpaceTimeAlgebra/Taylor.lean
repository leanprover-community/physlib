/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import PhyslibAlpha.SpaceAndTime.SpaceTime.SpaceTimeAlgebra.Basic
/-!
# Taylor data of matrices of jets

Matrices of jets are determined by, and can be built from, their base-point Taylor data.

## i. Overview

A jet is determined by the base-point values of its iterated derivatives, and every family of
such values is realized by a jet, `SpaceTimeAlgebra.ofDerivValues` (both in Physlib). This file
carries these two facts, Taylor determinacy and Taylor completeness, over to matrices of jets
entrywise. `taylorMatrix` builds the matrix of jets with prescribed base-point Taylor data, and
`derivValueMatrix` reads the base-point Taylor data off a matrix of jets. They are what make a
Lie algebra jet of a matrix gauge group determined by, and freely prescribed through, its
base-point Taylor data.

## ii. Key results

- `SpaceTimeAlgebra.taylorMatrix` : the matrix of jets with prescribed base-point Taylor data.
- `SpaceTimeAlgebra.map_constantCoeff_iteratedPDeriv_taylorMatrix` : Taylor completeness for
  matrices of jets.
- `SpaceTimeAlgebra.derivValueMatrix` : the base-point Taylor data of a matrix of jets.
- `SpaceTimeAlgebra.derivValueMatrix_eq_smul_map_coeff` : the base-point derivative along
  `s` is `s!` times the matrix of Taylor coefficients of `x^s`.
- `SpaceTimeAlgebra.matrix_ext_of_derivValueMatrix` : Taylor determinacy for matrices of jets.

## iii. Table of contents

- A. Taylor completeness
- B. Base-point derivatives of matrices of jets

## iv. References

* None.

-/

@[expose] public section

namespace SpaceTimeAlgebra

open MvPowerSeries

/-!

## A. Taylor completeness

-/

/-- The matrix of jets with prescribed base-point Taylor data `M`, entrywise. -/
noncomputable def taylorMatrix {κ : Type} (M : Multiset (Fin 1 ⊕ Fin 3) → Matrix κ κ ℂ) :
    Matrix κ κ SpaceTimeAlgebra :=
  Matrix.of fun i j => ofDerivValues fun s => M s i j

/-- An entry of `taylorMatrix M` is the jet with the Taylor data of that entry. -/
lemma taylorMatrix_apply {κ : Type} (M : Multiset (Fin 1 ⊕ Fin 3) → Matrix κ κ ℂ) (i j : κ) :
    taylorMatrix M i j = ofDerivValues fun s => M s i j :=
  rfl

/-- The base-point Taylor data of `taylorMatrix M` are `M`, entrywise. -/
lemma map_constantCoeff_iteratedPDeriv_taylorMatrix {κ : Type}
    (M : Multiset (Fin 1 ⊕ Fin 3) → Matrix κ κ ℂ) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    (taylorMatrix M).map (fun f => constantCoeff (iteratedPDeriv s f)) = M s := by
  ext i j
  rw [Matrix.map_apply, taylorMatrix_apply, constantCoeff_iteratedPDeriv_ofDerivValues]

/-!

## B. Base-point derivatives of matrices of jets

-/

section DerivValueMatrix

variable {κ : Type}

/-- The base-point values of the iterated derivatives of a matrix of jets along a multiset
  of directions, taken entrywise. These are the Taylor coefficients up to the factorial
  factor, matching `SpaceTimeAlgebra.ofDerivValues`. -/
noncomputable def derivValueMatrix (s : Multiset (Fin 1 ⊕ Fin 3))
    (A : Matrix κ κ SpaceTimeAlgebra) : Matrix κ κ ℂ :=
  A.map fun f => constantCoeff (iteratedPDeriv s f)

/-- One more direction in `s` differentiates the matrix entrywise first. -/
lemma derivValueMatrix_cons (μ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (A : Matrix κ κ SpaceTimeAlgebra) :
    derivValueMatrix (μ ::ₘ s) A = derivValueMatrix s (A.map (pderiv μ)) := by
  ext i j
  simp [derivValueMatrix]

/-- The base-point Taylor data of a matrix of jets are additive. -/
lemma derivValueMatrix_add (s : Multiset (Fin 1 ⊕ Fin 3)) (A B : Matrix κ κ SpaceTimeAlgebra) :
    derivValueMatrix s (A + B) = derivValueMatrix s A + derivValueMatrix s B := by
  ext i j
  simp [derivValueMatrix, iteratedPDeriv_add]

/-- The base-point Taylor data of a matrix of jets commute with real scaling. -/
lemma derivValueMatrix_real_smul (s : Multiset (Fin 1 ⊕ Fin 3)) (r : ℝ)
    (A : Matrix κ κ SpaceTimeAlgebra) :
    derivValueMatrix s (r • A) = r • derivValueMatrix s A := by
  ext i j
  simp only [derivValueMatrix, Matrix.map_apply, Matrix.smul_apply]
  rw [← algebraMap_smul ℂ r, iteratedPDeriv_smul, MvPowerSeries.constantCoeff_smul,
    algebraMap_smul]

@[simp]
lemma derivValueMatrix_zero_right (s : Multiset (Fin 1 ⊕ Fin 3)) :
    derivValueMatrix s (0 : Matrix κ κ SpaceTimeAlgebra) = 0 := by
  ext i j
  simp [derivValueMatrix]

variable [Fintype κ] [DecidableEq κ]

@[simp]
lemma derivValueMatrix_zero (A : Matrix κ κ SpaceTimeAlgebra) :
    derivValueMatrix 0 A = (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix A := rfl

omit [Fintype κ] [DecidableEq κ] in
/-- The base-point derivative of a matrix of jets along `s` is `s!` times its matrix of
  Taylor coefficients of `x^s`, with `s!` the product of the factorials of the
  multiplicities in `s`. -/
lemma derivValueMatrix_eq_smul_map_coeff (s : Multiset (Fin 1 ⊕ Fin 3))
    (A : Matrix κ κ SpaceTimeAlgebra) :
    derivValueMatrix s A = ((∏ ν, (s.count ν).factorial : ℕ) : ℝ) •
      A.map (coeff (Multiset.toFinsupp s)) := by
  ext i j
  simp only [derivValueMatrix, Matrix.map_apply, Matrix.smul_apply, constantCoeff_iteratedPDeriv,
    Complex.real_smul, Complex.ofReal_natCast]

omit [Fintype κ] [DecidableEq κ] in
/-- A matrix of jets is determined by its base-point derivatives. -/
lemma matrix_ext_of_derivValueMatrix {A B : Matrix κ κ SpaceTimeAlgebra}
    (h : ∀ s, derivValueMatrix s A = derivValueMatrix s B) : A = B :=
  Matrix.ext fun i j => ext_of_constantCoeff_iteratedPDeriv fun s =>
    congrArg (fun M => M i j) (h s)

end DerivValueMatrix

end SpaceTimeAlgebra
