/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import PhyslibAlpha.Relativity.General.InitialData.FlatSlice
import Mathlib.Tactic.NormNum

/-!

# Anisotropic non-vacuum ADM initial slice

Concrete non-vacuum ADM Cauchy data `anisotropicSliceData` on flat Euclidean `ℝ³` with Hamiltonian
constraint `H = 2 ≠ 0`.

## i. Overview

Equipping flat Euclidean 3-space `euclideanMetric3` with the anisotropic extrinsic curvature
`K = diag(1, 1, 0)` yields a non-vacuum slice `anisotropicSliceData` whose Hamiltonian constraint
evaluates to `H = (tr K)² - K_ij K^ij = 4 - 2 = 2 ≠ 0`, proving that the ADM vacuum constraints
are nontrivial even on spatially flat slices.

## ii. Key results

- `anisotropicExtrinsicCurvature`, `anisotropicSliceData` : flat `ℝ³` Cauchy data with
  anisotropic extrinsic curvature `K = diag(1, 1, 0)`.
- `anisotropicSliceData_hamiltonianConstraint`,
  `anisotropicSliceData_hamiltonianConstraint_ne_zero` : evaluation `H = 2` and non-vacuum proof.

## iii. Table of contents

- A. Anisotropic extrinsic curvature and non-vacuum witness

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 10 (Sec. 10.2). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 21.
  [ref: mtw_1973_gravitation]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 4
  (https://arxiv.org/pdf/gr-qc/9712019#page=104). [ref: Carroll1997]
* R. Arnowitt, S. Deser, and C. W. Misner, *The Dynamics of General Relativity*, in *Gravitation: An
  Introduction to Current Research* (1962) (https://arxiv.org/pdf/gr-qc/0405109#page=1).
  [ref: ADM1962]
-/

@[expose] public section

namespace GeneralRelativity

/-!

## A. Anisotropic extrinsic curvature and non-vacuum witness

An explicit non-zero extrinsic curvature on Euclidean `ℝ³` demonstrates that spatial flatness alone
does not guarantee satisfaction of the ADM Hamiltonian constraint.

-/

/-- Anisotropic extrinsic curvature `K = diag(1, 1, 0)` on flat Euclidean space, representing a
spatial slice contracting or expanding along two axes but not the third. -/
def anisotropicExtrinsicCurvature : Tensor2 3 := !![(1 : ℝ), 0, 0; 0, 1, 0; 0, 0, 0]

/-- Symmetry of `anisotropicExtrinsicCurvature`. -/
lemma anisotropicExtrinsicCurvature_symm : IsSymm anisotropicExtrinsicCurvature := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [anisotropicExtrinsicCurvature]

/-- Non-vacuum ADM test slice on flat Euclidean `ℝ³` with anisotropic extrinsic curvature
`K = diag(1, 1, 0)`. -/
def anisotropicSliceData : InitialData where
  h := euclideanMetric3
  R3 := RiemannTensor.flat 3
  K := anisotropicExtrinsicCurvature
  Ksymm := anisotropicExtrinsicCurvature_symm

/-- The Hamiltonian constraint of `anisotropicSliceData` equals
`(tr K)² - K_ij K^ij = 4 - 2 = 2`. -/
lemma anisotropicSliceData_hamiltonianConstraint :
    anisotropicSliceData.hamiltonianConstraint = 2 := by
  simp [InitialData.hamiltonianConstraint, anisotropicSliceData, euclideanMetric3,
    anisotropicExtrinsicCurvature, ricciScalar, metricTrace, Fin.sum_univ_three]
  norm_num

/-- Non-vanishing Hamiltonian constraint (`H = 2 ≠ 0`), showing that the ADM vacuum constraints
are non-trivial even on spatially flat slices. -/
lemma anisotropicSliceData_hamiltonianConstraint_ne_zero :
    anisotropicSliceData.hamiltonianConstraint ≠ 0 := by
  rw [anisotropicSliceData_hamiltonianConstraint]
  norm_num

end GeneralRelativity
