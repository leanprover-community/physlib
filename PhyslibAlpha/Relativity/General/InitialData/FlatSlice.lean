/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import PhyslibAlpha.Relativity.General.InitialData.Basic
import Mathlib.Tactic.NormNum

/-!

# Flat and anisotropic ADM initial slices

Concrete vacuum (`flatData`) and non-vacuum (`anisotropicSliceData`) ADM Cauchy data on flat
Euclidean `ℝ³`.

## i. Overview

On flat Euclidean 3-space `euclid3`, taking zero extrinsic curvature (`K = 0`) gives Minkowski's
`t = 0` slice `flatData`, which satisfies both the Hamiltonian and momentum vacuum constraints. In
contrast, equipping `euclid3` with the anisotropic extrinsic curvature `K = diag(1, 1, 0)` yields a
non-vacuum slice (`anisotropicSliceData`) with Hamiltonian constraint `H = 2 ≠ 0`, proving that
the ADM vacuum constraints are nontrivial even on spatially flat slices.

## ii. Key results

- `euclid3`, `flatData`, `flatData_isVacuum` : flat `ℝ³` with `K = 0` satisfies both vacuum
  constraints.
- `anisotropicSliceData`, `anisotropicSliceData_hamiltonianConstraint`,
  `anisotropicSliceData_hamiltonianConstraint_ne_zero` : anisotropic extrinsic curvature
  `K = diag(1, 1, 0)` on flat `ℝ³` yields Hamiltonian constraint `H = 2 ≠ 0`.

## iii. Table of contents

- A. Flat and anisotropic Cauchy slices

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

## A. Flat and anisotropic Cauchy slices

-/

/-- The Euclidean metric on `Fin 3`. -/
def euclid3 : MetricTensor 3 where
  g := 1
  ginv := 1
  symm := Matrix.isSymm_one
  inv_left := one_mul 1
  inv_right := one_mul 1

/-- Flat space `ℝ³` with vanishing extrinsic curvature: the `t = 0` slice of Minkowski
spacetime. -/
def flatData : InitialData where
  h := euclid3
  R3 := RiemannTensor.flat 3
  K := 0
  Ksymm := Matrix.isSymm_zero

/-- The flat initial slice has vanishing Hamiltonian constraint. -/
lemma flatData_ham_zero : flatData.hamiltonianConstraint = 0 := by
  rw [InitialData.hamiltonianConstraint_eq_ricciScalar_of_K_zero flatData rfl]
  show ricciScalar euclid3 (RiemannTensor.flat 3) = 0
  simp [ricciScalar]

/-- Constant zero extrinsic curvature satisfies the momentum constraint. -/
lemma flatData_mom_zero : ∀ i, flatData.momentumConstraint (fun _ => 0) i = 0 :=
  InitialData.momConstraint_zero_of_dK_zero flatData (fun _ => 0) (fun _ => rfl)

/-- Minkowski's initial slice satisfies both vacuum constraints. -/
lemma flatData_isVacuum : flatData.IsVacuumData (fun _ => 0) :=
  ⟨flatData_ham_zero, flatData_mom_zero⟩

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
  h := euclid3
  R3 := RiemannTensor.flat 3
  K := anisotropicExtrinsicCurvature
  Ksymm := anisotropicExtrinsicCurvature_symm

/-- The Hamiltonian constraint of `anisotropicSliceData` equals
`(tr K)² - K_ij K^ij = 4 - 2 = 2`. -/
lemma anisotropicSliceData_hamiltonianConstraint :
    anisotropicSliceData.hamiltonianConstraint = 2 := by
  simp [InitialData.hamiltonianConstraint, anisotropicSliceData, euclid3,
    anisotropicExtrinsicCurvature, ricciScalar, metricTrace, Fin.sum_univ_three]
  norm_num

/-- Non-vanishing Hamiltonian constraint (`H = 2 ≠ 0`), showing that the ADM vacuum constraints
are non-trivial even on spatially flat slices. -/
lemma anisotropicSliceData_hamiltonianConstraint_ne_zero :
    anisotropicSliceData.hamiltonianConstraint ≠ 0 := by
  rw [anisotropicSliceData_hamiltonianConstraint]
  norm_num

end GeneralRelativity
