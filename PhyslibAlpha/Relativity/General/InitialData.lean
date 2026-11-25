/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.Matrix.Notation
public import PhyslibAlpha.Relativity.Metrics.Basic
public import PhyslibAlpha.Relativity.Metrics.ScalarCurvature
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!

# The initial value problem: constraint equations

The Hamiltonian and momentum constraints on a three-dimensional Cauchy slice.

## i. Overview

In the ADM 3+1 decomposition of vacuum general relativity, initial data on a spatial slice `Σ`
consist of a Riemannian 3-metric `h`, its 3D curvature tensor `R3`, and a symmetric extrinsic
curvature `K`. The normal components of `G = 0` impose the Hamiltonian constraint
`H = ³R + (tr K)² - K_ij K^ij = 0` and the momentum constraint `M_i = ∂_j K_ij - ∂_i (tr K) = 0`.

This module formalises the constraint functions, their reductions under a moment of time
symmetry (`K = 0`) and maximal slicing (`tr K = 0`), a concrete flat vacuum data set
(`flatData`), and a non-vacuum example with anisotropic extrinsic curvature
(`anisotropicSliceData` with `H = 2`) proving that the constraints are nontrivial. Global
development existence (Choquet–Bruhat–Geroch) is quasilinear hyperbolic PDE theory and is neither
formalised nor axiomatised here.

## ii. Key results

- `InitialData`, `InitialData.hamiltonianConstraint`, `InitialData.momentumConstraint`,
  `InitialData.IsVacuumData` : Cauchy data and vacuum constraint equations.
- `InitialData.ham_zero_iff_scalarCurv_zero_of_K_zero` : time-symmetric vacuum data are
  scalar flat.
- `InitialData.hamiltonianConstraint_eq_of_trace_zero` : maximal-slicing reduction `H = ³R - K_ij
  K^ij`.
- `flatData_isVacuum` : flat `ℝ³` with `K = 0` satisfies both vacuum constraints.
- `anisotropicSliceData_hamiltonianConstraint_ne_zero` : anisotropic extrinsic curvature
  `K = diag(1, 1, 0)` on flat `ℝ³` yields Hamiltonian constraint `H = 2 ≠ 0`.

## iii. Table of contents

- A. Initial data and constraint equations
- B. Moment of time symmetry and maximal slicing reductions
- C. Concrete vacuum and non-vacuum data

## iv. References

* R. M. Wald, *General Relativity* (1984). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973). [ref: mtw_1973_gravitation]

-/

@[expose] public section

namespace GeneralRelativity

/-!

## A. Initial data and constraint equations

An ADM Cauchy slice packages the induced Riemannian 3-metric `h`, its spatial Riemann curvature
`R3`, and the extrinsic curvature `K_{ij}` measuring how the slice embeds into 4D spacetime.

-/

/-- Initial data on a three-dimensional spatial slice: the induced Riemannian metric `h`, its
Riemann tensor `R3`, and the symmetric extrinsic curvature `K`. -/
structure InitialData where
  /-- Induced Riemannian 3-metric on the spatial slice. -/
  h : MetricTensor 3
  /-- Three-dimensional Riemann curvature tensor of `h`. -/
  R3 : RiemannTensor 3
  /-- Symmetric extrinsic curvature `K_{ij}` of the slice. -/
  K : Tensor2 3
  /-- Symmetry of the extrinsic curvature. -/
  Ksymm : IsSymm K

namespace InitialData

/-- The momentum constraint `M_i = g^{jk} ∂_j K_{ik} - g^{jk} ∂_i K_{jk}` on a spatial slice `D`,
with partial derivatives supplied as `dK μ i j = ∂_μ K_{ij}`. -/
noncomputable def momentumConstraint (D : InitialData) (dK : Fin 3 → Tensor2 3) (i : Fin 3) :
    ℝ :=
  (∑ j, ∑ k, D.h.ginv j k * dK j i k) - ∑ j, ∑ k, D.h.ginv j k * dK i j k

/-- The Hamiltonian (energy) constraint `H = ³R + (tr K)² - K_ij K^ij`, contracting `K` with the
inverse spatial metric `D.h.ginv`. -/
noncomputable def hamiltonianConstraint (D : InitialData) : ℝ :=
  ricciScalar D.h D.R3 + (metricTrace D.h D.K) ^ 2
    - ∑ i, ∑ j, ∑ k, ∑ l, D.h.ginv i k * D.h.ginv j l * D.K i j * D.K k l

/-- Combined predicate stating that the data satisfy both vacuum constraints. -/
def IsVacuumData (D : InitialData) (dK : Fin 3 → Tensor2 3) : Prop :=
  D.hamiltonianConstraint = 0 ∧ ∀ i, D.momentumConstraint dK i = 0

/-!

## B. Moment of time symmetry and maximal slicing reductions

At a moment of time symmetry (`K = 0`) or maximal slicing (`tr K = 0`), the Hamiltonian constraint
simplifies directly into algebraic conditions on the spatial scalar curvature `³R`.

-/

/-- At a moment of time symmetry (`K = 0`), the Hamiltonian constraint reduces to the 3D scalar
curvature. -/
lemma hamiltonianConstraint_eq_ricciScalar_of_K_zero (D : InitialData) (hK : D.K = 0) :
    D.hamiltonianConstraint = ricciScalar D.h D.R3 := by
  simp [hamiltonianConstraint, metricTrace, hK]

/-- At a moment of time symmetry (`K = 0`), vanishing Hamiltonian constraint is equivalent to
scalar flatness. -/
lemma ham_zero_iff_scalarCurv_zero_of_K_zero (D : InitialData)
    (hK : D.K = 0) : D.hamiltonianConstraint = 0 ↔ ricciScalar D.h D.R3 = 0 := by
  rw [hamiltonianConstraint_eq_ricciScalar_of_K_zero D hK]

/-- Under maximal slicing (`tr K = 0`), the Hamiltonian constraint becomes
`H = ³R - K_ij K^ij`. -/
lemma hamiltonianConstraint_eq_of_trace_zero (D : InitialData) (htr : metricTrace D.h D.K = 0) :
    D.hamiltonianConstraint =
      ricciScalar D.h D.R3 -
        ∑ i, ∑ j, ∑ k, ∑ l, D.h.ginv i k * D.h.ginv j l * D.K i j * D.K k l := by
  simp [hamiltonianConstraint, htr]

/-- On a scalar-flat slice, `H = 0` forces `(tr K)² = K_ij K^ij`. -/
lemma trace_sq_eq_of_ham_zero (D : InitialData) (hH : D.hamiltonianConstraint = 0)
    (hR : ricciScalar D.h D.R3 = 0) :
    (metricTrace D.h D.K) ^ 2 =
      ∑ i, ∑ j, ∑ k, ∑ l, D.h.ginv i k * D.h.ginv j l * D.K i j * D.K k l := by
  simp only [hamiltonianConstraint] at hH
  linarith

/-- Constant extrinsic curvature (`∂_μ K = 0`) satisfies the momentum constraint identically. -/
lemma momConstraint_zero_of_dK_zero (D : InitialData) (dK : Fin 3 → Tensor2 3)
    (hdK : ∀ μ, dK μ = 0) : ∀ i, D.momentumConstraint dK i = 0 := by
  intro i
  simp [momentumConstraint, hdK]

end InitialData

/-!

## C. Concrete vacuum and non-vacuum data

Flat Euclidean `ℝ³` with zero extrinsic curvature solves both vacuum constraints, whereas a
spatially flat slice carrying anisotropic extrinsic curvature violates the vacuum Hamiltonian
constraint.

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
