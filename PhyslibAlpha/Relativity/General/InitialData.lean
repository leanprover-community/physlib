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
(`flatData`), and a non-vacuum example (`squeezedData` with `H = 2`) proving that the
constraints are nontrivial. Global development existence (Choquet–Bruhat–Geroch) is quasilinear
hyperbolic PDE theory and is neither formalised nor axiomatised here.

## ii. Key results

- `InitialData`, `InitialData.ham`, `momConstraint`, `InitialData.IsVacuumData` : Cauchy data
  and vacuum constraint equations.
- `InitialData.ham_zero_iff_scalarCurv_zero_of_K_zero` : time-symmetric vacuum data are
  scalar flat.
- `InitialData.ham_eq_of_trace_zero` : maximal-slicing reduction `H = ³R - K_ij K^ij`.
- `flatData_isVacuum` : flat `ℝ³` with `K = 0` satisfies both vacuum constraints.
- `squeezedData_ham_ne_zero` : `K = diag(1, 1, 0)` on flat `ℝ³` has `H = 2 ≠ 0`.

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

-/

/-- Vacuum initial data on a three-dimensional spatial slice: the induced metric `h`, its
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

/-- The momentum constraint `M_i = ∂_j K_ij - ∂_i (tr K)` in flat-slice coordinates, with
partial derivatives supplied as `dK μ i j = ∂_μ K_ij`. -/
noncomputable def momConstraint (dK : Fin 3 → Tensor2 3) (i : Fin 3) : ℝ :=
  (∑ j, dK j i j) - ∑ j, dK i j j

namespace InitialData

/-- The Hamiltonian (energy) constraint `H = ³R + (tr K)² - K_ij K^ij` in orthonormal
coordinates on the slice. -/
noncomputable def ham (D : InitialData) : ℝ :=
  scalarCurv D.h D.R3 + (∑ i, D.K i i) ^ 2 - ∑ i, ∑ j, D.K i j * D.K i j

/-- Combined predicate stating that the data satisfy both vacuum constraints. -/
def IsVacuumData (D : InitialData) (dK : Fin 3 → Tensor2 3) : Prop :=
  D.ham = 0 ∧ ∀ i, momConstraint dK i = 0

/-!

## B. Moment of time symmetry and maximal slicing reductions

-/

/-- At a moment of time symmetry (`K = 0`), the Hamiltonian constraint reduces to the 3D scalar
curvature. -/
lemma ham_eq_scalarCurv_of_K_zero (D : InitialData) (hK : D.K = 0) :
    D.ham = scalarCurv D.h D.R3 := by
  simp [ham, hK]

/-- At a moment of time symmetry (`K = 0`), vanishing Hamiltonian constraint is equivalent to
scalar flatness. -/
lemma ham_zero_iff_scalarCurv_zero_of_K_zero (D : InitialData)
    (hK : D.K = 0) : D.ham = 0 ↔ scalarCurv D.h D.R3 = 0 := by
  rw [ham_eq_scalarCurv_of_K_zero D hK]

/-- Under maximal slicing (`tr K = 0`), the Hamiltonian constraint becomes
`H = ³R - K_ij K^ij`. -/
lemma ham_eq_of_trace_zero (D : InitialData) (htr : (∑ i, D.K i i) = 0) :
    D.ham = scalarCurv D.h D.R3 - ∑ i, ∑ j, D.K i j * D.K i j := by
  simp [ham, htr]

/-- On a scalar-flat slice, `H = 0` forces `(tr K)² = K_ij K^ij`. -/
lemma trace_sq_eq_of_ham_zero (D : InitialData) (hH : D.ham = 0)
    (hR : scalarCurv D.h D.R3 = 0) :
    (∑ i, D.K i i) ^ 2 = ∑ i, ∑ j, D.K i j * D.K i j := by
  simp only [ham] at hH
  linarith

end InitialData

/-- Constant extrinsic curvature (`∂_μ K = 0`) satisfies the momentum constraint identically. -/
lemma momConstraint_zero_of_dK_zero (dK : Fin 3 → Tensor2 3)
    (hdK : ∀ μ, dK μ = 0) : ∀ i, momConstraint dK i = 0 := by
  intro i
  simp [momConstraint, hdK]

/-!

## C. Concrete vacuum and non-vacuum data

-/

/-- The Euclidean metric on `Fin 3`. -/
def euclid3 : MetricTensor 3 where
  g := 1
  ginv := 1
  symm := isSymm_one
  inv_left := one_mul 1
  inv_right := one_mul 1

/-- Flat space `ℝ³` with vanishing extrinsic curvature: the `t = 0` slice of Minkowski
spacetime. -/
def flatData : InitialData where
  h := euclid3
  R3 := RiemannTensor.flat 3
  K := 0
  Ksymm := isSymm_zero

/-- The flat initial slice has vanishing Hamiltonian constraint. -/
lemma flatData_ham_zero : flatData.ham = 0 := by
  rw [InitialData.ham_eq_scalarCurv_of_K_zero flatData rfl]
  show scalarCurv euclid3 (RiemannTensor.flat 3) = 0
  simp [scalarCurv]

/-- Constant zero extrinsic curvature satisfies the momentum constraint. -/
lemma flatData_mom_zero : ∀ i, momConstraint (fun _ => 0) i = 0 :=
  momConstraint_zero_of_dK_zero (fun _ => 0) (fun _ => rfl)

/-- Minkowski's initial slice satisfies both vacuum constraints. -/
lemma flatData_isVacuum : flatData.IsVacuumData (fun _ => 0) :=
  ⟨flatData_ham_zero, flatData_mom_zero⟩

/-- Extrinsic curvature `diag(1, 1, 0)` on flat space. -/
def squeezedK : Tensor2 3 := !![(1 : ℝ), 0, 0; 0, 1, 0; 0, 0, 0]

/-- Symmetry of `squeezedK`. -/
lemma squeezedK_symm : IsSymm squeezedK := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [squeezedK]

/-- Flat space with `K = diag(1, 1, 0)`. -/
def squeezedData : InitialData where
  h := euclid3
  R3 := RiemannTensor.flat 3
  K := squeezedK
  Ksymm := squeezedK_symm

/-- The Hamiltonian constraint of `squeezedData` equals `(tr K)² - K_ij K^ij = 4 - 2 = 2`. -/
lemma squeezedData_ham : squeezedData.ham = 2 := by
  simp [InitialData.ham, squeezedData, euclid3, squeezedK, scalarCurv,
    Fin.sum_univ_three]
  norm_num

/-- Thus the vacuum constraints are not automatic even on flat space. -/
lemma squeezedData_ham_ne_zero : squeezedData.ham ≠ 0 := by
  rw [squeezedData_ham]
  norm_num

end GeneralRelativity
