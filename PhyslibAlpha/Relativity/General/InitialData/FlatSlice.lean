/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.General.InitialData.Basic

/-!

# Flat ADM initial slice

Concrete vacuum ADM Cauchy data (`flatInitialData`) on flat Euclidean `ℝ³` (`euclideanMetric3`).

## i. Overview

On flat Euclidean 3-space `euclideanMetric3`, taking zero extrinsic curvature (`K = 0`) gives
Minkowski's `t = 0` slice `flatInitialData`, which satisfies both the Hamiltonian and momentum
vacuum constraints identically.

## ii. Key results

- `euclideanMetric3`, `flatInitialData` : Euclidean 3-metric and Minkowski `t = 0` Cauchy data.
- `flatInitialData_hamiltonianConstraint_zero`, `flatInitialData_momentumConstraint_zero`,
  `flatInitialData_isVacuum` : verification that flat `ℝ³` with `K = 0` satisfies both vacuum
  constraints.

## iii. Table of contents

- A. Flat Euclidean Cauchy slice

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

## A. Flat Euclidean Cauchy slice

Equipping the identity metric `euclideanMetric3` with flat 3D curvature and zero extrinsic curvature
produces vacuum initial data for Minkowski spacetime.

-/

/-- The Euclidean metric `δ_{ij}` on `Fin 3`. -/
def euclideanMetric3 : MetricTensor 3 where
  g := 1
  ginv := 1
  symm := Matrix.isSymm_one
  inv_left := one_mul 1
  inv_right := one_mul 1

/-- Flat space `ℝ³` with vanishing extrinsic curvature: the `t = 0` slice of Minkowski
spacetime. -/
def flatInitialData : InitialData where
  h := euclideanMetric3
  R3 := RiemannTensor.flat 3
  K := 0
  Ksymm := Matrix.isSymm_zero

/-- The flat initial slice has vanishing Hamiltonian constraint. -/
lemma flatInitialData_hamiltonianConstraint_zero : flatInitialData.hamiltonianConstraint = 0 := by
  rw [InitialData.hamiltonianConstraint_eq_ricciScalar_of_K_zero flatInitialData rfl]
  exact ricciScalar_flat euclideanMetric3

/-- Zero extrinsic curvature has zero covariant derivative, so the flat slice satisfies the
momentum constraint. -/
lemma flatInitialData_momentumConstraint_zero :
    ∀ i, flatInitialData.momentumConstraint 0 (fun _ => 0) i = 0 := by
  apply InitialData.momentumConstraint_zero_of_covariantDeriv_zero
  intro μ i j
  simp [InitialData.covariantDerivTensor2, flatInitialData]

/-- Minkowski's initial slice satisfies both vacuum constraints. -/
lemma flatInitialData_isVacuum : flatInitialData.IsVacuumData 0 (fun _ => 0) :=
  ⟨flatInitialData_hamiltonianConstraint_zero, flatInitialData_momentumConstraint_zero⟩

end GeneralRelativity
