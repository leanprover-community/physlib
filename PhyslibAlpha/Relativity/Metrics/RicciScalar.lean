/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.Metrics.MetricTrace
public import PhyslibAlpha.Relativity.Metrics.Ricci
public import PhyslibAlpha.Relativity.Tensors.RicciTensor

/-!

# Scalar curvature

The Ricci scalar curvature `R = g^{ij} Ric_{ij}` of a metric and Riemann curvature tensor, and its
coordinate counterpart.

## i. Overview

Contracting the Ricci tensor against the inverse metric produces the scalar curvature invariant
`R = g^{ij} Ric_{ij}`, both for a bundled `MetricTensor` acting on an algebraic `RiemannTensor`
and, coordinate by coordinate, for a metric field and its inverse.  This module defines both
`ricciScalar` functions and verifies that they vanish identically for flat spacetime and for a
constant metric.

## ii. Key results

- `ricciScalar` : scalar curvature `R = ∑ i j, g^{ij} Ric_{ij}` of a `MetricTensor` and a
  `RiemannTensor`.
- `ricciScalar_eq_metricTrace` : the scalar curvature as the metric trace of the Ricci tensor.
- `ricciScalar_flat` : vanishing scalar curvature for flat spacetime.
- `CoordinateCurvature.ricciScalar`, `CoordinateCurvature.ricciScalar_const` : the coordinate
  scalar curvature and its vanishing for a constant metric.

## iii. Table of contents

- A. Scalar curvature
- B. Coordinate scalar curvature

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 3 (Sec. 3.2). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 13.
  [ref: mtw_1973_gravitation]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 3
  (https://arxiv.org/pdf/gr-qc/9712019#page=78). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

/-!

## A. Scalar curvature

The scalar curvature invariant enters the Einstein–Hilbert action and the trace-reversed Einstein
tensor.

-/

/-- Scalar curvature `R = ∑ i j, g^{ij} Ric_{ij}`. -/
noncomputable def ricciScalar {n : ℕ} (M : MetricTensor n) (R : RiemannTensor n) : ℝ :=
  ∑ i, ∑ j, M.ginv i j * ricci M R i j

/-- Scalar curvature is the metric trace of the Ricci tensor. -/
lemma ricciScalar_eq_metricTrace {n : ℕ} (M : MetricTensor n) (R : RiemannTensor n) :
    ricciScalar M R = metricTrace M (ricci M R) := rfl

/-- The flat Riemann curvature tensor has identically vanishing scalar curvature. -/
@[simp]
lemma ricciScalar_flat {n : ℕ} (M : MetricTensor n) :
    ricciScalar M (RiemannTensor.flat n) = 0 := by
  simp [ricciScalar]

namespace CoordinateCurvature

/-!

## B. Coordinate scalar curvature

Contracting the coordinate Ricci tensor with the inverse metric field gives the scalar curvature
of a coordinate metric.

-/

/-- The coordinate scalar curvature `R = ∑ σ ν, g^{σν} Ric_{σν}`. -/
noncomputable def ricciScalar {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n)
    (x : Fin n → ℝ) : ℝ :=
  ∑ σ, ∑ ν, ginv x σ ν * ricciTensor g ginv x σ ν

/-- A constant metric has zero scalar curvature. -/
lemma ricciScalar_const {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) (G : Tensor2 n)
    (hg : ∀ x, g x = G) (x : Fin n → ℝ) : ricciScalar g ginv x = 0 := by
  simp only [ricciScalar]
  apply Finset.sum_eq_zero
  intro σ _
  apply Finset.sum_eq_zero
  intro ν _
  rw [ricciTensor_const g ginv G hg x σ ν]
  ring

end CoordinateCurvature

end GeneralRelativity
