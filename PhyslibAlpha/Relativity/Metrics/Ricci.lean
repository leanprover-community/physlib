/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.Metrics.Riemann

/-!

# Coordinate Ricci curvature

Ricci tensor and scalar curvature obtained by contracting the coordinate Riemann tensor.

## i. Overview

The Ricci tensor `Ric_{σν} = ∑ ρ, R^ρ_{σρν}` contracts the coordinate Riemann tensor, and the
scalar curvature `R = ∑ σ ν, g^{σν} Ric_{σν}` contracts the Ricci tensor with the inverse metric.
The chart-level API is `CoordinateMetric.ricciTensor` and `CoordinateMetric.ricciScalar`.

## ii. Key results

- `CoordinateCurvature.ricciTensor` : coordinate Ricci tensor.
- `CoordinateCurvature.ricciScalar` : coordinate scalar curvature.
- `CoordinateMetric.ricciTensor`, `CoordinateMetric.ricciScalar` : Ricci curvature of a
  `CoordinateMetric`.

## iii. Table of contents

- A. Ricci tensor and scalar curvature

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 3 (Sec. 3.2). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 8 & Ch. 13.
  [ref: mtw_1973_gravitation]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 3 (Sec. 3.7)
  (https://arxiv.org/pdf/gr-qc/9712019#page=80). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

namespace CoordinateCurvature

/-!

## A. Ricci tensor and scalar curvature

Contracting the Riemann tensor in its first and third indices gives the Ricci tensor, and a
further contraction with the inverse metric gives the scalar curvature.

-/

/-- The coordinate Ricci tensor `Ric_{σν} = ∑ ρ, R^ρ_{σρν}`. -/
noncomputable def ricciTensor {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n)
    (x : Fin n → ℝ) (σ ν : Fin n) : ℝ :=
  ∑ ρ, riemann g ginv x ρ σ ρ ν

/-- The coordinate scalar curvature `R = ∑ σ ν, g^{σν} Ric_{σν}`. -/
noncomputable def ricciScalar {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n)
    (x : Fin n → ℝ) : ℝ :=
  ∑ σ, ∑ ν, ginv x σ ν * ricciTensor g ginv x σ ν

end CoordinateCurvature

/-- Ricci tensor of a `CoordinateMetric`. -/
noncomputable def CoordinateMetric.ricciTensor {n : ℕ} (C : CoordinateMetric n)
    (x : Fin n → ℝ) (σ ν : Fin n) : ℝ :=
  CoordinateCurvature.ricciTensor C.g C.ginv x σ ν

/-- Unfolding lemma for `CoordinateMetric.ricciTensor`. -/
@[simp] lemma CoordinateMetric.ricciTensor_apply {n : ℕ} (C : CoordinateMetric n)
    (x : Fin n → ℝ) (σ ν : Fin n) :
    C.ricciTensor x σ ν = CoordinateCurvature.ricciTensor C.g C.ginv x σ ν := rfl

/-- Scalar curvature of a `CoordinateMetric`. -/
noncomputable def CoordinateMetric.ricciScalar {n : ℕ} (C : CoordinateMetric n)
    (x : Fin n → ℝ) : ℝ :=
  CoordinateCurvature.ricciScalar C.g C.ginv x

/-- Unfolding lemma for `CoordinateMetric.ricciScalar`. -/
@[simp] lemma CoordinateMetric.ricciScalar_apply {n : ℕ} (C : CoordinateMetric n)
    (x : Fin n → ℝ) : C.ricciScalar x = CoordinateCurvature.ricciScalar C.g C.ginv x := rfl

end GeneralRelativity
