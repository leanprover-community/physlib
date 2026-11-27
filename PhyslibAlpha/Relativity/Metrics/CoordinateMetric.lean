/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Data.Set.Basic
public import PhyslibAlpha.Relativity.Metrics.Pipeline

/-!

# Coordinate metrics

Spacetime metrics on coordinate charts, pointwise `MetricTensor` restrictions, and coordinate
curvature operators.

## i. Overview

A `CoordinateMetric n` pairs a coordinate-dependent symmetric metric field `g_{ij}(x)` with its
inverse `g^{ij}(x)` and the regular chart domain on which they are two-sided inverses. At any
regular point in the domain, `CoordinateMetric.metricTensor` restricts it to a pointwise
`MetricTensor n`, while `christoffel`, `riemann`, `ricciTensor`, `ricciScalar`, and
`einsteinTensor` evaluate the Levi-Civita connection and curvature tensors on the chart.

## ii. Key results

- `CoordinateMetric`, `CoordinateMetric.metricTensor` : coordinate metric field with its regular
  domain and pointwise `MetricTensor` restriction.
- `CoordinateMetric.christoffel`, `CoordinateMetric.riemann`, `CoordinateMetric.ricciTensor`,
  `CoordinateMetric.ricciScalar`, `CoordinateMetric.einsteinTensor` : the Levi-Civita
  connection and curvature tensors of a `CoordinateMetric`.

## iii. Table of contents

- A. Coordinate metrics and curvature operators

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 3 (Sec. 3.1). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 8 & Ch. 13.
  [ref: mtw_1973_gravitation]
* B. O'Neill, *Semi-Riemannian Geometry With Applications to Relativity* (1983), Ch. 3.
  [ref: oneill_1983_semi_riemannian]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 3
  (https://arxiv.org/pdf/gr-qc/9712019#page=58). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

/-!

## A. Coordinate metrics and curvature operators

A `CoordinateMetric` records a coordinate-dependent metric tensor field `g_{ij}(x)` together with
its inverse `g^{ij}(x)` and the regular coordinate domain where both remain nondegenerate.

-/

/-- A coordinate-chart metric field `g` paired with its inverse `ginv` and regularity domain. -/
structure CoordinateMetric (n : ℕ) where
  /-- The covariant metric component field `g_{ij}(x)`. -/
  g : (Fin n → ℝ) → Tensor2 n
  /-- The contravariant inverse metric component field `g^{ij}(x)`. -/
  ginv : (Fin n → ℝ) → Tensor2 n
  /-- Regular coordinate domain where `g` is nondegenerate. -/
  domain : Set (Fin n → ℝ)
  /-- Symmetry of the covariant metric at every point. -/
  symm : ∀ x, IsSymm (g x)
  /-- Left-to-right inverse relation `g(x) * ginv(x) = 1` on `domain`. -/
  inv_left : ∀ x ∈ domain, g x * ginv x = 1
  /-- Right-to-left inverse relation `ginv(x) * g(x) = 1` on `domain`. -/
  inv_right : ∀ x ∈ domain, ginv x * g x = 1

/-- Restrict a coordinate metric to a pointwise `MetricTensor` at a regular point in its
domain. -/
def CoordinateMetric.metricTensor {n : ℕ} (C : CoordinateMetric n) (x : Fin n → ℝ)
    (hx : x ∈ C.domain) : MetricTensor n where
  g := C.g x
  ginv := C.ginv x
  symm := C.symm x
  inv_left := C.inv_left x hx
  inv_right := C.inv_right x hx

/-- Christoffel symbols of a `CoordinateMetric`. -/
noncomputable def CoordinateMetric.christoffel {n : ℕ} (C : CoordinateMetric n)
    (x : Fin n → ℝ) (k i j : Fin n) : ℝ :=
  CoordinateCurvature.christoffel C.g C.ginv x k i j

/-- Riemann curvature tensor of a `CoordinateMetric`. -/
noncomputable def CoordinateMetric.riemann {n : ℕ} (C : CoordinateMetric n)
    (x : Fin n → ℝ) (ρ σ μ ν : Fin n) : ℝ :=
  CoordinateCurvature.riemann C.g C.ginv x ρ σ μ ν

/-- Ricci tensor of a `CoordinateMetric`. -/
noncomputable def CoordinateMetric.ricciTensor {n : ℕ} (C : CoordinateMetric n)
    (x : Fin n → ℝ) (σ ν : Fin n) : ℝ :=
  CoordinateCurvature.ricciTensor C.g C.ginv x σ ν

/-- Scalar curvature of a `CoordinateMetric`. -/
noncomputable def CoordinateMetric.ricciScalar {n : ℕ} (C : CoordinateMetric n)
    (x : Fin n → ℝ) : ℝ :=
  CoordinateCurvature.ricciScalar C.g C.ginv x

/-- Einstein tensor of a `CoordinateMetric`. -/
noncomputable def CoordinateMetric.einsteinTensor {n : ℕ} (C : CoordinateMetric n)
    (x : Fin n → ℝ) (i j : Fin n) : ℝ :=
  CoordinateCurvature.einsteinTensor C.g C.ginv x i j

end GeneralRelativity
