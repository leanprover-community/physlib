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

Coordinate-chart metric fields (`CoordinateMetric`), regular chart `MetricTensor` projections,
and `CoordinateMetric` methods delegating to `GeneralRelativity.Pipeline`.

## i. Overview

A `CoordinateMetric n` packages a coordinate-dependent symmetric metric field `g`, its inverse
`ginv`, and the regular chart `domain` on which `g` and `ginv` are two-sided inverses. At any
point `x ∈ C.domain`, `C.metricTensor x hx` yields a bundled `MetricTensor n`, while
`CoordinateMetric.{christoffel, riemann, ricciTensorOf, ricciScalarOf, einsteinTensorOf}`
delegate directly to `Pipeline`.

## ii. Key results

- `CoordinateMetric`, `CoordinateMetric.metricTensor` : coordinate metric field bundled with its
  regular domain and two-sided inverse proofs.
- `CoordinateMetric.christoffel`, `CoordinateMetric.riemann`, `CoordinateMetric.ricciTensorOf`,
  `CoordinateMetric.ricciScalarOf`, `CoordinateMetric.einsteinTensorOf` : coordinate curvature
  operators for `CoordinateMetric`.

## iii. Table of contents

- A. Coordinate metric bundles and pipeline projections

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

## A. Coordinate metric bundles and pipeline projections

A `CoordinateMetric` bundles a coordinate-dependent metric tensor field `g_{ij}(x)` together with
its inverse `g^{ij}(x)` and the regular chart domain where both matrices remain nondegenerate.

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

/-- Package a `CoordinateMetric` at a regular point `x ∈ C.domain` as a `MetricTensor`. -/
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
  Pipeline.christoffel C.g C.ginv x k i j

/-- Riemann curvature tensor of a `CoordinateMetric`. -/
noncomputable def CoordinateMetric.riemann {n : ℕ} (C : CoordinateMetric n)
    (x : Fin n → ℝ) (ρ σ μ ν : Fin n) : ℝ :=
  Pipeline.riemann C.g C.ginv x ρ σ μ ν

/-- Ricci tensor of a `CoordinateMetric`. -/
noncomputable def CoordinateMetric.ricciTensorOf {n : ℕ} (C : CoordinateMetric n)
    (x : Fin n → ℝ) (σ ν : Fin n) : ℝ :=
  Pipeline.ricciTensorOf C.g C.ginv x σ ν

/-- Scalar curvature of a `CoordinateMetric`. -/
noncomputable def CoordinateMetric.ricciScalarOf {n : ℕ} (C : CoordinateMetric n)
    (x : Fin n → ℝ) : ℝ :=
  Pipeline.ricciScalarOf C.g C.ginv x

/-- Einstein tensor of a `CoordinateMetric`. -/
noncomputable def CoordinateMetric.einsteinTensorOf {n : ℕ} (C : CoordinateMetric n)
    (x : Fin n → ℝ) (i j : Fin n) : ℝ :=
  Pipeline.einsteinTensorOf C.g C.ginv x i j

end GeneralRelativity
