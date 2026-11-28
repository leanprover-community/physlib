/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.General.GeodesicSystem
public import PhyslibAlpha.Relativity.Metrics.Basic
public import PhyslibAlpha.Relativity.Metrics.Christoffel
public import PhyslibAlpha.Relativity.Metrics.Einstein
public import PhyslibAlpha.Relativity.Metrics.Minkowski
public import PhyslibAlpha.Relativity.Metrics.Ricci
public import PhyslibAlpha.Relativity.Metrics.RicciScalar
public import PhyslibAlpha.Relativity.Metrics.Riemann
public import PhyslibAlpha.Relativity.Tensors.EinsteinTensor

/-!

# Coordinate metrics

Coordinate-chart metric fields, their pointwise `MetricTensor` restrictions, and the chart-level
connection and curvature operators.

## i. Overview

A `CoordinateMetric n` collects a coordinate-dependent symmetric metric field `g_{ij}(x)`, its
inverse `g^{ij}(x)`, and the regular chart domain on which the two are two-sided inverses. At a
point of that domain `CoordinateMetric.metricTensor` restricts the field to a pointwise
`MetricTensor n`. On the chart, `CoordinateMetric.christoffel` assembles the Levi-Civita symbols
from the field and its inverse, `CoordinateMetric.geodesicAccel` gives the geodesic acceleration,
and `CoordinateMetric.riemann`, `CoordinateMetric.ricciTensor`, `CoordinateMetric.ricciScalar`,
and `CoordinateMetric.einsteinTensor` evaluate the curvature componentwise.

## ii. Key results

- `CoordinateMetric`, `CoordinateMetric.metricTensor` : coordinate metric field with its regular
  domain and pointwise `MetricTensor` restriction.
- `CoordinateMetric.christoffel`, `CoordinateMetric.geodesicAccel`, `CoordinateMetric.IsGeodesic`,
  `CoordinateMetric.isGeodesic_iff` : chart connection and geodesic motion.
- `CoordinateMetric.riemann`, `CoordinateMetric.ricciTensor`, `CoordinateMetric.ricciScalar`,
  `CoordinateMetric.einsteinTensor` : Levi-Civita curvature of a coordinate metric.

## iii. Table of contents

- A. Coordinate metrics and pointwise restrictions
- B. Connection, geodesics, and curvature

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 3 (Sec. 3.1). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 8 & Ch. 13.
  [ref: mtw_1973_gravitation]
* B. O'Neill, *Semi-Riemannian Geometry With Applications to Relativity* (1983), Ch. 3.
  [ref: oneill_1983_semi_riemannian]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 3 (Sec. 3.1)
  (https://arxiv.org/pdf/gr-qc/9712019#page=58). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

/-!

## A. Coordinate metrics and pointwise restrictions

A coordinate metric field carries its own regularity domain, so pointwise `MetricTensor`s — and
with them the inverse-metric contractions — exist exactly at the chart points where `g` and
`ginv` are two-sided inverses.

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

/-- The covariant field of the pointwise metric is `C.g x`. -/
@[simp] lemma CoordinateMetric.metricTensor_g {n : ℕ} (C : CoordinateMetric n)
    (x : Fin n → ℝ) (hx : x ∈ C.domain) : (C.metricTensor x hx).g = C.g x := rfl

/-- The inverse field of the pointwise metric is `C.ginv x`. -/
@[simp] lemma CoordinateMetric.metricTensor_ginv {n : ℕ} (C : CoordinateMetric n)
    (x : Fin n → ℝ) (hx : x ∈ C.domain) : (C.metricTensor x hx).ginv = C.ginv x := rfl

/-!

## B. Connection, geodesics, and curvature

The Levi-Civita connection is assembled from the metric field and its explicit inverse;
contracting the derivatives of the symbols gives the Riemann, Ricci, scalar, and Einstein tensors
componentwise, and the same symbols give the affine geodesic equation of the chart.

-/

/-- Christoffel symbols of a `CoordinateMetric`. -/
noncomputable def CoordinateMetric.christoffel {n : ℕ} (C : CoordinateMetric n)
    (x : Fin n → ℝ) (k i j : Fin n) : ℝ :=
  CoordinateCurvature.christoffel C.g C.ginv x k i j

/-- The Christoffel symbol of a coordinate metric is the Christoffel symbol of its metric field
and its inverse. -/
@[simp] lemma CoordinateMetric.christoffel_apply {n : ℕ} (C : CoordinateMetric n)
    (x : Fin n → ℝ) (k i j : Fin n) :
    C.christoffel x k i j = CoordinateCurvature.christoffel C.g C.ginv x k i j := rfl

/-- Chart geodesic acceleration `-Γ^k_{ij}(x) v^i v^j` of a coordinate metric at position `x` for
velocity `v`. -/
noncomputable def CoordinateMetric.geodesicAccel {n : ℕ} (C : CoordinateMetric n)
    (x v : Fin n → ℝ) : Fin n → ℝ :=
  fun k => -∑ i, ∑ j, C.christoffel x k i j * v i * v j

/-- Predicate asserting that `(γ, w)` solves the coordinate geodesic equation of `C` on a
parameter set `s`, with acceleration supplied by `C.geodesicAccel`. -/
def CoordinateMetric.IsGeodesic {n : ℕ} (C : CoordinateMetric n) (s : Set ℝ)
    (γ w : ℝ → Fin n → ℝ) : Prop :=
  ∀ t ∈ s, HasDerivAt γ (w t) t ∧ HasDerivAt w (C.geodesicAccel (γ t) (w t)) t

/-- A `GeodesicSystem` whose acceleration agrees with the chart Christoffel acceleration of `C`
has exactly the same free-fall trajectories as `C`. -/
lemma CoordinateMetric.isGeodesic_iff {n : ℕ} (C : CoordinateMetric n)
    (G : GeodesicSystem (Fin n → ℝ))
    (hΓ : ∀ x v, G.accel x v = C.geodesicAccel x v) (s : Set ℝ) (γ w : ℝ → Fin n → ℝ) :
    C.IsGeodesic s γ w ↔ GeneralRelativity.IsGeodesic G s γ w := by
  constructor <;> intro h t ht
  · simpa [CoordinateMetric.IsGeodesic, GeneralRelativity.IsGeodesic, hΓ] using h t ht
  · simpa [CoordinateMetric.IsGeodesic, GeneralRelativity.IsGeodesic, hΓ] using h t ht

/-- Riemann curvature tensor of a `CoordinateMetric`. -/
noncomputable def CoordinateMetric.riemann {n : ℕ} (C : CoordinateMetric n)
    (x : Fin n → ℝ) (ρ σ μ ν : Fin n) : ℝ :=
  CoordinateCurvature.riemann C.g C.ginv x ρ σ μ ν

/-- The Riemann tensor of a coordinate metric is the Riemann tensor of its metric field and its
inverse. -/
@[simp] lemma CoordinateMetric.riemann_apply {n : ℕ} (C : CoordinateMetric n)
    (x : Fin n → ℝ) (ρ σ μ ν : Fin n) :
    C.riemann x ρ σ μ ν = CoordinateCurvature.riemann C.g C.ginv x ρ σ μ ν := rfl

/-- Ricci tensor of a `CoordinateMetric`. -/
noncomputable def CoordinateMetric.ricciTensor {n : ℕ} (C : CoordinateMetric n)
    (x : Fin n → ℝ) (σ ν : Fin n) : ℝ :=
  CoordinateCurvature.ricciTensor C.g C.ginv x σ ν

/-- The Ricci tensor of a coordinate metric is the Ricci tensor of its metric field and its
inverse. -/
@[simp] lemma CoordinateMetric.ricciTensor_apply {n : ℕ} (C : CoordinateMetric n)
    (x : Fin n → ℝ) (σ ν : Fin n) :
    C.ricciTensor x σ ν = CoordinateCurvature.ricciTensor C.g C.ginv x σ ν := rfl

/-- Scalar curvature of a `CoordinateMetric`. -/
noncomputable def CoordinateMetric.ricciScalar {n : ℕ} (C : CoordinateMetric n)
    (x : Fin n → ℝ) : ℝ :=
  CoordinateCurvature.ricciScalar C.g C.ginv x

/-- The Ricci scalar of a coordinate metric is the Ricci scalar of its metric field and its
inverse. -/
@[simp] lemma CoordinateMetric.ricciScalar_apply {n : ℕ} (C : CoordinateMetric n)
    (x : Fin n → ℝ) : C.ricciScalar x = CoordinateCurvature.ricciScalar C.g C.ginv x := rfl

/-- Einstein tensor of a `CoordinateMetric`. -/
noncomputable def CoordinateMetric.einsteinTensor {n : ℕ} (C : CoordinateMetric n)
    (x : Fin n → ℝ) (i j : Fin n) : ℝ :=
  CoordinateCurvature.einsteinTensor C.g C.ginv x i j

/-- The Einstein tensor of a coordinate metric is the Einstein tensor of its metric field and its
inverse. -/
@[simp] lemma CoordinateMetric.einsteinTensor_apply {n : ℕ} (C : CoordinateMetric n)
    (x : Fin n → ℝ) (i j : Fin n) :
    C.einsteinTensor x i j = CoordinateCurvature.einsteinTensor C.g C.ginv x i j := rfl

end GeneralRelativity
