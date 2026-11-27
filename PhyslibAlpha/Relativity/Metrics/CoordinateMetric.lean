/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.Metrics.Basic
public import PhyslibAlpha.Relativity.Metrics.Christoffel
public import PhyslibAlpha.Relativity.Metrics.Einstein
public import PhyslibAlpha.Relativity.Metrics.Minkowski
public import PhyslibAlpha.Relativity.Metrics.Ricci
public import PhyslibAlpha.Relativity.Metrics.Riemann
public import PhyslibAlpha.Relativity.Tensors.EinsteinTensor

/-!

# Coordinate metrics

Spacetime metrics on coordinate charts, pointwise `MetricTensor` restrictions, and coordinate
curvature operators.

## i. Overview

A `CoordinateMetric n` pairs a coordinate-dependent symmetric metric field `g_{ij}(x)` with its
inverse `g^{ij}(x)` and the regular chart domain on which they are two-sided inverses. At any
regular point in the domain, `CoordinateMetric.metricTensor` restricts it to a pointwise
`MetricTensor n`, while the chart-level operators `CoordinateMetric.christoffel`,
`CoordinateMetric.riemann`, `CoordinateMetric.ricciTensor`, `CoordinateMetric.ricciScalar`, and
`CoordinateMetric.einsteinTensor` evaluate the Levi-Civita connection and curvature tensors.

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

## A. Coordinate metrics and curvature operators

The chart-level connection and curvature operators are defined in the Christoffel, Riemann,
Ricci, and Einstein modules and re-exported here.
-/
