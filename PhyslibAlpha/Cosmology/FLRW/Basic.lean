/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import PhyslibAlpha.Relativity.Metrics.CoordinateMetric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!

# FLRW spacetime metric and inverse

Comoving spherical FLRW spacetimes `FLRWSpacetime` with diagonal metric and inverse, their
symmetry and two-sided invertibility, and the induced `MetricTensor 4` and `CoordinateMetric 4`.

## i. Overview

The homogeneous, isotropic Friedmann–Lemaître–Robertson–Walker (FLRW) spacetime in comoving
spherical coordinates `x = (t, r, θ, φ)` is parameterized by a scale factor `a(t)` and normalized
spatial curvature `k`, carrying the diagonal line element:

`g = diag(-1, a(t)² / (1 - k r²), a(t)² r², a(t)² r² sin²θ)`.

This module treats the homogeneous, isotropic Friedmann–Lemaître–Robertson–Walker (FLRW) spacetimes
`FLRWSpacetime` of scale factor `a(t)`, spatial curvature `k`, and coordinate metric `metric`,
establishes the symmetry and two-sided invertibility of the inverse `metricInv` on the regular chart
domain, and constructs the resulting `MetricTensor 4` and `CoordinateMetric 4`.

## ii. Key results

- `FLRWSpacetime` : comoving FLRW spacetime parameterized by scale factor `a` and curvature `k`.
- `FLRWSpacetime.metric`, `FLRWSpacetime.metricInv` : diagonal FLRW metric and inverse in
  comoving coordinates `(t, r, θ, φ)`.
- `FLRWSpacetime.metric_symm`, `FLRWSpacetime.metric_mul_inv`, `FLRWSpacetime.metricInv_mul` :
  symmetry and two-sided inverse identities on the regular coordinate domain.
- `FLRWSpacetime.metricTensor`, `FLRWSpacetime.toCoordinateMetric` : `MetricTensor 4` at a regular
  point and `CoordinateMetric 4` on the regular chart.

## iii. Table of contents

- A. FLRW spacetime structure, metric, and CoordinateMetric

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 5 (Sec. 5.1-5.2). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 27.
  [ref: mtw_1973_gravitation]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 8
  (https://arxiv.org/pdf/gr-qc/9712019#page=201). [ref: Carroll1997]
-/

@[expose] public section

open GeneralRelativity

namespace Cosmology

namespace FLRW

/-!

## A. FLRW spacetime structure, metric, and CoordinateMetric

In comoving coordinates `(t, r, θ, φ)`, the spatially homogeneous and isotropic FLRW line element
is diagonal, invertible whenever the scale factor `a(t)`, radius `r`, `1 - k r²`, and `sin θ` are
non-zero.

-/

/-- Comoving Friedmann–Lemaître–Robertson–Walker (FLRW) spacetime parameterized by a scale
factor `a(t)` and spatial curvature `k`. -/
structure FLRWSpacetime where
  /-- Scale factor `a(t)` as a function of comoving coordinate time. -/
  a : ℝ → ℝ
  /-- Normalized spatial curvature parameter `k`. -/
  k : ℝ

namespace FLRWSpacetime

/-- A regular chart point of an FLRW metric: the scale factor, `r`, `1 - k r²`, and `sin θ` are
all nonzero, so the metric and its inverse are both defined. -/
structure RegularPoint (S : FLRWSpacetime) where
  /-- Comoving coordinate point `(t, r, θ, φ)`. -/
  x : Fin 4 → ℝ
  /-- The scale factor does not vanish at the time. -/
  ha : S.a (x 0) ≠ 0
  /-- The radial coordinate is nonzero. -/
  hr : x 1 ≠ 0
  /-- The spatial curvature factor `1 - k r²` is nonzero. -/
  hkr : 1 - S.k * (x 1) ^ 2 ≠ 0
  /-- The polar angle is away from the axis. -/
  hsin : Real.sin (x 2) ≠ 0

/-- The FLRW metric in comoving coordinates `(t, r, θ, φ)` with scale factor `S.a(t)` and spatial
curvature parameter `S.k`. -/
noncomputable def metric (S : FLRWSpacetime) (x : Fin 4 → ℝ) : Tensor2 4 :=
  Matrix.of fun i j =>
    if i = j then
      if i = 0 then -1
      else if i = 1 then (S.a (x 0)) ^ 2 / (1 - S.k * (x 1) ^ 2)
      else if i = 2 then (S.a (x 0)) ^ 2 * (x 1) ^ 2
      else (S.a (x 0)) ^ 2 * (x 1) ^ 2 * Real.sin (x 2) ^ 2
    else 0

/-- The inverse of the FLRW metric in `(t, r, θ, φ)` coordinates. -/
noncomputable def metricInv (S : FLRWSpacetime) (x : Fin 4 → ℝ) : Tensor2 4 :=
  Matrix.of fun i j =>
    if i = j then
      if i = 0 then -1
      else if i = 1 then (1 - S.k * (x 1) ^ 2) / (S.a (x 0)) ^ 2
      else if i = 2 then ((S.a (x 0)) ^ 2 * (x 1) ^ 2)⁻¹
      else ((S.a (x 0)) ^ 2 * (x 1) ^ 2 * Real.sin (x 2) ^ 2)⁻¹
    else 0

/-- Symmetry of `FLRWSpacetime.metric`. -/
lemma metric_symm (S : FLRWSpacetime) (x : Fin 4 → ℝ) : IsSymm (S.metric x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply, metric]

/-- `S.metricInv x * S.metric x = 1` on the regular coordinate domain. -/
lemma metricInv_mul (S : FLRWSpacetime) (x : Fin 4 → ℝ) (ha : S.a (x 0) ≠ 0)
    (hr : x 1 ≠ 0) (hkr : 1 - S.k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0) :
    S.metricInv x * S.metric x = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [metric, metricInv, Matrix.mul_apply]
  · field_simp [ha, hkr]
  · field_simp [ha, hr]
  · field_simp [ha, hr, hsin]

/-- `S.metric x * S.metricInv x = 1` on the regular coordinate domain. -/
lemma metric_mul_inv (S : FLRWSpacetime) (x : Fin 4 → ℝ) (ha : S.a (x 0) ≠ 0)
    (hr : x 1 ≠ 0) (hkr : 1 - S.k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0) :
    S.metric x * S.metricInv x = 1 :=
  mul_eq_one_of_isSymm_of_mul_eq_one (metric_symm S x) (metricInv_mul S x ha hr hkr hsin)

/-- The FLRW metric as a `MetricTensor 4` at a point where the scale factor, `r`, `1 - k r²`, and
`sin θ` are nonzero. -/
noncomputable def metricTensor (S : FLRWSpacetime) (x : Fin 4 → ℝ) (ha : S.a (x 0) ≠ 0)
    (hr : x 1 ≠ 0) (hkr : 1 - S.k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0) :
    MetricTensor 4 where
  g := S.metric x
  ginv := S.metricInv x
  symm := S.metric_symm x
  inv_left := S.metric_mul_inv x ha hr hkr hsin
  inv_right := S.metricInv_mul x ha hr hkr hsin

/-- The FLRW metric at a bundled regular chart point. -/
noncomputable def RegularPoint.metricTensor {S : FLRWSpacetime} (p : S.RegularPoint) :
    MetricTensor 4 :=
  S.metricTensor p.x p.ha p.hr p.hkr p.hsin

/-- Right inverse identity at a bundled regular chart point. -/
lemma RegularPoint.metric_mul_inv {S : FLRWSpacetime} (p : S.RegularPoint) :
    S.metric p.x * S.metricInv p.x = 1 :=
  S.metric_mul_inv p.x p.ha p.hr p.hkr p.hsin

/-- Left inverse identity at a bundled regular chart point. -/
lemma RegularPoint.metricInv_mul {S : FLRWSpacetime} (p : S.RegularPoint) :
    S.metricInv p.x * S.metric p.x = 1 :=
  S.metricInv_mul p.x p.ha p.hr p.hkr p.hsin

/-- The FLRW metric as a `CoordinateMetric 4` on its regular comoving chart where
`a(t) ≠ 0`, `r ≠ 0`, `1 - k r² ≠ 0`, `sin θ ≠ 0`. -/
noncomputable def toCoordinateMetric (S : FLRWSpacetime) : CoordinateMetric 4 where
  g := S.metric
  ginv := S.metricInv
  domain :=
    {x | S.a (x 0) ≠ 0 ∧ x 1 ≠ 0 ∧ 1 - S.k * (x 1) ^ 2 ≠ 0 ∧ Real.sin (x 2) ≠ 0}
  symm := S.metric_symm
  inv_left x hx := S.metric_mul_inv x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2
  inv_right x hx := S.metricInv_mul x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2

/-- The covariant field of `S.toCoordinateMetric` is `S.metric`. -/
@[simp] lemma toCoordinateMetric_g (S : FLRWSpacetime) :
    S.toCoordinateMetric.g = S.metric := rfl

/-- The inverse field of `S.toCoordinateMetric` is `S.metricInv`. -/
@[simp] lemma toCoordinateMetric_ginv (S : FLRWSpacetime) :
    S.toCoordinateMetric.ginv = S.metricInv := rfl

end FLRWSpacetime

end FLRW

end Cosmology
