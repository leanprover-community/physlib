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

# Static spherically symmetric metrics

Static spherically symmetric metric `StaticSphericalMetric`, its diagonal coordinate metric and
inverse in `(t, r, θ, φ)` coordinates, symmetry, two-sided invertibility, and `CoordinateMetric 4`
instance.

## i. Overview

A general static spherically symmetric four-dimensional metric in coordinates `(t, r, θ, φ)` is
parameterized by a single radial metric function `f(r) = S.metricFn r`:

`ds² = -f(r) dt² + f(r)⁻¹ dr² + r² dθ² + r² sin²θ dφ²`.

This module defines `StaticSphericalMetric` in terms of `f` and establishes the nondegeneracy of the
metric on the regular chart `{x | x 1 ≠ 0 ∧ S.metricFn (x 1) ≠ 0 ∧ Real.sin (x 2) ≠ 0}`,
yielding both pointwise `MetricTensor 4` instances and a `CoordinateMetric 4`.

## ii. Key results

- `StaticSphericalMetric` : a static spherically symmetric metric parameterized by its radial metric
  function `metricFn`.
- `StaticSphericalMetric.metric`, `StaticSphericalMetric.metricInv`,
  `StaticSphericalMetric.metric_symm`, `StaticSphericalMetric.metric_mul_inv`,
  `StaticSphericalMetric.metricInv_mul` : coordinate metric, inverse, symmetry, and invertibility.
- `StaticSphericalMetric.metricTensor`, `StaticSphericalMetric.toCoordinateMetric` : certified
  `MetricTensor 4` and `CoordinateMetric 4` instances.

## iii. Table of contents

- A. Metric, inverse, and MetricTensor

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 6 (Sec. 6.1). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 23 (Sec. 23.2).
  [ref: mtw_1973_gravitation]
* B. O'Neill, *Semi-Riemannian Geometry With Applications to Relativity* (1983), Ch. 13.
  [ref: oneill_1983_semi_riemannian]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 7
  (https://arxiv.org/pdf/gr-qc/9712019#page=168). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

namespace StaticSpherical

/-!

## A. Metric, inverse, and MetricTensor

On a static spherically symmetric spacetime parameterized by a single radial metric function
`f(r)`, the diagonal metric `diag(-f, f⁻¹, r², r² sin²θ)` is nondegenerate everywhere away from the
origin (`r = 0`), Killing horizons (`f = 0`), and polar coordinate axis (`sin θ = 0`).

-/

/-- A static spherically symmetric four-dimensional metric determined by a single radial metric
function `f(r)` in coordinates `(t, r, θ, φ)`: the restricted ansatz `g_tt = -f(r)`,
`g_rr = f(r)⁻¹`, `g_{θθ} = r²`, `g_{φφ} = r² sin²θ`, which automatically satisfies
`g_tt g_rr = -1`. Metrics without this pairing of the `tt` and `rr` components are not
representable. -/
structure StaticSphericalMetric where
  /-- The radial metric function `f(r)` entering `g_tt = -f(r)` and `g_rr = f(r)⁻¹`. -/
  metricFn : ℝ → ℝ

namespace StaticSphericalMetric

/-- A regular chart point of a static spherically symmetric metric: `r ≠ 0`, `f(r) ≠ 0`, and
`sin θ ≠ 0`, so the metric and its inverse are both defined. -/
structure RegularPoint (S : StaticSphericalMetric) where
  /-- Coordinate point `(t, r, θ, φ)`. -/
  x : Fin 4 → ℝ
  /-- The radial coordinate is nonzero. -/
  hr : x 1 ≠ 0
  /-- The metric function is nonzero at the radius. -/
  hf : S.metricFn (x 1) ≠ 0
  /-- The polar angle is away from the axis. -/
  hsin : Real.sin (x 2) ≠ 0

/-- General static spherically symmetric metric `diag(-f(r), f(r)⁻¹, r², r² sin²θ)` in
coordinates `(t, r, θ, φ)`. -/
noncomputable def metric (S : StaticSphericalMetric) (x : Fin 4 → ℝ) : Tensor2 4 :=
  Matrix.of fun i j =>
    if i = j then
      if i = 0 then -(S.metricFn (x 1))
      else if i = 1 then (S.metricFn (x 1))⁻¹
      else if i = 2 then (x 1) ^ 2
      else (x 1) ^ 2 * Real.sin (x 2) ^ 2
    else 0

/-- Inverse of the general static spherically symmetric metric. -/
noncomputable def metricInv (S : StaticSphericalMetric) (x : Fin 4 → ℝ) : Tensor2 4 :=
  Matrix.of fun i j =>
    if i = j then
      if i = 0 then -(S.metricFn (x 1))⁻¹
      else if i = 1 then S.metricFn (x 1)
      else if i = 2 then ((x 1) ^ 2)⁻¹
      else ((x 1) ^ 2 * Real.sin (x 2) ^ 2)⁻¹
    else 0

/-- Symmetry of the static spherically symmetric metric tensor. -/
lemma metric_symm (S : StaticSphericalMetric) (x : Fin 4 → ℝ) :
    IsSymm (S.metric x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply, metric]

/-- Right inverse identity `g * g⁻¹ = 1` on the regular chart `r ≠ 0`, `f(r) ≠ 0`,
`sin θ ≠ 0`. -/
lemma metric_mul_inv (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.metricFn (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) :
    S.metric x * S.metricInv x = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [metric, metricInv, Matrix.mul_apply]
  · field_simp [hf]
  · field_simp [hf]
  · field_simp [hr]
  · field_simp [hr, hsin]

/-- Left inverse identity `g⁻¹ * g = 1` on the regular chart `r ≠ 0`, `f(r) ≠ 0`,
`sin θ ≠ 0`. -/
lemma metricInv_mul (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.metricFn (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) :
    S.metricInv x * S.metric x = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [metric, metricInv, Matrix.mul_apply]
  · field_simp [hf]
  · field_simp [hf]
  · field_simp [hr]
  · field_simp [hr, hsin]

/-- The metric as a `MetricTensor 4` at a point away from coordinate and horizon
singularities. -/
noncomputable def metricTensor (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.metricFn (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) : MetricTensor 4 where
  g := S.metric x
  ginv := S.metricInv x
  symm := S.metric_symm x
  inv_left := S.metric_mul_inv x hr hf hsin
  inv_right := S.metricInv_mul x hr hf hsin

/-- The metric at a bundled regular chart point. -/
noncomputable def RegularPoint.metricTensor {S : StaticSphericalMetric} (p : S.RegularPoint) :
    MetricTensor 4 :=
  S.metricTensor p.x p.hr p.hf p.hsin

/-- Right inverse identity at a bundled regular chart point. -/
lemma RegularPoint.metric_mul_inv {S : StaticSphericalMetric} (p : S.RegularPoint) :
    S.metric p.x * S.metricInv p.x = 1 :=
  S.metric_mul_inv p.x p.hr p.hf p.hsin

/-- Left inverse identity at a bundled regular chart point. -/
lemma RegularPoint.metricInv_mul {S : StaticSphericalMetric} (p : S.RegularPoint) :
    S.metricInv p.x * S.metric p.x = 1 :=
  S.metricInv_mul p.x p.hr p.hf p.hsin

/-- The metric as a `CoordinateMetric 4` on its regular chart where
`r ≠ 0`, `f(r) ≠ 0`, `sin θ ≠ 0`. -/
noncomputable def toCoordinateMetric (S : StaticSphericalMetric) : CoordinateMetric 4 where
  g := S.metric
  ginv := S.metricInv
  domain := {x | x 1 ≠ 0 ∧ S.metricFn (x 1) ≠ 0 ∧ Real.sin (x 2) ≠ 0}
  symm := S.metric_symm
  inv_left x hx := S.metric_mul_inv x hx.1 hx.2.1 hx.2.2
  inv_right x hx := S.metricInv_mul x hx.1 hx.2.1 hx.2.2

/-- The covariant field of `S.toCoordinateMetric` is `S.metric`. -/
@[simp] lemma toCoordinateMetric_g (S : StaticSphericalMetric) :
    S.toCoordinateMetric.g = S.metric := rfl

/-- The inverse field of `S.toCoordinateMetric` is `S.metricInv`. -/
@[simp] lemma toCoordinateMetric_ginv (S : StaticSphericalMetric) :
    S.toCoordinateMetric.ginv = S.metricInv := rfl

end StaticSphericalMetric

end StaticSpherical

end GeneralRelativity
