/-
Copyright (c) 2026 The Gravitation formalisation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/

module

public import PhyslibAlpha.Relativity.General.ManifoldInterface
public import PhyslibAlpha.Relativity.Metrics.Basic
public import PhyslibAlpha.Relativity.Metrics.CoordinateMetric
public import PhyslibAlpha.Relativity.General.Schwarzschild.CoordinateCurvature
public import PhyslibAlpha.Relativity.General.Schwarzschild.SchwarzschildManifold
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

/-!

# Ingoing Eddington–Finkelstein chart

## i. Overview

This module adds the ingoing Eddington–Finkelstein chart for Schwarzschild
spacetime.  In coordinates `(v, r, θ, φ)`, with `v = t + r*` and
`dr*/dr = (1 - 2M/r)⁻¹`, the line element is

`ds² = -(1 - 2M/r) dv² + 2 dv dr + r² dΩ²`.

The cross term makes the metric nondegenerate at the horizon `r = 2M`, where
the Schwarzschild `(t, r, θ, φ)` components have `g_rr = (1 - 2M/r)⁻¹`
divergent.  The chart still excludes the curvature singularity `r = 0` and the
polar axis `sin θ = 0`, but it removes the horizon obstruction.

This is a chart-level metric and inverse.  It is not a global
`ChartSpacetime`, whose `chart` field is a global equivalence to all of
`Fin 4 → ℝ`; instead it is packaged below as a `PartialChartSpacetime` on
the open set `r ≠ 0 ∧ sin θ ≠ 0`.  The coordinate curvature pipeline is
evaluated directly on the EF components, so Ricci flatness below does not pass
through the Schwarzschild chart and does not assume `1 - 2M/r ≠ 0`.

## ii. Key results

- `metric`, `metricInv` : the ingoing Eddington–Finkelstein components and
  their explicit inverse.
- `metricTensor` : a bundled `MetricTensor 4` for `r ≠ 0` and `sin θ ≠ 0`,
  with no `1 - 2M/r ≠ 0` hypothesis.
- `partialChart`, `partialChartDomain` : the EF metric packaged as a
  `PartialChartSpacetime` on its restricted domain.
- `partialChart_isSmooth` : the EF partial chart satisfies the smoothness
  certificate `PartialChartSpacetime.IsSmooth`.
- `horizonTensor` : the same bundle at `r = 2M` when `M ≠ 0`.
- `horizonTensor_ginv_rr`, `horizonTensor_g_vr` : the inverse `rr` component
  vanishes while the cross component remains `1`, so the horizon is regular.
- `ricciTensorOf_metric` : the coordinate Ricci tensor computed directly from
  the EF metric is zero for every `r ≠ 0` and `sin θ ≠ 0`.
- `ricciTensorOf_metric_horizon` : the same Ricci-flatness statement at
  `r = 2M`.
- `tortoiseStar`, `deriv_tortoiseStar` : the tortoise coordinate on `r > 2M`
  and its derivative `(1 - 2M/r)⁻¹`.
- `schwarzschildToEF`, `transitionJacobian`, `schwarzschild_eq_pullback` : the
  overlap transition map to Schwarzschild coordinates, its Jacobian, and the
  metric pullback identity on the exterior overlap.
- `schwarzschildEFTransition` : the EF–Schwarzschild exterior overlap as a
  `PartialChartTransition`.

## iii. Table of contents

- A. Metric and inverse
- B. Direct Christoffel and Ricci computation
- C. The partial chart
- D. The horizon `r = 2M`
- E. The tortoise coordinate
- F. Overlap with the Schwarzschild exterior chart

## iv. References

* S. M. Carroll, *Lecture Notes on General Relativity*, arXiv:gr-qc/9712019,
  Ch. 7, pp. 174–175. [ref: Carroll1997, pp. 174–175]
* R. M. Wald, *General Relativity*, University of Chicago Press, 1984, Ch. 6.
  [ref: wald_1984_general_relativity, Ch. 6]

-/
@[expose] public section

namespace GeneralRelativity

namespace EddingtonFinkelstein

open scoped ContDiff

/-! ## A. Metric and inverse -/

/-- Ingoing Eddington–Finkelstein metric in `(v, r, θ, φ)` coordinates. -/
noncomputable def metric (M : ℝ) (x : Fin 4 → ℝ) : Tensor2 4 :=
  fun i j =>
    if i = 0 then
      if j = 0 then -(1 - 2 * M / x 1)
      else if j = 1 then 1 else 0
    else if i = 1 then
      if j = 0 then 1 else 0
    else if i = 2 then
      if j = 2 then (x 1) ^ 2 else 0
    else
      if j = 3 then (x 1) ^ 2 * Real.sin (x 2) ^ 2 else 0

/-- Explicit inverse of `metric`.  The `(v,r)` block is
`[[-(1 - 2M/r), 1], [1, 0]]⁻¹ = [[0, 1], [1, 1 - 2M/r]]`. -/
noncomputable def metricInv (M : ℝ) (x : Fin 4 → ℝ) : Tensor2 4 :=
  fun i j =>
    if i = 0 then
      if j = 1 then 1 else 0
    else if i = 1 then
      if j = 0 then 1
      else if j = 1 then 1 - 2 * M / x 1
      else 0
    else if i = 2 then
      if j = 2 then ((x 1) ^ 2)⁻¹ else 0
    else
      if j = 3 then ((x 1) ^ 2 * Real.sin (x 2) ^ 2)⁻¹ else 0

lemma metric_symm (M : ℝ) (x : Fin 4 → ℝ) : IsSymm (metric M x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [metric, Matrix.transpose_apply]

lemma metric_mul_inv (M : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hsin : Real.sin (x 2) ≠ 0) :
    metric M x * metricInv M x = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [metric, metricInv, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals field_simp [hr, hsin]

lemma metricInv_mul (M : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hsin : Real.sin (x 2) ≠ 0) :
    metricInv M x * metric M x = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [metric, metricInv, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals field_simp [hr, hsin]

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! ## B. Direct Christoffel and Ricci computation -/

private lemma deriv_const_mul_inv_sq (M r : ℝ) (hr : r ≠ 0) :
    deriv (fun s : ℝ => M * s⁻¹ ^ 2) r = -2 * M / r ^ 3 := by
  have h := (hasDerivAt_inv hr).pow 2
  have h' := h.const_mul M
  have hfun : (fun s : ℝ => M * s⁻¹ ^ 2) = fun y => M * ((fun s : ℝ => s⁻¹) ^ 2) y := by
    funext s
    simp [Pi.pow_apply]
  rw [hfun, h'.deriv]
  field_simp [hr]
  simp [hr]

private lemma deriv_const_mul_inv_cube (M r : ℝ) (hr : r ≠ 0) :
    deriv (fun s : ℝ => M * s⁻¹ ^ 3) r = -3 * M / r ^ 4 := by
  have h := (hasDerivAt_inv hr).pow 3
  have h' := h.const_mul M
  have hfun : (fun s : ℝ => M * s⁻¹ ^ 3) = fun y => M * ((fun s : ℝ => s⁻¹) ^ 3) y := by
    funext s
    simp [Pi.pow_apply]
  rw [hfun, h'.deriv]
  field_simp [hr]
  simp [hr]

private lemma deriv_gamma_100 (M r : ℝ) (hr : r ≠ 0) :
    deriv (fun s : ℝ => M * s⁻¹ ^ 2 - 2 * M ^ 2 * s⁻¹ ^ 3) r =
      -2 * M / r ^ 3 + 6 * M ^ 2 / r ^ 4 := by
  change deriv ((fun s : ℝ => M * s⁻¹ ^ 2) - fun s : ℝ => 2 * M ^ 2 * s⁻¹ ^ 3) r =
    -2 * M / r ^ 3 + 6 * M ^ 2 / r ^ 4
  rw [deriv_sub (by fun_prop) (by fun_prop)]
  simp [hr]
  field_simp [hr]
  ring

private lemma deriv_gamma_100_alt (M r : ℝ) (hr : r ≠ 0) :
    deriv (fun s : ℝ => M * s * s⁻¹ ^ 3 - M ^ 2 * s⁻¹ ^ 3 * 2) r =
      -2 * M / r ^ 3 + 6 * M ^ 2 / r ^ 4 := by
  have h : (fun s : ℝ => M * s * s⁻¹ ^ 3 - M ^ 2 * s⁻¹ ^ 3 * 2) =ᶠ[nhds r]
      fun s => M * s⁻¹ ^ 2 - 2 * M ^ 2 * s⁻¹ ^ 3 := by
    filter_upwards [eventually_ne_nhds hr] with s hs
    field_simp [hs]
  rw [h.deriv_eq]
  exact deriv_gamma_100 M r hr

@[simp] private lemma deriv_gamma_100_field (M r : ℝ) (hr : r ≠ 0) :
    deriv (fun s : ℝ => M * (s - M * 2) / s ^ 3) r =
      -2 * M / r ^ 3 + 6 * M ^ 2 / r ^ 4 := by
  have h : (fun s : ℝ => M * (s - M * 2) / s ^ 3) =ᶠ[nhds r]
      fun s => M * s⁻¹ ^ 2 - 2 * M ^ 2 * s⁻¹ ^ 3 := by
    filter_upwards [eventually_ne_nhds hr] with s hs
    field_simp [hs]
  rw [h.deriv_eq]
  exact deriv_gamma_100 M r hr

/-- Explicit nonzero Christoffel symbols of the ingoing EF metric. -/
private noncomputable def efGamma (M : ℝ) (x : Fin 4 → ℝ) (k i j : Fin 4) : ℝ :=
  if k = 0 then
    if i = 0 ∧ j = 0 then M / (x 1) ^ 2
    else if i = 2 ∧ j = 2 then -(x 1)
    else if i = 3 ∧ j = 3 then -(x 1) * Real.sin (x 2) ^ 2
    else 0
  else if k = 1 then
    if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then -M / (x 1) ^ 2
    else if i = 0 ∧ j = 0 then M * (x 1)⁻¹ ^ 2 - 2 * M ^ 2 * (x 1)⁻¹ ^ 3
    else if i = 2 ∧ j = 2 then -(x 1) + 2 * M
    else if i = 3 ∧ j = 3 then (-(x 1) + 2 * M) * Real.sin (x 2) ^ 2
    else 0
  else if k = 2 then
    if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then 1 / (x 1)
    else if i = 3 ∧ j = 3 then -Real.sin (x 2) * Real.cos (x 2)
    else 0
  else
    if (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) then 1 / (x 1)
    else if (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) then
      Real.cos (x 2) / Real.sin (x 2)
    else 0

/-- Coordinate derivatives of `efGamma`, including both radial and angular
derivatives. -/
private noncomputable def efGammaDeriv (M : ℝ) (x : Fin 4 → ℝ) (μ k i j : Fin 4) : ℝ :=
  if μ = 1 then
    if k = 0 ∧ i = 0 ∧ j = 0 then -2 * M / (x 1) ^ 3
    else if k = 0 ∧ i = 2 ∧ j = 2 then -1
    else if k = 0 ∧ i = 3 ∧ j = 3 then -Real.sin (x 2) ^ 2
    else if k = 1 ∧ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) then 2 * M / (x 1) ^ 3
    else if k = 1 ∧ i = 0 ∧ j = 0 then
      -2 * M / (x 1) ^ 3 + 6 * M ^ 2 / (x 1) ^ 4
    else if k = 1 ∧ i = 2 ∧ j = 2 then -1
    else if k = 1 ∧ i = 3 ∧ j = 3 then -Real.sin (x 2) ^ 2
    else if k = 2 ∧ ((i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)) then -1 / (x 1) ^ 2
    else if k = 3 ∧ ((i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1)) then -1 / (x 1) ^ 2
    else 0
  else if μ = 2 then
    if k = 0 ∧ i = 3 ∧ j = 3 then
      -2 * (x 1) * Real.sin (x 2) * Real.cos (x 2)
    else if k = 1 ∧ i = 3 ∧ j = 3 then
      (-(x 1) + 2 * M) * (2 * Real.sin (x 2) * Real.cos (x 2))
    else if k = 2 ∧ i = 3 ∧ j = 3 then
      Real.sin (x 2) ^ 2 - Real.cos (x 2) ^ 2
    else if k = 3 ∧ ((i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)) then
      -1 / Real.sin (x 2) ^ 2
    else 0
  else 0

set_option maxHeartbeats 2000000 in
private lemma christoffel_eq_efGamma (M : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hsin : Real.sin (x 2) ≠ 0) (k i j : Fin 4) :
    CoordinateCurvature.christoffel (metric M) (metricInv M) x k i j = efGamma M x k i j := by
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [CoordinateCurvature.christoffel, CoordinateCurvature.coordDeriv, efGamma, metric,
      metricInv,
      Fin.sum_univ_four] <;>
    try field_simp [hr, hsin] <;>
    try ring_nf

set_option maxHeartbeats 2000000 in
private lemma coordDeriv_efGamma_eq (M : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hsin : Real.sin (x 2) ≠ 0) (μ k i j : Fin 4) :
    CoordinateCurvature.coordDeriv μ (fun y => efGamma M y k i j) x = efGammaDeriv M x μ k i j := by
  fin_cases μ <;> fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [CoordinateCurvature.coordDeriv, efGamma, efGammaDeriv, hr, hsin] <;>
    try ring_nf <;>
    try field_simp [hr, hsin] <;>
    try rw [deriv_gamma_100_alt M (x 1) hr] <;>
    try field_simp [hr, hsin] <;>
    try rw [deriv_gamma_100_field M (x 1) hr] <;>
    try field_simp [hr, hsin] <;>
    try ring_nf
  all_goals try rw [deriv_gamma_100_field M (x 1) hr]
  all_goals try field_simp [hr, hsin]
  all_goals try ring_nf
  all_goals try nlinarith [Real.sin_sq_add_cos_sq (x 2)]

set_option maxHeartbeats 4000000

/-- **Direct Ricci flatness in Eddington–Finkelstein coordinates.**  The
coordinate Ricci tensor obtained from `metric` and `metricInv` vanishes at every
point with `r ≠ 0` and `sin θ ≠ 0`.  No condition on `1 - 2M/r` is used, so the
statement includes the horizon `r = 2M`. -/
lemma ricciTensorOf_metric (M : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hsin : Real.sin (x 2) ≠ 0) (σ ν : Fin 4) :
    CoordinateCurvature.ricciTensor (metric M) (metricInv M) x σ ν = 0 := by
  have hr' : ∀ᶠ y in nhds x, y 1 ≠ 0 :=
    (continuous_apply 1).continuousAt.eventually_ne hr
  have hsin' : ∀ᶠ y in nhds x, Real.sin (y 2) ≠ 0 :=
    (Real.continuous_sin.continuousAt.comp (continuous_apply 2).continuousAt).eventually_ne hsin
  have hcoord : ∀ (μ k i j : Fin 4),
      CoordinateCurvature.coordDeriv μ
        (fun y => CoordinateCurvature.christoffel (metric M) (metricInv M) y k i j) x =
      CoordinateCurvature.coordDeriv μ (fun y => efGamma M y k i j) x := by
    intro μ k i j
    apply CoordinateCurvature.coordDeriv_congr_nhds
    filter_upwards [hr', hsin'] with y hy1 hy2
    exact christoffel_eq_efGamma M y hy1 hy2 k i j
  fin_cases σ <;> fin_cases ν <;>
    simp [CoordinateCurvature.ricciTensor, CoordinateCurvature.riemann, hcoord,
      coordDeriv_efGamma_eq,
      christoffel_eq_efGamma, Fin.sum_univ_four, hr, hsin]
  all_goals simp [efGamma, efGammaDeriv]
  all_goals try field_simp [hr, hsin]
  all_goals try ring_nf
  all_goals try linear_combination (-(x 1)) * Real.sin_sq_add_cos_sq (x 2)

/-- The ingoing Eddington–Finkelstein metric as a bundled `MetricTensor 4`.
The only coordinate exclusions are the curvature singularity `r = 0` and the
polar axis `sin θ = 0`; in particular there is no horizon hypothesis. -/
noncomputable def metricTensor (M : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hsin : Real.sin (x 2) ≠ 0) : MetricTensor 4 where
  g := metric M x
  ginv := metricInv M x
  symm := metric_symm M x
  inv_left := metric_mul_inv M x hr hsin
  inv_right := metricInv_mul M x hr hsin

/-! ## C. The partial chart -/

/-- The open Eddington–Finkelstein chart domain: `r ≠ 0` and `sin θ ≠ 0`. -/
def partialChartDomain : Set (Fin 4 → ℝ) :=
  {x | x 1 ≠ 0 ∧ Real.sin (x 2) ≠ 0}

/-- The Eddington–Finkelstein chart domain is open. -/
lemma partialChartDomain_isOpen : IsOpen partialChartDomain := by
  have h1 : IsOpen {x : SpacetimeChart | x 1 ≠ 0} :=
    (continuous_apply 1).isOpen_preimage ({0}ᶜ) isOpen_compl_singleton
  have hsin_cont : Continuous (fun x : SpacetimeChart => Real.sin (x 2)) :=
    Real.continuous_sin.comp (continuous_apply 2)
  have h2 : IsOpen {x : SpacetimeChart | Real.sin (x 2) ≠ 0} :=
    hsin_cont.isOpen_preimage ({0}ᶜ) isOpen_compl_singleton
  rw [partialChartDomain, Set.ofPred_and]
  exact h1.inter h2

/-- The Eddington–Finkelstein metric packaged as a partial chart on its
restricted domain. -/
noncomputable def partialChart (M : ℝ) : PartialChartSpacetime where
  domain := partialChartDomain
  domain_open := partialChartDomain_isOpen
  metric := fun x hx => metricTensor M x hx.1 hx.2

/-- Alias for `partialChart`. -/
noncomputable def partialChartSpacetime (M : ℝ) : PartialChartSpacetime :=
  partialChart M

lemma contDiffOn_ef_metric_component (M : ℝ) (i j : Fin 4) :
    ContDiffOn ℝ ∞ (fun x : SpacetimeChart => metric M x i j) partialChartDomain := by
  have hcoord (k : Fin 4) :
      ContDiffOn ℝ ∞ (fun x : SpacetimeChart => x k) partialChartDomain :=
    contDiffOn_apply (𝕜 := ℝ) (F' := fun _ : Fin 4 => ℝ) k partialChartDomain
  have hsin : ContDiffOn ℝ ∞ (fun x : SpacetimeChart => Real.sin (x 2))
      partialChartDomain :=
    (Real.contDiff_sin.comp
      (contDiff_apply (𝕜 := ℝ) (F' := fun _ : Fin 4 => ℝ) 2)).contDiffOn
  have hinv : ContDiffOn ℝ ∞ (fun x : SpacetimeChart => (x 1)⁻¹)
      partialChartDomain := by
    refine ContDiffOn.comp (𝕜 := ℝ) (n := ∞)
      (contDiffOn_inv (𝕜 := ℝ) (𝕜' := ℝ) (n := ∞)) (hcoord 1) ?_
    intro x hx
    exact hx.1
  fin_cases i <;> fin_cases j <;>
    simp [metric]
  · have heq : (fun x : SpacetimeChart => 2 * M / x 1 - 1) =
        (fun x : SpacetimeChart => 2 * M * (x 1)⁻¹ - 1) := by
      funext x
      rw [div_eq_mul_inv]
    rw [heq]
    exact ContDiffOn.sub
      (ContDiffOn.mul (contDiffOn_const (c := 2 * M)) hinv)
      (contDiffOn_const (c := (1 : ℝ)))
  · exact contDiffOn_const
  · exact contDiffOn_const
  · exact contDiffOn_const
  · exact contDiffOn_const
  · exact contDiffOn_const
  · exact contDiffOn_const
  · exact contDiffOn_const
  · exact contDiffOn_const
  · exact contDiffOn_const
  · exact (hcoord 1).pow 2
  · exact contDiffOn_const
  · exact contDiffOn_const
  · exact contDiffOn_const
  · exact contDiffOn_const
  · exact ContDiffOn.mul ((hcoord 1).pow 2) (hsin.pow 2)

/-- The Eddington–Finkelstein partial chart is smooth on its domain. -/
lemma partialChart_isSmooth (M : ℝ) : (partialChart M).IsSmooth := by
  intro i j
  refine ⟨fun x => metric M x i j, contDiffOn_ef_metric_component M i j, ?_⟩
  intro x hx
  rfl

/-- Alias for `partialChart`. -/
noncomputable def restrictedChart (M : ℝ) : PartialChartSpacetime :=
  partialChart M

/-- Alias for `partialChart`. -/
noncomputable def restrictedChartSpacetime (M : ℝ) : PartialChartSpacetime :=
  partialChart M

/-! ## D. The horizon `r = 2M` -/

/-- The horizon point `r = 2M` in Eddington–Finkelstein coordinates. -/
def horizonPoint (M v θ φ : ℝ) : Fin 4 → ℝ :=
  ![v, 2 * M, θ, φ]

lemma horizonPoint_one (M v θ φ : ℝ) : horizonPoint M v θ φ 1 = 2 * M := by
  simp [horizonPoint]

lemma horizonPoint_two (M v θ φ : ℝ) : horizonPoint M v θ φ 2 = θ := by
  simp [horizonPoint]

/-- The Eddington–Finkelstein `MetricTensor 4` at the horizon `r = 2M`. -/
noncomputable def horizonTensor (M v θ φ : ℝ) (hM : M ≠ 0)
    (hsin : Real.sin θ ≠ 0) : MetricTensor 4 :=
  metricTensor M (horizonPoint M v θ φ)
    (by
      simp only [horizonPoint_one]
      exact mul_ne_zero two_ne_zero hM)
    (by
      simpa [horizonPoint] using hsin)

/-- At the horizon the `rr` metric component vanishes, as it must in this
chart. -/
lemma horizonTensor_g_rr (M v θ φ : ℝ) (hM : M ≠ 0)
    (hsin : Real.sin θ ≠ 0) : (horizonTensor M v θ φ hM hsin).g 1 1 = 0 := by
  simp [horizonTensor, metricTensor, metric, horizonPoint]

/-- At the horizon the inverse `rr` component also vanishes: there is no
divergent `(1 - 2M/r)⁻¹` factor. -/
lemma horizonTensor_ginv_rr (M v θ φ : ℝ) (hM : M ≠ 0)
    (hsin : Real.sin θ ≠ 0) : (horizonTensor M v θ φ hM hsin).ginv 1 1 = 0 := by
  simp [horizonTensor, metricTensor, metricInv, horizonPoint]
  field_simp [hM]
  norm_num

/-- The cross component remains `1` at the horizon, so the vanishing `rr`
components do not make the metric degenerate. -/
lemma horizonTensor_g_vr (M v θ φ : ℝ) (hM : M ≠ 0)
    (hsin : Real.sin θ ≠ 0) : (horizonTensor M v θ φ hM hsin).g 0 1 = 1 := by
  simp [horizonTensor, metricTensor, metric, horizonPoint]

/-- **Ricci flatness at the horizon.**  The EF metric field at `r = 2M` has
vanishing coordinate Ricci tensor.  This is the same direct computation as
`ricciTensorOf_metric`, evaluated at the horizon, not a limit or an analytic
continuation from the exterior Schwarzschild chart. -/
lemma ricciTensorOf_metric_horizon (M v θ φ : ℝ) (hM : M ≠ 0)
    (hsin : Real.sin θ ≠ 0) (σ ν : Fin 4) :
    CoordinateCurvature.ricciTensor (metric M) (metricInv M) (horizonPoint M v θ φ) σ ν = 0 := by
  exact ricciTensorOf_metric M (horizonPoint M v θ φ)
    (by
      simp only [horizonPoint_one]
      exact mul_ne_zero two_ne_zero hM)
    (by
      simpa [horizonPoint] using hsin) σ ν

/-! ## E. The tortoise coordinate -/

/-- The tortoise coordinate `r* = r + 2M ln(r/2M - 1)` on the exterior `r > 2M`. -/
noncomputable def tortoiseStar (M r : ℝ) : ℝ :=
  r + 2 * M * Real.log (r / (2 * M) - 1)

/-- Derivative of the tortoise coordinate on the exterior:
`d(r*)/dr = (1 - 2M/r)⁻¹`. -/
lemma deriv_tortoiseStar (M r : ℝ) (hM : 0 < M) (hr : 2 * M < r) :
    deriv (fun s : ℝ => tortoiseStar M s) r = (1 - 2 * M / r)⁻¹ := by
  have hx1 : (0 : ℝ) < r := by linarith
  have h2M : (2 : ℝ) * M ≠ 0 := mul_ne_zero two_ne_zero hM.ne'
  have harg : 0 < r / (2 * M) - 1 := by
    have h2 : r / (2 * M) - 1 = (r - 2 * M) / (2 * M) := by
      field_simp
    rw [h2]
    exact div_pos (by linarith) (by positivity)
  have hinner : DifferentiableAt ℝ (fun s : ℝ => s / (2 * M) - 1) r := by fun_prop
  have hlog : DifferentiableAt ℝ (fun s : ℝ => Real.log (s / (2 * M) - 1)) r :=
    hinner.log harg.ne'
  have hlin : deriv (fun s : ℝ => s / (2 * M) - 1) r = 1 / (2 * M) := by
    have hsub : deriv (fun s : ℝ => s / (2 * M) - 1) r =
        deriv (fun s : ℝ => s / (2 * M)) r - deriv (fun s : ℝ => (1 : ℝ)) r := by
      exact deriv_sub (by fun_prop) (by fun_prop)
    rw [hsub, deriv_const]
    have h1 : deriv (fun s : ℝ => s / (2 * M)) r = 1 / (2 * M) := by
      have heq : (fun s : ℝ => s / (2 * M)) = (fun s : ℝ => (2 * M)⁻¹ * s) := by
        funext s
        field_simp [h2M]
      rw [heq, deriv_const_mul_id ((2 * M)⁻¹), one_div]
    rw [h1]
    simp
  have hlogd : deriv (fun s : ℝ => Real.log (s / (2 * M) - 1)) r =
      (r / (2 * M) - 1)⁻¹ * (1 / (2 * M)) := by
    have hchain := deriv_comp r (Real.differentiableAt_log harg.ne') hinner
    rw [Real.deriv_log, hlin] at hchain
    exact hchain
  have hcm : deriv (fun s : ℝ => 2 * M * Real.log (s / (2 * M) - 1)) r =
      2 * M * ((r / (2 * M) - 1)⁻¹ * (1 / (2 * M))) := by
    have h := deriv_const_mul (2 * M) hlog
    rwa [hlogd] at h
  have hid : deriv (fun s : ℝ => s) r = 1 := by simp
  have hdecomp : deriv (fun s : ℝ => tortoiseStar M s) r =
      deriv (fun s : ℝ => s) r +
        deriv (fun s : ℝ => 2 * M * Real.log (s / (2 * M) - 1)) r := by
    have hsplit : (fun s : ℝ => tortoiseStar M s) = (fun s : ℝ => s) +
        (fun s : ℝ => 2 * M * Real.log (s / (2 * M) - 1)) := rfl
    rw [hsplit]
    exact deriv_add (by fun_prop) (hlog.const_mul (2 * M))
  have hf : (1 : ℝ) - 2 * M / r ≠ 0 := by
    have hfrm : (1 : ℝ) - 2 * M / r = (r - 2 * M) / r := by
      field_simp
    rw [hfrm]
    exact div_ne_zero (by linarith) hx1.ne'
  rw [hdecomp, hid, hcm]
  field_simp [hx1.ne', h2M, harg.ne', hf]
  ring

/-- The tortoise coordinate is smooth on the exterior. -/
lemma contDiffOn_tortoiseStar (M : ℝ) (hM : 0 < M) :
    ContDiffOn ℝ ∞ (fun r : ℝ => tortoiseStar M r) {r : ℝ | 2 * M < r} := by
  have h2M : (2 : ℝ) * M ≠ 0 := mul_ne_zero two_ne_zero hM.ne'
  have hinner : ContDiffOn ℝ ∞ (fun r : ℝ => r / (2 * M) - 1)
      {r : ℝ | 2 * M < r} :=
    (contDiffOn_id.div_const (2 * M)).sub contDiffOn_const
  have hmem : Set.MapsTo (fun r : ℝ => r / (2 * M) - 1) {r : ℝ | 2 * M < r}
      {0}ᶜ := by
    intro r hr
    have hrlt : 2 * M < r := hr
    have h2 : r / (2 * M) - 1 = (r - 2 * M) / (2 * M) := by
      field_simp
    have hpos : 0 < r / (2 * M) - 1 := by
      rw [h2]
      exact div_pos (by linarith) (by positivity)
    show r / (2 * M) - 1 ≠ 0
    exact ne_of_gt hpos
  have hlog : ContDiffOn ℝ ∞ (fun r : ℝ => Real.log (r / (2 * M) - 1))
      {r : ℝ | 2 * M < r} :=
    Real.contDiffOn_log.comp hinner hmem
  show ContDiffOn ℝ ∞ (fun r : ℝ => r + 2 * M * Real.log (r / (2 * M) - 1))
    {r : ℝ | 2 * M < r}
  exact contDiffOn_id.add (contDiffOn_const.mul hlog)

/-! ## F. Overlap with the Schwarzschild exterior chart -/

/-- The overlap transition map: Schwarzschild `(t, r, θ, φ)` to EF
`(v, r, θ, φ)` via `v = t + r*`. -/
noncomputable def schwarzschildToEF (M : ℝ) (x : SpacetimeChart) : SpacetimeChart :=
  fun i => if i = 0 then x 0 + tortoiseStar M (x 1) else x i

@[simp] lemma schwarzschildToEF_zero (M : ℝ) (x : SpacetimeChart) :
    schwarzschildToEF M x 0 = x 0 + tortoiseStar M (x 1) := by
  simp [schwarzschildToEF]

@[simp] lemma schwarzschildToEF_one (M : ℝ) (x : SpacetimeChart) :
    schwarzschildToEF M x 1 = x 1 := by
  simp [schwarzschildToEF]

@[simp] lemma schwarzschildToEF_two (M : ℝ) (x : SpacetimeChart) :
    schwarzschildToEF M x 2 = x 2 := by
  simp [schwarzschildToEF]

@[simp] lemma schwarzschildToEF_three (M : ℝ) (x : SpacetimeChart) :
    schwarzschildToEF M x 3 = x 3 := by
  simp [schwarzschildToEF]

/-- The transition map is smooth on the exterior overlap. -/
lemma contDiffOn_schwarzschildToEF (M : ℝ) (hM : 0 < M) :
    ContDiffOn ℝ ∞ (schwarzschildToEF M) {x : SpacetimeChart | 2 * M < x 1} := by
  rw [contDiffOn_pi]
  intro i
  fin_cases i
  · exact (contDiffOn_apply (𝕜 := ℝ) (F' := fun _ : Fin 4 => ℝ) 0 _).add
      ((contDiffOn_tortoiseStar M hM).comp
        (contDiffOn_apply (𝕜 := ℝ) (F' := fun _ : Fin 4 => ℝ) 1 _)
        (by intro x hx; exact hx))
  · exact contDiffOn_apply (𝕜 := ℝ) (F' := fun _ : Fin 4 => ℝ) 1 _
  · exact contDiffOn_apply (𝕜 := ℝ) (F' := fun _ : Fin 4 => ℝ) 2 _
  · exact contDiffOn_apply (𝕜 := ℝ) (F' := fun _ : Fin 4 => ℝ) 3 _

/-- The Jacobian of the overlap transition map: the identity except for the
`(v, r)` entry `(1 - 2M/r)⁻¹`. -/
noncomputable def transitionJacobian (M : ℝ) (x : SpacetimeChart) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  fun α μ => if α = 0 ∧ μ = 1 then (1 - 2 * M / x 1)⁻¹
    else if α = μ then 1 else 0

/-- The `(v, r)` Jacobian entry is the tortoise derivative. -/
lemma transitionJacobian_zero_one (M : ℝ) (x : SpacetimeChart) (hM : 0 < M)
    (hr : 2 * M < x 1) :
    transitionJacobian M x 0 1 = deriv (fun s : ℝ => tortoiseStar M s) (x 1) := by
  have hJ : transitionJacobian M x 0 1 = (1 - 2 * M / x 1)⁻¹ := by
    simp [transitionJacobian]
  rw [hJ]
  exact (deriv_tortoiseStar M (x 1) hM hr).symm

/-- The Schwarzschild exterior metric is the pullback of the EF metric under
the overlap transition map. -/
lemma schwarzschild_eq_pullback (M : ℝ) (x : SpacetimeChart) (hM : 0 < M)
    (hr : 2 * M < x 1) :
    (schwarzschildSpacetime M).metric x =
      (transitionJacobian M x).transpose * metric M (schwarzschildToEF M x) *
        transitionJacobian M x := by
  have hx1 : (0 : ℝ) < x 1 := by linarith
  have hf : (1 : ℝ) - 2 * M / x 1 ≠ 0 := by
    have hfrm : (1 : ℝ) - 2 * M / x 1 = (x 1 - 2 * M) / x 1 := by
      field_simp
    rw [hfrm]
    exact div_ne_zero (by linarith) hx1.ne'
  ext σ ν
  fin_cases σ <;> fin_cases ν <;>
    simp [Schwarzschild.SchwarzschildSpacetime.metric, Schwarzschild.SchwarzschildSpacetime.metric,
      StaticSpherical.StaticSphericalMetric.metric, schwarzschildSpacetime,
        Schwarzschild.SchwarzschildSpacetime.metricFn,
      Schwarzschild.SchwarzschildSpacetime.toStaticSpherical,
      metric, schwarzschildToEF, transitionJacobian,
      Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four] <;>
    field_simp [hx1.ne', hM.ne', hf] <;>
    (first | exact Or.inl (by ring) | ring)

/-- The EF–Schwarzschild exterior overlap: on `r > 2M` the Schwarzschild metric
is the pullback of the EF metric, patching the two partial charts. -/
noncomputable def schwarzschildEFTransition (M : ℝ) (hM : 0 < M) :
    PartialChartTransition (Schwarzschild.exteriorPartialChart M hM) (partialChart M) where
  overlap := Schwarzschild.exteriorPartialDomain M
  overlap_open := Schwarzschild.exteriorPartialDomain_isOpen M
  overlap_subset := Set.Subset.rfl
  toFun := schwarzschildToEF M
  smooth := (contDiffOn_schwarzschildToEF M hM).mono (by
    intro x hx
    obtain ⟨h1, -⟩ := hx
    exact h1)
  maps_into := by
    intro x hx
    obtain ⟨hr, hsin⟩ := hx
    constructor
    · simp only [schwarzschildToEF_one]
      have hx1 : (0 : ℝ) < x 1 := by linarith
      exact hx1.ne'
    · simp only [schwarzschildToEF_two]
      exact hsin
  jacobian := transitionJacobian M
  metric_pullback := by
    intro x hx
    obtain ⟨hr, -⟩ := hx
    exact schwarzschild_eq_pullback M x hM hr

end EddingtonFinkelstein

/-- Global alias for the Eddington–Finkelstein partial chart. -/
noncomputable def eddingtonFinkelsteinPartialChart (M : ℝ) : PartialChartSpacetime :=
  EddingtonFinkelstein.partialChart M

/-- Global alias for the Eddington–Finkelstein partial chart. -/
noncomputable def eddingtonFinkelsteinPartialChartSpacetime (M : ℝ) :
    PartialChartSpacetime :=
  EddingtonFinkelstein.partialChart M

/-- Global alias for the Eddington–Finkelstein partial chart. -/
noncomputable def eddingtonFinkelsteinRestrictedChart (M : ℝ) : PartialChartSpacetime :=
  EddingtonFinkelstein.partialChart M

/-- Global alias for the Eddington–Finkelstein partial chart. -/
noncomputable def eddingtonFinkelsteinChart (M : ℝ) : PartialChartSpacetime :=
  EddingtonFinkelstein.partialChart M

end GeneralRelativity
