/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import PhyslibAlpha.Relativity.Metrics.CoordinateMetric
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!

# General static spherically symmetric metrics

Metric-pipeline engine computing Christoffel symbols, Riemann, Ricci, scalar, and Einstein tensors
for any static spherically symmetric metric `ds² = -f(r) dt² + f(r)⁻¹ dr² + r² dΩ²`.

## i. Overview

A general static spherically symmetric four-dimensional metric in coordinates `(t, r, θ, φ)` is
parameterised by a single radial lapse function `f : ℝ → ℝ`:

`g = diag(-f(r), f(r)⁻¹, r², r² sin²θ)`.

This module feeds `staticSphericalMetric f` and its inverse directly through
`GeneralRelativity.Pipeline`, establishing:

- `staticSphericalMetricTensor` : bundled `MetricTensor 4` at any nondegenerate chart point
  `(r ≠ 0, f(r) ≠ 0, sin θ ≠ 0)`.
- `christoffel_eq_staticSphericalChristoffel` and `pd_staticSphericalChristoffel_eq_deriv` : exact
  identification of all 64 Christoffel symbols and all 256 Christoffel partial derivatives from
  smoothness of `f` at `r`.
- `ricciTensorOf_staticSpherical`, `ricciScalarOf_staticSpherical`, and
  `einsteinTensorOf_staticSpherical` :
  exact closed-form coordinate Ricci, scalar, and Einstein tensors in terms of `f`, `f'`, and `f''`.

This general engine instantiates immediately to Schwarzschild, Schwarzschild–de Sitter, and
Reissner–Nordström electrovacuum spacetimes.

## ii. Key results

- `StaticSphericalMetric` : bundle of a static spherically symmetric metric
  parameterised by its radial lapse function.
- `staticSphericalMetric`, `staticSphericalMetricInv`, `staticSphericalMetricTensor` : metric,
  inverse, and certified `MetricTensor 4` bundle.
- `staticSphericalChristoffel`, `staticSphericalChristoffelDeriv` : closed-form Christoffel and
  partial-derivative tables.
- `christoffel_eq_staticSphericalChristoffel`, `riemann_staticSpherical_eq_data` :
  metric-to-Riemann bridge.
- `ricciTensorOf_staticSpherical`, `ricciScalarOf_staticSpherical`,
  `einsteinTensorOf_staticSpherical` :
  pipeline curvature formulas for arbitrary twice-differentiable `f`.

## iii. Table of contents

- A. Metric, inverse, and MetricTensor bundle
- B. Christoffel symbols and metric partial derivatives
- C. Second-order Christoffel derivative table
- D. Ricci, scalar, and Einstein tensors through the pipeline

## iv. References

* R. M. Wald, *General Relativity* (1984). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973). [ref: mtw_1973_gravitation]
* B. O'Neill, *Semi-Riemannian Geometry With Applications to Relativity* (1983). [ref:
  oneill_1983_semi_riemannian]

-/

@[expose] public section

namespace GeneralRelativity

namespace StaticSpherical

open GeneralRelativity.Pipeline

/-!

## A. Metric, inverse, and MetricTensor bundle

-/

/-- A static spherically symmetric four-dimensional spacetime metric determined by a radial
lapse function `f(r)` in coordinates `(t, r, θ, φ)`. -/
structure StaticSphericalMetric where
  /-- The radial lapse profile `f(r)`. -/
  lapse : ℝ → ℝ

/-- General static spherically symmetric metric `diag(-f(r), f(r)⁻¹, r², r² sin²θ)` in
coordinates `x = (t, r, θ, φ)`. -/
noncomputable def staticSphericalMetric (f : ℝ → ℝ) (x : Fin 4 → ℝ) : Tensor2 4 :=
  fun i j =>
    if i = j then
      if i = 0 then -(f (x 1))
      else if i = 1 then (f (x 1))⁻¹
      else if i = 2 then (x 1) ^ 2
      else (x 1) ^ 2 * Real.sin (x 2) ^ 2
    else 0

/-- Inverse of the general static spherically symmetric metric. -/
noncomputable def staticSphericalMetricInv (f : ℝ → ℝ) (x : Fin 4 → ℝ) : Tensor2 4 :=
  fun i j =>
    if i = j then
      if i = 0 then -(f (x 1))⁻¹
      else if i = 1 then f (x 1)
      else if i = 2 then ((x 1) ^ 2)⁻¹
      else ((x 1) ^ 2 * Real.sin (x 2) ^ 2)⁻¹
    else 0

/-- Symmetry of `staticSphericalMetric`. -/
lemma staticSphericalMetric_symm (f : ℝ → ℝ) (x : Fin 4 → ℝ) :
    IsSymm (staticSphericalMetric f x) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [staticSphericalMetric]

/-- Left/right inverse identity `g * g⁻¹ = 1` on the regular chart `r ≠ 0`, `f(r) ≠ 0`,
`sin θ ≠ 0`. -/
lemma staticSphericalMetric_mul_inv (f : ℝ → ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : f (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) :
    staticSphericalMetric f x * staticSphericalMetricInv f x = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [staticSphericalMetric, staticSphericalMetricInv, Matrix.mul_apply]
  · field_simp [hf]
  · field_simp [hf]
  · field_simp [hr]
  · field_simp [hr, hsin]

/-- Inverse identity `g⁻¹ * g = 1` on the regular chart `r ≠ 0`, `f(r) ≠ 0`, `sin θ ≠ 0`. -/
lemma staticSphericalMetricInv_mul (f : ℝ → ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : f (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) :
    staticSphericalMetricInv f x * staticSphericalMetric f x = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [staticSphericalMetric, staticSphericalMetricInv, Matrix.mul_apply]
  · field_simp [hf]
  · field_simp [hf]
  · field_simp [hr]
  · field_simp [hr, hsin]

/-- Bundled `MetricTensor 4` for any static spherically symmetric metric away from coordinate and
horizon singularities. -/
noncomputable def staticSphericalMetricTensor (f : ℝ → ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : f (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) : MetricTensor 4 where
  g := staticSphericalMetric f x
  ginv := staticSphericalMetricInv f x
  symm := staticSphericalMetric_symm f x
  inv_left := staticSphericalMetric_mul_inv f x hr hf hsin
  inv_right := staticSphericalMetricInv_mul f x hr hf hsin

/-!

## B. Christoffel symbols and metric partial derivatives

-/

/-- Closed-form Christoffel symbols `Γ^k_{ij}` of `staticSphericalMetric f` in `(t, r, θ, φ)`
coordinates. Factored out separately from `Pipeline.christoffel` so symbolic radial
differentiation avoids differentiating 4-term metric-inverse sums at each step. -/
noncomputable def staticSphericalChristoffel (f : ℝ → ℝ) (x : Fin 4 → ℝ) (k i j : Fin 4) : ℝ :=
  if k = 0 then
    (if (i = 1 ∧ j = 0) ∨ (i = 0 ∧ j = 1) then deriv f (x 1) / (2 * f (x 1)) else 0)
  else if k = 1 then
    (if i = 0 ∧ j = 0 then f (x 1) * deriv f (x 1) / 2
     else if i = 1 ∧ j = 1 then -(deriv f (x 1) / (2 * f (x 1)))
     else if i = 2 ∧ j = 2 then -(x 1 * f (x 1))
     else if i = 3 ∧ j = 3 then -(x 1 * Real.sin (x 2) ^ 2 * f (x 1))
     else 0)
  else if k = 2 then
    (if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then 1 / x 1
     else if i = 3 ∧ j = 3 then -(Real.sin (x 2) * Real.cos (x 2)) else 0)
  else
    (if (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) then 1 / x 1
     else if (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) then Real.cos (x 2) / Real.sin (x 2) else 0)

@[simp]
private lemma pd_metric_t (f : ℝ → ℝ) (x : Fin 4 → ℝ) (a b : Fin 4) :
    pd 0 (fun y => staticSphericalMetric f y a b) x = 0 := by
  fin_cases a <;> fin_cases b <;> simp [pd, staticSphericalMetric]

@[simp]
private lemma pd_metric_phi (f : ℝ → ℝ) (x : Fin 4 → ℝ) (a b : Fin 4) :
    pd 3 (fun y => staticSphericalMetric f y a b) x = 0 := by
  fin_cases a <;> fin_cases b <;> simp [pd, staticSphericalMetric]

private lemma pd_metric_theta_33 (f : ℝ → ℝ) (x : Fin 4 → ℝ) :
    pd 2 (fun y => staticSphericalMetric f y 3 3) x
      = 2 * (x 1) ^ 2 * Real.sin (x 2) * Real.cos (x 2) := by
  have hfun : (fun s : ℝ => staticSphericalMetric f (Function.update x 2 s) 3 3)
      = fun s : ℝ => (x 1) ^ 2 * Real.sin s ^ 2 := by
    funext s
    simp [staticSphericalMetric]
  have hsinSq : HasDerivAt (fun s : ℝ => Real.sin s ^ 2)
      (2 * Real.sin (x 2) * Real.cos (x 2)) (x 2) := by
    convert (Real.hasDerivAt_sin (x 2)).pow 2 using 1
    ring
  rw [pd, hfun, (hsinSq.const_mul ((x 1) ^ 2)).deriv]
  ring

private lemma pd_metric_theta (f : ℝ → ℝ) (x : Fin 4 → ℝ) (a b : Fin 4) :
    pd 2 (fun y => staticSphericalMetric f y a b) x
      = if a = 3 ∧ b = 3 then 2 * (x 1) ^ 2 * Real.sin (x 2) * Real.cos (x 2) else 0 := by
  fin_cases a <;> fin_cases b <;>
    first
    | exact pd_metric_theta_33 f x
    | simp [pd, staticSphericalMetric]

private lemma pd_metric_r_00 (f : ℝ → ℝ) (x : Fin 4 → ℝ)
    (hf_diff : DifferentiableAt ℝ f (x 1)) :
    pd 1 (fun y => staticSphericalMetric f y 0 0) x = -(deriv f (x 1)) := by
  have hfun : (fun s : ℝ => staticSphericalMetric f (Function.update x 1 s) 0 0)
      = fun s : ℝ => -f s := by
    funext s
    simp [staticSphericalMetric]
  have hd : HasDerivAt (fun s : ℝ => -f s) (-deriv f (x 1)) (x 1) := hf_diff.hasDerivAt.neg
  rw [pd, hfun, hd.deriv]

private lemma pd_metric_r_11 (f : ℝ → ℝ) (x : Fin 4 → ℝ)
    (hf_diff : DifferentiableAt ℝ f (x 1)) (hf : f (x 1) ≠ 0) :
    pd 1 (fun y => staticSphericalMetric f y 1 1) x = -(deriv f (x 1)) / (f (x 1)) ^ 2 := by
  have hfun : (fun s : ℝ => staticSphericalMetric f (Function.update x 1 s) 1 1)
      = fun s : ℝ => (f s)⁻¹ := by
    funext s
    simp [staticSphericalMetric]
  have hd : HasDerivAt (fun s : ℝ => (f s)⁻¹) (-deriv f (x 1) / (f (x 1)) ^ 2) (x 1) := by
    convert hf_diff.hasDerivAt.inv hf using 1
  rw [pd, hfun, hd.deriv]

private lemma pd_metric_r_22 (f : ℝ → ℝ) (x : Fin 4 → ℝ) :
    pd 1 (fun y => staticSphericalMetric f y 2 2) x = 2 * (x 1) := by
  have hfun : (fun s : ℝ => staticSphericalMetric f (Function.update x 1 s) 2 2)
      = fun s : ℝ => s ^ 2 := by
    funext s
    simp [staticSphericalMetric]
  rw [pd, hfun]
  simp

private lemma pd_metric_r_33 (f : ℝ → ℝ) (x : Fin 4 → ℝ) :
    pd 1 (fun y => staticSphericalMetric f y 3 3) x = 2 * (x 1) * Real.sin (x 2) ^ 2 := by
  have hfun : (fun s : ℝ => staticSphericalMetric f (Function.update x 1 s) 3 3)
      = fun s : ℝ => s ^ 2 * Real.sin (x 2) ^ 2 := by
    funext s
    simp [staticSphericalMetric]
  have hd : HasDerivAt (fun s : ℝ => s ^ 2 * Real.sin (x 2) ^ 2)
      (2 * (x 1) * Real.sin (x 2) ^ 2) (x 1) := by
    convert (hasDerivAt_pow 2 (x 1)).mul_const (Real.sin (x 2) ^ 2) using 1
    ring
  rw [pd, hfun, hd.deriv]

private lemma pd_metric_r (f : ℝ → ℝ) (x : Fin 4 → ℝ) (hf_diff : DifferentiableAt ℝ f (x 1))
    (hf : f (x 1) ≠ 0) (a b : Fin 4) :
    pd 1 (fun y => staticSphericalMetric f y a b) x
      = if a = 0 ∧ b = 0 then -(deriv f (x 1))
        else if a = 1 ∧ b = 1 then -(deriv f (x 1)) / (f (x 1)) ^ 2
        else if a = 2 ∧ b = 2 then 2 * (x 1)
        else if a = 3 ∧ b = 3 then 2 * (x 1) * Real.sin (x 2) ^ 2
        else 0 := by
  fin_cases a <;> fin_cases b <;>
    first
    | exact pd_metric_r_00 f x hf_diff
    | exact pd_metric_r_11 f x hf_diff hf
    | exact pd_metric_r_22 f x
    | exact pd_metric_r_33 f x
    | simp [pd, staticSphericalMetric]

/-- All 64 Christoffel symbols computed by `christoffel` match `staticSphericalChristoffel` at any
regular
point where `f` is differentiable. -/
lemma christoffel_eq_staticSphericalChristoffel (f : ℝ → ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : f (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) (hf_diff : DifferentiableAt ℝ f (x 1)) :
    ∀ k i j, christoffel (staticSphericalMetric f) (staticSphericalMetricInv f) x k i j
      = staticSphericalChristoffel f x k i j := by
  intro k i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [christoffel, staticSphericalChristoffel, staticSphericalMetricInv,
      pd_metric_theta, pd_metric_r f x hf_diff hf]
  all_goals field_simp [hr, hf, hsin]

/-- Neighbourhood equality promotes `christoffel = staticSphericalChristoffel` to coordinate partial
derivatives along every axis `μ`. -/
lemma pd_christoffel_eq_pd_staticSphericalChristoffel (f : ℝ → ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : f (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (hf_diff : ∀ᶠ s in nhds (x 1), DifferentiableAt ℝ f s) (μ a b c : Fin 4) :
    pd μ (fun y => christoffel (staticSphericalMetric f) (staticSphericalMetricInv f) y a b c) x
      = pd μ (fun y => staticSphericalChristoffel f y a b c) x := by
  fin_cases μ
  · have heq : (fun s : ℝ =>
        christoffel (staticSphericalMetric f) (staticSphericalMetricInv f)
          (Function.update x 0 s) a b c)
        =ᶠ[nhds (x 0)] (fun s : ℝ => staticSphericalChristoffel f (Function.update x 0 s) a b c) :=
      Filter.Eventually.of_forall (fun s =>
        christoffel_eq_staticSphericalChristoffel f (Function.update x 0 s) hr hf hsin
          hf_diff.self_of_nhds a b c)
    exact Filter.EventuallyEq.deriv_eq heq
  · have hr' : ∀ᶠ s in nhds (x 1), s ≠ 0 := eventually_ne_nhds hr
    have hcont : ContinuousAt f (x 1) := hf_diff.self_of_nhds.continuousAt
    have hf' : ∀ᶠ s in nhds (x 1), f s ≠ 0 := hcont.eventually_ne hf
    have heq : (fun s : ℝ =>
        christoffel (staticSphericalMetric f) (staticSphericalMetricInv f)
          (Function.update x 1 s) a b c)
        =ᶠ[nhds (x 1)] (fun s :
          ℝ => staticSphericalChristoffel f (Function.update x 1 s) a b c) := by
      filter_upwards [hr', hf', hf_diff] with s hs1 hs2 hs3
      exact christoffel_eq_staticSphericalChristoffel f (Function.update x 1 s)
        (by simpa using hs1) (by simpa using hs2) (by simpa using hsin)
        (by simpa using hs3) a b c
    exact Filter.EventuallyEq.deriv_eq heq
  · have hsin' : ∀ᶠ s in nhds (x 2), Real.sin s ≠ 0 :=
      Real.continuous_sin.continuousAt.eventually_ne hsin
    have heq : (fun s : ℝ =>
        christoffel (staticSphericalMetric f) (staticSphericalMetricInv f)
          (Function.update x 2 s) a b c)
        =ᶠ[nhds (x 2)] (fun s :
          ℝ => staticSphericalChristoffel f (Function.update x 2 s) a b c) := by
      filter_upwards [hsin'] with s hs
      exact christoffel_eq_staticSphericalChristoffel f (Function.update x 2 s)
        (by simpa using hr) (by simpa using hf) (by simpa using hs)
        (by simpa using hf_diff.self_of_nhds) a b c
    exact Filter.EventuallyEq.deriv_eq heq
  · have heq : (fun s : ℝ =>
        christoffel (staticSphericalMetric f) (staticSphericalMetricInv f)
          (Function.update x 3 s) a b c)
        =ᶠ[nhds (x 3)] (fun s : ℝ => staticSphericalChristoffel f (Function.update x 3 s) a b c) :=
      Filter.Eventually.of_forall (fun s =>
        christoffel_eq_staticSphericalChristoffel f (Function.update x 3 s) hr hf hsin
          hf_diff.self_of_nhds a b c)
    exact Filter.EventuallyEq.deriv_eq heq

/-!

## C. Second-order Christoffel derivative table

-/

/-- Closed-form partial-derivative table `∂_μ staticSphericalChristoffel^k_{ij}` across all
256 index tuples `(μ, k, i, j)`, separating scalar differentiation from `Pipeline.riemann`
assembly. -/
noncomputable def staticSphericalChristoffelDeriv (f : ℝ → ℝ) (μ : Fin 4) (x : Fin 4 → ℝ)
    (k i j : Fin 4) : ℝ :=
  if μ = 1 then
    (if k = 0 ∧ ((i = 1 ∧ j = 0) ∨ (i = 0 ∧ j = 1)) then
       (deriv (deriv f) (x 1) * f (x 1) - (deriv f (x 1)) ^ 2) / (2 * (f (x 1)) ^ 2)
     else if k = 1 ∧ i = 0 ∧ j = 0 then
       ((deriv f (x 1)) ^ 2 + f (x 1) * deriv (deriv f) (x 1)) / 2
     else if k = 1 ∧ i = 1 ∧ j = 1 then
       -((deriv (deriv f) (x 1) * f (x 1) - (deriv f (x 1)) ^ 2) / (2 * (f (x 1)) ^ 2))
     else if k = 1 ∧ i = 2 ∧ j = 2 then
       -f (x 1) - x 1 * deriv f (x 1)
     else if k = 1 ∧ i = 3 ∧ j = 3 then
       (-f (x 1) - x 1 * deriv f (x 1)) * Real.sin (x 2) ^ 2
     else if (k = 2 ∧ ((i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)))
         ∨ (k = 3 ∧ ((i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1))) then
       -1 / (x 1) ^ 2
     else 0)
  else if μ = 2 then
    (if k = 1 ∧ i = 3 ∧ j = 3 then
       -(x 1 * (2 * Real.sin (x 2) * Real.cos (x 2)) * f (x 1))
     else if k = 2 ∧ i = 3 ∧ j = 3 then
       Real.sin (x 2) ^ 2 - Real.cos (x 2) ^ 2
     else if k = 3 ∧ ((i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)) then
       -1 / Real.sin (x 2) ^ 2
     else 0)
  else 0

private lemma pd_G_r_001 (f : ℝ → ℝ) (x : Fin 4 → ℝ) (hf : f (x 1) ≠ 0)
    (hf1 : DifferentiableAt ℝ f (x 1)) (hf2 : DifferentiableAt ℝ (deriv f) (x 1)) :
    pd 1 (fun y => staticSphericalChristoffel f y 0 0 1) x
      = staticSphericalChristoffelDeriv f 1 x 0 0 1 := by
  have hfun : (fun s : ℝ => staticSphericalChristoffel f (Function.update x 1 s) 0 0 1)
      = fun s : ℝ => deriv f s / (2 * f s) := by
    funext s
    simp [staticSphericalChristoffel]
  have h2f : 2 * f (x 1) ≠ 0 := mul_ne_zero (by norm_num) hf
  have hd : HasDerivAt (fun s : ℝ => deriv f s / (2 * f s))
      ((deriv (deriv f) (x 1) * (2 * f (x 1)) - deriv f (x 1) * (2 * deriv f (x 1)))
        / (2 * f (x 1)) ^ 2) (x 1) := by
    convert hf2.hasDerivAt.div (hf1.hasDerivAt.const_mul 2) h2f using 1
  rw [pd, hfun, hd.deriv]
  simp [staticSphericalChristoffelDeriv]
  field_simp [hf]

private lemma pd_G_r_100 (f : ℝ → ℝ) (x : Fin 4 → ℝ) (hf1 : DifferentiableAt ℝ f (x 1))
    (hf2 : DifferentiableAt ℝ (deriv f) (x 1)) :
    pd 1 (fun y => staticSphericalChristoffel f y 1 0 0) x
      = staticSphericalChristoffelDeriv f 1 x 1 0 0 := by
  have hfun : (fun s : ℝ => staticSphericalChristoffel f (Function.update x 1 s) 1 0 0)
      = fun s : ℝ => f s * deriv f s / 2 := by
    funext s
    simp [staticSphericalChristoffel]
  have hd : HasDerivAt (fun s : ℝ => f s * deriv f s / 2)
      ((deriv f (x 1) * deriv f (x 1) + f (x 1) * deriv (deriv f) (x 1)) / 2) (x 1) := by
    convert (hf1.hasDerivAt.mul hf2.hasDerivAt).div_const 2 using 1
  rw [pd, hfun, hd.deriv]
  simp [staticSphericalChristoffelDeriv]
  ring

private lemma pd_G_r_111 (f : ℝ → ℝ) (x : Fin 4 → ℝ) (hf : f (x 1) ≠ 0)
    (hf1 : DifferentiableAt ℝ f (x 1)) (hf2 : DifferentiableAt ℝ (deriv f) (x 1)) :
    pd 1 (fun y => staticSphericalChristoffel f y 1 1 1) x
      = staticSphericalChristoffelDeriv f 1 x 1 1 1 := by
  have hfun : (fun s : ℝ => staticSphericalChristoffel f (Function.update x 1 s) 1 1 1)
      = fun s : ℝ => -(deriv f s / (2 * f s)) := by
    funext s
    simp [staticSphericalChristoffel]
  have h2f : 2 * f (x 1) ≠ 0 := mul_ne_zero (by norm_num) hf
  have hd : HasDerivAt (fun s : ℝ => -(deriv f s / (2 * f s)))
      (-((deriv (deriv f) (x 1) * (2 * f (x 1)) - deriv f (x 1) * (2 * deriv f (x 1)))
        / (2 * f (x 1)) ^ 2)) (x 1) := by
    convert (hf2.hasDerivAt.div (hf1.hasDerivAt.const_mul 2) h2f).neg using 1
  rw [pd, hfun, hd.deriv]
  simp [staticSphericalChristoffelDeriv]
  field_simp [hf]

private lemma pd_G_r_122 (f : ℝ → ℝ) (x : Fin 4 → ℝ) (hf1 : DifferentiableAt ℝ f (x 1)) :
    pd 1 (fun y => staticSphericalChristoffel f y 1 2 2) x
      = staticSphericalChristoffelDeriv f 1 x 1 2 2 := by
  have hfun : (fun s : ℝ => staticSphericalChristoffel f (Function.update x 1 s) 1 2 2)
      = fun s : ℝ => -(s * f s) := by
    funext s
    simp [staticSphericalChristoffel]
  have hd : HasDerivAt (fun s : ℝ => -(s * f s))
      (-(1 * f (x 1) + x 1 * deriv f (x 1))) (x 1) := by
    convert ((hasDerivAt_id (x 1)).mul hf1.hasDerivAt).neg using 2 <;> simp
  rw [pd, hfun, hd.deriv]
  simp [staticSphericalChristoffelDeriv]
  ring

private lemma pd_G_r_133 (f : ℝ → ℝ) (x : Fin 4 → ℝ) (hf1 : DifferentiableAt ℝ f (x 1)) :
    pd 1 (fun y => staticSphericalChristoffel f y 1 3 3) x
      = staticSphericalChristoffelDeriv f 1 x 1 3 3 := by
  have hfun : (fun s : ℝ => staticSphericalChristoffel f (Function.update x 1 s) 1 3 3)
      = fun s : ℝ => -(s * (Real.sin (x 2) ^ 2 * f s)) := by
    funext s
    simp [staticSphericalChristoffel]
    ring
  have hd : HasDerivAt (fun s : ℝ => -(s * (Real.sin (x 2) ^ 2 * f s)))
      (-(1 * (Real.sin (x 2) ^ 2 * f (x 1))
        + x 1 * (Real.sin (x 2) ^ 2 * deriv f (x 1)))) (x 1) := by
    convert ((hasDerivAt_id (x 1)).mul (hf1.hasDerivAt.const_mul (Real.sin (x 2) ^ 2))).neg
      using 2 <;> simp
  rw [pd, hfun, hd.deriv]
  simp [staticSphericalChristoffelDeriv]
  ring

private lemma pd_G_r_inv (x : Fin 4 → ℝ) (hr : x 1 ≠ 0) (k i j : Fin 4)
    (hmatch : (k = 2 ∧ ((i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)))
      ∨ (k = 3 ∧ ((i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1)))) :
    pd 1 (fun y => staticSphericalChristoffel f y k i j) x
      = staticSphericalChristoffelDeriv f 1 x k i j := by
  have hderiv : deriv (fun s : ℝ => 1 / s) (x 1) = -1 / (x 1) ^ 2 := by
    have hfun : (fun s : ℝ => 1 / s) = fun s : ℝ => s⁻¹ := by funext s; simp [one_div]
    rw [hfun, (hasDerivAt_inv hr).deriv]
    ring
  rcases hmatch with ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · have hfun : (fun s : ℝ => staticSphericalChristoffel f (Function.update x 1 s) 2 1 2)
        = fun s : ℝ => 1 / s := by funext s; simp [staticSphericalChristoffel]
    rw [pd, hfun, hderiv]; simp [staticSphericalChristoffelDeriv]
  · have hfun : (fun s : ℝ => staticSphericalChristoffel f (Function.update x 1 s) 2 2 1)
        = fun s : ℝ => 1 / s := by funext s; simp [staticSphericalChristoffel]
    rw [pd, hfun, hderiv]; simp [staticSphericalChristoffelDeriv]
  · have hfun : (fun s : ℝ => staticSphericalChristoffel f (Function.update x 1 s) 3 1 3)
        = fun s : ℝ => 1 / s := by funext s; simp [staticSphericalChristoffel]
    rw [pd, hfun, hderiv]; simp [staticSphericalChristoffelDeriv]
  · have hfun : (fun s : ℝ => staticSphericalChristoffel f (Function.update x 1 s) 3 3 1)
        = fun s : ℝ => 1 / s := by funext s; simp [staticSphericalChristoffel]
    rw [pd, hfun, hderiv]; simp [staticSphericalChristoffelDeriv]

private lemma pd_G_t_133 (f : ℝ → ℝ) (x : Fin 4 → ℝ) :
    pd 2 (fun y => staticSphericalChristoffel f y 1 3 3) x
      = staticSphericalChristoffelDeriv f 2 x 1 3 3 := by
  have hfun : (fun s : ℝ => staticSphericalChristoffel f (Function.update x 2 s) 1 3 3)
      = fun s : ℝ => -(x 1 * Real.sin s ^ 2 * f (x 1)) := by
    funext s
    simp [staticSphericalChristoffel]
  have hsinSq : HasDerivAt (fun s : ℝ => Real.sin s ^ 2)
      (2 * Real.sin (x 2) * Real.cos (x 2)) (x 2) := by
    convert (Real.hasDerivAt_sin (x 2)).pow 2 using 1
    ring
  have hd := ((hsinSq.const_mul (x 1)).mul_const (f (x 1))).neg
  have hderiv : deriv (fun s : ℝ => -(x 1 * Real.sin s ^ 2 * f (x 1))) (x 2)
      = -(x 1 * (2 * Real.sin (x 2) * Real.cos (x 2)) * f (x 1)) := hd.deriv
  rw [pd, hfun, hderiv]
  simp [staticSphericalChristoffelDeriv]

private lemma pd_G_t_233 (f : ℝ → ℝ) (x : Fin 4 → ℝ) :
    pd 2 (fun y => staticSphericalChristoffel f y 2 3 3) x
      = staticSphericalChristoffelDeriv f 2 x 2 3 3 := by
  have hfun : (fun s : ℝ => staticSphericalChristoffel f (Function.update x 2 s) 2 3 3)
      = fun s : ℝ => -(Real.sin s * Real.cos s) := by
    funext s
    simp [staticSphericalChristoffel]
  have hd : HasDerivAt (fun s : ℝ => -(Real.sin s * Real.cos s))
      (Real.sin (x 2) ^ 2 - Real.cos (x 2) ^ 2) (x 2) := by
    convert ((Real.hasDerivAt_sin (x 2)).mul (Real.hasDerivAt_cos (x 2))).neg using 1
    ring
  rw [pd, hfun, hd.deriv]
  simp [staticSphericalChristoffelDeriv]

private lemma pd_G_t_323 (f : ℝ → ℝ) (x : Fin 4 → ℝ) (hsin : Real.sin (x 2) ≠ 0) :
    pd 2 (fun y => staticSphericalChristoffel f y 3 2 3) x
      = staticSphericalChristoffelDeriv f 2 x 3 2 3 := by
  have hfun : (fun s : ℝ => staticSphericalChristoffel f (Function.update x 2 s) 3 2 3)
      = fun s : ℝ => Real.cos s / Real.sin s := by
    funext s
    simp [staticSphericalChristoffel]
  have hsc : Real.sin (x 2) ^ 2 + Real.cos (x 2) ^ 2 = 1 := Real.sin_sq_add_cos_sq (x 2)
  have hd : HasDerivAt (fun s : ℝ => Real.cos s / Real.sin s)
      (-1 / Real.sin (x 2) ^ 2) (x 2) := by
    have h := (Real.hasDerivAt_cos (x 2)).div (Real.hasDerivAt_sin (x 2)) hsin
    have h1 : -Real.sin (x 2) * Real.sin (x 2) - Real.cos (x 2) * Real.cos (x 2) = -1 := by
      linear_combination -hsc
    convert h using 1
    rw [h1]
  rw [pd, hfun, hd.deriv]
  simp [staticSphericalChristoffelDeriv]

private lemma pd_G_eq_03 (f : ℝ → ℝ) (x : Fin 4 → ℝ) (μ k i j : Fin 4)
    (hμ : μ = 0 ∨ μ = 3) :
    pd μ (fun y => staticSphericalChristoffel f y k i j) x
      = staticSphericalChristoffelDeriv f μ x k i j := by
  rcases hμ with rfl | rfl
  · fin_cases k <;> fin_cases i <;> fin_cases j <;> simp [pd, staticSphericalChristoffel,
    staticSphericalChristoffelDeriv]
  · fin_cases k <;> fin_cases i <;> fin_cases j <;> simp [pd, staticSphericalChristoffel,
    staticSphericalChristoffelDeriv]

private lemma pd_G_eq_2 (f : ℝ → ℝ) (x : Fin 4 → ℝ) (hsin : Real.sin (x 2) ≠ 0)
    (k i j : Fin 4) :
    pd 2 (fun y => staticSphericalChristoffel f y k i j) x
      = staticSphericalChristoffelDeriv f 2 x k i j := by
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    first
    | exact pd_G_t_133 f x
    | exact pd_G_t_233 f x
    | exact pd_G_t_323 f x hsin
    | simp [pd, staticSphericalChristoffel, staticSphericalChristoffelDeriv]

private lemma pd_G_eq_1 (f : ℝ → ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0) (hf : f (x 1) ≠ 0)
    (hf1 : DifferentiableAt ℝ f (x 1)) (hf2 : DifferentiableAt ℝ (deriv f) (x 1))
    (k i j : Fin 4) :
    pd 1 (fun y => staticSphericalChristoffel f y k i j) x
      = staticSphericalChristoffelDeriv f 1 x k i j := by
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    first
    | exact pd_G_r_001 f x hf hf1 hf2
    | exact pd_G_r_100 f x hf1 hf2
    | exact pd_G_r_111 f x hf hf1 hf2
    | exact pd_G_r_122 f x hf1
    | exact pd_G_r_133 f x hf1
    | exact pd_G_r_inv x hr _ _ _ (by decide)
    | simp [pd, staticSphericalChristoffel, staticSphericalChristoffelDeriv]

/-- Complete identification of all 256 partial derivatives of `staticSphericalChristoffel` with
`staticSphericalChristoffelDeriv`. -/
lemma pd_staticSphericalChristoffel_eq_deriv (f : ℝ → ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : f (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (hf1 : DifferentiableAt ℝ f (x 1)) (hf2 : DifferentiableAt ℝ (deriv f) (x 1))
    (μ k i j : Fin 4) :
    pd μ (fun y => staticSphericalChristoffel f y k i j) x
      = staticSphericalChristoffelDeriv f μ x k i j := by
  fin_cases μ
  · exact pd_G_eq_03 f x 0 k i j (Or.inl rfl)
  · exact pd_G_eq_1 f x hr hf hf1 hf2 k i j
  · exact pd_G_eq_2 f x hsin k i j
  · exact pd_G_eq_03 f x 3 k i j (Or.inr rfl)

/-!

## D. Ricci, scalar, and Einstein tensors through the pipeline

-/

/-- The pipeline Riemann tensor of `staticSphericalMetric f` equals
`riemannFromData (staticSphericalChristoffel f) (staticSphericalChristoffelDeriv f)` across all
256 components. -/
lemma riemann_staticSpherical_eq_data (f : ℝ → ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : f (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (hf_diff : ∀ᶠ s in nhds (x 1), DifferentiableAt ℝ f s)
    (hf2 : DifferentiableAt ℝ (deriv f) (x 1)) (ρ σ μ ν : Fin 4) :
    riemann (staticSphericalMetric f) (staticSphericalMetricInv f) x ρ σ μ ν
      = riemannFromData (staticSphericalChristoffel f) (staticSphericalChristoffelDeriv f) x ρ σ μ
          ν := by
  rw [riemann_eq_riemannFromData]
  have hf1 : DifferentiableAt ℝ f (x 1) := hf_diff.self_of_nhds
  have h1 : pd μ (fun y =>
      christoffel (staticSphericalMetric f) (staticSphericalMetricInv f) y ρ ν σ) x
      = staticSphericalChristoffelDeriv f μ x ρ ν σ :=
    (pd_christoffel_eq_pd_staticSphericalChristoffel f x hr hf hsin hf_diff μ ρ ν σ).trans
      (pd_staticSphericalChristoffel_eq_deriv f x hr hf hsin hf1 hf2 μ ρ ν σ)
  have h2 : pd ν (fun y =>
      christoffel (staticSphericalMetric f) (staticSphericalMetricInv f) y ρ μ σ) x
      = staticSphericalChristoffelDeriv f ν x ρ μ σ :=
    (pd_christoffel_eq_pd_staticSphericalChristoffel f x hr hf hsin hf_diff ν ρ μ σ).trans
      (pd_staticSphericalChristoffel_eq_deriv f x hr hf hsin hf1 hf2 ν ρ μ σ)
  simp only [riemannFromData, h1, h2, christoffel_eq_staticSphericalChristoffel f x hr hf hsin hf1]

private lemma ricci_ss_00 (f : ℝ → ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0) (hf : f (x 1) ≠ 0)
    (hsin : Real.sin (x 2) ≠ 0) (hf_diff : ∀ᶠ s in nhds (x 1), DifferentiableAt ℝ f s)
    (hf2 : DifferentiableAt ℝ (deriv f) (x 1)) :
    ricciTensorOf (staticSphericalMetric f) (staticSphericalMetricInv f) x 0 0
      = f (x 1) * (deriv (deriv f) (x 1) / 2 + deriv f (x 1) / x 1) := by
  simp [ricciTensorOf, Fin.sum_univ_four,
    riemann_staticSpherical_eq_data f x hr hf hsin hf_diff hf2,
    riemannFromData, staticSphericalChristoffel, staticSphericalChristoffelDeriv]
  field_simp [hr, hf]
  ring

private lemma ricci_ss_11 (f : ℝ → ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0) (hf : f (x 1) ≠ 0)
    (hsin : Real.sin (x 2) ≠ 0) (hf_diff : ∀ᶠ s in nhds (x 1), DifferentiableAt ℝ f s)
    (hf2 : DifferentiableAt ℝ (deriv f) (x 1)) :
    ricciTensorOf (staticSphericalMetric f) (staticSphericalMetricInv f) x 1 1
      = -(deriv (deriv f) (x 1) / 2 + deriv f (x 1) / x 1) / f (x 1) := by
  simp [ricciTensorOf, Fin.sum_univ_four,
    riemann_staticSpherical_eq_data f x hr hf hsin hf_diff hf2,
    riemannFromData, staticSphericalChristoffel, staticSphericalChristoffelDeriv]
  field_simp [hr, hf]
  ring

private lemma ricci_ss_22 (f : ℝ → ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0) (hf : f (x 1) ≠ 0)
    (hsin : Real.sin (x 2) ≠ 0) (hf_diff : ∀ᶠ s in nhds (x 1), DifferentiableAt ℝ f s)
    (hf2 : DifferentiableAt ℝ (deriv f) (x 1)) :
    ricciTensorOf (staticSphericalMetric f) (staticSphericalMetricInv f) x 2 2
      = 1 - f (x 1) - x 1 * deriv f (x 1) := by
  simp [ricciTensorOf, Fin.sum_univ_four,
    riemann_staticSpherical_eq_data f x hr hf hsin hf_diff hf2,
    riemannFromData, staticSphericalChristoffel, staticSphericalChristoffelDeriv]
  field_simp [hr, hf, hsin]
  rw [Real.sin_sq (x 2)]
  ring

private lemma ricci_ss_33 (f : ℝ → ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0) (hf : f (x 1) ≠ 0)
    (hsin : Real.sin (x 2) ≠ 0) (hf_diff : ∀ᶠ s in nhds (x 1), DifferentiableAt ℝ f s)
    (hf2 : DifferentiableAt ℝ (deriv f) (x 1)) :
    ricciTensorOf (staticSphericalMetric f) (staticSphericalMetricInv f) x 3 3
      = (1 - f (x 1) - x 1 * deriv f (x 1)) * Real.sin (x 2) ^ 2 := by
  simp [ricciTensorOf, Fin.sum_univ_four,
    riemann_staticSpherical_eq_data f x hr hf hsin hf_diff hf2,
    riemannFromData, staticSphericalChristoffel, staticSphericalChristoffelDeriv]
  field_simp [hr, hf, hsin]
  ring

/-- Complete coordinate-pipeline Ricci tensor for any static spherically symmetric metric
`ds² = -f(r) dt² + f(r)⁻¹ dr² + r² dΩ²`. -/
lemma ricciTensorOf_staticSpherical (f : ℝ → ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : f (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (hf_diff : ∀ᶠ s in nhds (x 1), DifferentiableAt ℝ f s)
    (hf2 : DifferentiableAt ℝ (deriv f) (x 1)) (σ ν : Fin 4) :
    ricciTensorOf (staticSphericalMetric f) (staticSphericalMetricInv f) x σ ν
      = if σ = ν then
          if σ = 0 then f (x 1) * (deriv (deriv f) (x 1) / 2 + deriv f (x 1) / x 1)
          else if σ = 1 then -(deriv (deriv f) (x 1) / 2 + deriv f (x 1) / x 1) / f (x 1)
          else if σ = 2 then 1 - f (x 1) - x 1 * deriv f (x 1)
          else (1 - f (x 1) - x 1 * deriv f (x 1)) * Real.sin (x 2) ^ 2
        else 0 := by
  fin_cases σ <;> fin_cases ν
  · simpa using ricci_ss_00 f x hr hf hsin hf_diff hf2
  · simp [ricciTensorOf, Fin.sum_univ_four,
      riemann_staticSpherical_eq_data f x hr hf hsin hf_diff hf2,
      riemannFromData, staticSphericalChristoffel, staticSphericalChristoffelDeriv]
  · simp [ricciTensorOf, Fin.sum_univ_four,
      riemann_staticSpherical_eq_data f x hr hf hsin hf_diff hf2,
      riemannFromData, staticSphericalChristoffel, staticSphericalChristoffelDeriv]
  · simp [ricciTensorOf, Fin.sum_univ_four,
      riemann_staticSpherical_eq_data f x hr hf hsin hf_diff hf2,
      riemannFromData, staticSphericalChristoffel, staticSphericalChristoffelDeriv]
  · simp [ricciTensorOf, Fin.sum_univ_four,
      riemann_staticSpherical_eq_data f x hr hf hsin hf_diff hf2,
      riemannFromData, staticSphericalChristoffel, staticSphericalChristoffelDeriv]
  · simpa using ricci_ss_11 f x hr hf hsin hf_diff hf2
  · simp [ricciTensorOf, Fin.sum_univ_four,
      riemann_staticSpherical_eq_data f x hr hf hsin hf_diff hf2,
      riemannFromData, staticSphericalChristoffel, staticSphericalChristoffelDeriv]
  · simp [ricciTensorOf, Fin.sum_univ_four,
      riemann_staticSpherical_eq_data f x hr hf hsin hf_diff hf2,
      riemannFromData, staticSphericalChristoffel, staticSphericalChristoffelDeriv]
  · simp [ricciTensorOf, Fin.sum_univ_four,
      riemann_staticSpherical_eq_data f x hr hf hsin hf_diff hf2,
      riemannFromData, staticSphericalChristoffel, staticSphericalChristoffelDeriv]
  · simp [ricciTensorOf, Fin.sum_univ_four,
      riemann_staticSpherical_eq_data f x hr hf hsin hf_diff hf2,
      riemannFromData, staticSphericalChristoffel, staticSphericalChristoffelDeriv]
    ring
  · simpa using ricci_ss_22 f x hr hf hsin hf_diff hf2
  · simp [ricciTensorOf, Fin.sum_univ_four,
      riemann_staticSpherical_eq_data f x hr hf hsin hf_diff hf2,
      riemannFromData, staticSphericalChristoffel, staticSphericalChristoffelDeriv]
  · simp [ricciTensorOf, Fin.sum_univ_four,
      riemann_staticSpherical_eq_data f x hr hf hsin hf_diff hf2,
      riemannFromData, staticSphericalChristoffel, staticSphericalChristoffelDeriv]
  · simp [ricciTensorOf, Fin.sum_univ_four,
      riemann_staticSpherical_eq_data f x hr hf hsin hf_diff hf2,
      riemannFromData, staticSphericalChristoffel, staticSphericalChristoffelDeriv]
  · simp [ricciTensorOf, Fin.sum_univ_four,
      riemann_staticSpherical_eq_data f x hr hf hsin hf_diff hf2,
      riemannFromData, staticSphericalChristoffel, staticSphericalChristoffelDeriv]
  · simpa using ricci_ss_33 f x hr hf hsin hf_diff hf2

/-- Scalar curvature computed by `ricciScalarOf` for `staticSphericalMetric f`:
`S = -f'' - 4 f'/r + 2 (1 - f) / r²`. -/
lemma ricciScalarOf_staticSpherical (f : ℝ → ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : f (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (hf_diff : ∀ᶠ s in nhds (x 1), DifferentiableAt ℝ f s)
    (hf2 : DifferentiableAt ℝ (deriv f) (x 1)) :
    ricciScalarOf (staticSphericalMetric f) (staticSphericalMetricInv f) x
      = -deriv (deriv f) (x 1) - 4 * deriv f (x 1) / x 1 + 2 * (1 - f (x 1)) / (x 1) ^ 2 := by
  simp only [ricciScalarOf, ricciTensorOf_staticSpherical f x hr hf hsin hf_diff hf2]
  simp only [Fin.sum_univ_four, staticSphericalMetricInv, Fin.reduceEq, ↓reduceIte,
    Fin.isValue, mul_zero, add_zero, zero_add]
  field_simp [hr, hf, hsin]
  ring

/-- Einstein tensor computed by `einsteinTensorOf` for `staticSphericalMetric f`. -/
lemma einsteinTensorOf_staticSpherical (f : ℝ → ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : f (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (hf_diff : ∀ᶠ s in nhds (x 1), DifferentiableAt ℝ f s)
    (hf2 : DifferentiableAt ℝ (deriv f) (x 1)) (i j : Fin 4) :
    einsteinTensorOf (staticSphericalMetric f) (staticSphericalMetricInv f) x i j
      = if i = j then
          if i = 0 then f (x 1) * (1 - f (x 1) - x 1 * deriv f (x 1)) / (x 1) ^ 2
          else if i = 1 then -(1 - f (x 1) - x 1 * deriv f (x 1)) / ((x 1) ^ 2 * f (x 1))
          else if i = 2 then (x 1) ^ 2 * (deriv (deriv f) (x 1) / 2 + deriv f (x 1) / x 1)
          else (x 1) ^ 2 * Real.sin (x 2) ^ 2
            * (deriv (deriv f) (x 1) / 2 + deriv f (x 1) / x 1)
        else 0 := by
  simp only [einsteinTensorOf, ricciTensorOf_staticSpherical f x hr hf hsin hf_diff hf2,
    ricciScalarOf_staticSpherical f x hr hf hsin hf_diff hf2, staticSphericalMetric]
  fin_cases i <;> fin_cases j <;> simp
  · field_simp [hr]; ring
  · field_simp [hr, hf]; ring
  · field_simp [hr]; ring
  · field_simp [hr]; ring

end StaticSpherical

end GeneralRelativity
