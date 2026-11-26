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
for any `StaticSphericalMetric` `ds² = -f(r) dt² + f(r)⁻¹ dr² + r² dΩ²`.

## i. Overview

A general static spherically symmetric four-dimensional metric in coordinates `(t, r, θ, φ)` is
bundled as `S : StaticSphericalMetric` parameterised by its radial lapse `S.lapse : ℝ → ℝ`:

`g = diag(-f(r), f(r)⁻¹, r², r² sin²θ)`.

This module feeds `S.metric` and `S.metricInv` directly through `GeneralRelativity.Pipeline`,
establishing:

- `StaticSphericalMetric.metricTensor` : bundled `MetricTensor 4` at any nondegenerate chart point
  `(r ≠ 0, S.lapse r ≠ 0, sin θ ≠ 0)`.
- `StaticSphericalMetric.christoffel_eq` and `StaticSphericalMetric.pd_christoffel_eq_deriv` :
  exact identification of all 64 Christoffel symbols and all 256 Christoffel partial derivatives
  from smoothness of `S.lapse` at `r`.
- `StaticSphericalMetric.ricciTensorOf`, `StaticSphericalMetric.ricciScalarOf`, and
  `StaticSphericalMetric.einsteinTensorOf` : exact closed-form coordinate Ricci, scalar, and
  Einstein tensors in terms of `S.lapse`, `(S.lapse)'`, and `(S.lapse)''`.

This general engine instantiates immediately to Schwarzschild, Schwarzschild–de Sitter, and
Reissner–Nordström electrovacuum spacetimes.

## ii. Key results

- `StaticSphericalMetric` : bundle of a static spherically symmetric metric parameterised by its
  radial lapse function.
- `StaticSphericalMetric.metric`, `StaticSphericalMetric.metricInv`,
  `StaticSphericalMetric.metric_symm`, `StaticSphericalMetric.metric_mul_inv`,
  `StaticSphericalMetric.metricTensor` : metric, inverse, and certified `MetricTensor 4` bundle.
- `StaticSphericalMetric.christoffel`, `StaticSphericalMetric.christoffelDeriv` : closed-form
  Christoffel and partial-derivative tables.
- `StaticSphericalMetric.christoffel_eq`, `StaticSphericalMetric.eventually_christoffel_eq`,
  `StaticSphericalMetric.riemann_eq_data` : metric-to-Riemann bridge.
- `StaticSphericalMetric.ricciTensorOf`, `StaticSphericalMetric.ricciScalarOf`,
  `StaticSphericalMetric.einsteinTensorOf` : pipeline curvature formulas for arbitrary
  twice-differentiable `S.lapse`.

## iii. Table of contents

- A. Metric, inverse, and MetricTensor bundle
- B. Christoffel symbols and metric partial derivatives
- C. Second-order Christoffel derivative table
- D. Ricci, scalar, and Einstein tensors through the pipeline

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

open GeneralRelativity.Pipeline

/-!

## A. Metric, inverse, and MetricTensor bundle

On a static spherically symmetric spacetime parameterized by a single radial lapse `f(r)`, the
diagonal metric `diag(-f, f⁻¹, r², r² sin²θ)` is nondegenerate everywhere away from the origin
(`r = 0`), horizons (`f = 0`), and polar axis (`sin θ = 0`).

-/

/-- A static spherically symmetric four-dimensional spacetime metric determined by a radial
lapse function `f(r)` in coordinates `(t, r, θ, φ)`. -/
structure StaticSphericalMetric where
  /-- The radial lapse profile `f(r)`. -/
  lapse : ℝ → ℝ

namespace StaticSphericalMetric

/-- General static spherically symmetric metric `diag(-f(r), f(r)⁻¹, r², r² sin²θ)` in
coordinates `x = (t, r, θ, φ)`. -/
noncomputable def metric (S : StaticSphericalMetric) (x : Fin 4 → ℝ) : Tensor2 4 :=
  fun i j =>
    if i = j then
      if i = 0 then -(S.lapse (x 1))
      else if i = 1 then (S.lapse (x 1))⁻¹
      else if i = 2 then (x 1) ^ 2
      else (x 1) ^ 2 * Real.sin (x 2) ^ 2
    else 0

/-- Inverse of the general static spherically symmetric metric. -/
noncomputable def metricInv (S : StaticSphericalMetric) (x : Fin 4 → ℝ) : Tensor2 4 :=
  fun i j =>
    if i = j then
      if i = 0 then -(S.lapse (x 1))⁻¹
      else if i = 1 then S.lapse (x 1)
      else if i = 2 then ((x 1) ^ 2)⁻¹
      else ((x 1) ^ 2 * Real.sin (x 2) ^ 2)⁻¹
    else 0

/-- Symmetry of `S.metric`. -/
lemma metric_symm (S : StaticSphericalMetric) (x : Fin 4 → ℝ) :
    IsSymm (S.metric x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply, metric]

/-- Left/right inverse identity `g * g⁻¹ = 1` on the regular chart `r ≠ 0`, `f(r) ≠ 0`,
`sin θ ≠ 0`. -/
lemma metric_mul_inv (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.lapse (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) :
    S.metric x * S.metricInv x = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [metric, metricInv, Matrix.mul_apply]
  · field_simp [hf]
  · field_simp [hf]
  · field_simp [hr]
  · field_simp [hr, hsin]

/-- Inverse identity `g⁻¹ * g = 1` on the regular chart `r ≠ 0`, `f(r) ≠ 0`, `sin θ ≠ 0`. -/
lemma metricInv_mul (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.lapse (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) :
    S.metricInv x * S.metric x = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [metric, metricInv, Matrix.mul_apply]
  · field_simp [hf]
  · field_simp [hf]
  · field_simp [hr]
  · field_simp [hr, hsin]

/-- Bundled `MetricTensor 4` for any static spherically symmetric metric away from coordinate and
horizon singularities. -/
noncomputable def metricTensor (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.lapse (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) : MetricTensor 4 where
  g := S.metric x
  ginv := S.metricInv x
  symm := S.metric_symm x
  inv_left := S.metric_mul_inv x hr hf hsin
  inv_right := S.metricInv_mul x hr hf hsin

/-!

## B. Christoffel symbols and metric partial derivatives

Computing the coordinate derivatives of `g_{ij}(x)` evaluates every one of the 64 Levi-Civita
Christoffel symbols into closed form `S.christoffel`, parametrized solely by `S.lapse` and its
radial derivative `(S.lapse)'`.

-/

-- Factored out separately from `Pipeline.christoffel` so symbolic radial differentiation avoids
-- differentiating 4-term metric-inverse sums at each step.
/-- Closed-form Levi-Civita Christoffel symbols `Γ^k_{ij}` of `S.metric` in
`(t, r, θ, φ)` coordinates. -/
noncomputable def christoffel (S : StaticSphericalMetric) (x : Fin 4 → ℝ)
    (k i j : Fin 4) : ℝ :=
  if k = 0 then
    (if (i = 1 ∧ j = 0) ∨ (i = 0 ∧ j = 1) then
      deriv S.lapse (x 1) / (2 * S.lapse (x 1))
     else 0)
  else if k = 1 then
    (if i = 0 ∧ j = 0 then S.lapse (x 1) * deriv S.lapse (x 1) / 2
     else if i = 1 ∧ j = 1 then -(deriv S.lapse (x 1) / (2 * S.lapse (x 1)))
     else if i = 2 ∧ j = 2 then -(x 1 * S.lapse (x 1))
     else if i = 3 ∧ j = 3 then -(x 1 * Real.sin (x 2) ^ 2 * S.lapse (x 1))
     else 0)
  else if k = 2 then
    (if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then 1 / x 1
     else if i = 3 ∧ j = 3 then -(Real.sin (x 2) * Real.cos (x 2)) else 0)
  else
    (if (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) then 1 / x 1
     else if (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) then Real.cos (x 2) / Real.sin (x 2) else 0)

@[simp]
private lemma pd_metric_t (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (a b : Fin 4) :
    coordDeriv 0 (fun y => S.metric y a b) x = 0 := by
  fin_cases a <;> fin_cases b <;> simp [coordDeriv, metric]

@[simp]
private lemma pd_metric_phi (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (a b : Fin 4) :
    coordDeriv 3 (fun y => S.metric y a b) x = 0 := by
  fin_cases a <;> fin_cases b <;> simp [coordDeriv, metric]

private lemma pd_metric_theta_33 (S : StaticSphericalMetric) (x : Fin 4 → ℝ) :
    coordDeriv 2 (fun y => S.metric y 3 3) x
      = 2 * (x 1) ^ 2 * Real.sin (x 2) * Real.cos (x 2) := by
  have hfun : (fun s : ℝ => S.metric (Function.update x 2 s) 3 3)
      = fun s : ℝ => (x 1) ^ 2 * Real.sin s ^ 2 := by
    funext s
    simp [metric]
  have hsinSq : HasDerivAt (fun s : ℝ => Real.sin s ^ 2)
      (2 * Real.sin (x 2) * Real.cos (x 2)) (x 2) := hasDerivAt_sin_sq (x 2)
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ (hsinSq.const_mul ((x 1) ^ 2)))]
  ring

private lemma pd_metric_theta (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (a b : Fin 4) :
    coordDeriv 2 (fun y => S.metric y a b) x
      = if a = 3 ∧ b = 3 then 2 * (x 1) ^ 2 * Real.sin (x 2) * Real.cos (x 2) else 0 := by
  fin_cases a <;> fin_cases b <;>
    first
    | exact pd_metric_theta_33 S x
    | simp [coordDeriv, metric]

private lemma pd_metric_r_00 (S : StaticSphericalMetric) (x : Fin 4 → ℝ)
    (hf_diff : DifferentiableAt ℝ S.lapse (x 1)) :
    coordDeriv 1 (fun y => S.metric y 0 0) x = -(deriv S.lapse (x 1)) := by
  have hfun : (fun s : ℝ => S.metric (Function.update x 1 s) 0 0)
      = fun s : ℝ => -S.lapse s := by
    funext s
    simp [metric]
  have hd : HasDerivAt (fun s : ℝ => -S.lapse s) (-deriv S.lapse (x 1)) (x 1) :=
    hf_diff.hasDerivAt.neg
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hd)]

private lemma pd_metric_r_11 (S : StaticSphericalMetric) (x : Fin 4 → ℝ)
    (hf_diff : DifferentiableAt ℝ S.lapse (x 1)) (hf : S.lapse (x 1) ≠ 0) :
    coordDeriv 1 (fun y => S.metric y 1 1) x = -(deriv S.lapse (x 1)) / (S.lapse (x 1)) ^ 2 := by
  have hfun : (fun s : ℝ => S.metric (Function.update x 1 s) 1 1)
      = fun s : ℝ => (S.lapse s)⁻¹ := by
    funext s
    simp [metric]
  have hd : HasDerivAt (fun s : ℝ => (S.lapse s)⁻¹)
      (-deriv S.lapse (x 1) / (S.lapse (x 1)) ^ 2) (x 1) := by
    convert hf_diff.hasDerivAt.inv hf using 1
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hd)]

private lemma pd_metric_r_22 (S : StaticSphericalMetric) (x : Fin 4 → ℝ) :
    coordDeriv 1 (fun y => S.metric y 2 2) x = 2 * (x 1) := by
  have hfun : (fun s : ℝ => S.metric (Function.update x 1 s) 2 2)
      = fun s : ℝ => s ^ 2 := by
    funext s
    simp [metric]
  rw [coordDeriv, hfun]
  simp

private lemma pd_metric_r_33 (S : StaticSphericalMetric) (x : Fin 4 → ℝ) :
    coordDeriv 1 (fun y => S.metric y 3 3) x = 2 * (x 1) * Real.sin (x 2) ^ 2 := by
  have hfun : (fun s : ℝ => S.metric (Function.update x 1 s) 3 3)
      = fun s : ℝ => s ^ 2 * Real.sin (x 2) ^ 2 := by
    funext s
    simp [metric]
  have hd : HasDerivAt (fun s : ℝ => s ^ 2 * Real.sin (x 2) ^ 2)
      (2 * (x 1) * Real.sin (x 2) ^ 2) (x 1) := by
    convert (hasDerivAt_pow 2 (x 1)).mul_const (Real.sin (x 2) ^ 2) using 1
    ring
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hd)]

private lemma pd_metric_r (S : StaticSphericalMetric) (x : Fin 4 → ℝ)
    (hf_diff : DifferentiableAt ℝ S.lapse (x 1)) (hf : S.lapse (x 1) ≠ 0) (a b : Fin 4) :
    coordDeriv 1 (fun y => S.metric y a b) x
      = if a = 0 ∧ b = 0 then -(deriv S.lapse (x 1))
        else if a = 1 ∧ b = 1 then -(deriv S.lapse (x 1)) / (S.lapse (x 1)) ^ 2
        else if a = 2 ∧ b = 2 then 2 * (x 1)
        else if a = 3 ∧ b = 3 then 2 * (x 1) * Real.sin (x 2) ^ 2
        else 0 := by
  fin_cases a <;> fin_cases b <;>
    first
    | exact pd_metric_r_00 S x hf_diff
    | exact pd_metric_r_11 S x hf_diff hf
    | exact pd_metric_r_22 S x
    | exact pd_metric_r_33 S x
    | simp [coordDeriv, metric]

/-- All 64 Christoffel symbols computed by `Pipeline.christoffel` match `S.christoffel` at any
regular point where `S.lapse` is differentiable. -/
lemma christoffel_eq (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.lapse (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (hf_diff : DifferentiableAt ℝ S.lapse (x 1)) :
    ∀ k i j, Pipeline.christoffel S.metric S.metricInv x k i j = S.christoffel x k i j := by
  intro k i j
  fin_cases k
  · fin_cases i <;> fin_cases j <;>
      simp [Pipeline.christoffel, christoffel, metricInv,
        pd_metric_theta, pd_metric_r S x hf_diff hf]
    all_goals field_simp [hr, hf, hsin]
  · fin_cases i <;> fin_cases j <;>
      simp [Pipeline.christoffel, christoffel, metricInv,
        pd_metric_theta, pd_metric_r S x hf_diff hf]
    all_goals field_simp [hr, hf, hsin]
  · fin_cases i <;> fin_cases j <;>
      simp [Pipeline.christoffel, christoffel, metricInv,
        pd_metric_theta, pd_metric_r S x hf_diff hf]
    all_goals field_simp [hr, hf, hsin]
  · fin_cases i <;> fin_cases j <;>
      simp [Pipeline.christoffel, christoffel, metricInv,
        pd_metric_theta, pd_metric_r S x hf_diff hf]
    all_goals field_simp [hr, hf, hsin]

/-- Neighbourhood equality of `Pipeline.christoffel` and `S.christoffel` around `x`. -/
lemma eventually_christoffel_eq (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.lapse (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (hf_diff : ∀ᶠ s in nhds (x 1), DifferentiableAt ℝ S.lapse s) (a b c : Fin 4) :
    (fun y => Pipeline.christoffel S.metric S.metricInv y a b c)
      =ᶠ[nhds x] fun y => S.christoffel y a b c := by
  have hc1 : Continuous (fun y : Fin 4 → ℝ => y 1) := continuous_apply 1
  have hc2 : Continuous (fun y : Fin 4 → ℝ => y 2) := continuous_apply 2
  have hcont : ContinuousAt S.lapse (x 1) := hf_diff.self_of_nhds.continuousAt
  have hr' : ∀ᶠ y in nhds x, y 1 ≠ 0 := (hc1.continuousAt.eventually_ne hr)
  have hf' : ∀ᶠ y in nhds x, S.lapse (y 1) ≠ 0 :=
    (hc1.continuousAt (x := x)).tendsto.eventually (hcont.eventually_ne hf)
  have hsin' : ∀ᶠ y in nhds x, Real.sin (y 2) ≠ 0 :=
    (hc2.continuousAt (x := x)).tendsto.eventually
      (Real.continuous_sin.continuousAt.eventually_ne hsin)
  have hdiff' : ∀ᶠ y in nhds x, DifferentiableAt ℝ S.lapse (y 1) :=
    hc1.continuousAt.tendsto.eventually hf_diff
  filter_upwards [hr', hf', hsin', hdiff'] with y hyr hyf hysin hydiff
  exact S.christoffel_eq y hyr hyf hysin hydiff a b c

/-- Neighbourhood equality promotes `Pipeline.christoffel = S.christoffel` to coordinate partial
derivatives along every axis `μ`. -/
lemma pd_christoffel_eq (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.lapse (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (hf_diff : ∀ᶠ s in nhds (x 1), DifferentiableAt ℝ S.lapse s) (μ a b c : Fin 4) :
    coordDeriv μ (fun y => Pipeline.christoffel S.metric S.metricInv y a b c) x
      = coordDeriv μ (fun y => S.christoffel y a b c) x :=
  coordDeriv_congr_nhds μ x (S.eventually_christoffel_eq x hr hf hsin hf_diff a b c)

/-!

## C. Second-order Christoffel derivative table

Differentiating each closed-form Christoffel symbol produces the complete 256-entry derivative table
`S.christoffelDeriv`, isolating second-order radial derivatives `(S.lapse)''` from Riemann
contraction loops.

-/

-- Separates scalar differentiation from `Pipeline.riemann` assembly.
/-- Closed-form partial-derivative table `∂_μ Γ^k_{ij}` of `S.christoffel` across all 256
coordinate and connection index tuples `(μ, k, i, j)`. -/
noncomputable def christoffelDeriv (S : StaticSphericalMetric) (μ : Fin 4) (x : Fin 4 → ℝ)
    (k i j : Fin 4) : ℝ :=
  if μ = 1 then
    (if k = 0 ∧ ((i = 1 ∧ j = 0) ∨ (i = 0 ∧ j = 1)) then
       (deriv (deriv S.lapse) (x 1) * S.lapse (x 1) - (deriv S.lapse (x 1)) ^ 2) /
         (2 * (S.lapse (x 1)) ^ 2)
     else if k = 1 ∧ i = 0 ∧ j = 0 then
       ((deriv S.lapse (x 1)) ^ 2 + S.lapse (x 1) * deriv (deriv S.lapse) (x 1)) / 2
     else if k = 1 ∧ i = 1 ∧ j = 1 then
       -((deriv (deriv S.lapse) (x 1) * S.lapse (x 1) - (deriv S.lapse (x 1)) ^ 2) /
         (2 * (S.lapse (x 1)) ^ 2))
     else if k = 1 ∧ i = 2 ∧ j = 2 then
       -S.lapse (x 1) - x 1 * deriv S.lapse (x 1)
     else if k = 1 ∧ i = 3 ∧ j = 3 then
       (-S.lapse (x 1) - x 1 * deriv S.lapse (x 1)) * Real.sin (x 2) ^ 2
     else if (k = 2 ∧ ((i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)))
         ∨ (k = 3 ∧ ((i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1))) then
       -1 / (x 1) ^ 2
     else 0)
  else if μ = 2 then
    (if k = 1 ∧ i = 3 ∧ j = 3 then
       -(x 1 * (2 * Real.sin (x 2) * Real.cos (x 2)) * S.lapse (x 1))
     else if k = 2 ∧ i = 3 ∧ j = 3 then
       Real.sin (x 2) ^ 2 - Real.cos (x 2) ^ 2
     else if k = 3 ∧ ((i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)) then
       -1 / Real.sin (x 2) ^ 2
     else 0)
  else 0

private lemma pd_G_r_001 (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (hf : S.lapse (x 1) ≠ 0)
    (hf1 : DifferentiableAt ℝ S.lapse (x 1)) (hf2 : DifferentiableAt ℝ (deriv S.lapse) (x 1)) :
    coordDeriv 1 (fun y => S.christoffel y 0 0 1) x = S.christoffelDeriv 1 x 0 0 1 := by
  have hfun : (fun s : ℝ => S.christoffel (Function.update x 1 s) 0 0 1)
      = fun s : ℝ => deriv S.lapse s / (2 * S.lapse s) := by
    funext s
    simp [christoffel]
  have h2f : 2 * S.lapse (x 1) ≠ 0 := mul_ne_zero (by norm_num) hf
  have hd : HasDerivAt (fun s : ℝ => deriv S.lapse s / (2 * S.lapse s))
      ((deriv (deriv S.lapse) (x 1) * (2 * S.lapse (x 1))
        - deriv S.lapse (x 1) * (2 * deriv S.lapse (x 1))) / (2 * S.lapse (x 1)) ^ 2) (x 1) := by
    convert hf2.hasDerivAt.div (hf1.hasDerivAt.const_mul 2) h2f using 1
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hd)]
  simp [christoffelDeriv]
  field_simp [hf]

private lemma pd_G_r_100 (S : StaticSphericalMetric) (x : Fin 4 → ℝ)
    (hf1 : DifferentiableAt ℝ S.lapse (x 1)) (hf2 : DifferentiableAt ℝ (deriv S.lapse) (x 1)) :
    coordDeriv 1 (fun y => S.christoffel y 1 0 0) x = S.christoffelDeriv 1 x 1 0 0 := by
  have hfun : (fun s : ℝ => S.christoffel (Function.update x 1 s) 1 0 0)
      = fun s : ℝ => S.lapse s * deriv S.lapse s / 2 := by
    funext s
    simp [christoffel]
  have hd : HasDerivAt (fun s : ℝ => S.lapse s * deriv S.lapse s / 2)
      ((deriv S.lapse (x 1) * deriv S.lapse (x 1)
        + S.lapse (x 1) * deriv (deriv S.lapse) (x 1)) / 2) (x 1) := by
    convert (hf1.hasDerivAt.mul hf2.hasDerivAt).div_const 2 using 1
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hd)]
  simp [christoffelDeriv]
  ring

private lemma pd_G_r_111 (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (hf : S.lapse (x 1) ≠ 0)
    (hf1 : DifferentiableAt ℝ S.lapse (x 1)) (hf2 : DifferentiableAt ℝ (deriv S.lapse) (x 1)) :
    coordDeriv 1 (fun y => S.christoffel y 1 1 1) x = S.christoffelDeriv 1 x 1 1 1 := by
  have hfun : (fun s : ℝ => S.christoffel (Function.update x 1 s) 1 1 1)
      = fun s : ℝ => -(deriv S.lapse s / (2 * S.lapse s)) := by
    funext s
    simp [christoffel]
  have h2f : 2 * S.lapse (x 1) ≠ 0 := mul_ne_zero (by norm_num) hf
  have hd : HasDerivAt (fun s : ℝ => -(deriv S.lapse s / (2 * S.lapse s)))
      (-((deriv (deriv S.lapse) (x 1) * (2 * S.lapse (x 1))
        - deriv S.lapse (x 1) * (2 * deriv S.lapse (x 1))) / (2 * S.lapse (x 1)) ^ 2)) (x 1) := by
    convert (hf2.hasDerivAt.div (hf1.hasDerivAt.const_mul 2) h2f).neg using 1
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hd)]
  simp [christoffelDeriv]
  field_simp [hf]

private lemma pd_G_r_122 (S : StaticSphericalMetric) (x : Fin 4 → ℝ)
    (hf1 : DifferentiableAt ℝ S.lapse (x 1)) :
    coordDeriv 1 (fun y => S.christoffel y 1 2 2) x = S.christoffelDeriv 1 x 1 2 2 := by
  have hfun : (fun s : ℝ => S.christoffel (Function.update x 1 s) 1 2 2)
      = fun s : ℝ => -(s * S.lapse s) := by
    funext s
    simp [christoffel]
  have hd : HasDerivAt (fun s : ℝ => -(s * S.lapse s))
      (-(1 * S.lapse (x 1) + x 1 * deriv S.lapse (x 1))) (x 1) := by
    convert ((hasDerivAt_id (x 1)).mul hf1.hasDerivAt).neg using 2 <;> simp
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hd)]
  simp [christoffelDeriv]
  ring

private lemma pd_G_r_133 (S : StaticSphericalMetric) (x : Fin 4 → ℝ)
    (hf1 : DifferentiableAt ℝ S.lapse (x 1)) :
    coordDeriv 1 (fun y => S.christoffel y 1 3 3) x = S.christoffelDeriv 1 x 1 3 3 := by
  have hfun : (fun s : ℝ => S.christoffel (Function.update x 1 s) 1 3 3)
      = fun s : ℝ => -(s * (Real.sin (x 2) ^ 2 * S.lapse s)) := by
    funext s
    simp [christoffel]
    ring
  have hd : HasDerivAt (fun s : ℝ => -(s * (Real.sin (x 2) ^ 2 * S.lapse s)))
      (-(1 * (Real.sin (x 2) ^ 2 * S.lapse (x 1))
        + x 1 * (Real.sin (x 2) ^ 2 * deriv S.lapse (x 1)))) (x 1) := by
    convert ((hasDerivAt_id (x 1)).mul (hf1.hasDerivAt.const_mul (Real.sin (x 2) ^ 2))).neg
      using 2 <;> simp
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hd)]
  simp [christoffelDeriv]
  ring

private lemma pd_G_r_inv (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0) (k i j : Fin 4)
    (hmatch : (k = 2 ∧ ((i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)))
      ∨ (k = 3 ∧ ((i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1)))) :
    coordDeriv 1 (fun y => S.christoffel y k i j) x = S.christoffelDeriv 1 x k i j := by
  have hderiv : deriv (fun s : ℝ => 1 / s) (x 1) = -1 / (x 1) ^ 2 := by
    have hfun : (fun s : ℝ => 1 / s) = fun s : ℝ => s⁻¹ := by funext s; simp [one_div]
    rw [hfun, (hasDerivAt_inv hr).deriv]
    ring
  rcases hmatch with ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · have hfun : (fun s : ℝ => S.christoffel (Function.update x 1 s) 2 1 2)
        = fun s : ℝ => 1 / s := by funext s; simp [christoffel]
    rw [coordDeriv, hfun, hderiv]; simp [christoffelDeriv]
  · have hfun : (fun s : ℝ => S.christoffel (Function.update x 1 s) 2 2 1)
        = fun s : ℝ => 1 / s := by funext s; simp [christoffel]
    rw [coordDeriv, hfun, hderiv]; simp [christoffelDeriv]
  · have hfun : (fun s : ℝ => S.christoffel (Function.update x 1 s) 3 1 3)
        = fun s : ℝ => 1 / s := by funext s; simp [christoffel]
    rw [coordDeriv, hfun, hderiv]; simp [christoffelDeriv]
  · have hfun : (fun s : ℝ => S.christoffel (Function.update x 1 s) 3 3 1)
        = fun s : ℝ => 1 / s := by funext s; simp [christoffel]
    rw [coordDeriv, hfun, hderiv]; simp [christoffelDeriv]

private lemma pd_G_t_133 (S : StaticSphericalMetric) (x : Fin 4 → ℝ) :
    coordDeriv 2 (fun y => S.christoffel y 1 3 3) x = S.christoffelDeriv 2 x 1 3 3 := by
  have hfun : (fun s : ℝ => S.christoffel (Function.update x 2 s) 1 3 3)
      = fun s : ℝ => -(x 1 * Real.sin s ^ 2 * S.lapse (x 1)) := by
    funext s
    simp [christoffel]
  have hsinSq : HasDerivAt (fun s : ℝ => Real.sin s ^ 2)
      (2 * Real.sin (x 2) * Real.cos (x 2)) (x 2) := hasDerivAt_sin_sq (x 2)
  have hd := ((hsinSq.const_mul (x 1)).mul_const (S.lapse (x 1))).neg
  have hderiv : deriv (fun s : ℝ => -(x 1 * Real.sin s ^ 2 * S.lapse (x 1))) (x 2)
      = -(x 1 * (2 * Real.sin (x 2) * Real.cos (x 2)) * S.lapse (x 1)) := hd.deriv
  rw [coordDeriv, hfun, hderiv]
  simp [christoffelDeriv]

private lemma pd_G_t_233 (S : StaticSphericalMetric) (x : Fin 4 → ℝ) :
    coordDeriv 2 (fun y => S.christoffel y 2 3 3) x = S.christoffelDeriv 2 x 2 3 3 := by
  have hfun : (fun s : ℝ => S.christoffel (Function.update x 2 s) 2 3 3)
      = fun s : ℝ => -(Real.sin s * Real.cos s) := by
    funext s
    simp [christoffel]
  have hd : HasDerivAt (fun s : ℝ => -(Real.sin s * Real.cos s))
      (Real.sin (x 2) ^ 2 - Real.cos (x 2) ^ 2) (x 2) := by
    convert ((Real.hasDerivAt_sin (x 2)).mul (Real.hasDerivAt_cos (x 2))).neg using 1
    ring
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hd)]
  simp [christoffelDeriv]

private lemma pd_G_t_323 (S : StaticSphericalMetric) (x : Fin 4 → ℝ)
    (hsin : Real.sin (x 2) ≠ 0) :
    coordDeriv 2 (fun y => S.christoffel y 3 2 3) x = S.christoffelDeriv 2 x 3 2 3 := by
  have hfun : (fun s : ℝ => S.christoffel (Function.update x 2 s) 3 2 3)
      = fun s : ℝ => Real.cos s / Real.sin s := by
    funext s
    simp [christoffel]
  have hsc : Real.sin (x 2) ^ 2 + Real.cos (x 2) ^ 2 = 1 := Real.sin_sq_add_cos_sq (x 2)
  have hd : HasDerivAt (fun s : ℝ => Real.cos s / Real.sin s)
      (-1 / Real.sin (x 2) ^ 2) (x 2) := by
    have h := (Real.hasDerivAt_cos (x 2)).div (Real.hasDerivAt_sin (x 2)) hsin
    have h1 : -Real.sin (x 2) * Real.sin (x 2) - Real.cos (x 2) * Real.cos (x 2) = -1 := by
      linear_combination -hsc
    convert h using 1
    rw [h1]
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hd)]
  simp [christoffelDeriv]

private lemma pd_G_eq_03 (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (μ k i j : Fin 4)
    (hμ : μ = 0 ∨ μ = 3) :
    coordDeriv μ (fun y => S.christoffel y k i j) x = S.christoffelDeriv μ x k i j := by
  rcases hμ with rfl | rfl
  · fin_cases k <;>
      (fin_cases i <;> fin_cases j <;> simp [coordDeriv, christoffel, christoffelDeriv])
  · fin_cases k <;>
      (fin_cases i <;> fin_cases j <;> simp [coordDeriv, christoffel, christoffelDeriv])

private lemma pd_G_eq_2 (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (hsin : Real.sin (x 2) ≠ 0)
    (k i j : Fin 4) :
    coordDeriv 2 (fun y => S.christoffel y k i j) x = S.christoffelDeriv 2 x k i j := by
  fin_cases k <;>
    (fin_cases i <;> fin_cases j <;>
      first
      | exact pd_G_t_133 S x
      | exact pd_G_t_233 S x
      | exact pd_G_t_323 S x hsin
      | simp [coordDeriv, christoffel, christoffelDeriv])

private lemma pd_G_eq_1 (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.lapse (x 1) ≠ 0) (hf1 : DifferentiableAt ℝ S.lapse (x 1))
    (hf2 : DifferentiableAt ℝ (deriv S.lapse) (x 1)) (k i j : Fin 4) :
    coordDeriv 1 (fun y => S.christoffel y k i j) x = S.christoffelDeriv 1 x k i j := by
  fin_cases k <;>
    (fin_cases i <;> fin_cases j <;>
      first
      | exact pd_G_r_001 S x hf hf1 hf2
      | exact pd_G_r_100 S x hf1 hf2
      | exact pd_G_r_111 S x hf hf1 hf2
      | exact pd_G_r_122 S x hf1
      | exact pd_G_r_133 S x hf1
      | exact pd_G_r_inv S x hr _ _ _ (by decide)
      | simp [coordDeriv, christoffel, christoffelDeriv])

/-- Complete identification of all 256 partial derivatives of `S.christoffel` with
`S.christoffelDeriv`. -/
lemma pd_christoffel_eq_deriv (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.lapse (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (hf1 : DifferentiableAt ℝ S.lapse (x 1)) (hf2 : DifferentiableAt ℝ (deriv S.lapse) (x 1))
    (μ k i j : Fin 4) :
    coordDeriv μ (fun y => S.christoffel y k i j) x = S.christoffelDeriv μ x k i j := by
  fin_cases μ
  · exact pd_G_eq_03 S x 0 k i j (Or.inl rfl)
  · exact pd_G_eq_1 S x hr hf hf1 hf2 k i j
  · exact pd_G_eq_2 S x hsin k i j
  · exact pd_G_eq_03 S x 3 k i j (Or.inr rfl)

/-!

## D. Ricci, scalar, and Einstein tensors through the pipeline

Feeding `S.christoffel` and `S.christoffelDeriv` into `riemannFromData` computes the full
coordinate-pipeline Ricci tensor, Ricci scalar `S = -f'' - 4 f'/r + 2(1 - f)/r²`, and Einstein
tensor for any `StaticSphericalMetric`.

-/

/-- The pipeline Riemann tensor of `S.metric` equals
`riemannFromData S.christoffel S.christoffelDeriv` across all 256 components. -/
lemma riemann_eq_data (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.lapse (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (hf_diff : ∀ᶠ s in nhds (x 1), DifferentiableAt ℝ S.lapse s)
    (hf2 : DifferentiableAt ℝ (deriv S.lapse) (x 1)) (ρ σ μ ν : Fin 4) :
    Pipeline.riemann S.metric S.metricInv x ρ σ μ ν
      = riemannFromData S.christoffel S.christoffelDeriv x ρ σ μ ν := by
  rw [riemann_eq_riemannFromData]
  have hf1 : DifferentiableAt ℝ S.lapse (x 1) := hf_diff.self_of_nhds
  have h1 : coordDeriv μ (fun y =>
      Pipeline.christoffel S.metric S.metricInv y ρ ν σ) x
      = S.christoffelDeriv μ x ρ ν σ :=
    (S.pd_christoffel_eq x hr hf hsin hf_diff μ ρ ν σ).trans
      (S.pd_christoffel_eq_deriv x hr hf hsin hf1 hf2 μ ρ ν σ)
  have h2 : coordDeriv ν (fun y =>
      Pipeline.christoffel S.metric S.metricInv y ρ μ σ) x
      = S.christoffelDeriv ν x ρ μ σ :=
    (S.pd_christoffel_eq x hr hf hsin hf_diff ν ρ μ σ).trans
      (S.pd_christoffel_eq_deriv x hr hf hsin hf1 hf2 ν ρ μ σ)
  simp only [riemannFromData, h1, h2, S.christoffel_eq x hr hf hsin hf1]

private lemma ricci_ss_00 (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.lapse (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (hf_diff : ∀ᶠ s in nhds (x 1), DifferentiableAt ℝ S.lapse s)
    (hf2 : DifferentiableAt ℝ (deriv S.lapse) (x 1)) :
    Pipeline.ricciTensorOf S.metric S.metricInv x 0 0
      = S.lapse (x 1) * (deriv (deriv S.lapse) (x 1) / 2 + deriv S.lapse (x 1) / x 1) := by
  simp [Pipeline.ricciTensorOf, Fin.sum_univ_four,
    S.riemann_eq_data x hr hf hsin hf_diff hf2,
    riemannFromData, christoffel, christoffelDeriv]
  field_simp [hr, hf]
  ring

private lemma ricci_ss_11 (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.lapse (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (hf_diff : ∀ᶠ s in nhds (x 1), DifferentiableAt ℝ S.lapse s)
    (hf2 : DifferentiableAt ℝ (deriv S.lapse) (x 1)) :
    Pipeline.ricciTensorOf S.metric S.metricInv x 1 1
      = -(deriv (deriv S.lapse) (x 1) / 2 + deriv S.lapse (x 1) / x 1) / S.lapse (x 1) := by
  simp [Pipeline.ricciTensorOf, Fin.sum_univ_four,
    S.riemann_eq_data x hr hf hsin hf_diff hf2,
    riemannFromData, christoffel, christoffelDeriv]
  field_simp [hr, hf]
  ring

private lemma ricci_ss_22 (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.lapse (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (hf_diff : ∀ᶠ s in nhds (x 1), DifferentiableAt ℝ S.lapse s)
    (hf2 : DifferentiableAt ℝ (deriv S.lapse) (x 1)) :
    Pipeline.ricciTensorOf S.metric S.metricInv x 2 2
      = 1 - S.lapse (x 1) - x 1 * deriv S.lapse (x 1) := by
  simp [Pipeline.ricciTensorOf, Fin.sum_univ_four,
    S.riemann_eq_data x hr hf hsin hf_diff hf2,
    riemannFromData, christoffel, christoffelDeriv]
  field_simp [hr, hf, hsin]
  rw [Real.sin_sq (x 2)]
  ring

private lemma ricci_ss_33 (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.lapse (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (hf_diff : ∀ᶠ s in nhds (x 1), DifferentiableAt ℝ S.lapse s)
    (hf2 : DifferentiableAt ℝ (deriv S.lapse) (x 1)) :
    Pipeline.ricciTensorOf S.metric S.metricInv x 3 3
      = (1 - S.lapse (x 1) - x 1 * deriv S.lapse (x 1)) * Real.sin (x 2) ^ 2 := by
  simp [Pipeline.ricciTensorOf, Fin.sum_univ_four,
    S.riemann_eq_data x hr hf hsin hf_diff hf2,
    riemannFromData, christoffel, christoffelDeriv]
  field_simp [hr, hf, hsin]
  ring

private lemma ricci_ss_offdiag (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.lapse (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (hf_diff : ∀ᶠ s in nhds (x 1), DifferentiableAt ℝ S.lapse s)
    (hf2 : DifferentiableAt ℝ (deriv S.lapse) (x 1)) {σ ν : Fin 4} (h : σ ≠ ν) :
    Pipeline.ricciTensorOf S.metric S.metricInv x σ ν = 0 := by
  fin_cases σ <;> fin_cases ν <;> try exact absurd rfl h
  all_goals
    simp [Pipeline.ricciTensorOf, Fin.sum_univ_four,
      S.riemann_eq_data x hr hf hsin hf_diff hf2,
      riemannFromData, christoffel, christoffelDeriv]
  ring

/-- Complete coordinate-pipeline Ricci tensor for any `StaticSphericalMetric`
`ds² = -f(r) dt² + f(r)⁻¹ dr² + r² dΩ²`. -/
lemma ricciTensorOf (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.lapse (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (hf_diff : ∀ᶠ s in nhds (x 1), DifferentiableAt ℝ S.lapse s)
    (hf2 : DifferentiableAt ℝ (deriv S.lapse) (x 1)) (σ ν : Fin 4) :
    Pipeline.ricciTensorOf S.metric S.metricInv x σ ν
      = if σ = ν then
          if σ = 0 then S.lapse (x 1) * (deriv (deriv S.lapse) (x 1) / 2
            + deriv S.lapse (x 1) / x 1)
          else if σ = 1 then -(deriv (deriv S.lapse) (x 1) / 2
            + deriv S.lapse (x 1) / x 1) / S.lapse (x 1)
          else if σ = 2 then 1 - S.lapse (x 1) - x 1 * deriv S.lapse (x 1)
          else (1 - S.lapse (x 1) - x 1 * deriv S.lapse (x 1)) * Real.sin (x 2) ^ 2
        else 0 := by
  fin_cases σ <;> fin_cases ν
  · simpa using ricci_ss_00 S x hr hf hsin hf_diff hf2
  · simpa using ricci_ss_offdiag S x hr hf hsin hf_diff hf2 (by decide)
  · simpa using ricci_ss_offdiag S x hr hf hsin hf_diff hf2 (by decide)
  · simpa using ricci_ss_offdiag S x hr hf hsin hf_diff hf2 (by decide)
  · simpa using ricci_ss_offdiag S x hr hf hsin hf_diff hf2 (by decide)
  · simpa using ricci_ss_11 S x hr hf hsin hf_diff hf2
  · simpa using ricci_ss_offdiag S x hr hf hsin hf_diff hf2 (by decide)
  · simpa using ricci_ss_offdiag S x hr hf hsin hf_diff hf2 (by decide)
  · simpa using ricci_ss_offdiag S x hr hf hsin hf_diff hf2 (by decide)
  · simpa using ricci_ss_offdiag S x hr hf hsin hf_diff hf2 (by decide)
  · simpa using ricci_ss_22 S x hr hf hsin hf_diff hf2
  · simpa using ricci_ss_offdiag S x hr hf hsin hf_diff hf2 (by decide)
  · simpa using ricci_ss_offdiag S x hr hf hsin hf_diff hf2 (by decide)
  · simpa using ricci_ss_offdiag S x hr hf hsin hf_diff hf2 (by decide)
  · simpa using ricci_ss_offdiag S x hr hf hsin hf_diff hf2 (by decide)
  · simpa using ricci_ss_33 S x hr hf hsin hf_diff hf2

/-- Scalar curvature computed by `Pipeline.ricciScalarOf` for `S.metric`:
`R = -f'' - 4 f'/r + 2 (1 - f) / r²`. -/
lemma ricciScalarOf (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.lapse (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (hf_diff : ∀ᶠ s in nhds (x 1), DifferentiableAt ℝ S.lapse s)
    (hf2 : DifferentiableAt ℝ (deriv S.lapse) (x 1)) :
    Pipeline.ricciScalarOf S.metric S.metricInv x
      = -deriv (deriv S.lapse) (x 1) - 4 * deriv S.lapse (x 1) / x 1
          + 2 * (1 - S.lapse (x 1)) / (x 1) ^ 2 := by
  simp only [Pipeline.ricciScalarOf, S.ricciTensorOf x hr hf hsin hf_diff hf2]
  simp only [Fin.sum_univ_four, metricInv, Fin.reduceEq, ↓reduceIte,
    Fin.isValue, mul_zero, add_zero, zero_add]
  field_simp [hr, hf, hsin]
  ring

/-- Einstein tensor computed by `Pipeline.einsteinTensorOf` for `S.metric`. -/
lemma einsteinTensorOf (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.lapse (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (hf_diff : ∀ᶠ s in nhds (x 1), DifferentiableAt ℝ S.lapse s)
    (hf2 : DifferentiableAt ℝ (deriv S.lapse) (x 1)) (i j : Fin 4) :
    Pipeline.einsteinTensorOf S.metric S.metricInv x i j
      = if i = j then
          if i = 0 then S.lapse (x 1) * (1 - S.lapse (x 1) - x 1 * deriv S.lapse (x 1)) / (x 1) ^ 2
          else if i = 1 then
            -(1 - S.lapse (x 1) - x 1 * deriv S.lapse (x 1)) / ((x 1) ^ 2 * S.lapse (x 1))
          else if i = 2 then
            (x 1) ^ 2 * (deriv (deriv S.lapse) (x 1) / 2 + deriv S.lapse (x 1) / x 1)
          else (x 1) ^ 2 * Real.sin (x 2) ^ 2
            * (deriv (deriv S.lapse) (x 1) / 2 + deriv S.lapse (x 1) / x 1)
        else 0 := by
  simp only [Pipeline.einsteinTensorOf, S.ricciTensorOf x hr hf hsin hf_diff hf2,
    S.ricciScalarOf x hr hf hsin hf_diff hf2, metric]
  fin_cases i <;> fin_cases j <;> simp
  · field_simp [hr]; ring
  · field_simp [hr, hf]; ring
  · field_simp [hr]; ring
  · field_simp [hr]; ring

end StaticSphericalMetric

end StaticSpherical

end GeneralRelativity
