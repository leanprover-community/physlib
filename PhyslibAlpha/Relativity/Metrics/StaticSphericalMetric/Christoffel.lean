/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import PhyslibAlpha.Relativity.Metrics.StaticSphericalMetric.Basic
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

# Static spherically symmetric Christoffel symbols and derivatives

Closed-form Levi-Civita connection coefficients `StaticSphericalMetric.christoffel` and their
partial derivatives `StaticSphericalMetric.christoffelDeriv`, verified against
`Pipeline.christoffel`.

## i. Overview

Differentiating `ds² = -f(r) dt² + f(r)⁻¹ dr² + r² dθ² + r² sin²θ dφ²` produces only radial and
polar coordinate derivatives of the metric components, since the metric is static (`∂_t g = 0`)
and axisymmetric (`∂_φ g = 0`). Combining these derivatives with `S.metricInv` identifies all 64
components of `Pipeline.christoffel` with the closed-form table `S.christoffel` and identifies all
256 coordinate partial derivatives `∂_μ Γ^k_{ij}` with `S.christoffelDeriv`.

## ii. Key results

- `christoffelThetaPhiPhi_from_metric`, `christoffelPhiPhiTheta_from_metric` : angular
  Levi-Civita connection coefficients of 2-spheres of radius `r`.
- `StaticSphericalMetric.christoffel`, `StaticSphericalMetric.christoffelDeriv` : closed-form
  Christoffel and partial-derivative tables.
- `StaticSphericalMetric.christoffel_eq`, `StaticSphericalMetric.eventually_christoffel_eq`,
  `StaticSphericalMetric.pd_christoffel_eq`, `StaticSphericalMetric.pd_christoffel_eq_deriv` :
  agreement with `Pipeline.christoffel` and its partial derivatives.

## iii. Table of contents

- A. Angular Christoffel symbols and metric partial derivatives
- B. Second-order Christoffel derivative table

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 6 (Sec. 6.1). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 23 (Sec. 23.2).
  [ref: mtw_1973_gravitation]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 7
  (https://arxiv.org/pdf/gr-qc/9712019#page=168). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

namespace StaticSpherical

open GeneralRelativity.Pipeline

/-!

## A. Angular Christoffel symbols and metric partial derivatives

Because a static spherically symmetric metric is invariant under time translations and rotations,
only radial (`∂_r`) and polar (`∂_θ`) derivatives contribute to the Levi-Civita connection.

-/

/-- Angular Christoffel symbol on a 2-sphere of radius `r`:
`Γ^θ_{φφ} = (1/2) g^{θθ} (-∂_θ g_{φφ}) = -sin θ cos θ`. -/
lemma christoffelThetaPhiPhi_from_metric (r th : ℝ) (hr : r ≠ 0) :
    (1 / 2 : ℝ) * (r ^ 2)⁻¹ * (-(2 * r ^ 2 * Real.sin th * Real.cos th))
      = -(Real.sin th * Real.cos th) := by
  field_simp

/-- Angular Christoffel symbol on a 2-sphere of radius `r`:
`Γ^φ_{θφ} = (1/2) g^{φφ} ∂_θ g_{φφ} = cos θ / sin θ`. -/
lemma christoffelPhiPhiTheta_from_metric (r th : ℝ) (hr : r ≠ 0) (hsin : Real.sin th ≠ 0) :
    (1 / 2 : ℝ) * (r ^ 2 * Real.sin th ^ 2)⁻¹ * (2 * r ^ 2 * Real.sin th * Real.cos th)
      = Real.cos th / Real.sin th := by
  field_simp

namespace StaticSphericalMetric

/-- Closed-form Levi-Civita Christoffel symbols `Γ^k_{ij}` for a static spherically symmetric
metric in `(t, r, θ, φ)` coordinates. -/
noncomputable def christoffel (S : StaticSphericalMetric) (x : Fin 4 → ℝ)
    (k i j : Fin 4) : ℝ :=
  if k = 0 then
    (if (i = 1 ∧ j = 0) ∨ (i = 0 ∧ j = 1) then
      deriv S.metricFn (x 1) / (2 * S.metricFn (x 1))
     else 0)
  else if k = 1 then
    (if i = 0 ∧ j = 0 then S.metricFn (x 1) * deriv S.metricFn (x 1) / 2
     else if i = 1 ∧ j = 1 then -(deriv S.metricFn (x 1) / (2 * S.metricFn (x 1)))
     else if i = 2 ∧ j = 2 then -(x 1 * S.metricFn (x 1))
     else if i = 3 ∧ j = 3 then -(x 1 * Real.sin (x 2) ^ 2 * S.metricFn (x 1))
     else 0)
  else if k = 2 then
    (if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then 1 / x 1
     else if i = 3 ∧ j = 3 then -(Real.sin (x 2) * Real.cos (x 2)) else 0)
  else
    (if (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) then 1 / x 1
     else if (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) then Real.cos (x 2) / Real.sin (x 2) else 0)

@[simp]
private lemma metricDeriv_t_eq_zero (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (a b : Fin 4) :
    coordDeriv 0 (fun y => S.metric y a b) x = 0 :=
  coordDeriv_const_slice 0 (S.metric x a b) fun _ => by simp [metric]

@[simp]
private lemma metricDeriv_phi_eq_zero (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (a b : Fin 4) :
    coordDeriv 3 (fun y => S.metric y a b) x = 0 :=
  coordDeriv_const_slice 3 (S.metric x a b) fun _ => by simp [metric]

private lemma metricDeriv_theta_33 (S : StaticSphericalMetric) (x : Fin 4 → ℝ) :
    coordDeriv 2 (fun y => S.metric y 3 3) x
      = 2 * (x 1) ^ 2 * Real.sin (x 2) * Real.cos (x 2) := by
  have hfun : (fun s : ℝ => S.metric (Function.update x 2 s) 3 3)
      = fun s : ℝ => (x 1) ^ 2 * Real.sin s ^ 2 := by
    funext s
    simp [metric]
  have hsinSq : HasDerivAt (fun s : ℝ => Real.sin s ^ 2)
      (2 * Real.sin (x 2) * Real.cos (x 2)) (x 2) :=
    ((hasDerivAt_pow 2 (Real.sin (x 2))).comp (x 2)
      (Real.hasDerivAt_sin (x 2))).congr_deriv (by ring)
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ (hsinSq.const_mul ((x 1) ^ 2)))]
  ring

private lemma metricDeriv_theta (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (a b : Fin 4) :
    coordDeriv 2 (fun y => S.metric y a b) x
      = if a = 3 ∧ b = 3 then 2 * (x 1) ^ 2 * Real.sin (x 2) * Real.cos (x 2) else 0 := by
  fin_cases a <;> fin_cases b <;>
    first
    | exact metricDeriv_theta_33 S x
    | simp [coordDeriv, metric]

private lemma metricDeriv_r_00 (S : StaticSphericalMetric) (x : Fin 4 → ℝ)
    (hf_diff : DifferentiableAt ℝ S.metricFn (x 1)) :
    coordDeriv 1 (fun y => S.metric y 0 0) x = -(deriv S.metricFn (x 1)) := by
  have hfun : (fun s : ℝ => S.metric (Function.update x 1 s) 0 0)
      = fun s : ℝ => -S.metricFn s := by
    funext s
    simp [metric]
  have hd : HasDerivAt (fun s : ℝ => -S.metricFn s) (-deriv S.metricFn (x 1)) (x 1) :=
    hf_diff.hasDerivAt.neg
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hd)]

private lemma metricDeriv_r_11 (S : StaticSphericalMetric) (x : Fin 4 → ℝ)
    (hf_diff : DifferentiableAt ℝ S.metricFn (x 1)) (hf : S.metricFn (x 1) ≠ 0) :
    coordDeriv 1 (fun y => S.metric y 1 1) x
      = -(deriv S.metricFn (x 1)) / (S.metricFn (x 1)) ^ 2 := by
  have hfun : (fun s : ℝ => S.metric (Function.update x 1 s) 1 1)
      = fun s : ℝ => (S.metricFn s)⁻¹ := by
    funext s
    simp [metric]
  have hd : HasDerivAt (fun s : ℝ => (S.metricFn s)⁻¹)
      (-deriv S.metricFn (x 1) / (S.metricFn (x 1)) ^ 2) (x 1) := by
    convert hf_diff.hasDerivAt.inv hf using 1
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hd)]

private lemma metricDeriv_r_22 (S : StaticSphericalMetric) (x : Fin 4 → ℝ) :
    coordDeriv 1 (fun y => S.metric y 2 2) x = 2 * (x 1) := by
  have hfun : (fun s : ℝ => S.metric (Function.update x 1 s) 2 2)
      = fun s : ℝ => s ^ 2 := by
    funext s
    simp [metric]
  rw [coordDeriv, hfun]
  simp

private lemma metricDeriv_r_33 (S : StaticSphericalMetric) (x : Fin 4 → ℝ) :
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

private lemma metricDeriv_r (S : StaticSphericalMetric) (x : Fin 4 → ℝ)
    (hf_diff : DifferentiableAt ℝ S.metricFn (x 1)) (hf : S.metricFn (x 1) ≠ 0)
    (a b : Fin 4) :
    coordDeriv 1 (fun y => S.metric y a b) x
      = if a = 0 ∧ b = 0 then -(deriv S.metricFn (x 1))
        else if a = 1 ∧ b = 1 then -(deriv S.metricFn (x 1)) / (S.metricFn (x 1)) ^ 2
        else if a = 2 ∧ b = 2 then 2 * (x 1)
        else if a = 3 ∧ b = 3 then 2 * (x 1) * Real.sin (x 2) ^ 2
        else 0 := by
  fin_cases a <;> fin_cases b <;>
    first
    | exact metricDeriv_r_00 S x hf_diff
    | exact metricDeriv_r_11 S x hf_diff hf
    | exact metricDeriv_r_22 S x
    | exact metricDeriv_r_33 S x
    | simp [coordDeriv, metric]

/-- All 64 Christoffel symbols computed by `Pipeline.christoffel` agree with the closed-form
connection table at every regular point where the radial metric function is differentiable. -/
lemma christoffel_eq (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.metricFn (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (hf_diff : DifferentiableAt ℝ S.metricFn (x 1)) :
    ∀ k i j, Pipeline.christoffel S.metric S.metricInv x k i j = S.christoffel x k i j := by
  intro k i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [Pipeline.christoffel, christoffel, metricInv,
      metricDeriv_theta, metricDeriv_r S x hf_diff hf] <;>
    field_simp [hr, hf, hsin]

/-- Neighbourhood equality between `Pipeline.christoffel` and the closed-form static spherical
Christoffel table around any regular point. -/
lemma eventually_christoffel_eq (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.metricFn (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (hf_diff : ∀ᶠ s in nhds (x 1), DifferentiableAt ℝ S.metricFn s) (a b c : Fin 4) :
    (fun y => Pipeline.christoffel S.metric S.metricInv y a b c)
      =ᶠ[nhds x] fun y => S.christoffel y a b c := by
  have hc1 : Continuous (fun y : Fin 4 → ℝ => y 1) := continuous_apply 1
  have hc2 : Continuous (fun y : Fin 4 → ℝ => y 2) := continuous_apply 2
  have hcont : ContinuousAt S.metricFn (x 1) := hf_diff.self_of_nhds.continuousAt
  have hr' : ∀ᶠ y in nhds x, y 1 ≠ 0 := hc1.continuousAt.eventually_ne hr
  have hf' : ∀ᶠ y in nhds x, S.metricFn (y 1) ≠ 0 :=
    (hc1.continuousAt (x := x)).tendsto.eventually (hcont.eventually_ne hf)
  have hsin' : ∀ᶠ y in nhds x, Real.sin (y 2) ≠ 0 :=
    (hc2.continuousAt (x := x)).tendsto.eventually
      (Real.continuous_sin.continuousAt.eventually_ne hsin)
  have hdiff' : ∀ᶠ y in nhds x, DifferentiableAt ℝ S.metricFn (y 1) :=
    hc1.continuousAt.tendsto.eventually hf_diff
  filter_upwards [hr', hf', hsin', hdiff'] with y hyr hyf hysin hydiff
  exact S.christoffel_eq y hyr hyf hysin hydiff a b c

/-- Equality of coordinate partial derivatives of `Pipeline.christoffel` and the closed-form
static spherical Christoffel table along every coordinate axis. -/
lemma pd_christoffel_eq (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.metricFn (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (hf_diff : ∀ᶠ s in nhds (x 1), DifferentiableAt ℝ S.metricFn s) (μ a b c : Fin 4) :
    coordDeriv μ (fun y => Pipeline.christoffel S.metric S.metricInv y a b c) x
      = coordDeriv μ (fun y => S.christoffel y a b c) x :=
  coordDeriv_congr_nhds μ x (S.eventually_christoffel_eq x hr hf hsin hf_diff a b c)

/-!

## B. Second-order Christoffel derivative table

Differentiating each closed-form Christoffel symbol with respect to `(t, r, θ, φ)` isolates the
second radial derivative `f''(r)` that enters the Riemann and Ricci curvature components.

-/

/-- Closed-form partial-derivative table `∂_μ Γ^k_{ij}` for a static spherically symmetric metric
across all 256 index tuples `(μ, k, i, j)`. -/
noncomputable def christoffelDeriv (S : StaticSphericalMetric) (μ : Fin 4) (x : Fin 4 → ℝ)
    (k i j : Fin 4) : ℝ :=
  if μ = 1 then
    (if k = 0 ∧ ((i = 1 ∧ j = 0) ∨ (i = 0 ∧ j = 1)) then
       (deriv (deriv S.metricFn) (x 1) * S.metricFn (x 1) - (deriv S.metricFn (x 1)) ^ 2) /
         (2 * (S.metricFn (x 1)) ^ 2)
     else if k = 1 ∧ i = 0 ∧ j = 0 then
       ((deriv S.metricFn (x 1)) ^ 2 + S.metricFn (x 1) * deriv (deriv S.metricFn) (x 1)) / 2
     else if k = 1 ∧ i = 1 ∧ j = 1 then
       -((deriv (deriv S.metricFn) (x 1) * S.metricFn (x 1) - (deriv S.metricFn (x 1)) ^ 2) /
         (2 * (S.metricFn (x 1)) ^ 2))
     else if k = 1 ∧ i = 2 ∧ j = 2 then
       -S.metricFn (x 1) - x 1 * deriv S.metricFn (x 1)
     else if k = 1 ∧ i = 3 ∧ j = 3 then
       (-S.metricFn (x 1) - x 1 * deriv S.metricFn (x 1)) * Real.sin (x 2) ^ 2
     else if (k = 2 ∧ ((i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)))
         ∨ (k = 3 ∧ ((i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1))) then
       -1 / (x 1) ^ 2
     else 0)
  else if μ = 2 then
    (if k = 1 ∧ i = 3 ∧ j = 3 then
       -(x 1 * (2 * Real.sin (x 2) * Real.cos (x 2)) * S.metricFn (x 1))
     else if k = 2 ∧ i = 3 ∧ j = 3 then
       Real.sin (x 2) ^ 2 - Real.cos (x 2) ^ 2
     else if k = 3 ∧ ((i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)) then
       -1 / Real.sin (x 2) ^ 2
     else 0)
  else 0

private lemma christoffelDeriv_r_001 (S : StaticSphericalMetric) (x : Fin 4 → ℝ)
    (hf : S.metricFn (x 1) ≠ 0) (hf1 : DifferentiableAt ℝ S.metricFn (x 1))
    (hf2 : DifferentiableAt ℝ (deriv S.metricFn) (x 1)) :
    coordDeriv 1 (fun y => S.christoffel y 0 0 1) x = S.christoffelDeriv 1 x 0 0 1 := by
  have hfun : (fun s : ℝ => S.christoffel (Function.update x 1 s) 0 0 1)
      = fun s : ℝ => deriv S.metricFn s / (2 * S.metricFn s) := by
    funext s
    simp [christoffel]
  have h2f : 2 * S.metricFn (x 1) ≠ 0 := mul_ne_zero (by norm_num) hf
  have hd : HasDerivAt (fun s : ℝ => deriv S.metricFn s / (2 * S.metricFn s))
      ((deriv (deriv S.metricFn) (x 1) * (2 * S.metricFn (x 1))
        - deriv S.metricFn (x 1) * (2 * deriv S.metricFn (x 1))) /
        (2 * S.metricFn (x 1)) ^ 2) (x 1) := by
    convert hf2.hasDerivAt.div (hf1.hasDerivAt.const_mul 2) h2f using 1
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hd)]
  simp [christoffelDeriv]
  field_simp [hf]

private lemma christoffelDeriv_r_100 (S : StaticSphericalMetric) (x : Fin 4 → ℝ)
    (hf1 : DifferentiableAt ℝ S.metricFn (x 1))
    (hf2 : DifferentiableAt ℝ (deriv S.metricFn) (x 1)) :
    coordDeriv 1 (fun y => S.christoffel y 1 0 0) x = S.christoffelDeriv 1 x 1 0 0 := by
  have hfun : (fun s : ℝ => S.christoffel (Function.update x 1 s) 1 0 0)
      = fun s : ℝ => S.metricFn s * deriv S.metricFn s / 2 := by
    funext s
    simp [christoffel]
  have hd : HasDerivAt (fun s : ℝ => S.metricFn s * deriv S.metricFn s / 2)
      ((deriv S.metricFn (x 1) * deriv S.metricFn (x 1)
        + S.metricFn (x 1) * deriv (deriv S.metricFn) (x 1)) / 2) (x 1) := by
    convert (hf1.hasDerivAt.mul hf2.hasDerivAt).div_const 2 using 1
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hd)]
  simp [christoffelDeriv]
  ring

private lemma christoffelDeriv_r_111 (S : StaticSphericalMetric) (x : Fin 4 → ℝ)
    (hf : S.metricFn (x 1) ≠ 0) (hf1 : DifferentiableAt ℝ S.metricFn (x 1))
    (hf2 : DifferentiableAt ℝ (deriv S.metricFn) (x 1)) :
    coordDeriv 1 (fun y => S.christoffel y 1 1 1) x = S.christoffelDeriv 1 x 1 1 1 := by
  have hfun : (fun s : ℝ => S.christoffel (Function.update x 1 s) 1 1 1)
      = fun s : ℝ => -(deriv S.metricFn s / (2 * S.metricFn s)) := by
    funext s
    simp [christoffel]
  have h2f : 2 * S.metricFn (x 1) ≠ 0 := mul_ne_zero (by norm_num) hf
  have hd : HasDerivAt (fun s : ℝ => -(deriv S.metricFn s / (2 * S.metricFn s)))
      (-((deriv (deriv S.metricFn) (x 1) * (2 * S.metricFn (x 1))
        - deriv S.metricFn (x 1) * (2 * deriv S.metricFn (x 1))) /
        (2 * S.metricFn (x 1)) ^ 2)) (x 1) := by
    convert (hf2.hasDerivAt.div (hf1.hasDerivAt.const_mul 2) h2f).neg using 1
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hd)]
  simp [christoffelDeriv]
  field_simp [hf]

private lemma christoffelDeriv_r_122 (S : StaticSphericalMetric) (x : Fin 4 → ℝ)
    (hf1 : DifferentiableAt ℝ S.metricFn (x 1)) :
    coordDeriv 1 (fun y => S.christoffel y 1 2 2) x = S.christoffelDeriv 1 x 1 2 2 := by
  have hfun : (fun s : ℝ => S.christoffel (Function.update x 1 s) 1 2 2)
      = fun s : ℝ => -(s * S.metricFn s) := by
    funext s
    simp [christoffel]
  have hd : HasDerivAt (fun s : ℝ => -(s * S.metricFn s))
      (-(1 * S.metricFn (x 1) + x 1 * deriv S.metricFn (x 1))) (x 1) := by
    convert ((hasDerivAt_id (x 1)).mul hf1.hasDerivAt).neg using 2 <;> simp
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hd)]
  simp [christoffelDeriv]
  ring

private lemma christoffelDeriv_r_133 (S : StaticSphericalMetric) (x : Fin 4 → ℝ)
    (hf1 : DifferentiableAt ℝ S.metricFn (x 1)) :
    coordDeriv 1 (fun y => S.christoffel y 1 3 3) x = S.christoffelDeriv 1 x 1 3 3 := by
  have hfun : (fun s : ℝ => S.christoffel (Function.update x 1 s) 1 3 3)
      = fun s : ℝ => -(s * (Real.sin (x 2) ^ 2 * S.metricFn s)) := by
    funext s
    simp [christoffel]
    ring
  have hd : HasDerivAt (fun s : ℝ => -(s * (Real.sin (x 2) ^ 2 * S.metricFn s)))
      (-(1 * (Real.sin (x 2) ^ 2 * S.metricFn (x 1))
        + x 1 * (Real.sin (x 2) ^ 2 * deriv S.metricFn (x 1)))) (x 1) := by
    convert ((hasDerivAt_id (x 1)).mul (hf1.hasDerivAt.const_mul (Real.sin (x 2) ^ 2))).neg
      using 2 <;> simp
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hd)]
  simp [christoffelDeriv]
  ring

private lemma christoffelDeriv_r_inv (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (k i j : Fin 4)
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

private lemma christoffelDeriv_theta_133 (S : StaticSphericalMetric) (x : Fin 4 → ℝ) :
    coordDeriv 2 (fun y => S.christoffel y 1 3 3) x = S.christoffelDeriv 2 x 1 3 3 := by
  have hfun : (fun s : ℝ => S.christoffel (Function.update x 2 s) 1 3 3)
      = fun s : ℝ => -(x 1 * Real.sin s ^ 2 * S.metricFn (x 1)) := by
    funext s
    simp [christoffel]
  have hsinSq : HasDerivAt (fun s : ℝ => Real.sin s ^ 2)
      (2 * Real.sin (x 2) * Real.cos (x 2)) (x 2) :=
    ((hasDerivAt_pow 2 (Real.sin (x 2))).comp (x 2)
      (Real.hasDerivAt_sin (x 2))).congr_deriv (by ring)
  have hd := ((hsinSq.const_mul (x 1)).mul_const (S.metricFn (x 1))).neg
  have hderiv : deriv (fun s : ℝ => -(x 1 * Real.sin s ^ 2 * S.metricFn (x 1))) (x 2)
      = -(x 1 * (2 * Real.sin (x 2) * Real.cos (x 2)) * S.metricFn (x 1)) := hd.deriv
  rw [coordDeriv, hfun, hderiv]
  simp [christoffelDeriv]

private lemma christoffelDeriv_theta_233 (S : StaticSphericalMetric) (x : Fin 4 → ℝ) :
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

private lemma christoffelDeriv_theta_323 (S : StaticSphericalMetric) (x : Fin 4 → ℝ)
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

private lemma christoffelDeriv_t_phi_eq (S : StaticSphericalMetric) (x : Fin 4 → ℝ)
    (μ k i j : Fin 4) (hμ : μ = 0 ∨ μ = 3) :
    coordDeriv μ (fun y => S.christoffel y k i j) x = S.christoffelDeriv μ x k i j := by
  rcases hμ with rfl | rfl
  · have hc : coordDeriv 0 (fun y => S.christoffel y k i j) x = 0 :=
      coordDeriv_const_slice 0 (S.christoffel x k i j) fun _ => by simp [christoffel]
    simp [hc, christoffelDeriv]
  · have hc : coordDeriv 3 (fun y => S.christoffel y k i j) x = 0 :=
      coordDeriv_const_slice 3 (S.christoffel x k i j) fun _ => by simp [christoffel]
    simp [hc, christoffelDeriv]

private lemma christoffelDeriv_theta_eq (S : StaticSphericalMetric) (x : Fin 4 → ℝ)
    (hsin : Real.sin (x 2) ≠ 0) (k i j : Fin 4) :
    coordDeriv 2 (fun y => S.christoffel y k i j) x = S.christoffelDeriv 2 x k i j := by
  fin_cases k <;>
    (fin_cases i <;> fin_cases j <;>
      first
      | exact christoffelDeriv_theta_133 S x
      | exact christoffelDeriv_theta_233 S x
      | exact christoffelDeriv_theta_323 S x hsin
      | simp [coordDeriv, christoffel, christoffelDeriv])

private lemma christoffelDeriv_r_eq (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.metricFn (x 1) ≠ 0) (hf1 : DifferentiableAt ℝ S.metricFn (x 1))
    (hf2 : DifferentiableAt ℝ (deriv S.metricFn) (x 1)) (k i j : Fin 4) :
    coordDeriv 1 (fun y => S.christoffel y k i j) x = S.christoffelDeriv 1 x k i j := by
  fin_cases k <;>
    (fin_cases i <;> fin_cases j <;>
      first
      | exact christoffelDeriv_r_001 S x hf hf1 hf2
      | exact christoffelDeriv_r_100 S x hf1 hf2
      | exact christoffelDeriv_r_111 S x hf hf1 hf2
      | exact christoffelDeriv_r_122 S x hf1
      | exact christoffelDeriv_r_133 S x hf1
      | exact christoffelDeriv_r_inv S x hr _ _ _ (by decide)
      | simp [coordDeriv, christoffel, christoffelDeriv])

/-- Complete identification of all 256 partial derivatives of the static spherical Christoffel
symbols with `StaticSphericalMetric.christoffelDeriv`. -/
lemma pd_christoffel_eq_deriv (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.metricFn (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (hf1 : DifferentiableAt ℝ S.metricFn (x 1))
    (hf2 : DifferentiableAt ℝ (deriv S.metricFn) (x 1)) (μ k i j : Fin 4) :
    coordDeriv μ (fun y => S.christoffel y k i j) x = S.christoffelDeriv μ x k i j := by
  fin_cases μ
  · exact christoffelDeriv_t_phi_eq S x 0 k i j (Or.inl rfl)
  · exact christoffelDeriv_r_eq S x hr hf hf1 hf2 k i j
  · exact christoffelDeriv_theta_eq S x hsin k i j
  · exact christoffelDeriv_t_phi_eq S x 3 k i j (Or.inr rfl)

end StaticSphericalMetric

end StaticSpherical

end GeneralRelativity
