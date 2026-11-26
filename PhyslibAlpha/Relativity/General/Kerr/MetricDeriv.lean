/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.General.Kerr.Basic
public import PhyslibAlpha.Relativity.Metrics.CoordinateMetric
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!

# Boyer–Lindquist Kerr metric partial derivatives

Analytical coordinate partial derivatives `KerrSpacetime.metricCoordDeriv` of the Boyer–Lindquist
metric along `(t, r, θ, φ)` and verification against `coordDeriv`.

## i. Overview

Because the Boyer–Lindquist Kerr metric is stationary (`∂_t g = 0`) and axisymmetric
(`∂_φ g = 0`), only its radial (`∂_r`) and polar (`∂_θ`) partial derivatives are non-zero. This
module defines the closed-form derivative table `KerrSpacetime.metricCoordDeriv`, differentiates
the auxiliary Boyer–Lindquist functions `Σ`, `Δ`, and `axialFactor`, and verifies all 64 partial
derivatives `coordDeriv μ (fun y => K.metric y i j) x = K.metricCoordDeriv μ x i j`.

## ii. Key results

- `KerrSpacetime.metricCoordDeriv` : closed-form Boyer–Lindquist metric partial derivatives.
- `KerrSpacetime.hasDerivAt_sigma_r`, `KerrSpacetime.hasDerivAt_sigma_theta`,
  `KerrSpacetime.hasDerivAt_delta_r` : derivatives of `Σ` and `Δ`.
- `KerrSpacetime.pd_metric_eq` : agreement of `coordDeriv` with `KerrSpacetime.metricCoordDeriv`
  across all 64 components.

## iii. Table of contents

- A. Partial derivatives of the Kerr metric

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 12 (Sec. 12.3). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 33.
  [ref: mtw_1973_gravitation]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 7
  (https://arxiv.org/pdf/gr-qc/9712019#page=187). [ref: Carroll1997]
* S. Chandrasekhar, *The Mathematical Theory of Black Holes* (1983), Ch. 6. [ref: Chandrasekhar1983]
-/

@[expose] public section

namespace GeneralRelativity

namespace Kerr

open Pipeline

namespace KerrSpacetime

/-!

## A. Partial derivatives of the Kerr metric

Differentiating the stationary, axisymmetric Boyer–Lindquist metric components isolates the `r`
and `θ` derivatives of `Σ`, `Δ`, and `axialFactor` from the Christoffel inverse-metric sum.

-/

/-- Analytical coordinate partial derivatives `∂_μ (K.metric · i j)` in Boyer–Lindquist coordinates
`x = (t, r, θ, φ)`. -/
noncomputable def metricCoordDeriv (K : KerrSpacetime) (μ : Fin 4) (x : Fin 4 → ℝ)
    (i j : Fin 4) : ℝ :=
  let r := x 1
  let c := Real.cos (x 2)
  let s := Real.sin (x 2)
  let sig := K.sigma r (x 2)
  let del := K.delta r
  let aval := K.axialFactor r (x 2)
  if μ = 1 then
    if i = 0 ∧ j = 0 then -(2 * K.M * (r ^ 2 - K.a ^ 2 * c ^ 2) / sig ^ 2)
    else if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then
      2 * K.M * K.a * s ^ 2 * (r ^ 2 - K.a ^ 2 * c ^ 2) / sig ^ 2
    else if i = 1 ∧ j = 1 then (2 * r * del - sig * (2 * r - 2 * K.M)) / del ^ 2
    else if i = 2 ∧ j = 2 then 2 * r
    else if i = 3 ∧ j = 3 then
      s ^ 2 * ((4 * r * (r ^ 2 + K.a ^ 2) - K.a ^ 2 * (2 * r - 2 * K.M) * s ^ 2) * sig
        - 2 * r * aval) / sig ^ 2
    else 0
  else if μ = 2 then
    if i = 0 ∧ j = 0 then 4 * K.M * K.a ^ 2 * r * c * s / sig ^ 2
    else if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then
      -4 * K.M * K.a * r * s * c * (r ^ 2 + K.a ^ 2) / sig ^ 2
    else if i = 1 ∧ j = 1 then -2 * K.a ^ 2 * c * s / del
    else if i = 2 ∧ j = 2 then -2 * K.a ^ 2 * c * s
    else if i = 3 ∧ j = 3 then
      ((-2 * K.a ^ 2 * del * s ^ 3 * c + 2 * aval * s * c) * sig
        + 2 * K.a ^ 2 * c * s ^ 3 * aval) / sig ^ 2
    else 0
  else 0

/-- Radial derivative of Boyer–Lindquist `Σ = r² + a² cos² θ`: `∂_r Σ = 2 r`. -/
lemma hasDerivAt_sigma_r (K : KerrSpacetime) (r θ : ℝ) :
    HasDerivAt (fun s => K.sigma s θ) (2 * r) r :=
  ((hasDerivAt_pow 2 r).add_const (K.a ^ 2 * Real.cos θ ^ 2)).congr_deriv (by ring)

/-- Angular derivative of Boyer–Lindquist `Σ = r² + a² cos² θ`:
`∂_θ Σ = -2 a² cos θ sin θ`. -/
lemma hasDerivAt_sigma_theta (K : KerrSpacetime) (r θ : ℝ) :
    HasDerivAt (fun t => K.sigma r t) (-2 * K.a ^ 2 * Real.cos θ * Real.sin θ) θ :=
  ((((hasDerivAt_pow 2 (Real.cos θ)).comp θ (Real.hasDerivAt_cos θ)).const_mul
    (K.a ^ 2)).const_add (r ^ 2)).congr_deriv (by ring)

/-- Radial derivative of Boyer–Lindquist `Δ = r² - 2 M r + a²`: `∂_r Δ = 2 r - 2 M`. -/
lemma hasDerivAt_delta_r (K : KerrSpacetime) (r : ℝ) :
    HasDerivAt K.delta (2 * r - 2 * K.M) r := by
  have h1 := ((hasDerivAt_pow 2 r).fun_sub
    ((hasDerivAt_const r (2 * K.M)).fun_mul (hasDerivAt_id r))).fun_add
      (hasDerivAt_const r (K.a ^ 2))
  exact h1.congr_deriv (by ring)

private lemma hasDerivAt_axialFactor_r (K : KerrSpacetime) (r θ : ℝ) :
    HasDerivAt (fun s => K.axialFactor s θ)
      (4 * r * (r ^ 2 + K.a ^ 2) - K.a ^ 2 * (2 * r - 2 * K.M) * Real.sin θ ^ 2) r := by
  have h1 : HasDerivAt (fun s : ℝ => (s ^ 2 + K.a ^ 2) ^ 2)
      (2 * (r ^ 2 + K.a ^ 2) * (2 * r)) r :=
    (((hasDerivAt_pow 2 r).add_const (K.a ^ 2)).pow 2).congr_deriv (by ring)
  have h2 : HasDerivAt (fun s : ℝ => K.a ^ 2 * K.delta s * Real.sin θ ^ 2)
      (K.a ^ 2 * (2 * r - 2 * K.M) * Real.sin θ ^ 2) r :=
    (((K.hasDerivAt_delta_r r).const_mul (K.a ^ 2)).mul_const (Real.sin θ ^ 2)).congr_deriv
      (by ring)
  exact (h1.fun_sub h2).congr_deriv (by ring)

private lemma hasDerivAt_axialFactor_theta (K : KerrSpacetime) (r θ : ℝ) :
    HasDerivAt (fun t => K.axialFactor r t)
      (-2 * K.a ^ 2 * K.delta r * Real.sin θ * Real.cos θ) θ :=
  ((hasDerivAt_const θ ((r ^ 2 + K.a ^ 2) ^ 2)).fun_sub
    (((hasDerivAt_pow 2 (Real.sin θ)).comp θ (Real.hasDerivAt_sin θ)).const_mul
      (K.a ^ 2 * K.delta r))).congr_deriv (by ring)

private lemma metricDeriv_r_00 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) :
    coordDeriv 1 (fun y => K.metric y 0 0) x = K.metricCoordDeriv 1 x 0 0 := by
  have hfun : (fun s => K.metric (Function.update x 1 s) 0 0)
      = fun s => -(1 - 2 * K.M * s / K.sigma s (x 2)) := by funext s; simp [metric]
  have hm : HasDerivAt (fun s : ℝ => 2 * K.M * s) (2 * K.M) (x 1) :=
    ((hasDerivAt_const (x 1) (2 * K.M)).fun_mul (hasDerivAt_id (x 1))).congr_deriv (by ring)
  have hq := hm.fun_div (K.hasDerivAt_sigma_r (x 1) (x 2)) hsig
  have hd := ((hasDerivAt_const (x 1) 1).fun_sub hq).fun_neg
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hd)]
  simp only [metricCoordDeriv, sigma, Fin.isValue, and_self, ↓reduceIte]
  field_simp [hsig]; ring

private lemma metricDeriv_r_03 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) :
    coordDeriv 1 (fun y => K.metric y 0 3) x = K.metricCoordDeriv 1 x 0 3 := by
  have hfun : (fun s => K.metric (Function.update x 1 s) 0 3)
      = fun s => -(2 * K.M * K.a * s * Real.sin (x 2) ^ 2 / K.sigma s (x 2)) := by
    funext s; simp [metric]
  have hm : HasDerivAt (fun s : ℝ => 2 * K.M * K.a * s * Real.sin (x 2) ^ 2)
      (2 * K.M * K.a * Real.sin (x 2) ^ 2) (x 1) :=
    ((((hasDerivAt_const (x 1) (2 * K.M * K.a)).fun_mul (hasDerivAt_id (x 1))).mul_const
      (Real.sin (x 2) ^ 2))).congr_deriv (by ring)
  have hq := (hm.fun_div (K.hasDerivAt_sigma_r (x 1) (x 2)) hsig).fun_neg
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hq)]
  simp only [metricCoordDeriv, sigma, Fin.isValue, Fin.reduceEq, and_false, and_true, or_false,
    ↓reduceIte]
  field_simp [hsig]; ring

private lemma metricDeriv_r_11 (K : KerrSpacetime) (x : Fin 4 → ℝ) (hdel : K.delta (x 1) ≠ 0) :
    coordDeriv 1 (fun y => K.metric y 1 1) x = K.metricCoordDeriv 1 x 1 1 := by
  have hfun : (fun s => K.metric (Function.update x 1 s) 1 1)
      = fun s => K.sigma s (x 2) / K.delta s := by funext s; simp [metric]
  have hd := (K.hasDerivAt_sigma_r (x 1) (x 2)).fun_div (K.hasDerivAt_delta_r (x 1)) hdel
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hd)]
  simp [metricCoordDeriv]

private lemma metricDeriv_r_22 (K : KerrSpacetime) (x : Fin 4 → ℝ) :
    coordDeriv 1 (fun y => K.metric y 2 2) x = K.metricCoordDeriv 1 x 2 2 := by
  have hfun : (fun s => K.metric (Function.update x 1 s) 2 2)
      = fun s => K.sigma s (x 2) := by funext s; simp [metric]
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ (K.hasDerivAt_sigma_r (x 1) (x 2)))]
  simp [metricCoordDeriv]

private lemma metricDeriv_r_33 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) :
    coordDeriv 1 (fun y => K.metric y 3 3) x = K.metricCoordDeriv 1 x 3 3 := by
  have hfun : (fun s => K.metric (Function.update x 1 s) 3 3)
      = fun s => K.axialFactor s (x 2) * Real.sin (x 2) ^ 2 / K.sigma s (x 2) := by
    funext s; simp [metric]
  have hnum := (K.hasDerivAt_axialFactor_r (x 1) (x 2)).mul_const (Real.sin (x 2) ^ 2)
  have hq := hnum.fun_div (K.hasDerivAt_sigma_r (x 1) (x 2)) hsig
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hq)]
  have hval : K.metricCoordDeriv 1 x 3 3 = Real.sin (x 2) ^ 2 *
      ((4 * x 1 * (x 1 ^ 2 + K.a ^ 2) - K.a ^ 2 * (2 * x 1 - 2 * K.M) * Real.sin (x 2) ^ 2)
          * K.sigma (x 1) (x 2) - 2 * x 1 * K.axialFactor (x 1) (x 2))
        / K.sigma (x 1) (x 2) ^ 2 := by
    simp [metricCoordDeriv]
  rw [hval]
  ring

private lemma metricDeriv_r_30 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) :
    coordDeriv 1 (fun y => K.metric y 3 0) x = K.metricCoordDeriv 1 x 3 0 := by
  have hs : (fun y => K.metric y 3 0) = fun y => K.metric y 0 3 := by
    funext y; exact (K.metric_symm y).apply 0 3
  rw [hs, metricDeriv_r_03 K x hsig]
  simp [metricCoordDeriv]

private lemma metricDeriv_r (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) (hdel : K.delta (x 1) ≠ 0) (i j : Fin 4) :
    coordDeriv 1 (fun y => K.metric y i j) x = K.metricCoordDeriv 1 x i j := by
  fin_cases i <;> fin_cases j
  · exact metricDeriv_r_00 K x hsig
  · simp [coordDeriv, metric, metricCoordDeriv]
  · simp [coordDeriv, metric, metricCoordDeriv]
  · exact metricDeriv_r_03 K x hsig
  · simp [coordDeriv, metric, metricCoordDeriv]
  · exact metricDeriv_r_11 K x hdel
  · simp [coordDeriv, metric, metricCoordDeriv]
  · simp [coordDeriv, metric, metricCoordDeriv]
  · simp [coordDeriv, metric, metricCoordDeriv]
  · simp [coordDeriv, metric, metricCoordDeriv]
  · exact metricDeriv_r_22 K x
  · simp [coordDeriv, metric, metricCoordDeriv]
  · exact metricDeriv_r_30 K x hsig
  · simp [coordDeriv, metric, metricCoordDeriv]
  · simp [coordDeriv, metric, metricCoordDeriv]
  · exact metricDeriv_r_33 K x hsig

private lemma metricDeriv_theta_00 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) :
    coordDeriv 2 (fun y => K.metric y 0 0) x = K.metricCoordDeriv 2 x 0 0 := by
  have hfun : (fun t => K.metric (Function.update x 2 t) 0 0)
      = fun t => -(1 - 2 * K.M * x 1 / K.sigma (x 1) t) := by funext t; simp [metric]
  have hq := (hasDerivAt_const (x 2) (2 * K.M * x 1)).fun_div
    (K.hasDerivAt_sigma_theta (x 1) (x 2)) hsig
  have hd := ((hasDerivAt_const (x 2) 1).fun_sub hq).fun_neg
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hd)]
  simp only [metricCoordDeriv, Fin.isValue, Fin.reduceEq, and_self, ↓reduceIte]
  ring

private lemma metricDeriv_theta_03 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) :
    coordDeriv 2 (fun y => K.metric y 0 3) x = K.metricCoordDeriv 2 x 0 3 := by
  have hfun : (fun t => K.metric (Function.update x 2 t) 0 3)
      = fun t => -(2 * K.M * K.a * x 1 * Real.sin t ^ 2 / K.sigma (x 1) t) := by
    funext t; simp [metric]
  have hsinSq : HasDerivAt (fun t : ℝ => Real.sin t ^ 2)
      (2 * Real.sin (x 2) * Real.cos (x 2)) (x 2) :=
    ((hasDerivAt_pow 2 (Real.sin (x 2))).comp (x 2)
      (Real.hasDerivAt_sin (x 2))).congr_deriv (by ring)
  have hm := hsinSq.const_mul (2 * K.M * K.a * x 1)
  have hq := (hm.fun_div (K.hasDerivAt_sigma_theta (x 1) (x 2)) hsig).fun_neg
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hq)]
  have hval : K.metricCoordDeriv 2 x 0 3 =
      -4 * K.M * K.a * x 1 * Real.sin (x 2) * Real.cos (x 2) * (x 1 ^ 2 + K.a ^ 2)
        / K.sigma (x 1) (x 2) ^ 2 := by
    simp [metricCoordDeriv]
  rw [hval]
  field_simp [hsig]
  simp only [sigma, Real.sin_sq (x 2)]
  ring

private lemma metricDeriv_theta_11 (K : KerrSpacetime) (x : Fin 4 → ℝ) :
    coordDeriv 2 (fun y => K.metric y 1 1) x = K.metricCoordDeriv 2 x 1 1 := by
  have hfun : (fun t => K.metric (Function.update x 2 t) 1 1)
      = fun t => K.sigma (x 1) t / K.delta (x 1) := by funext t; simp [metric]
  have hd := (K.hasDerivAt_sigma_theta (x 1) (x 2)).div_const (K.delta (x 1))
  have hval : K.metricCoordDeriv 2 x 1 1 =
      -2 * K.a ^ 2 * Real.cos (x 2) * Real.sin (x 2) / K.delta (x 1) := by
    simp [metricCoordDeriv]
  rw [coordDeriv, hfun, hd.deriv, hval]

private lemma metricDeriv_theta_22 (K : KerrSpacetime) (x : Fin 4 → ℝ) :
    coordDeriv 2 (fun y => K.metric y 2 2) x = K.metricCoordDeriv 2 x 2 2 := by
  have hfun : (fun t => K.metric (Function.update x 2 t) 2 2)
      = fun t => K.sigma (x 1) t := by funext t; simp [metric]
  have hval : K.metricCoordDeriv 2 x 2 2 = -2 * K.a ^ 2 * Real.cos (x 2) * Real.sin (x 2) := by
    simp [metricCoordDeriv]
  rw [coordDeriv, hfun, (K.hasDerivAt_sigma_theta (x 1) (x 2)).deriv, hval]

private lemma metricDeriv_theta_33 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) :
    coordDeriv 2 (fun y => K.metric y 3 3) x = K.metricCoordDeriv 2 x 3 3 := by
  have hfun : (fun t => K.metric (Function.update x 2 t) 3 3)
      = fun t => K.axialFactor (x 1) t * Real.sin t ^ 2 / K.sigma (x 1) t := by
    funext t; simp [metric]
  have hsinSq : HasDerivAt (fun t : ℝ => Real.sin t ^ 2)
      (2 * Real.sin (x 2) * Real.cos (x 2)) (x 2) :=
    ((hasDerivAt_pow 2 (Real.sin (x 2))).comp (x 2)
      (Real.hasDerivAt_sin (x 2))).congr_deriv (by ring)
  have hnum := (K.hasDerivAt_axialFactor_theta (x 1) (x 2)).fun_mul hsinSq
  have hq := hnum.fun_div (K.hasDerivAt_sigma_theta (x 1) (x 2)) hsig
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hq)]
  have hval : K.metricCoordDeriv 2 x 3 3 =
      ((-2 * K.a ^ 2 * K.delta (x 1) * Real.sin (x 2) ^ 3 * Real.cos (x 2)
            + 2 * K.axialFactor (x 1) (x 2) * Real.sin (x 2) * Real.cos (x 2))
          * K.sigma (x 1) (x 2)
        + 2 * K.a ^ 2 * Real.cos (x 2) * Real.sin (x 2) ^ 3 * K.axialFactor (x 1) (x 2))
      / K.sigma (x 1) (x 2) ^ 2 := by
    simp [metricCoordDeriv]
  rw [hval]
  ring

private lemma metricDeriv_theta_30 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) :
    coordDeriv 2 (fun y => K.metric y 3 0) x = K.metricCoordDeriv 2 x 3 0 := by
  have hs : (fun y => K.metric y 3 0) = fun y => K.metric y 0 3 := by
    funext y; exact (K.metric_symm y).apply 0 3
  rw [hs, metricDeriv_theta_03 K x hsig]
  simp [metricCoordDeriv]

private lemma metricDeriv_theta (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) (i j : Fin 4) :
    coordDeriv 2 (fun y => K.metric y i j) x = K.metricCoordDeriv 2 x i j := by
  fin_cases i <;> fin_cases j
  · exact metricDeriv_theta_00 K x hsig
  · simp [coordDeriv, metric, metricCoordDeriv]
  · simp [coordDeriv, metric, metricCoordDeriv]
  · exact metricDeriv_theta_03 K x hsig
  · simp [coordDeriv, metric, metricCoordDeriv]
  · exact metricDeriv_theta_11 K x
  · simp [coordDeriv, metric, metricCoordDeriv]
  · simp [coordDeriv, metric, metricCoordDeriv]
  · simp [coordDeriv, metric, metricCoordDeriv]
  · simp [coordDeriv, metric, metricCoordDeriv]
  · exact metricDeriv_theta_22 K x
  · simp [coordDeriv, metric, metricCoordDeriv]
  · exact metricDeriv_theta_30 K x hsig
  · simp [coordDeriv, metric, metricCoordDeriv]
  · simp [coordDeriv, metric, metricCoordDeriv]
  · exact metricDeriv_theta_33 K x hsig

/-- Complete identification of all 64 partial derivatives of `K.metric` with
`K.metricCoordDeriv`. -/
lemma pd_metric_eq (K : KerrSpacetime) (μ : Fin 4) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) (hdel : K.delta (x 1) ≠ 0) (i j : Fin 4) :
    coordDeriv μ (fun y => K.metric y i j) x = K.metricCoordDeriv μ x i j := by
  fin_cases μ
  · simp [coordDeriv, metric, metricCoordDeriv, sigma, delta, axialFactor]
  · exact metricDeriv_r K x hsig hdel i j
  · exact metricDeriv_theta K x hsig i j
  · simp [coordDeriv, metric, metricCoordDeriv, sigma, delta, axialFactor]

end KerrSpacetime

end Kerr

end GeneralRelativity
