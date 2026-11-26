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
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!

# Boyer–Lindquist Kerr metric partial derivatives and Christoffel symbols

Analytical partial derivatives of `KerrSpacetime.metric`, all 20 independent Christoffel connection
coefficients `KerrSpacetime.christoffel`, their agreement with `Pipeline.christoffel`, and the
contracted trace `KerrSpacetime.christoffelTrace`.

## i. Overview

This module evaluates the Boyer–Lindquist metric partial derivatives `KerrSpacetime.metricD` (`∂_r`
and `∂_θ`, with `∂_t = ∂_φ = 0`), proves `pd_metric_eq`, defines the analytical closed-form
Christoffel symbol table `KerrSpacetime.christoffel` (20 non-zero symmetric components) and its
contraction trace `KerrSpacetime.christoffelTrace`
(`tr_r = 2 r / Σ`, `tr_θ = cot θ - 2 a² cos θ sin θ / Σ`), and establishes that
`Pipeline.christoffel K.metric K.metricInv` equals `K.christoffel` everywhere on regular
coordinates (`Σ ≠ 0`, `Δ ≠ 0`, `sin θ ≠ 0`) and on a neighborhood thereof.

## ii. Key results

- `KerrSpacetime.metricD`, `KerrSpacetime.pd_metric_eq` : partial derivatives of the Kerr metric.
- `KerrSpacetime.christoffel`, `KerrSpacetime.christoffel_symm` : explicit Christoffel symbols of
  Boyer–Lindquist Kerr spacetime.
- `KerrSpacetime.christoffel_eq`, `KerrSpacetime.eventually_christoffel_eq` : agreement with
  `Pipeline.christoffel`.
- `KerrSpacetime.christoffelTrace`, `KerrSpacetime.sum_christoffel_trace` : contracted Christoffel
  trace `∑ ρ, Γ^ρ_{ρ μ}`.

## iii. Table of contents

- A. Partial derivatives of the Kerr metric
- B. Explicit Boyer–Lindquist Christoffel symbols
- C. Agreement with the coordinate pipeline and trace identity

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

-/

/-- Analytical coordinate partial derivatives `∂_μ (K.metric · i j)` in Boyer–Lindquist coordinates
`x = (t, r, θ, φ)`. -/
noncomputable def metricD (K : KerrSpacetime) (μ : Fin 4) (x : Fin 4 → ℝ) (i j : Fin 4) : ℝ :=
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
lemma hasDerivAt_sigma_th (K : KerrSpacetime) (r θ : ℝ) :
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

private lemma hasDerivAt_axialFactor_th (K : KerrSpacetime) (r θ : ℝ) :
    HasDerivAt (fun t => K.axialFactor r t)
      (-2 * K.a ^ 2 * K.delta r * Real.sin θ * Real.cos θ) θ :=
  ((hasDerivAt_const θ ((r ^ 2 + K.a ^ 2) ^ 2)).fun_sub
    (((hasDerivAt_pow 2 (Real.sin θ)).comp θ (Real.hasDerivAt_sin θ)).const_mul
      (K.a ^ 2 * K.delta r))).congr_deriv (by ring)

private lemma pd_metric_1_00 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) :
    coordDeriv 1 (fun y => K.metric y 0 0) x = K.metricD 1 x 0 0 := by
  have hfun : (fun s => K.metric (Function.update x 1 s) 0 0)
      = fun s => -(1 - 2 * K.M * s / K.sigma s (x 2)) := by funext s; simp [metric]
  have hm : HasDerivAt (fun s : ℝ => 2 * K.M * s) (2 * K.M) (x 1) :=
    ((hasDerivAt_const (x 1) (2 * K.M)).fun_mul (hasDerivAt_id (x 1))).congr_deriv (by ring)
  have hq := hm.fun_div (K.hasDerivAt_sigma_r (x 1) (x 2)) hsig
  have hd := ((hasDerivAt_const (x 1) 1).fun_sub hq).fun_neg
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hd)]
  simp only [metricD, sigma, Fin.isValue, and_self, ↓reduceIte]
  field_simp [hsig]; ring

private lemma pd_metric_1_03 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) :
    coordDeriv 1 (fun y => K.metric y 0 3) x = K.metricD 1 x 0 3 := by
  have hfun : (fun s => K.metric (Function.update x 1 s) 0 3)
      = fun s => -(2 * K.M * K.a * s * Real.sin (x 2) ^ 2 / K.sigma s (x 2)) := by
    funext s; simp [metric]
  have hm : HasDerivAt (fun s : ℝ => 2 * K.M * K.a * s * Real.sin (x 2) ^ 2)
      (2 * K.M * K.a * Real.sin (x 2) ^ 2) (x 1) :=
    ((((hasDerivAt_const (x 1) (2 * K.M * K.a)).fun_mul (hasDerivAt_id (x 1))).mul_const
      (Real.sin (x 2) ^ 2))).congr_deriv (by ring)
  have hq := (hm.fun_div (K.hasDerivAt_sigma_r (x 1) (x 2)) hsig).fun_neg
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hq)]
  simp only [metricD, sigma, Fin.isValue, Fin.reduceEq, and_false, and_true, or_false,
    ↓reduceIte]
  field_simp [hsig]; ring

private lemma pd_metric_1_11 (K : KerrSpacetime) (x : Fin 4 → ℝ) (hdel : K.delta (x 1) ≠ 0) :
    coordDeriv 1 (fun y => K.metric y 1 1) x = K.metricD 1 x 1 1 := by
  have hfun : (fun s => K.metric (Function.update x 1 s) 1 1)
      = fun s => K.sigma s (x 2) / K.delta s := by funext s; simp [metric]
  have hd := (K.hasDerivAt_sigma_r (x 1) (x 2)).fun_div (K.hasDerivAt_delta_r (x 1)) hdel
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hd)]
  simp [metricD]

private lemma pd_metric_1_22 (K : KerrSpacetime) (x : Fin 4 → ℝ) :
    coordDeriv 1 (fun y => K.metric y 2 2) x = K.metricD 1 x 2 2 := by
  have hfun : (fun s => K.metric (Function.update x 1 s) 2 2)
      = fun s => K.sigma s (x 2) := by funext s; simp [metric]
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ (K.hasDerivAt_sigma_r (x 1) (x 2)))]
  simp [metricD]

private lemma pd_metric_1_33 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) :
    coordDeriv 1 (fun y => K.metric y 3 3) x = K.metricD 1 x 3 3 := by
  have hfun : (fun s => K.metric (Function.update x 1 s) 3 3)
      = fun s => K.axialFactor s (x 2) * Real.sin (x 2) ^ 2 / K.sigma s (x 2) := by
    funext s; simp [metric]
  have hnum := (K.hasDerivAt_axialFactor_r (x 1) (x 2)).mul_const (Real.sin (x 2) ^ 2)
  have hq := hnum.fun_div (K.hasDerivAt_sigma_r (x 1) (x 2)) hsig
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hq)]
  have hval : K.metricD 1 x 3 3 = Real.sin (x 2) ^ 2 *
      ((4 * x 1 * (x 1 ^ 2 + K.a ^ 2) - K.a ^ 2 * (2 * x 1 - 2 * K.M) * Real.sin (x 2) ^ 2)
          * K.sigma (x 1) (x 2) - 2 * x 1 * K.axialFactor (x 1) (x 2))
        / K.sigma (x 1) (x 2) ^ 2 := by
    simp [metricD]
  rw [hval]
  ring

private lemma pd_metric_1_30 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) :
    coordDeriv 1 (fun y => K.metric y 3 0) x = K.metricD 1 x 3 0 := by
  have hs : (fun y => K.metric y 3 0) = fun y => K.metric y 0 3 := by
    funext y; exact (K.metric_symm y).apply 0 3
  rw [hs, pd_metric_1_03 K x hsig]
  simp [metricD]

private lemma pd_metric_1 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) (hdel : K.delta (x 1) ≠ 0) (i j : Fin 4) :
    coordDeriv 1 (fun y => K.metric y i j) x = K.metricD 1 x i j := by
  fin_cases i <;> fin_cases j
  · exact pd_metric_1_00 K x hsig
  · simp [coordDeriv, metric, metricD]
  · simp [coordDeriv, metric, metricD]
  · exact pd_metric_1_03 K x hsig
  · simp [coordDeriv, metric, metricD]
  · exact pd_metric_1_11 K x hdel
  · simp [coordDeriv, metric, metricD]
  · simp [coordDeriv, metric, metricD]
  · simp [coordDeriv, metric, metricD]
  · simp [coordDeriv, metric, metricD]
  · exact pd_metric_1_22 K x
  · simp [coordDeriv, metric, metricD]
  · exact pd_metric_1_30 K x hsig
  · simp [coordDeriv, metric, metricD]
  · simp [coordDeriv, metric, metricD]
  · exact pd_metric_1_33 K x hsig

private lemma pd_metric_2_00 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) :
    coordDeriv 2 (fun y => K.metric y 0 0) x = K.metricD 2 x 0 0 := by
  have hfun : (fun t => K.metric (Function.update x 2 t) 0 0)
      = fun t => -(1 - 2 * K.M * x 1 / K.sigma (x 1) t) := by funext t; simp [metric]
  have hq := (hasDerivAt_const (x 2) (2 * K.M * x 1)).fun_div
    (K.hasDerivAt_sigma_th (x 1) (x 2)) hsig
  have hd := ((hasDerivAt_const (x 2) 1).fun_sub hq).fun_neg
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hd)]
  simp only [metricD, Fin.isValue, Fin.reduceEq, and_self, ↓reduceIte]
  ring

private lemma pd_metric_2_03 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) :
    coordDeriv 2 (fun y => K.metric y 0 3) x = K.metricD 2 x 0 3 := by
  have hfun : (fun t => K.metric (Function.update x 2 t) 0 3)
      = fun t => -(2 * K.M * K.a * x 1 * Real.sin t ^ 2 / K.sigma (x 1) t) := by
    funext t; simp [metric]
  have hsinSq : HasDerivAt (fun t : ℝ => Real.sin t ^ 2)
      (2 * Real.sin (x 2) * Real.cos (x 2)) (x 2) :=
    ((hasDerivAt_pow 2 (Real.sin (x 2))).comp (x 2)
      (Real.hasDerivAt_sin (x 2))).congr_deriv (by ring)
  have hm := hsinSq.const_mul (2 * K.M * K.a * x 1)
  have hq := (hm.fun_div (K.hasDerivAt_sigma_th (x 1) (x 2)) hsig).fun_neg
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hq)]
  have hval : K.metricD 2 x 0 3 =
      -4 * K.M * K.a * x 1 * Real.sin (x 2) * Real.cos (x 2) * (x 1 ^ 2 + K.a ^ 2)
        / K.sigma (x 1) (x 2) ^ 2 := by
    simp [metricD]
  rw [hval]
  field_simp [hsig]
  simp only [sigma, Real.sin_sq (x 2)]
  ring

private lemma pd_metric_2_11 (K : KerrSpacetime) (x : Fin 4 → ℝ) :
    coordDeriv 2 (fun y => K.metric y 1 1) x = K.metricD 2 x 1 1 := by
  have hfun : (fun t => K.metric (Function.update x 2 t) 1 1)
      = fun t => K.sigma (x 1) t / K.delta (x 1) := by funext t; simp [metric]
  have hd := (K.hasDerivAt_sigma_th (x 1) (x 2)).div_const (K.delta (x 1))
  have hval : K.metricD 2 x 1 1 =
      -2 * K.a ^ 2 * Real.cos (x 2) * Real.sin (x 2) / K.delta (x 1) := by
    simp [metricD]
  rw [coordDeriv, hfun, hd.deriv, hval]

private lemma pd_metric_2_22 (K : KerrSpacetime) (x : Fin 4 → ℝ) :
    coordDeriv 2 (fun y => K.metric y 2 2) x = K.metricD 2 x 2 2 := by
  have hfun : (fun t => K.metric (Function.update x 2 t) 2 2)
      = fun t => K.sigma (x 1) t := by funext t; simp [metric]
  have hval : K.metricD 2 x 2 2 = -2 * K.a ^ 2 * Real.cos (x 2) * Real.sin (x 2) := by
    simp [metricD]
  rw [coordDeriv, hfun, (K.hasDerivAt_sigma_th (x 1) (x 2)).deriv, hval]

private lemma pd_metric_2_33 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) :
    coordDeriv 2 (fun y => K.metric y 3 3) x = K.metricD 2 x 3 3 := by
  have hfun : (fun t => K.metric (Function.update x 2 t) 3 3)
      = fun t => K.axialFactor (x 1) t * Real.sin t ^ 2 / K.sigma (x 1) t := by
    funext t; simp [metric]
  have hsinSq : HasDerivAt (fun t : ℝ => Real.sin t ^ 2)
      (2 * Real.sin (x 2) * Real.cos (x 2)) (x 2) :=
    ((hasDerivAt_pow 2 (Real.sin (x 2))).comp (x 2)
      (Real.hasDerivAt_sin (x 2))).congr_deriv (by ring)
  have hnum := (K.hasDerivAt_axialFactor_th (x 1) (x 2)).fun_mul hsinSq
  have hq := hnum.fun_div (K.hasDerivAt_sigma_th (x 1) (x 2)) hsig
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hq)]
  have hval : K.metricD 2 x 3 3 =
      ((-2 * K.a ^ 2 * K.delta (x 1) * Real.sin (x 2) ^ 3 * Real.cos (x 2)
            + 2 * K.axialFactor (x 1) (x 2) * Real.sin (x 2) * Real.cos (x 2))
          * K.sigma (x 1) (x 2)
        + 2 * K.a ^ 2 * Real.cos (x 2) * Real.sin (x 2) ^ 3 * K.axialFactor (x 1) (x 2))
      / K.sigma (x 1) (x 2) ^ 2 := by
    simp [metricD]
  rw [hval]
  ring

private lemma pd_metric_2_30 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) :
    coordDeriv 2 (fun y => K.metric y 3 0) x = K.metricD 2 x 3 0 := by
  have hs : (fun y => K.metric y 3 0) = fun y => K.metric y 0 3 := by
    funext y; exact (K.metric_symm y).apply 0 3
  rw [hs, pd_metric_2_03 K x hsig]
  simp [metricD]

private lemma pd_metric_2 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) (i j : Fin 4) :
    coordDeriv 2 (fun y => K.metric y i j) x = K.metricD 2 x i j := by
  fin_cases i <;> fin_cases j
  · exact pd_metric_2_00 K x hsig
  · simp [coordDeriv, metric, metricD]
  · simp [coordDeriv, metric, metricD]
  · exact pd_metric_2_03 K x hsig
  · simp [coordDeriv, metric, metricD]
  · exact pd_metric_2_11 K x
  · simp [coordDeriv, metric, metricD]
  · simp [coordDeriv, metric, metricD]
  · simp [coordDeriv, metric, metricD]
  · simp [coordDeriv, metric, metricD]
  · exact pd_metric_2_22 K x
  · simp [coordDeriv, metric, metricD]
  · exact pd_metric_2_30 K x hsig
  · simp [coordDeriv, metric, metricD]
  · simp [coordDeriv, metric, metricD]
  · exact pd_metric_2_33 K x hsig

/-- Complete identification of all 64 partial derivatives of `K.metric` with `K.metricD`. -/
lemma pd_metric_eq (K : KerrSpacetime) (μ : Fin 4) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) (hdel : K.delta (x 1) ≠ 0) (i j : Fin 4) :
    coordDeriv μ (fun y => K.metric y i j) x = K.metricD μ x i j := by
  fin_cases μ
  · simp [coordDeriv, metric, metricD, sigma, delta, axialFactor]
  · exact pd_metric_1 K x hsig hdel i j
  · exact pd_metric_2 K x hsig i j
  · simp [coordDeriv, metric, metricD, sigma, delta, axialFactor]

/-!

## B. Explicit Boyer–Lindquist Christoffel symbols

-/

-- Factored out from `Pipeline.christoffel` so rational derivative reductions remain tractable.
/-- Closed-form Levi-Civita Christoffel symbols `Γ^k_{ij}` of the Boyer–Lindquist Kerr metric. -/
noncomputable def christoffel (K : KerrSpacetime) (x : Fin 4 → ℝ) (k i j : Fin 4) : ℝ :=
  let r := x 1
  let c := Real.cos (x 2)
  let s := Real.sin (x 2)
  let sig := K.sigma r (x 2)
  let del := K.delta r
  if k = 0 then
    if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then
      K.M * (K.a ^ 2 + r ^ 2) * (r ^ 2 - K.a ^ 2 * c ^ 2) / (sig ^ 2 * del)
    else if (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) then
      -2 * K.M * K.a ^ 2 * c * r * s / sig ^ 2
    else if (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) then
      -K.M * K.a * s ^ 2
          * (-K.a ^ 4 * c ^ 2 + K.a ^ 2 * c ^ 2 * r ^ 2 + K.a ^ 2 * r ^ 2 + 3 * r ^ 4)
        / (sig ^ 2 * del)
    else if (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) then
      2 * K.M * K.a ^ 3 * c * r * s ^ 3 / sig ^ 2
    else 0
  else if k = 1 then
    if i = 0 ∧ j = 0 then K.M * (r ^ 2 - K.a ^ 2 * c ^ 2) * del / sig ^ 3
    else if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then
      -K.M * K.a * s ^ 2 * (r ^ 2 - K.a ^ 2 * c ^ 2) * del / sig ^ 3
    else if i = 1 ∧ j = 1 then
      -(-K.M * K.a ^ 2 * c ^ 2 + K.M * r ^ 2 + K.a ^ 2 * c ^ 2 * r - K.a ^ 2 * r) / (sig * del)
    else if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then -K.a ^ 2 * c * s / sig
    else if i = 2 ∧ j = 2 then -r * del / sig
    else if i = 3 ∧ j = 3 then
      -s ^ 2 * del * (-K.M * K.a ^ 4 * c ^ 4 + K.M * K.a ^ 4 * c ^ 2
        + K.M * K.a ^ 2 * c ^ 2 * r ^ 2 - K.M * K.a ^ 2 * r ^ 2 + K.a ^ 4 * c ^ 4 * r
        + 2 * K.a ^ 2 * c ^ 2 * r ^ 3 + r ^ 5) / sig ^ 3
    else 0
  else if k = 2 then
    if i = 0 ∧ j = 0 then -2 * K.M * K.a ^ 2 * c * r * s / sig ^ 3
    else if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then
      2 * K.M * K.a * c * r * s * (K.a ^ 2 + r ^ 2) / sig ^ 3
    else if i = 1 ∧ j = 1 then K.a ^ 2 * c * s / (sig * del)
    else if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then r / sig
    else if i = 2 ∧ j = 2 then -K.a ^ 2 * c * s / sig
    else if i = 3 ∧ j = 3 then
      -c * s * (-2 * K.M * K.a ^ 4 * c ^ 4 * r + 2 * K.M * K.a ^ 4 * r
        - 4 * K.M * K.a ^ 2 * c ^ 2 * r ^ 3 + 4 * K.M * K.a ^ 2 * r ^ 3 + K.a ^ 6 * c ^ 4
        + K.a ^ 4 * c ^ 4 * r ^ 2 + 2 * K.a ^ 4 * c ^ 2 * r ^ 2 + 2 * K.a ^ 2 * c ^ 2 * r ^ 4
        + K.a ^ 2 * r ^ 4 + r ^ 6) / sig ^ 3
    else 0
  else
    if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then
      K.M * K.a * (r ^ 2 - K.a ^ 2 * c ^ 2) / (sig ^ 2 * del)
    else if (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) then -2 * K.M * K.a * c * r / (s * sig ^ 2)
    else if (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) then
      (-K.M * K.a ^ 4 * c ^ 4 + K.M * K.a ^ 4 * c ^ 2 - K.M * K.a ^ 2 * c ^ 2 * r ^ 2
        - K.M * K.a ^ 2 * r ^ 2 - 2 * K.M * r ^ 4 + K.a ^ 4 * c ^ 4 * r
        + 2 * K.a ^ 2 * c ^ 2 * r ^ 3 + r ^ 5) / (sig ^ 2 * del)
    else if (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) then
      c * (-2 * K.M * K.a ^ 2 * c ^ 2 * r + 2 * K.M * K.a ^ 2 * r + K.a ^ 4 * c ^ 4
        + 2 * K.a ^ 2 * c ^ 2 * r ^ 2 + r ^ 4) / (s * sig ^ 2)
    else 0

/-- Lower-index symmetry of `K.christoffel`. -/
lemma christoffel_symm (K : KerrSpacetime) (x : Fin 4 → ℝ) (k i j : Fin 4) :
    K.christoffel x k i j = K.christoffel x k j i := by
  fin_cases k <;> fin_cases i <;> fin_cases j <;> simp [christoffel]

/-- `K.christoffel` does not depend on the `t` (`μ = 0`) or `φ` (`μ = 3`) coordinates. -/
lemma pd_christoffel_const_03 (K : KerrSpacetime) (x : Fin 4 → ℝ) (μ : Fin 4) (hμ : μ = 0 ∨ μ = 3)
    (k i j : Fin 4) : coordDeriv μ (fun y => K.christoffel y k i j) x = 0 := by
  rcases hμ with rfl | rfl
  · exact coordDeriv_const_slice 0 (K.christoffel x k i j)
      (fun _ => by simp [christoffel, sigma, delta])
  · exact coordDeriv_const_slice 3 (K.christoffel x k i j)
      (fun _ => by simp [christoffel, sigma, delta])

/-!

## C. Agreement with the coordinate pipeline and trace identity

-/

private lemma christoffel_0 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) (hdel : K.delta (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0)
    (i j : Fin 4) :
    Pipeline.christoffel K.metric K.metricInv x 0 i j = K.christoffel x 0 i j := by
  have hs2 : Real.sin (x 2) ^ 2 = 1 - Real.cos (x 2) ^ 2 := Real.sin_sq (x 2)
  simp only [Pipeline.christoffel, Fin.sum_univ_four, K.pd_metric_eq _ x hsig hdel]
  fin_cases i <;> fin_cases j <;>
    simp only [metricInv, metricD, christoffel] <;> norm_num
  all_goals
    field_simp [hsig, hdel, hs]
    simp -failIfUnchanged only [sigma, delta, axialFactor, hs2]
    ring

private lemma christoffel_1 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) (hdel : K.delta (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0)
    (i j : Fin 4) :
    Pipeline.christoffel K.metric K.metricInv x 1 i j = K.christoffel x 1 i j := by
  have hs2 : Real.sin (x 2) ^ 2 = 1 - Real.cos (x 2) ^ 2 := Real.sin_sq (x 2)
  simp only [Pipeline.christoffel, Fin.sum_univ_four, K.pd_metric_eq _ x hsig hdel]
  fin_cases i <;> fin_cases j <;>
    simp only [metricInv, metricD, christoffel] <;> norm_num
  all_goals field_simp [hsig, hdel, hs]
  all_goals simp -failIfUnchanged only [sigma, delta, axialFactor, hs2]
  all_goals ring

private lemma christoffel_2 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) (hdel : K.delta (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0)
    (i j : Fin 4) :
    Pipeline.christoffel K.metric K.metricInv x 2 i j = K.christoffel x 2 i j := by
  have hs2 : Real.sin (x 2) ^ 2 = 1 - Real.cos (x 2) ^ 2 := Real.sin_sq (x 2)
  simp only [Pipeline.christoffel, Fin.sum_univ_four, K.pd_metric_eq _ x hsig hdel]
  fin_cases i <;> fin_cases j <;>
    simp only [metricInv, metricD, christoffel] <;> norm_num
  all_goals field_simp [hsig, hdel, hs]
  all_goals simp -failIfUnchanged only [sigma, delta, axialFactor, hs2]
  all_goals ring

private lemma christoffel_3 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) (hdel : K.delta (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0)
    (i j : Fin 4) :
    Pipeline.christoffel K.metric K.metricInv x 3 i j = K.christoffel x 3 i j := by
  have hs2 : Real.sin (x 2) ^ 2 = 1 - Real.cos (x 2) ^ 2 := Real.sin_sq (x 2)
  simp only [Pipeline.christoffel, Fin.sum_univ_four, K.pd_metric_eq _ x hsig hdel]
  fin_cases i <;> fin_cases j <;>
    simp only [metricInv, metricD, christoffel] <;> norm_num
  all_goals
    field_simp [hsig, hdel, hs]
    simp -failIfUnchanged only [sigma, delta, axialFactor, hs2]
    ring

/-- Every Christoffel symbol computed via `Pipeline.christoffel` agrees with `K.christoffel` at
every regular coordinate point (`Σ ≠ 0`, `Δ ≠ 0`, `sin θ ≠ 0`). -/
lemma christoffel_eq (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) (hdel : K.delta (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0)
    (k i j : Fin 4) :
    Pipeline.christoffel K.metric K.metricInv x k i j = K.christoffel x k i j := by
  fin_cases k
  · exact christoffel_0 K x hsig hdel hs i j
  · exact christoffel_1 K x hsig hdel hs i j
  · exact christoffel_2 K x hsig hdel hs i j
  · exact christoffel_3 K x hsig hdel hs i j

/-- Continuity-neighborhood equality between `Pipeline.christoffel` and `K.christoffel`. -/
lemma eventually_christoffel_eq (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) (hdel : K.delta (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0)
    (k i j : Fin 4) :
    (fun y => Pipeline.christoffel K.metric K.metricInv y k i j)
      =ᶠ[nhds x] fun y => K.christoffel y k i j := by
  have hcSig : Continuous (fun y : Fin 4 → ℝ => K.sigma (y 1) (y 2)) := by
    simp only [sigma]; fun_prop
  have hcDel : Continuous (fun y : Fin 4 → ℝ => K.delta (y 1)) := by
    simp only [delta]; fun_prop
  have hcS : Continuous (fun y : Fin 4 → ℝ => Real.sin (y 2)) := by fun_prop
  have hmem := (hcSig.continuousAt.eventually_ne hsig).and
    ((hcDel.continuousAt.eventually_ne hdel).and (hcS.continuousAt.eventually_ne hs))
  filter_upwards [hmem] with y ⟨hySig, hyDel, hyS⟩
  exact K.christoffel_eq y hySig hyDel hyS k i j

-- Factored out as an auxiliary scalar table because contracted derivatives simplify the vacuum
-- Ricci calculation.
/-- Contracted Boyer–Lindquist Kerr Christoffel trace `∑ ρ, Γ^ρ_{ρ μ} = ∂_μ ln(Σ sin θ)`. -/
noncomputable def christoffelTrace (K : KerrSpacetime) (x : Fin 4 → ℝ) (μ : Fin 4) : ℝ :=
  if μ = 1 then 2 * x 1 / K.sigma (x 1) (x 2)
  else if μ = 2 then
    Real.cos (x 2) / Real.sin (x 2)
      - 2 * K.a ^ 2 * Real.cos (x 2) * Real.sin (x 2) / K.sigma (x 1) (x 2)
  else 0

/-- Exact contraction identity `∑ ρ, K.christoffel x ρ ρ μ = K.christoffelTrace x μ`. -/
lemma sum_christoffel_trace (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) (hdel : K.delta (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0)
    (μ : Fin 4) :
    (∑ ρ : Fin 4, K.christoffel x ρ ρ μ) = K.christoffelTrace x μ := by
  have hs2 : Real.sin (x 2) ^ 2 = 1 - Real.cos (x 2) ^ 2 := Real.sin_sq (x 2)
  fin_cases μ
  · simp [Fin.sum_univ_four, christoffel, christoffelTrace]
  · simp only [Fin.sum_univ_four, christoffel, christoffelTrace]
    norm_num
    field_simp [hsig, hdel]
    simp only [sigma, delta]
    ring
  · simp only [Fin.sum_univ_four, christoffel, christoffelTrace]
    norm_num
    field_simp [hsig, hs]
    simp only [sigma]
    rw [hs2]
    ring
  · simp [Fin.sum_univ_four, christoffel, christoffelTrace]

end KerrSpacetime

end Kerr

end GeneralRelativity
