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

Analytical partial derivatives of `kerrMetric`, all 20 independent Christoffel connection
coefficients `kerrChristoffel`, their agreement with `Pipeline.christoffel`, and the contracted
trace
`kerrChristoffelTrace`.

## i. Overview

This module evaluates the Boyer–Lindquist metric partial derivatives `kerrMetricD` (`∂_r` and
`∂_θ`, with `∂_t = ∂_φ = 0`), proves `pd_kerrMetric_eq`, defines the analytical closed-form
Christoffel symbol table `kerrChristoffel` (20 non-zero symmetric components) and its contraction
trace
`kerrChristoffelTrace` (`tr_r = 2 r / Σ`, `tr_θ = cot θ - 2 a² cos θ sin θ / Σ`), and establishes
that
`christoffel (kerrMetric M a) (kerrMetricInv M a)` equals `kerrChristoffel M a` everywhere on
regular
coordinates (`Σ ≠ 0`, `Δ ≠ 0`, `sin θ ≠ 0`) and on a neighborhood thereof.

## ii. Key results

- `kerrMetricD`, `pd_kerrMetric_eq` : partial derivatives of the Kerr metric.
- `kerrChristoffel`, `kerrChristoffel_symm` : explicit Christoffel symbols of Boyer–Lindquist Kerr
  spacetime.
- `christoffel_kerr_eq`, `eventually_christoffel_kerr_eq` : agreement with `Pipeline.christoffel`.
- `kerrChristoffelTrace`, `sum_kerrChristoffel_trace` : contracted Christoffel trace `∑ ρ, Γ^ρ_{ρ
  μ}`.

## iii. Table of contents

- A. Partial derivatives of the Kerr metric
- B. Explicit Boyer–Lindquist Christoffel symbols
- C. Agreement with the coordinate pipeline and trace identity

## iv. References

* R. M. Wald, *General Relativity* (1984). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973). [ref: mtw_1973_gravitation]

-/

@[expose] public section

namespace GeneralRelativity

namespace Kerr

open Pipeline

/-!

## A. Partial derivatives of the Kerr metric

-/

/-- Analytical coordinate partial derivatives `∂_μ (kerrMetric M a · i j)` in Boyer–Lindquist
coordinates `x = (t, r, θ, φ)`. -/
noncomputable def kerrMetricD (M a : ℝ) (μ : Fin 4) (x : Fin 4 → ℝ) (i j : Fin 4) : ℝ :=
  let r := x 1
  let c := Real.cos (x 2)
  let s := Real.sin (x 2)
  let sig := sigma a r (x 2)
  let del := delta M a r
  let bval := kerrAxialFactor M a r (x 2)
  if μ = 1 then
    if i = 0 ∧ j = 0 then -(2 * M * (r ^ 2 - a ^ 2 * c ^ 2) / sig ^ 2)
    else if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then
      2 * M * a * s ^ 2 * (r ^ 2 - a ^ 2 * c ^ 2) / sig ^ 2
    else if i = 1 ∧ j = 1 then (2 * r * del - sig * (2 * r - 2 * M)) / del ^ 2
    else if i = 2 ∧ j = 2 then 2 * r
    else if i = 3 ∧ j = 3 then
      s ^ 2 * ((4 * r * (r ^ 2 + a ^ 2) - a ^ 2 * (2 * r - 2 * M) * s ^ 2) * sig
        - 2 * r * bval) / sig ^ 2
    else 0
  else if μ = 2 then
    if i = 0 ∧ j = 0 then 4 * M * a ^ 2 * r * c * s / sig ^ 2
    else if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then
      -4 * M * a * r * s * c * (r ^ 2 + a ^ 2) / sig ^ 2
    else if i = 1 ∧ j = 1 then -2 * a ^ 2 * c * s / del
    else if i = 2 ∧ j = 2 then -2 * a ^ 2 * c * s
    else if i = 3 ∧ j = 3 then
      ((-2 * a ^ 2 * del * s ^ 3 * c + 2 * bval * s * c) * sig
        + 2 * a ^ 2 * c * s ^ 3 * bval) / sig ^ 2
    else 0
  else 0

/-- Radial derivative of Boyer–Lindquist `Σ = r² + a² cos² θ`: `∂_r Σ = 2 r`. -/
lemma hasDerivAt_sigma_r (a r θ : ℝ) :
    HasDerivAt (fun s => sigma a s θ) (2 * r) r :=
  ((hasDerivAt_pow 2 r).add_const (a ^ 2 * Real.cos θ ^ 2)).congr_deriv (by ring)

/-- Angular derivative of Boyer–Lindquist `Σ = r² + a² cos² θ`:
`∂_θ Σ = -2 a² cos θ sin θ`. -/
lemma hasDerivAt_sigma_th (a r θ : ℝ) :
    HasDerivAt (fun t => sigma a r t) (-2 * a ^ 2 * Real.cos θ * Real.sin θ) θ :=
  (((hasDerivAt_cos_sq θ).const_mul (a ^ 2)).const_add (r ^ 2)).congr_deriv (by ring)

/-- Radial derivative of Boyer–Lindquist `Δ = r² - 2 M r + a²`: `∂_r Δ = 2 r - 2 M`. -/
lemma hasDerivAt_delta_r (M a r : ℝ) :
    HasDerivAt (fun s => delta M a s) (2 * r - 2 * M) r := by
  have h1 := ((hasDerivAt_pow 2 r).fun_sub
    ((hasDerivAt_const r (2 * M)).fun_mul (hasDerivAt_id r))).fun_add (hasDerivAt_const r (a ^ 2))
  exact h1.congr_deriv (by ring)

private lemma hasDerivAt_bigB_r (M a r θ : ℝ) :
    HasDerivAt (fun s => kerrAxialFactor M a s θ)
      (4 * r * (r ^ 2 + a ^ 2) - a ^ 2 * (2 * r - 2 * M) * Real.sin θ ^ 2) r := by
  have h1 : HasDerivAt (fun s : ℝ => (s ^ 2 + a ^ 2) ^ 2) (2 * (r ^ 2 + a ^ 2) * (2 * r)) r :=
    (((hasDerivAt_pow 2 r).add_const (a ^ 2)).pow 2).congr_deriv (by ring)
  have h2 : HasDerivAt (fun s : ℝ => a ^ 2 * delta M a s * Real.sin θ ^ 2)
      (a ^ 2 * (2 * r - 2 * M) * Real.sin θ ^ 2) r :=
    (((hasDerivAt_delta_r M a r).const_mul (a ^ 2)).mul_const (Real.sin θ ^ 2)).congr_deriv
      (by ring)
  exact (h1.fun_sub h2).congr_deriv (by ring)

private lemma hasDerivAt_bigB_th (M a r θ : ℝ) :
    HasDerivAt (fun t => kerrAxialFactor M a r t)
      (-2 * a ^ 2 * delta M a r * Real.sin θ * Real.cos θ) θ :=
  ((hasDerivAt_const θ ((r ^ 2 + a ^ 2) ^ 2)).fun_sub
    ((hasDerivAt_sin_sq θ).const_mul (a ^ 2 * delta M a r))).congr_deriv (by ring)

private lemma pd_kerrMetric_1_00 (M a : ℝ) (x : Fin 4 → ℝ) (hsig : sigma a (x 1) (x 2) ≠ 0) :
    coordDeriv 1 (fun y => kerrMetric M a y 0 0) x = kerrMetricD M a 1 x 0 0 := by
  have hfun : (fun s => kerrMetric M a (Function.update x 1 s) 0 0)
      = fun s => -(1 - 2 * M * s / sigma a s (x 2)) := by funext s; simp [kerrMetric]
  have hm : HasDerivAt (fun s : ℝ => 2 * M * s) (2 * M) (x 1) :=
    ((hasDerivAt_const (x 1) (2 * M)).fun_mul (hasDerivAt_id (x 1))).congr_deriv (by ring)
  have hq := hm.fun_div (hasDerivAt_sigma_r a (x 1) (x 2)) hsig
  have hd := ((hasDerivAt_const (x 1) 1).fun_sub hq).fun_neg
  rw [coordDeriv, hfun, hd.deriv]
  simp only [kerrMetricD, sigma, Fin.isValue, and_self, ↓reduceIte]
  field_simp [hsig]; ring

private lemma pd_kerrMetric_1_03 (M a : ℝ) (x : Fin 4 → ℝ) (hsig : sigma a (x 1) (x 2) ≠ 0) :
    coordDeriv 1 (fun y => kerrMetric M a y 0 3) x = kerrMetricD M a 1 x 0 3 := by
  have hfun : (fun s => kerrMetric M a (Function.update x 1 s) 0 3)
      = fun s => -(2 * M * a * s * Real.sin (x 2) ^ 2 / sigma a s (x 2)) := by
    funext s; simp [kerrMetric]
  have hm : HasDerivAt (fun s : ℝ => 2 * M * a * s * Real.sin (x 2) ^ 2)
      (2 * M * a * Real.sin (x 2) ^ 2) (x 1) :=
    ((((hasDerivAt_const (x 1) (2 * M * a)).fun_mul (hasDerivAt_id (x 1))).mul_const
      (Real.sin (x 2) ^ 2))).congr_deriv (by ring)
  have hq := (hm.fun_div (hasDerivAt_sigma_r a (x 1) (x 2)) hsig).fun_neg
  rw [coordDeriv, hfun, hq.deriv]
  simp only [kerrMetricD, sigma, Fin.isValue, Fin.reduceEq, and_false, and_true, or_false,
    ↓reduceIte]
  field_simp [hsig]; ring

private lemma pd_kerrMetric_1_11 (M a : ℝ) (x : Fin 4 → ℝ) (hdel : delta M a (x 1) ≠ 0) :
    coordDeriv 1 (fun y => kerrMetric M a y 1 1) x = kerrMetricD M a 1 x 1 1 := by
  have hfun : (fun s => kerrMetric M a (Function.update x 1 s) 1 1)
      = fun s => sigma a s (x 2) / delta M a s := by funext s; simp [kerrMetric]
  have hd := (hasDerivAt_sigma_r a (x 1) (x 2)).fun_div (hasDerivAt_delta_r M a (x 1)) hdel
  rw [coordDeriv, hfun, hd.deriv]
  simp [kerrMetricD]

private lemma pd_kerrMetric_1_22 (M a : ℝ) (x : Fin 4 → ℝ) :
    coordDeriv 1 (fun y => kerrMetric M a y 2 2) x = kerrMetricD M a 1 x 2 2 := by
  have hfun : (fun s => kerrMetric M a (Function.update x 1 s) 2 2)
      = fun s => sigma a s (x 2) := by funext s; simp [kerrMetric]
  rw [coordDeriv, hfun, (hasDerivAt_sigma_r a (x 1) (x 2)).deriv]
  simp [kerrMetricD]

private lemma pd_kerrMetric_1_33 (M a : ℝ) (x : Fin 4 → ℝ) (hsig : sigma a (x 1) (x 2) ≠ 0) :
    coordDeriv 1 (fun y => kerrMetric M a y 3 3) x = kerrMetricD M a 1 x 3 3 := by
  have hfun : (fun s => kerrMetric M a (Function.update x 1 s) 3 3)
      = fun s => kerrAxialFactor M a s (x 2) * Real.sin (x 2) ^ 2 / sigma a s (x 2) := by
    funext s; simp [kerrMetric]
  have hnum := (hasDerivAt_bigB_r M a (x 1) (x 2)).mul_const (Real.sin (x 2) ^ 2)
  have hq := hnum.fun_div (hasDerivAt_sigma_r a (x 1) (x 2)) hsig
  rw [coordDeriv, hfun, hq.deriv]
  have hval : kerrMetricD M a 1 x 3 3 = Real.sin (x 2) ^ 2 *
      ((4 * x 1 * (x 1 ^ 2 + a ^ 2) - a ^ 2 * (2 * x 1 - 2 * M) * Real.sin (x 2) ^ 2)
          * sigma a (x 1) (x 2) - 2 * x 1 * kerrAxialFactor M a (x 1) (x 2))
        / sigma a (x 1) (x 2) ^ 2 := by
    simp [kerrMetricD]
  rw [hval]
  ring

private lemma pd_kerrMetric_1_30 (M a : ℝ) (x : Fin 4 → ℝ) (hsig : sigma a (x 1) (x 2) ≠ 0) :
    coordDeriv 1 (fun y => kerrMetric M a y 3 0) x = kerrMetricD M a 1 x 3 0 := by
  have hs : (fun y => kerrMetric M a y 3 0) = fun y => kerrMetric M a y 0 3 := by
    funext y; exact (kerrMetric_symm M a y).apply 0 3
  rw [hs, pd_kerrMetric_1_03 M a x hsig]
  simp [kerrMetricD]

private lemma pd_kerrMetric_1 (M a : ℝ) (x : Fin 4 → ℝ)
    (hsig : sigma a (x 1) (x 2) ≠ 0) (hdel : delta M a (x 1) ≠ 0) (i j : Fin 4) :
    coordDeriv 1 (fun y => kerrMetric M a y i j) x = kerrMetricD M a 1 x i j := by
  fin_cases i <;> fin_cases j
  · exact pd_kerrMetric_1_00 M a x hsig
  · simp [coordDeriv, kerrMetric, kerrMetricD]
  · simp [coordDeriv, kerrMetric, kerrMetricD]
  · exact pd_kerrMetric_1_03 M a x hsig
  · simp [coordDeriv, kerrMetric, kerrMetricD]
  · exact pd_kerrMetric_1_11 M a x hdel
  · simp [coordDeriv, kerrMetric, kerrMetricD]
  · simp [coordDeriv, kerrMetric, kerrMetricD]
  · simp [coordDeriv, kerrMetric, kerrMetricD]
  · simp [coordDeriv, kerrMetric, kerrMetricD]
  · exact pd_kerrMetric_1_22 M a x
  · simp [coordDeriv, kerrMetric, kerrMetricD]
  · exact pd_kerrMetric_1_30 M a x hsig
  · simp [coordDeriv, kerrMetric, kerrMetricD]
  · simp [coordDeriv, kerrMetric, kerrMetricD]
  · exact pd_kerrMetric_1_33 M a x hsig

private lemma pd_kerrMetric_2_00 (M a : ℝ) (x : Fin 4 → ℝ) (hsig : sigma a (x 1) (x 2) ≠ 0) :
    coordDeriv 2 (fun y => kerrMetric M a y 0 0) x = kerrMetricD M a 2 x 0 0 := by
  have hfun : (fun t => kerrMetric M a (Function.update x 2 t) 0 0)
      = fun t => -(1 - 2 * M * x 1 / sigma a (x 1) t) := by funext t; simp [kerrMetric]
  have hq := (hasDerivAt_const (x 2) (2 * M * x 1)).fun_div (hasDerivAt_sigma_th a (x 1) (x 2)) hsig
  have hd := ((hasDerivAt_const (x 2) 1).fun_sub hq).fun_neg
  rw [coordDeriv, hfun, hd.deriv]
  simp only [kerrMetricD, Fin.isValue, Fin.reduceEq, and_self, ↓reduceIte]
  ring

private lemma pd_kerrMetric_2_03 (M a : ℝ) (x : Fin 4 → ℝ) (hsig : sigma a (x 1) (x 2) ≠ 0) :
    coordDeriv 2 (fun y => kerrMetric M a y 0 3) x = kerrMetricD M a 2 x 0 3 := by
  have hfun : (fun t => kerrMetric M a (Function.update x 2 t) 0 3)
      = fun t => -(2 * M * a * x 1 * Real.sin t ^ 2 / sigma a (x 1) t) := by
    funext t; simp [kerrMetric]
  have hm := (hasDerivAt_sin_sq (x 2)).const_mul (2 * M * a * x 1)
  have hq := (hm.fun_div (hasDerivAt_sigma_th a (x 1) (x 2)) hsig).fun_neg
  rw [coordDeriv, hfun, hq.deriv]
  have hval : kerrMetricD M a 2 x 0 3 =
      -4 * M * a * x 1 * Real.sin (x 2) * Real.cos (x 2) * (x 1 ^ 2 + a ^ 2)
        / sigma a (x 1) (x 2) ^ 2 := by
    simp [kerrMetricD]
  rw [hval]
  field_simp [hsig]
  simp only [sigma, Real.sin_sq (x 2)]
  ring

private lemma pd_kerrMetric_2_11 (M a : ℝ) (x : Fin 4 → ℝ) :
    coordDeriv 2 (fun y => kerrMetric M a y 1 1) x = kerrMetricD M a 2 x 1 1 := by
  have hfun : (fun t => kerrMetric M a (Function.update x 2 t) 1 1)
      = fun t => sigma a (x 1) t / delta M a (x 1) := by funext t; simp [kerrMetric]
  have hd := (hasDerivAt_sigma_th a (x 1) (x 2)).div_const (delta M a (x 1))
  have hval : kerrMetricD M a 2 x 1 1 =
      -2 * a ^ 2 * Real.cos (x 2) * Real.sin (x 2) / delta M a (x 1) := by
    simp [kerrMetricD]
  rw [coordDeriv, hfun, hd.deriv, hval]

private lemma pd_kerrMetric_2_22 (M a : ℝ) (x : Fin 4 → ℝ) :
    coordDeriv 2 (fun y => kerrMetric M a y 2 2) x = kerrMetricD M a 2 x 2 2 := by
  have hfun : (fun t => kerrMetric M a (Function.update x 2 t) 2 2)
      = fun t => sigma a (x 1) t := by funext t; simp [kerrMetric]
  have hval : kerrMetricD M a 2 x 2 2 = -2 * a ^ 2 * Real.cos (x 2) * Real.sin (x 2) := by
    simp [kerrMetricD]
  rw [coordDeriv, hfun, (hasDerivAt_sigma_th a (x 1) (x 2)).deriv, hval]

private lemma pd_kerrMetric_2_33 (M a : ℝ) (x : Fin 4 → ℝ) (hsig : sigma a (x 1) (x 2) ≠ 0) :
    coordDeriv 2 (fun y => kerrMetric M a y 3 3) x = kerrMetricD M a 2 x 3 3 := by
  have hfun : (fun t => kerrMetric M a (Function.update x 2 t) 3 3)
      = fun t => kerrAxialFactor M a (x 1) t * Real.sin t ^ 2 / sigma a (x 1) t := by
    funext t; simp [kerrMetric]
  have hnum := (hasDerivAt_bigB_th M a (x 1) (x 2)).fun_mul (hasDerivAt_sin_sq (x 2))
  have hq := hnum.fun_div (hasDerivAt_sigma_th a (x 1) (x 2)) hsig
  rw [coordDeriv, hfun, hq.deriv]
  have hval : kerrMetricD M a 2 x 3 3 =
      ((-2 * a ^ 2 * delta M a (x 1) * Real.sin (x 2) ^ 3 * Real.cos (x 2)
            + 2 * kerrAxialFactor M a (x 1) (x 2) * Real.sin (x 2) * Real.cos (x 2))
          * sigma a (x 1) (x 2)
        + 2 * a ^ 2 * Real.cos (x 2) * Real.sin (x 2) ^ 3 * kerrAxialFactor M a (x 1) (x 2))
      / sigma a (x 1) (x 2) ^ 2 := by
    simp [kerrMetricD]
  rw [hval]
  ring

private lemma pd_kerrMetric_2_30 (M a : ℝ) (x : Fin 4 → ℝ) (hsig : sigma a (x 1) (x 2) ≠ 0) :
    coordDeriv 2 (fun y => kerrMetric M a y 3 0) x = kerrMetricD M a 2 x 3 0 := by
  have hs : (fun y => kerrMetric M a y 3 0) = fun y => kerrMetric M a y 0 3 := by
    funext y; exact (kerrMetric_symm M a y).apply 0 3
  rw [hs, pd_kerrMetric_2_03 M a x hsig]
  simp [kerrMetricD]

private lemma pd_kerrMetric_2 (M a : ℝ) (x : Fin 4 → ℝ)
    (hsig : sigma a (x 1) (x 2) ≠ 0) (i j : Fin 4) :
    coordDeriv 2 (fun y => kerrMetric M a y i j) x = kerrMetricD M a 2 x i j := by
  fin_cases i <;> fin_cases j
  · exact pd_kerrMetric_2_00 M a x hsig
  · simp [coordDeriv, kerrMetric, kerrMetricD]
  · simp [coordDeriv, kerrMetric, kerrMetricD]
  · exact pd_kerrMetric_2_03 M a x hsig
  · simp [coordDeriv, kerrMetric, kerrMetricD]
  · exact pd_kerrMetric_2_11 M a x
  · simp [coordDeriv, kerrMetric, kerrMetricD]
  · simp [coordDeriv, kerrMetric, kerrMetricD]
  · simp [coordDeriv, kerrMetric, kerrMetricD]
  · simp [coordDeriv, kerrMetric, kerrMetricD]
  · exact pd_kerrMetric_2_22 M a x
  · simp [coordDeriv, kerrMetric, kerrMetricD]
  · exact pd_kerrMetric_2_30 M a x hsig
  · simp [coordDeriv, kerrMetric, kerrMetricD]
  · simp [coordDeriv, kerrMetric, kerrMetricD]
  · exact pd_kerrMetric_2_33 M a x hsig

/-- Complete identification of all 64 partial derivatives of `kerrMetric M a` with `kerrMetricD`. -/
lemma pd_kerrMetric_eq (M a : ℝ) (μ : Fin 4) (x : Fin 4 → ℝ)
    (hsig : sigma a (x 1) (x 2) ≠ 0) (hdel : delta M a (x 1) ≠ 0) (i j : Fin 4) :
    coordDeriv μ (fun y => kerrMetric M a y i j) x = kerrMetricD M a μ x i j := by
  fin_cases μ
  · simp [coordDeriv, kerrMetric, kerrMetricD, sigma, delta, kerrAxialFactor]
  · exact pd_kerrMetric_1 M a x hsig hdel i j
  · exact pd_kerrMetric_2 M a x hsig i j
  · simp [coordDeriv, kerrMetric, kerrMetricD, sigma, delta, kerrAxialFactor]

/-!

## B. Explicit Boyer–Lindquist Christoffel symbols

-/

/-- Closed-form Levi-Civita Christoffel symbols `Γ^k_{ij}` of the Boyer–Lindquist Kerr metric,
factored out from `Pipeline.christoffel` so rational derivative reductions remain tractable. -/
noncomputable def kerrChristoffel (M a : ℝ) (x : Fin 4 → ℝ) (k i j : Fin 4) : ℝ :=
  let r := x 1
  let c := Real.cos (x 2)
  let s := Real.sin (x 2)
  let sig := sigma a r (x 2)
  let del := delta M a r
  if k = 0 then
    if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then
      M * (a ^ 2 + r ^ 2) * (r ^ 2 - a ^ 2 * c ^ 2) / (sig ^ 2 * del)
    else if (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) then
      -2 * M * a ^ 2 * c * r * s / sig ^ 2
    else if (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) then
      -M * a * s ^ 2 * (-a ^ 4 * c ^ 2 + a ^ 2 * c ^ 2 * r ^ 2 + a ^ 2 * r ^ 2 + 3 * r ^ 4)
        / (sig ^ 2 * del)
    else if (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) then
      2 * M * a ^ 3 * c * r * s ^ 3 / sig ^ 2
    else 0
  else if k = 1 then
    if i = 0 ∧ j = 0 then M * (r ^ 2 - a ^ 2 * c ^ 2) * del / sig ^ 3
    else if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then
      -M * a * s ^ 2 * (r ^ 2 - a ^ 2 * c ^ 2) * del / sig ^ 3
    else if i = 1 ∧ j = 1 then
      -(-M * a ^ 2 * c ^ 2 + M * r ^ 2 + a ^ 2 * c ^ 2 * r - a ^ 2 * r) / (sig * del)
    else if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then -a ^ 2 * c * s / sig
    else if i = 2 ∧ j = 2 then -r * del / sig
    else if i = 3 ∧ j = 3 then
      -s ^ 2 * del * (-M * a ^ 4 * c ^ 4 + M * a ^ 4 * c ^ 2 + M * a ^ 2 * c ^ 2 * r ^ 2
        - M * a ^ 2 * r ^ 2 + a ^ 4 * c ^ 4 * r + 2 * a ^ 2 * c ^ 2 * r ^ 3 + r ^ 5) / sig ^ 3
    else 0
  else if k = 2 then
    if i = 0 ∧ j = 0 then -2 * M * a ^ 2 * c * r * s / sig ^ 3
    else if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then
      2 * M * a * c * r * s * (a ^ 2 + r ^ 2) / sig ^ 3
    else if i = 1 ∧ j = 1 then a ^ 2 * c * s / (sig * del)
    else if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then r / sig
    else if i = 2 ∧ j = 2 then -a ^ 2 * c * s / sig
    else if i = 3 ∧ j = 3 then
      -c * s * (-2 * M * a ^ 4 * c ^ 4 * r + 2 * M * a ^ 4 * r - 4 * M * a ^ 2 * c ^ 2 * r ^ 3
        + 4 * M * a ^ 2 * r ^ 3 + a ^ 6 * c ^ 4 + a ^ 4 * c ^ 4 * r ^ 2
        + 2 * a ^ 4 * c ^ 2 * r ^ 2 + 2 * a ^ 2 * c ^ 2 * r ^ 4 + a ^ 2 * r ^ 4 + r ^ 6) / sig ^ 3
    else 0
  else
    if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then M * a * (r ^ 2 - a ^ 2 * c ^ 2) / (sig ^ 2 * del)
    else if (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) then -2 * M * a * c * r / (s * sig ^ 2)
    else if (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) then
      (-M * a ^ 4 * c ^ 4 + M * a ^ 4 * c ^ 2 - M * a ^ 2 * c ^ 2 * r ^ 2 - M * a ^ 2 * r ^ 2
        - 2 * M * r ^ 4 + a ^ 4 * c ^ 4 * r + 2 * a ^ 2 * c ^ 2 * r ^ 3 + r ^ 5) / (sig ^ 2 * del)
    else if (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) then
      c * (-2 * M * a ^ 2 * c ^ 2 * r + 2 * M * a ^ 2 * r + a ^ 4 * c ^ 4
        + 2 * a ^ 2 * c ^ 2 * r ^ 2 + r ^ 4) / (s * sig ^ 2)
    else 0

/-- Lower-index symmetry of `kerrChristoffel`. -/
lemma kerrChristoffel_symm (M a : ℝ) (x : Fin 4 → ℝ) (k i j : Fin 4) :
    kerrChristoffel M a x k i j = kerrChristoffel M a x k j i := by
  fin_cases k <;> fin_cases i <;> fin_cases j <;> simp [kerrChristoffel]

/-- `kerrChristoffel` does not depend on the `t` (`μ = 0`) or `φ` (`μ = 3`) coordinates. -/
lemma pd_kerrG_const_03 (M a : ℝ) (x : Fin 4 → ℝ) (μ : Fin 4) (hμ : μ = 0 ∨ μ = 3)
    (k i j : Fin 4) : coordDeriv μ (fun y => kerrChristoffel M a y k i j) x = 0 := by
  rcases hμ with rfl | rfl
  · have hfn : (fun s => kerrChristoffel M a (Function.update x 0 s) k i j)
    = fun _ => kerrChristoffel M a x k i j := by
      funext s; simp [kerrChristoffel, sigma, delta]
    rw [coordDeriv, hfn, deriv_const']
  · have hfn : (fun s => kerrChristoffel M a (Function.update x 3 s) k i j)
    = fun _ => kerrChristoffel M a x k i j := by
      funext s; simp [kerrChristoffel, sigma, delta]
    rw [coordDeriv, hfn, deriv_const']

/-!

## C. Agreement with the coordinate pipeline and trace identity

-/

private lemma christoffel_kerr_0 (M a : ℝ) (x : Fin 4 → ℝ)
    (hsig : sigma a (x 1) (x 2) ≠ 0) (hdel : delta M a (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0)
    (i j : Fin 4) :
    christoffel (kerrMetric M a) (kerrMetricInv M a) x 0 i j = kerrChristoffel M a x 0 i j := by
  have hs2 : Real.sin (x 2) ^ 2 = 1 - Real.cos (x 2) ^ 2 := Real.sin_sq (x 2)
  simp only [christoffel, Fin.sum_univ_four, pd_kerrMetric_eq M a _ x hsig hdel]
  fin_cases i <;> fin_cases j <;>
    simp only [kerrMetricInv, kerrMetricD, kerrChristoffel] <;> norm_num
  all_goals
    field_simp [hsig, hdel, hs]
    simp -failIfUnchanged only [sigma, delta, kerrAxialFactor, hs2]
    ring

private lemma christoffel_kerr_1 (M a : ℝ) (x : Fin 4 → ℝ)
    (hsig : sigma a (x 1) (x 2) ≠ 0) (hdel : delta M a (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0)
    (i j : Fin 4) :
    christoffel (kerrMetric M a) (kerrMetricInv M a) x 1 i j = kerrChristoffel M a x 1 i j := by
  have hs2 : Real.sin (x 2) ^ 2 = 1 - Real.cos (x 2) ^ 2 := Real.sin_sq (x 2)
  simp only [christoffel, Fin.sum_univ_four, pd_kerrMetric_eq M a _ x hsig hdel]
  fin_cases i <;> fin_cases j <;>
    simp only [kerrMetricInv, kerrMetricD, kerrChristoffel] <;> norm_num
  all_goals field_simp [hsig, hdel, hs]
  all_goals simp -failIfUnchanged only [sigma, delta, kerrAxialFactor, hs2]
  all_goals ring

private lemma christoffel_kerr_2 (M a : ℝ) (x : Fin 4 → ℝ)
    (hsig : sigma a (x 1) (x 2) ≠ 0) (hdel : delta M a (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0)
    (i j : Fin 4) :
    christoffel (kerrMetric M a) (kerrMetricInv M a) x 2 i j = kerrChristoffel M a x 2 i j := by
  have hs2 : Real.sin (x 2) ^ 2 = 1 - Real.cos (x 2) ^ 2 := Real.sin_sq (x 2)
  simp only [christoffel, Fin.sum_univ_four, pd_kerrMetric_eq M a _ x hsig hdel]
  fin_cases i <;> fin_cases j <;>
    simp only [kerrMetricInv, kerrMetricD, kerrChristoffel] <;> norm_num
  all_goals field_simp [hsig, hdel, hs]
  all_goals simp -failIfUnchanged only [sigma, delta, kerrAxialFactor, hs2]
  all_goals ring

private lemma christoffel_kerr_3 (M a : ℝ) (x : Fin 4 → ℝ)
    (hsig : sigma a (x 1) (x 2) ≠ 0) (hdel : delta M a (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0)
    (i j : Fin 4) :
    christoffel (kerrMetric M a) (kerrMetricInv M a) x 3 i j = kerrChristoffel M a x 3 i j := by
  have hs2 : Real.sin (x 2) ^ 2 = 1 - Real.cos (x 2) ^ 2 := Real.sin_sq (x 2)
  simp only [christoffel, Fin.sum_univ_four, pd_kerrMetric_eq M a _ x hsig hdel]
  fin_cases i <;> fin_cases j <;>
    simp only [kerrMetricInv, kerrMetricD, kerrChristoffel] <;> norm_num
  all_goals
    field_simp [hsig, hdel, hs]
    simp -failIfUnchanged only [sigma, delta, kerrAxialFactor, hs2]
    ring

/-- Every Christoffel symbol computed via `Pipeline.christoffel` agrees with `kerrChristoffel` at
every
regular coordinate point (`Σ ≠ 0`, `Δ ≠ 0`, `sin θ ≠ 0`). -/
lemma christoffel_kerr_eq (M a : ℝ) (x : Fin 4 → ℝ)
    (hsig : sigma a (x 1) (x 2) ≠ 0) (hdel : delta M a (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0)
    (k i j : Fin 4) :
    christoffel (kerrMetric M a) (kerrMetricInv M a) x k i j = kerrChristoffel M a x k i j := by
  fin_cases k
  · exact christoffel_kerr_0 M a x hsig hdel hs i j
  · exact christoffel_kerr_1 M a x hsig hdel hs i j
  · exact christoffel_kerr_2 M a x hsig hdel hs i j
  · exact christoffel_kerr_3 M a x hsig hdel hs i j

/-- Continuity-neighborhood equality between `Pipeline.christoffel` and `kerrChristoffel`. -/
lemma eventually_christoffel_kerr_eq (M a : ℝ) (x : Fin 4 → ℝ)
    (hsig : sigma a (x 1) (x 2) ≠ 0) (hdel : delta M a (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0)
    (k i j : Fin 4) :
    (fun y => christoffel (kerrMetric M a) (kerrMetricInv M a) y k i j)
      =ᶠ[nhds x] fun y => kerrChristoffel M a y k i j := by
  have hcSig : Continuous (fun y : Fin 4 → ℝ => sigma a (y 1) (y 2)) := by
    simp only [sigma]; fun_prop
  have hcDel : Continuous (fun y : Fin 4 → ℝ => delta M a (y 1)) := by
    simp only [delta]; fun_prop
  have hcS : Continuous (fun y : Fin 4 → ℝ => Real.sin (y 2)) := by fun_prop
  have hmem := (hcSig.continuousAt.eventually_ne hsig).and
    ((hcDel.continuousAt.eventually_ne hdel).and (hcS.continuousAt.eventually_ne hs))
  filter_upwards [hmem] with y ⟨hySig, hyDel, hyS⟩
  exact christoffel_kerr_eq M a y hySig hyDel hyS k i j

/-- Contracted Kerr Christoffel trace `∑ ρ, Γ^ρ_{ρ μ} = ∂_μ ln(Σ sin θ)`, factored out as an
auxiliary scalar table because contracted derivatives reduce the vacuum Ricci proof. -/
noncomputable def kerrChristoffelTrace (a : ℝ) (x : Fin 4 → ℝ) (μ : Fin 4) : ℝ :=
  if μ = 1 then 2 * x 1 / sigma a (x 1) (x 2)
  else if μ = 2 then
    Real.cos (x 2) / Real.sin (x 2)
      - 2 * a ^ 2 * Real.cos (x 2) * Real.sin (x 2) / sigma a (x 1) (x 2)
  else 0

/-- Exact contraction identity `∑ ρ, kerrChristoffel M a x ρ ρ μ = kerrChristoffelTrace a x μ`. -/
lemma sum_kerrChristoffel_trace (M a : ℝ) (x : Fin 4 → ℝ)
    (hsig : sigma a (x 1) (x 2) ≠ 0) (hdel : delta M a (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0)
    (μ : Fin 4) :
    (∑ ρ : Fin 4, kerrChristoffel M a x ρ ρ μ) = kerrChristoffelTrace a x μ := by
  have hs2 : Real.sin (x 2) ^ 2 = 1 - Real.cos (x 2) ^ 2 := Real.sin_sq (x 2)
  fin_cases μ
  · simp [Fin.sum_univ_four, kerrChristoffel, kerrChristoffelTrace]
  · simp only [Fin.sum_univ_four, kerrChristoffel, kerrChristoffelTrace]
    norm_num
    field_simp [hsig, hdel]
    simp only [sigma, delta]
    ring
  · simp only [Fin.sum_univ_four, kerrChristoffel, kerrChristoffelTrace]
    norm_num
    field_simp [hsig, hs]
    simp only [sigma]
    rw [hs2]
    ring
  · simp [Fin.sum_univ_four, kerrChristoffel, kerrChristoffelTrace]

end Kerr

end GeneralRelativity
