/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.General.Kerr.Christoffel
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!

# Kerr spacetime vacuum Einstein equations

Full pipeline proof that `KerrSpacetime` is Ricci flat, scalar flat, and satisfies the vacuum
Einstein equation `G = 0`.

## i. Overview

Using the coordinate-pipeline Christoffel agreement `KerrSpacetime.christoffel_eq` and trace
identity `KerrSpacetime.sum_christoffel_trace` from `Kerr.Christoffel`, this module evaluates all
required partial derivatives of `KerrSpacetime.christoffel` and `KerrSpacetime.christoffelTrace`
and proves that `Pipeline.ricciTensorOf K.metric K.metricInv x σ ν` vanishes for every coordinate
pair `(σ, ν)` at all regular points (`Σ ≠ 0`, `Δ ≠ 0`, `sin θ ≠ 0`). It immediately follows that
`ricciScalarOf` and `einsteinTensorOf` vanish identically.

## ii. Key results

- `KerrSpacetime.ricci`, `KerrSpacetime.einstein` : Boyer–Lindquist Kerr pipeline Ricci and Einstein
  tensors.
- `KerrSpacetime.christoffelTraceDeriv_rr`, `KerrSpacetime.christoffelTraceDeriv_rtheta`,
  `KerrSpacetime.christoffelTraceDeriv_thetar`, `KerrSpacetime.christoffelTraceDeriv_thetatheta` :
  partial derivatives of `KerrSpacetime.christoffelTrace`.
- `KerrSpacetime.ricciTensorOf_eq_zero` : vacuum Ricci flatness `Ric_{σ ν} = 0` via
  `Pipeline.ricciTensorOf`.
- `KerrSpacetime.ricciScalarOf_eq_zero` : vanishing scalar curvature `R = 0`.
- `KerrSpacetime.einsteinTensorOf_eq_zero` : vacuum Einstein equations `G_{i j} = 0`.

## iii. Table of contents

- A. Trace and Christoffel partial derivatives
- B. Ricci flatness through the coordinate pipeline
- C. Scalar curvature and vacuum Einstein equations

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

## A. Trace and Christoffel partial derivatives

Differentiating the Boyer–Lindquist Christoffel symbols and contracted trace `tr_μ = ∂_μ ln(Σ sin θ)`
along the `r` and `θ` coordinate slices prepares the cancellation of the Ricci tensor components.

-/

/-- Boyer–Lindquist Kerr Ricci tensor computed via `Pipeline.ricciTensorOf`. -/
noncomputable def ricci (K : KerrSpacetime) (x : Fin 4 → ℝ) : Tensor2 4 :=
  Pipeline.ricciTensorOf K.metric K.metricInv x

/-- Boyer–Lindquist Kerr Einstein tensor computed via `Pipeline.einsteinTensorOf`. -/
noncomputable def einstein (K : KerrSpacetime) (x : Fin 4 → ℝ) : Tensor2 4 :=
  Pipeline.einsteinTensorOf K.metric K.metricInv x

private lemma hasDerivAt_sigmaPow3_r (K : KerrSpacetime) (r θ : ℝ) :
    HasDerivAt (fun s => K.sigma s θ ^ 3) (3 * K.sigma r θ ^ 2 * (2 * r)) r :=
  ((K.hasDerivAt_sigma_r r θ).pow 3).congr_deriv (by ring)

private lemma hasDerivAt_sigmaPow3_theta (K : KerrSpacetime) (r θ : ℝ) :
    HasDerivAt (fun t => K.sigma r t ^ 3)
      (3 * K.sigma r θ ^ 2 * (-2 * K.a ^ 2 * Real.cos θ * Real.sin θ)) θ :=
  ((K.hasDerivAt_sigma_theta r θ).pow 3).congr_deriv (by ring)

private lemma differentiableAt_christoffel_r (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (_hsig : K.sigma (x 1) (x 2) ≠ 0) (_hdel : K.delta (x 1) ≠ 0) (_hs : Real.sin (x 2) ≠ 0)
    (k i j : Fin 4) :
    DifferentiableAt ℝ (fun s => K.christoffel (Function.update x 1 s) k i j) (x 1) := by
  have _ : DifferentiableAt ℝ (fun s => K.sigma s (x 2)) (x 1) :=
    (K.hasDerivAt_sigma_r (x 1) (x 2)).differentiableAt
  have _ : DifferentiableAt ℝ K.delta (x 1) :=
    (K.hasDerivAt_delta_r (x 1)).differentiableAt
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp only [christoffel, Function.update_self,
      Function.update_of_ne (by decide : (2 : Fin 4) ≠ 1)] <;>
    norm_num
  all_goals fun_prop (disch := positivity)

private lemma differentiableAt_christoffel_theta (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (_hsig : K.sigma (x 1) (x 2) ≠ 0) (_hdel : K.delta (x 1) ≠ 0) (_hs : Real.sin (x 2) ≠ 0)
    (k i j : Fin 4) :
    DifferentiableAt ℝ (fun t => K.christoffel (Function.update x 2 t) k i j) (x 2) := by
  have _ : DifferentiableAt ℝ (fun t => K.sigma (x 1) t) (x 2) :=
    (K.hasDerivAt_sigma_theta (x 1) (x 2)).differentiableAt
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp only [christoffel, Function.update_self,
      Function.update_of_ne (by decide : (1 : Fin 4) ≠ 2)] <;>
    norm_num
  all_goals fun_prop (disch := positivity)

/-- Radial partial derivative of the radial trace `∂_r (K.christoffelTrace · 1)`. -/
lemma christoffelTraceDeriv_rr (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) :
    coordDeriv 1 (fun y => K.christoffelTrace y 1) x
      = -2 * (x 1 ^ 2 - K.a ^ 2 * Real.cos (x 2) ^ 2) / K.sigma (x 1) (x 2) ^ 2 := by
  have hfun : (fun s => K.christoffelTrace (Function.update x 1 s) 1)
      = fun s => 2 * s / K.sigma s (x 2) := by funext s; simp [christoffelTrace]
  have hm : HasDerivAt (fun s : ℝ => 2 * s) 2 (x 1) :=
    ((hasDerivAt_const (x 1) 2).fun_mul (hasDerivAt_id (x 1))).congr_deriv (by ring)
  have hd := hm.fun_div (K.hasDerivAt_sigma_r (x 1) (x 2)) hsig
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hd)]
  field_simp [hsig]
  simp only [sigma]
  ring

/-- Polar partial derivative of the radial trace `∂_θ (K.christoffelTrace · 1)`. -/
lemma christoffelTraceDeriv_thetar (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) :
    coordDeriv 2 (fun y => K.christoffelTrace y 1) x
      = 4 * K.a ^ 2 * Real.cos (x 2) * x 1 * Real.sin (x 2) / K.sigma (x 1) (x 2) ^ 2 := by
  have hfun : (fun t => K.christoffelTrace (Function.update x 2 t) 1)
      = fun t => 2 * x 1 / K.sigma (x 1) t := by funext t; simp [christoffelTrace]
  have hd := (hasDerivAt_const (x 2) (2 * x 1)).fun_div
    (K.hasDerivAt_sigma_theta (x 1) (x 2)) hsig
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hd)]
  ring

/-- Radial partial derivative of the polar trace `∂_r (K.christoffelTrace · 2)`. -/
lemma christoffelTraceDeriv_rtheta (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) :
    coordDeriv 1 (fun y => K.christoffelTrace y 2) x
      = 4 * K.a ^ 2 * Real.cos (x 2) * x 1 * Real.sin (x 2) / K.sigma (x 1) (x 2) ^ 2 := by
  have hfun : (fun s => K.christoffelTrace (Function.update x 1 s) 2)
      = fun s => Real.cos (x 2) / Real.sin (x 2)
        - 2 * K.a ^ 2 * Real.cos (x 2) * Real.sin (x 2) / K.sigma s (x 2) := by
    funext s; simp [christoffelTrace]
  have hd1 := hasDerivAt_const (x 1) (Real.cos (x 2) / Real.sin (x 2))
  have hd2 := (hasDerivAt_const (x 1) (2 * K.a ^ 2 * Real.cos (x 2) * Real.sin (x 2))).fun_div
    (K.hasDerivAt_sigma_r (x 1) (x 2)) hsig
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ (hd1.fun_sub hd2))]
  ring

/-- Polar partial derivative of the polar trace `∂_θ (K.christoffelTrace · 2)`. -/
lemma christoffelTraceDeriv_thetatheta (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) (hs : Real.sin (x 2) ≠ 0) :
    coordDeriv 2 (fun y => K.christoffelTrace y 2) x
      = -(1 / Real.sin (x 2) ^ 2)
        - 2 * K.a ^ 2 * ((Real.cos (x 2) ^ 2 - Real.sin (x 2) ^ 2) * K.sigma (x 1) (x 2)
          + 2 * K.a ^ 2 * Real.cos (x 2) ^ 2 * Real.sin (x 2) ^ 2) / K.sigma (x 1) (x 2) ^ 2 := by
  have hfun : (fun t => K.christoffelTrace (Function.update x 2 t) 2)
      = fun t => Real.cos t / Real.sin t
        - 2 * K.a ^ 2 * (Real.cos t * Real.sin t) / K.sigma (x 1) t := by
    funext t; simp only [christoffelTrace, Fin.isValue, Fin.reduceEq, ↓reduceIte,
      Function.update_self,
      Function.update_of_ne (by decide : (1 : Fin 4) ≠ 2)]; ring
  have hcot := (Real.hasDerivAt_cos (x 2)).fun_div (Real.hasDerivAt_sin (x 2)) hs
  have hcs := (Real.hasDerivAt_cos (x 2)).fun_mul (Real.hasDerivAt_sin (x 2))
  have hnum := hcs.const_mul (2 * K.a ^ 2)
  have hq := hnum.fun_div (K.hasDerivAt_sigma_theta (x 1) (x 2)) hsig
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ (hcot.fun_sub hq))]
  have hsc := Real.sin_sq_add_cos_sq (x 2)
  field_simp [hs, hsig]
  linear_combination -K.sigma (x 1) (x 2) ^ 2 * hsc

private lemma hasDerivAt_christoffelNum_r_00 (K : KerrSpacetime) (x : Fin 4 → ℝ) :
    HasDerivAt (fun s => K.M * (s ^ 2 - K.a ^ 2 * Real.cos (x 2) ^ 2) * K.delta s)
      ((K.M * (2 * x 1)) * K.delta (x 1)
        + K.M * (x 1 ^ 2 - K.a ^ 2 * Real.cos (x 2) ^ 2) * (2 * x 1 - 2 * K.M)) (x 1) := by
  have h1 := (((hasDerivAt_pow 2 (x 1)).sub_const (K.a ^ 2 * Real.cos (x 2) ^ 2)).const_mul K.M)
  exact (h1.fun_mul (K.hasDerivAt_delta_r (x 1))).congr_deriv (by ring)

private lemma christoffelDeriv_r_00 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) (_hdel : K.delta (x 1) ≠ 0) :
    coordDeriv 1 (fun y => K.christoffel y 1 0 0) x =
      (-2 * K.M * (-K.M * K.a ^ 4 * Real.cos (x 2) ^ 4
        + 8 * K.M * K.a ^ 2 * Real.cos (x 2) ^ 2 * x 1 ^ 2
        - 3 * K.M * x 1 ^ 4 + K.a ^ 4 * Real.cos (x 2) ^ 4 * x 1
        - 4 * K.a ^ 4 * Real.cos (x 2) ^ 2 * x 1
        - 4 * K.a ^ 2 * Real.cos (x 2) ^ 2 * x 1 ^ 3 + 2 * K.a ^ 2 * x 1 ^ 3 + x 1 ^ 5))
        / K.sigma (x 1) (x 2) ^ 4 := by
  have hfun : (fun s => K.christoffel (Function.update x 1 s) 1 0 0)
      = fun s => (K.M * (s ^ 2 - K.a ^ 2 * Real.cos (x 2) ^ 2) * K.delta s)
        / K.sigma s (x 2) ^ 3 := by funext s; simp [christoffel]
  have hd := (hasDerivAt_christoffelNum_r_00 K x).fun_div
    (hasDerivAt_sigmaPow3_r K (x 1) (x 2)) (pow_ne_zero 3 hsig)
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hd)]
  field_simp [hsig]
  simp only [sigma, delta]
  ring

private lemma christoffelDeriv_r_03 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) :
    coordDeriv 1 (fun y => K.christoffel y 1 0 3) x =
      (2 * K.M * K.a * Real.sin (x 2) ^ 2 * (-K.M * K.a ^ 4 * Real.cos (x 2) ^ 4
        + 8 * K.M * K.a ^ 2 * Real.cos (x 2) ^ 2 * x 1 ^ 2 - 3 * K.M * x 1 ^ 4
        + K.a ^ 4 * Real.cos (x 2) ^ 4 * x 1 - 4 * K.a ^ 4 * Real.cos (x 2) ^ 2 * x 1
        - 4 * K.a ^ 2 * Real.cos (x 2) ^ 2 * x 1 ^ 3 + 2 * K.a ^ 2 * x 1 ^ 3 + x 1 ^ 5))
        / K.sigma (x 1) (x 2) ^ 4 := by
  have hfun : (fun s => K.christoffel (Function.update x 1 s) 1 0 3)
      = fun s => -(K.a * Real.sin (x 2) ^ 2)
        * ((K.M * (s ^ 2 - K.a ^ 2 * Real.cos (x 2) ^ 2) * K.delta s) / K.sigma s (x 2) ^ 3) := by
    funext s
    simp only [christoffel, Function.update_self,
      Function.update_of_ne (by decide : (2 : Fin 4) ≠ 1)]
    norm_num
    ring
  have hd := ((hasDerivAt_christoffelNum_r_00 K x).fun_div
    (hasDerivAt_sigmaPow3_r K (x 1) (x 2)) (pow_ne_zero 3 hsig)).const_mul
      (-(K.a * Real.sin (x 2) ^ 2))
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hd)]
  field_simp [hsig]
  simp only [sigma, delta]
  ring

private lemma christoffelDeriv_r_11 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) (hdel : K.delta (x 1) ≠ 0) :
    coordDeriv 1 (fun y => K.christoffel y 1 1 1) x =
      (2 * K.M ^ 2 * K.a ^ 4 * Real.cos (x 2) ^ 4
        + 8 * K.M ^ 2 * K.a ^ 2 * Real.cos (x 2) ^ 2 * x 1 ^ 2
        - 2 * K.M ^ 2 * x 1 ^ 4 - 2 * K.M * K.a ^ 4 * Real.cos (x 2) ^ 4 * x 1
        - 4 * K.M * K.a ^ 4 * Real.cos (x 2) ^ 2 * x 1
        - 8 * K.M * K.a ^ 2 * Real.cos (x 2) ^ 2 * x 1 ^ 3
        + 4 * K.M * K.a ^ 2 * x 1 ^ 3 + 2 * K.M * x 1 ^ 5 - K.a ^ 6 * Real.cos (x 2) ^ 4
        + K.a ^ 6 * Real.cos (x 2) ^ 2 + K.a ^ 4 * Real.cos (x 2) ^ 4 * x 1 ^ 2 - K.a ^ 4 * x 1 ^ 2
        + 3 * K.a ^ 2 * Real.cos (x 2) ^ 2 * x 1 ^ 4 - 3 * K.a ^ 2 * x 1 ^ 4)
        / (K.sigma (x 1) (x 2) ^ 2 * K.delta (x 1) ^ 2) := by
  let c0 : ℝ := -K.M * K.a ^ 2 * Real.cos (x 2) ^ 2
  let c1 : ℝ := K.a ^ 2 * Real.cos (x 2) ^ 2 - K.a ^ 2
  have hfun : (fun s => K.christoffel (Function.update x 1 s) 1 1 1)
      = fun s => (-(c0 + K.M * s ^ 2 + c1 * s)) / (K.sigma s (x 2) * K.delta s) := by
    funext s
    simp only [christoffel, c0, c1, Function.update_self,
      Function.update_of_ne (by decide : (2 : Fin 4) ≠ 1)]
    norm_num
    ring
  have hnum : HasDerivAt (fun s => -(c0 + K.M * s ^ 2 + c1 * s))
      (-(2 * K.M * x 1 + c1)) (x 1) := by
    have h1 := ((hasDerivAt_pow 2 (x 1)).const_mul K.M).const_add c0
    have h2 := (hasDerivAt_id' (x 1)).const_mul c1
    exact ((h1.fun_add h2).fun_neg).congr_deriv (by ring)
  have hden := (K.hasDerivAt_sigma_r (x 1) (x 2)).fun_mul (K.hasDerivAt_delta_r (x 1))
  have hd := hnum.fun_div hden (mul_ne_zero hsig hdel)
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hd)]
  field_simp [hsig, hdel]
  simp only [sigma, delta, c0, c1]
  ring

private lemma christoffelDeriv_r_12 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) :
    coordDeriv 1 (fun y => K.christoffel y 1 1 2) x =
      2 * K.a ^ 2 * Real.cos (x 2) * x 1 * Real.sin (x 2) / K.sigma (x 1) (x 2) ^ 2 := by
  have hfun : (fun s => K.christoffel (Function.update x 1 s) 1 1 2)
      = fun s => -K.a ^ 2 * Real.cos (x 2) * Real.sin (x 2) / K.sigma s (x 2) := by
    funext s; simp [christoffel]
  have hd := (hasDerivAt_const (x 1) (-K.a ^ 2 * Real.cos (x 2) * Real.sin (x 2))).fun_div
    (K.hasDerivAt_sigma_r (x 1) (x 2)) hsig
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hd)]
  ring

private lemma christoffelDeriv_r_22 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) :
    coordDeriv 1 (fun y => K.christoffel y 1 2 2) x =
      -(-4 * K.M * K.a ^ 2 * Real.cos (x 2) ^ 2 * x 1 + K.a ^ 4 * Real.cos (x 2) ^ 2
        + 3 * K.a ^ 2 * Real.cos (x 2) ^ 2 * x 1 ^ 2 - K.a ^ 2 * x 1 ^ 2 + x 1 ^ 4)
        / K.sigma (x 1) (x 2) ^ 2 := by
  have hfun : (fun s => K.christoffel (Function.update x 1 s) 1 2 2)
      = fun s => (-s * K.delta s) / K.sigma s (x 2) := by funext s; simp [christoffel]
  have hnum := (hasDerivAt_id' (x 1)).fun_neg.fun_mul (K.hasDerivAt_delta_r (x 1))
  have hd := hnum.fun_div (K.hasDerivAt_sigma_r (x 1) (x 2)) hsig
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hd)]
  field_simp [hsig]
  simp only [sigma, delta]
  ring

private lemma christoffelDeriv_r_33 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) :
    coordDeriv 1 (fun y => K.christoffel y 1 3 3) x =
      (-Real.sin (x 2) ^ 2 * (2 * K.M ^ 2 * K.a ^ 6 * Real.cos (x 2) ^ 6
        - 2 * K.M ^ 2 * K.a ^ 6 * Real.cos (x 2) ^ 4
        - 16 * K.M ^ 2 * K.a ^ 4 * Real.cos (x 2) ^ 4 * x 1 ^ 2
        + 16 * K.M ^ 2 * K.a ^ 4 * Real.cos (x 2) ^ 2 * x 1 ^ 2
        + 6 * K.M ^ 2 * K.a ^ 2 * Real.cos (x 2) ^ 2 * x 1 ^ 4 - 6 * K.M ^ 2 * K.a ^ 2 * x 1 ^ 4
        - 6 * K.M * K.a ^ 6 * Real.cos (x 2) ^ 6 * x 1
        + 10 * K.M * K.a ^ 6 * Real.cos (x 2) ^ 4 * x 1
        - 8 * K.M * K.a ^ 6 * Real.cos (x 2) ^ 2 * x 1
        - 12 * K.M * K.a ^ 4 * Real.cos (x 2) ^ 2 * x 1 ^ 3 + 4 * K.M * K.a ^ 4 * x 1 ^ 3
        - 6 * K.M * K.a ^ 2 * Real.cos (x 2) ^ 2 * x 1 ^ 5 + 2 * K.M * K.a ^ 2 * x 1 ^ 5
        + K.a ^ 8 * Real.cos (x 2) ^ 6 + 3 * K.a ^ 6 * Real.cos (x 2) ^ 6 * x 1 ^ 2
        + K.a ^ 6 * Real.cos (x 2) ^ 4 * x 1 ^ 2 + 7 * K.a ^ 4 * Real.cos (x 2) ^ 4 * x 1 ^ 4
        - K.a ^ 4 * Real.cos (x 2) ^ 2 * x 1 ^ 4 + 5 * K.a ^ 2 * Real.cos (x 2) ^ 2 * x 1 ^ 6
        - K.a ^ 2 * x 1 ^ 6 + x 1 ^ 8)) / K.sigma (x 1) (x 2) ^ 4 := by
  let k0 : ℝ := -K.M * K.a ^ 4 * Real.cos (x 2) ^ 4 + K.M * K.a ^ 4 * Real.cos (x 2) ^ 2
  let k2 : ℝ := K.M * K.a ^ 2 * Real.cos (x 2) ^ 2 - K.M * K.a ^ 2
  let k1 : ℝ := K.a ^ 4 * Real.cos (x 2) ^ 4
  let k3 : ℝ := 2 * K.a ^ 2 * Real.cos (x 2) ^ 2
  let P : ℝ → ℝ := fun s => k0 + k1 * s + k2 * s ^ 2 + k3 * s ^ 3 + s ^ 5
  let P' : ℝ := k1 + 2 * k2 * x 1 + 3 * k3 * x 1 ^ 2 + 5 * x 1 ^ 4
  have hP : HasDerivAt P P' (x 1) := by
    have h1 := ((hasDerivAt_id' (x 1)).const_mul k1).const_add k0
    have h2 := ((hasDerivAt_pow 2 (x 1)).const_mul k2)
    have h3 := ((hasDerivAt_pow 3 (x 1)).const_mul k3)
    have h5 := hasDerivAt_pow 5 (x 1)
    exact (((h1.fun_add h2).fun_add h3).fun_add h5).congr_deriv (by simp only [P']; ring)
  have hfun : (fun s => K.christoffel (Function.update x 1 s) 1 3 3)
      = fun s => -(Real.sin (x 2) ^ 2) * (K.delta s * P s / K.sigma s (x 2) ^ 3) := by
    funext s
    simp only [christoffel, P, k0, k1, k2, k3, Function.update_self,
      Function.update_of_ne (by decide : (2 : Fin 4) ≠ 1)]
    norm_num
    ring
  have hd := (((K.hasDerivAt_delta_r (x 1)).fun_mul hP).fun_div
    (hasDerivAt_sigmaPow3_r K (x 1) (x 2)) (pow_ne_zero 3 hsig)).const_mul
      (-(Real.sin (x 2) ^ 2))
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hd)]
  field_simp [hsig]
  simp only [sigma, delta, P, P', k0, k1, k2, k3]
  ring

private lemma christoffelDeriv_theta_00 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) :
    coordDeriv 2 (fun y => K.christoffel y 2 0 0) x =
      2 * K.M * K.a ^ 2 * x 1 * (-K.a ^ 2 * Real.cos (x 2) ^ 4
        - 5 * K.a ^ 2 * Real.cos (x 2) ^ 2 * Real.sin (x 2) ^ 2
        - Real.cos (x 2) ^ 2 * x 1 ^ 2 + x 1 ^ 2 * Real.sin (x 2) ^ 2)
        / K.sigma (x 1) (x 2) ^ 4 := by
  have hfun : (fun t => K.christoffel (Function.update x 2 t) 2 0 0)
      = fun t => (-2 * K.M * K.a ^ 2 * x 1)
        * (Real.cos t * Real.sin t / K.sigma (x 1) t ^ 3) := by
    funext t
    simp only [christoffel, Function.update_self,
      Function.update_of_ne (by decide : (1 : Fin 4) ≠ 2)]
    norm_num
    ring
  have hcs := (Real.hasDerivAt_cos (x 2)).fun_mul (Real.hasDerivAt_sin (x 2))
  have hd := (hcs.fun_div (hasDerivAt_sigmaPow3_theta K (x 1) (x 2))
    (pow_ne_zero 3 hsig)).const_mul (-2 * K.M * K.a ^ 2 * x 1)
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hd)]
  field_simp [hsig]
  simp only [sigma]
  ring

private lemma christoffelDeriv_theta_03 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) :
    coordDeriv 2 (fun y => K.christoffel y 2 0 3) x =
      -2 * K.M * K.a * x 1 * (K.a ^ 2 + x 1 ^ 2) * (-K.a ^ 2 * Real.cos (x 2) ^ 4
        - 5 * K.a ^ 2 * Real.cos (x 2) ^ 2 * Real.sin (x 2) ^ 2
        - Real.cos (x 2) ^ 2 * x 1 ^ 2 + x 1 ^ 2 * Real.sin (x 2) ^ 2)
        / K.sigma (x 1) (x 2) ^ 4 := by
  have hfun : (fun t => K.christoffel (Function.update x 2 t) 2 0 3)
      = fun t => (2 * K.M * K.a * x 1 * (K.a ^ 2 + x 1 ^ 2))
        * (Real.cos t * Real.sin t / K.sigma (x 1) t ^ 3) := by
    funext t
    simp only [christoffel, Function.update_self,
      Function.update_of_ne (by decide : (1 : Fin 4) ≠ 2)]
    norm_num
    ring
  have hcs := (Real.hasDerivAt_cos (x 2)).fun_mul (Real.hasDerivAt_sin (x 2))
  have hd := (hcs.fun_div (hasDerivAt_sigmaPow3_theta K (x 1) (x 2))
    (pow_ne_zero 3 hsig)).const_mul (2 * K.M * K.a * x 1 * (K.a ^ 2 + x 1 ^ 2))
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hd)]
  field_simp [hsig]
  simp only [sigma]
  ring

private lemma christoffelDeriv_theta_11 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) (hdel : K.delta (x 1) ≠ 0) :
    coordDeriv 2 (fun y => K.christoffel y 2 1 1) x =
      -K.a ^ 2 * (-K.a ^ 2 * Real.cos (x 2) ^ 4
        - K.a ^ 2 * Real.cos (x 2) ^ 2 * Real.sin (x 2) ^ 2
        - Real.cos (x 2) ^ 2 * x 1 ^ 2 + x 1 ^ 2 * Real.sin (x 2) ^ 2)
        / (K.sigma (x 1) (x 2) ^ 2 * K.delta (x 1)) := by
  have hfun : (fun t => K.christoffel (Function.update x 2 t) 2 1 1)
      = fun t => (K.a ^ 2 / K.delta (x 1)) * (Real.cos t * Real.sin t / K.sigma (x 1) t) := by
    funext t
    simp only [christoffel, Function.update_self,
      Function.update_of_ne (by decide : (1 : Fin 4) ≠ 2)]
    norm_num
    ring
  have hcs := (Real.hasDerivAt_cos (x 2)).fun_mul (Real.hasDerivAt_sin (x 2))
  have hd := (hcs.fun_div (K.hasDerivAt_sigma_theta (x 1) (x 2)) hsig).const_mul
    (K.a ^ 2 / K.delta (x 1))
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hd)]
  field_simp [hsig, hdel]
  simp only [sigma]
  ring

private lemma christoffelDeriv_theta_12 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) :
    coordDeriv 2 (fun y => K.christoffel y 2 1 2) x =
      2 * K.a ^ 2 * Real.cos (x 2) * x 1 * Real.sin (x 2) / K.sigma (x 1) (x 2) ^ 2 := by
  have hfun : (fun t => K.christoffel (Function.update x 2 t) 2 1 2)
      = fun t => x 1 / K.sigma (x 1) t := by funext t; simp [christoffel]
  have hd := (hasDerivAt_const (x 2) (x 1)).fun_div
    (K.hasDerivAt_sigma_theta (x 1) (x 2)) hsig
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hd)]
  ring

private lemma christoffelDeriv_theta_22 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) :
    coordDeriv 2 (fun y => K.christoffel y 2 2 2) x =
      K.a ^ 2 * (-K.a ^ 2 * Real.cos (x 2) ^ 4
        - K.a ^ 2 * Real.cos (x 2) ^ 2 * Real.sin (x 2) ^ 2
        - Real.cos (x 2) ^ 2 * x 1 ^ 2 + x 1 ^ 2 * Real.sin (x 2) ^ 2)
        / K.sigma (x 1) (x 2) ^ 2 := by
  have hfun : (fun t => K.christoffel (Function.update x 2 t) 2 2 2)
      = fun t => (-K.a ^ 2) * (Real.cos t * Real.sin t / K.sigma (x 1) t) := by
    funext t
    simp only [christoffel, Function.update_self,
      Function.update_of_ne (by decide : (1 : Fin 4) ≠ 2)]
    norm_num
    ring
  have hcs := (Real.hasDerivAt_cos (x 2)).fun_mul (Real.hasDerivAt_sin (x 2))
  have hd := (hcs.fun_div (K.hasDerivAt_sigma_theta (x 1) (x 2)) hsig).const_mul (-K.a ^ 2)
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hd)]
  field_simp [hsig]
  simp only [sigma]
  ring

private lemma christoffelDeriv_theta_33 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) :
    coordDeriv 2 (fun y => K.christoffel y 2 3 3) x =
      (2 * K.M * K.a ^ 6 * Real.cos (x 2) ^ 8 * x 1
        + 2 * K.M * K.a ^ 6 * Real.cos (x 2) ^ 6 * x 1 * Real.sin (x 2) ^ 2
        - 2 * K.M * K.a ^ 6 * Real.cos (x 2) ^ 4 * x 1
        - 10 * K.M * K.a ^ 6 * Real.cos (x 2) ^ 2 * x 1 * Real.sin (x 2) ^ 2
        + 6 * K.M * K.a ^ 4 * Real.cos (x 2) ^ 6 * x 1 ^ 3
        + 2 * K.M * K.a ^ 4 * Real.cos (x 2) ^ 4 * x 1 ^ 3 * Real.sin (x 2) ^ 2
        - 4 * K.M * K.a ^ 4 * Real.cos (x 2) ^ 4 * x 1 ^ 3
        - 20 * K.M * K.a ^ 4 * Real.cos (x 2) ^ 2 * x 1 ^ 3 * Real.sin (x 2) ^ 2
        - 2 * K.M * K.a ^ 4 * Real.cos (x 2) ^ 2 * x 1 ^ 3
        + 2 * K.M * K.a ^ 4 * x 1 ^ 3 * Real.sin (x 2) ^ 2
        + 4 * K.M * K.a ^ 2 * Real.cos (x 2) ^ 4 * x 1 ^ 5
        - 12 * K.M * K.a ^ 2 * Real.cos (x 2) ^ 2 * x 1 ^ 5 * Real.sin (x 2) ^ 2
        - 4 * K.M * K.a ^ 2 * Real.cos (x 2) ^ 2 * x 1 ^ 5
        + 4 * K.M * K.a ^ 2 * x 1 ^ 5 * Real.sin (x 2) ^ 2
        - K.a ^ 8 * Real.cos (x 2) ^ 8 - K.a ^ 8 * Real.cos (x 2) ^ 6 * Real.sin (x 2) ^ 2
        - K.a ^ 6 * Real.cos (x 2) ^ 8 * x 1 ^ 2
        - K.a ^ 6 * Real.cos (x 2) ^ 6 * x 1 ^ 2 * Real.sin (x 2) ^ 2
        - 3 * K.a ^ 6 * Real.cos (x 2) ^ 6 * x 1 ^ 2
        - K.a ^ 6 * Real.cos (x 2) ^ 4 * x 1 ^ 2 * Real.sin (x 2) ^ 2
        - 3 * K.a ^ 4 * Real.cos (x 2) ^ 6 * x 1 ^ 4
        - K.a ^ 4 * Real.cos (x 2) ^ 4 * x 1 ^ 4 * Real.sin (x 2) ^ 2
        - 3 * K.a ^ 4 * Real.cos (x 2) ^ 4 * x 1 ^ 4
        + K.a ^ 4 * Real.cos (x 2) ^ 2 * x 1 ^ 4 * Real.sin (x 2) ^ 2
        - 3 * K.a ^ 2 * Real.cos (x 2) ^ 4 * x 1 ^ 6
        + K.a ^ 2 * Real.cos (x 2) ^ 2 * x 1 ^ 6 * Real.sin (x 2) ^ 2
        - K.a ^ 2 * Real.cos (x 2) ^ 2 * x 1 ^ 6
        + K.a ^ 2 * x 1 ^ 6 * Real.sin (x 2) ^ 2
        - Real.cos (x 2) ^ 2 * x 1 ^ 8 + x 1 ^ 8 * Real.sin (x 2) ^ 2)
        / K.sigma (x 1) (x 2) ^ 4 := by
  let c4 : ℝ := -2 * K.M * K.a ^ 4 * x 1 + K.a ^ 6 + K.a ^ 4 * x 1 ^ 2
  let c2 : ℝ := -4 * K.M * K.a ^ 2 * x 1 ^ 3 + 2 * K.a ^ 4 * x 1 ^ 2 + 2 * K.a ^ 2 * x 1 ^ 4
  let c0 : ℝ := 2 * K.M * K.a ^ 4 * x 1 + 4 * K.M * K.a ^ 2 * x 1 ^ 3
    + K.a ^ 2 * x 1 ^ 4 + x 1 ^ 6
  let Q : ℝ → ℝ := fun t => c4 * Real.cos t ^ 4 + c2 * Real.cos t ^ 2 + c0
  let Q' : ℝ := -4 * c4 * Real.cos (x 2) ^ 3 * Real.sin (x 2)
    - 2 * c2 * Real.cos (x 2) * Real.sin (x 2)
  have hQ : HasDerivAt Q Q' (x 2) := by
    have h4 := (((hasDerivAt_pow 4 (Real.cos (x 2))).comp (x 2)
      (Real.hasDerivAt_cos (x 2))).const_mul c4)
    have h2 := (((hasDerivAt_pow 2 (Real.cos (x 2))).comp (x 2)
      (Real.hasDerivAt_cos (x 2))).const_mul c2)
    exact ((h4.fun_add h2).fun_add (hasDerivAt_const (x 2) c0)).congr_deriv
      (by simp only [Q']; ring)
  have hfun : (fun t => K.christoffel (Function.update x 2 t) 2 3 3)
      = fun t => -((Real.cos t * Real.sin t) * Q t / K.sigma (x 1) t ^ 3) := by
    funext t
    simp only [christoffel, Q, c4, c2, c0, Function.update_self,
      Function.update_of_ne (by decide : (1 : Fin 4) ≠ 2)]
    norm_num
    ring
  have hcs := (Real.hasDerivAt_cos (x 2)).fun_mul (Real.hasDerivAt_sin (x 2))
  have hd := (((hcs.fun_mul hQ).fun_div
    (hasDerivAt_sigmaPow3_theta K (x 1) (x 2)) (pow_ne_zero 3 hsig)).fun_neg)
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hd)]
  field_simp [hsig]
  simp only [sigma, Q, c4, c2, c0]
  ring

/-!

## B. Ricci flatness through the coordinate pipeline

Contracting all Riemann contributions using the trace derivative identities shows that every
component `Ric_{σ ν}` vanishes across both the `(t, φ)` and `(r, θ)` blocks and the off-block
entries.

-/

private lemma sum_pd_christoffel_diag (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) (hdel : K.delta (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0)
    (σ ν : Fin 4) :
    (∑ ρ : Fin 4, coordDeriv ν (fun y => K.christoffel y ρ ρ σ) x)
      = if ν = 1 ∨ ν = 2 then coordDeriv ν (fun y => K.christoffelTrace y σ) x else 0 := by
  have hcongrTr : (fun y => ∑ ρ : Fin 4, K.christoffel y ρ ρ σ) =ᶠ[nhds x]
      fun y => K.christoffelTrace y σ := by
    have hcSig : Continuous (fun y : Fin 4 → ℝ => K.sigma (y 1) (y 2)) := by
      simp only [sigma]; fun_prop
    have hcDel : Continuous (fun y : Fin 4 → ℝ => K.delta (y 1)) := by
      simp only [delta]; fun_prop
    have hcS : Continuous (fun y : Fin 4 → ℝ => Real.sin (y 2)) := by fun_prop
    filter_upwards [(hcSig.continuousAt.eventually_ne hsig).and
      ((hcDel.continuousAt.eventually_ne hdel).and (hcS.continuousAt.eventually_ne hs))]
      with y ⟨h1, h2, h3⟩
    exact K.sum_christoffel_trace y h1 h2 h3 σ
  have hν : ν = 0 ∨ ν = 1 ∨ ν = 2 ∨ ν = 3 := by fin_cases ν <;> decide
  rcases hν with rfl | rfl | rfl | rfl
  · simp [K.pd_christoffel_const_03 x 0 (Or.inl rfl)]
  · simp only [Fin.isValue, true_or, ↓reduceIte]
    rw [← coordDeriv_sum 1 (fun ρ y => K.christoffel y ρ ρ σ) x
      (fun ρ => differentiableAt_christoffel_r K x hsig hdel hs ρ ρ σ)]
    exact coordDeriv_congr_nhds 1 x hcongrTr
  · simp only [Fin.isValue, or_true, ↓reduceIte]
    rw [← coordDeriv_sum 2 (fun ρ y => K.christoffel y ρ ρ σ) x
      (fun ρ => differentiableAt_christoffel_theta K x hsig hdel hs ρ ρ σ)]
    exact coordDeriv_congr_nhds 2 x hcongrTr
  · simp [K.pd_christoffel_const_03 x 3 (Or.inr rfl)]

private lemma ricciOf_eq_sum (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) (hdel : K.delta (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0)
    (σ ν : Fin 4) :
    Pipeline.ricciTensorOf K.metric K.metricInv x σ ν
      = coordDeriv 1 (fun y => K.christoffel y 1 ν σ) x
        + coordDeriv 2 (fun y => K.christoffel y 2 ν σ) x
        - (if ν = 1 ∨ ν = 2 then coordDeriv ν (fun y => K.christoffelTrace y σ) x else 0)
        + ∑ lam : Fin 4, K.christoffelTrace x lam * K.christoffel x lam ν σ
        - ∑ ρ : Fin 4, ∑ lam : Fin 4,
          K.christoffel x ρ ν lam * K.christoffel x lam ρ σ := by
  have hev : ∀ k i j,
      (fun y => Pipeline.christoffel K.metric K.metricInv y k i j)
        =ᶠ[nhds x] fun y => K.christoffel y k i j :=
    K.eventually_christoffel_eq x hsig hdel hs
  have hpt : ∀ k i j,
      Pipeline.christoffel K.metric K.metricInv x k i j = K.christoffel x k i j :=
    K.christoffel_eq x hsig hdel hs
  have hpd : ∀ μ k i j,
      coordDeriv μ (fun y => Pipeline.christoffel K.metric K.metricInv y k i j) x
        = coordDeriv μ (fun y => K.christoffel y k i j) x :=
    fun μ k i j => coordDeriv_congr_nhds μ x (hev k i j)
  have hsumG : ∀ lam, (∑ ρ : Fin 4, K.christoffel x ρ ρ lam) = K.christoffelTrace x lam :=
    K.sum_christoffel_trace x hsig hdel hs
  have htr_pd := sum_pd_christoffel_diag K x hsig hdel hs σ ν
  simp only [Pipeline.ricciTensorOf, Pipeline.riemann, hpd, hpt, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]
  have h1 : (∑ ρ : Fin 4, coordDeriv ρ (fun y => K.christoffel y ρ ν σ) x)
      = coordDeriv 1 (fun y => K.christoffel y 1 ν σ) x
        + coordDeriv 2 (fun y => K.christoffel y 2 ν σ) x := by
    simp [Fin.sum_univ_four, K.pd_christoffel_const_03 x 0 (Or.inl rfl),
      K.pd_christoffel_const_03 x 3 (Or.inr rfl)]
  have h3 : (∑ ρ : Fin 4, ∑ lam : Fin 4,
    K.christoffel x ρ ρ lam * K.christoffel x lam ν σ)
      = ∑ lam : Fin 4, K.christoffelTrace x lam * K.christoffel x lam ν σ := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun lam _ => ?_
    rw [← Finset.sum_mul, hsumG lam]
  rw [h1, htr_pd, h3]
  ring

private lemma christoffel_swap_slice (K : KerrSpacetime) (k i j : Fin 4) :
    (fun y => K.christoffel y k i j) = fun y => K.christoffel y k j i :=
  funext fun y => K.christoffel_symm y k i j

private lemma sin_pow_four_eq (θ : ℝ) :
    Real.sin θ ^ 4 = (1 - Real.cos θ ^ 2) ^ 2 := by
  rw [show Real.sin θ ^ 4 = (Real.sin θ ^ 2) ^ 2 by ring, Real.sin_sq]

local macro "kerr_ricci_clear" : tactic =>
  `(tactic| {
    simp only [Fin.sum_univ_four, KerrSpacetime.christoffelTrace, KerrSpacetime.christoffel]
    norm_num
    field_simp
    simp -failIfUnchanged only [KerrSpacetime.sigma, KerrSpacetime.delta, Real.sin_sq,
      sin_pow_four_eq]
    ring
  })

private lemma ricciOf_00 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) (hdel : K.delta (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0) :
    Pipeline.ricciTensorOf K.metric K.metricInv x 0 0 = 0 := by
  rw [ricciOf_eq_sum K x hsig hdel hs 0 0, christoffelDeriv_r_00 K x hsig hdel,
    christoffelDeriv_theta_00 K x hsig]
  kerr_ricci_clear

private lemma ricciOf_03 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) (hdel : K.delta (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0) :
    Pipeline.ricciTensorOf K.metric K.metricInv x 0 3 = 0 := by
  rw [ricciOf_eq_sum K x hsig hdel hs 0 3,
    christoffel_swap_slice K 1 3 0, christoffel_swap_slice K 2 3 0,
    christoffelDeriv_r_03 K x hsig, christoffelDeriv_theta_03 K x hsig]
  kerr_ricci_clear

private lemma ricciOf_30 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) (hdel : K.delta (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0) :
    Pipeline.ricciTensorOf K.metric K.metricInv x 3 0 = 0 := by
  rw [ricciOf_eq_sum K x hsig hdel hs 3 0, christoffelDeriv_r_03 K x hsig,
    christoffelDeriv_theta_03 K x hsig]
  kerr_ricci_clear

private lemma ricciOf_11 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) (hdel : K.delta (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0) :
    Pipeline.ricciTensorOf K.metric K.metricInv x 1 1 = 0 := by
  rw [ricciOf_eq_sum K x hsig hdel hs 1 1, christoffelDeriv_r_11 K x hsig hdel,
    christoffelDeriv_theta_11 K x hsig hdel]
  simp only [Fin.isValue, ↓reduceIte, true_or]
  rw [K.christoffelTraceDeriv_rr x hsig]
  kerr_ricci_clear

private lemma ricciOf_12 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) (hdel : K.delta (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0) :
    Pipeline.ricciTensorOf K.metric K.metricInv x 1 2 = 0 := by
  rw [ricciOf_eq_sum K x hsig hdel hs 1 2,
    christoffel_swap_slice K 1 2 1, christoffel_swap_slice K 2 2 1,
    christoffelDeriv_r_12 K x hsig, christoffelDeriv_theta_12 K x hsig]
  simp only [Fin.isValue, ↓reduceIte, or_true]
  rw [K.christoffelTraceDeriv_thetar x hsig]
  kerr_ricci_clear

private lemma ricciOf_21 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) (hdel : K.delta (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0) :
    Pipeline.ricciTensorOf K.metric K.metricInv x 2 1 = 0 := by
  rw [ricciOf_eq_sum K x hsig hdel hs 2 1, christoffelDeriv_r_12 K x hsig,
    christoffelDeriv_theta_12 K x hsig]
  simp only [Fin.isValue, ↓reduceIte, true_or]
  rw [K.christoffelTraceDeriv_rtheta x hsig]
  kerr_ricci_clear

private lemma ricciOf_22 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) (hdel : K.delta (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0) :
    Pipeline.ricciTensorOf K.metric K.metricInv x 2 2 = 0 := by
  rw [ricciOf_eq_sum K x hsig hdel hs 2 2, christoffelDeriv_r_22 K x hsig,
    christoffelDeriv_theta_22 K x hsig]
  simp only [Fin.isValue, ↓reduceIte, or_true]
  rw [K.christoffelTraceDeriv_thetatheta x hsig hs]
  kerr_ricci_clear

private lemma ricciOf_33 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) (hdel : K.delta (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0) :
    Pipeline.ricciTensorOf K.metric K.metricInv x 3 3 = 0 := by
  rw [ricciOf_eq_sum K x hsig hdel hs 3 3, christoffelDeriv_r_33 K x hsig,
    christoffelDeriv_theta_33 K x hsig]
  kerr_ricci_clear

private lemma christoffelDeriv_zero_of_const (K : KerrSpacetime) (x : Fin 4 → ℝ) (μ k i j : Fin 4)
    (h : ∀ s, K.christoffel (Function.update x μ s) k i j = 0) :
    coordDeriv μ (fun y => K.christoffel y k i j) x = 0 :=
  coordDeriv_const_slice μ 0 h

private lemma christoffelTraceDeriv_zero_of_const (K : KerrSpacetime) (x : Fin 4 → ℝ) (μ σ : Fin 4)
    (h : ∀ s, K.christoffelTrace (Function.update x μ s) σ = 0) :
    coordDeriv μ (fun y => K.christoffelTrace y σ) x = 0 :=
  coordDeriv_const_slice μ 0 h

private lemma ricciOf_offblock (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) (hdel : K.delta (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0)
    (σ ν : Fin 4)
    (hoff : (σ = 0 ∧ (ν = 1 ∨ ν = 2)) ∨ ((σ = 1 ∨ σ = 2) ∧ (ν = 0 ∨ ν = 3))
      ∨ (σ = 3 ∧ (ν = 1 ∨ ν = 2))) :
    Pipeline.ricciTensorOf K.metric K.metricInv x σ ν = 0 := by
  rw [ricciOf_eq_sum K x hsig hdel hs σ ν]
  rcases hoff with ⟨rfl, rfl | rfl⟩ | ⟨rfl | rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩
  all_goals
    rw [christoffelDeriv_zero_of_const K x 1 1 _ _ (fun _ => by simp [christoffel]),
      christoffelDeriv_zero_of_const K x 2 2 _ _ (fun _ => by simp [christoffel])]
    simp only [Fin.isValue, Fin.reduceEq, or_self, true_or, or_true, ↓reduceIte]
    try rw [christoffelTraceDeriv_zero_of_const K x _ _ (fun _ => by simp [christoffelTrace])]
    simp only [Fin.sum_univ_four, christoffelTrace, christoffel]
    norm_num

/-- The Boyer–Lindquist Kerr metric has identically vanishing Ricci tensor at every regular
coordinate point (`Σ ≠ 0`, `Δ ≠ 0`, `sin θ ≠ 0`) through `GeneralRelativity.Pipeline`. -/
lemma ricciTensorOf_eq_zero (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) (hdel : K.delta (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0)
    (σ ν : Fin 4) :
    Pipeline.ricciTensorOf K.metric K.metricInv x σ ν = 0 := by
  fin_cases σ <;> fin_cases ν
  · exact ricciOf_00 K x hsig hdel hs
  · exact ricciOf_offblock K x hsig hdel hs 0 1 (by simp)
  · exact ricciOf_offblock K x hsig hdel hs 0 2 (by simp)
  · exact ricciOf_03 K x hsig hdel hs
  · exact ricciOf_offblock K x hsig hdel hs 1 0 (by simp)
  · exact ricciOf_11 K x hsig hdel hs
  · exact ricciOf_12 K x hsig hdel hs
  · exact ricciOf_offblock K x hsig hdel hs 1 3 (by simp)
  · exact ricciOf_offblock K x hsig hdel hs 2 0 (by simp)
  · exact ricciOf_21 K x hsig hdel hs
  · exact ricciOf_22 K x hsig hdel hs
  · exact ricciOf_offblock K x hsig hdel hs 2 3 (by simp)
  · exact ricciOf_30 K x hsig hdel hs
  · exact ricciOf_offblock K x hsig hdel hs 3 1 (by simp)
  · exact ricciOf_offblock K x hsig hdel hs 3 2 (by simp)
  · exact ricciOf_33 K x hsig hdel hs

/-!

## C. Scalar curvature and vacuum Einstein equations

Contraction of the vanishing Ricci tensor yields zero scalar curvature and vacuum Einstein
equations `G = 0`.

-/

/-- The Boyer–Lindquist Kerr metric has identically vanishing scalar curvature `R = 0`. -/
lemma ricciScalarOf_eq_zero (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) (hdel : K.delta (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0) :
    Pipeline.ricciScalarOf K.metric K.metricInv x = 0 := by
  simp [Pipeline.ricciScalarOf, K.ricciTensorOf_eq_zero x hsig hdel hs]

/-- Vacuum Einstein equations for the Kerr black hole through `GeneralRelativity.Pipeline`:
`G_{i j} = 0` for all `i, j : Fin 4`. -/
lemma einsteinTensorOf_eq_zero (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) (hdel : K.delta (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0)
    (i j : Fin 4) :
    Pipeline.einsteinTensorOf K.metric K.metricInv x i j = 0 := by
  simp [Pipeline.einsteinTensorOf, K.ricciTensorOf_eq_zero x hsig hdel hs,
    K.ricciScalarOf_eq_zero x hsig hdel hs]

end KerrSpacetime

end Kerr

end GeneralRelativity
