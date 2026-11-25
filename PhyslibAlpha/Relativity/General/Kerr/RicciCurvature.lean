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

Full pipeline proof that the Boyer–Lindquist Kerr metric is Ricci flat, scalar flat, and satisfies
the vacuum Einstein equation `G = 0`.

## i. Overview

Using the coordinate-pipeline Christoffel agreement `christoffel_kerr_eq` and trace identity
`sum_kerrChristoffel_trace` from `Kerr.Christoffel`, this module evaluates all required partial
derivatives of
`kerrChristoffel` and `kerrChristoffelTrace` and proves that `Pipeline.ricciTensorOf (kerrMetric M
a) (kerrMetricInv M a) x σ ν`
vanishes for every coordinate pair `(σ, ν)` at all regular points (`Σ ≠ 0`, `Δ ≠ 0`, `sin θ ≠ 0`).
It immediately follows that `ricciScalarOf` and `einsteinTensorOf` vanish identically.

## ii. Key results

- `kerrRicci`, `kerrEinstein` : Boyer–Lindquist Kerr pipeline Ricci and Einstein tensors.
- `pd_kerrChristoffelTrace_11`, `pd_kerrChristoffelTrace_12`, `pd_kerrChristoffelTrace_21`,
  `pd_kerrChristoffelTrace_22` : partial derivatives of `kerrChristoffelTrace`.
- `ricciTensorOf_kerr_eq_zero` : vacuum Ricci flatness `Ric_{σ ν} = 0` via `Pipeline.ricciTensorOf`.
- `ricciScalarOf_kerr_eq_zero` : vanishing scalar curvature `S = 0`.
- `einsteinTensorOf_kerr_eq_zero` : vacuum Einstein equations `G_{i j} = 0`.

## iii. Table of contents

- A. Trace and Christoffel partial derivatives
- B. Ricci flatness through the coordinate pipeline
- C. Scalar curvature and vacuum Einstein equations

## iv. References

* R. M. Wald, *General Relativity* (1984). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973). [ref: mtw_1973_gravitation]

-/

@[expose] public section

namespace GeneralRelativity

namespace Kerr

open Pipeline

/-!

## A. Trace and Christoffel partial derivatives

-/

/-- Boyer–Lindquist Kerr Ricci tensor computed via `Pipeline.ricciTensorOf`. -/
noncomputable def kerrRicci (M a : ℝ) (x : Fin 4 → ℝ) : Tensor2 4 :=
  ricciTensorOf (kerrMetric M a) (kerrMetricInv M a) x

/-- Boyer–Lindquist Kerr Einstein tensor computed via `Pipeline.einsteinTensorOf`. -/
noncomputable def kerrEinstein (M a : ℝ) (x : Fin 4 → ℝ) : Tensor2 4 :=
  einsteinTensorOf (kerrMetric M a) (kerrMetricInv M a) x

private lemma pd_eq_zero_of (μ : Fin 4) (f : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) (c : ℝ)
    (hf : ∀ s, f (Function.update x μ s) = c) : pd μ f x = 0 := by
  have hfn : (fun s => f (Function.update x μ s)) = fun _ => c := funext hf
  rw [pd, hfn, deriv_const']

private lemma hasDerivAt_sigma3_r (a r θ : ℝ) :
    HasDerivAt (fun s => sigma a s θ ^ 3) (3 * sigma a r θ ^ 2 * (2 * r)) r :=
  ((hasDerivAt_sigma_r a r θ).pow 3).congr_deriv (by ring)

private lemma hasDerivAt_sigma3_th (a r θ : ℝ) :
    HasDerivAt (fun t => sigma a r t ^ 3)
      (3 * sigma a r θ ^ 2 * (-2 * a ^ 2 * Real.cos θ * Real.sin θ)) θ :=
  ((hasDerivAt_sigma_th a r θ).pow 3).congr_deriv (by ring)

private lemma hasDerivAt_cos_mul_sin (θ : ℝ) :
    HasDerivAt (fun t => Real.cos t * Real.sin t)
      ((-Real.sin θ) * Real.sin θ + Real.cos θ * Real.cos θ) θ :=
  (Real.hasDerivAt_cos θ).fun_mul (Real.hasDerivAt_sin θ)

private lemma differentiableAt_kerrG_r' (M a : ℝ) (x : Fin 4 → ℝ)
    (_hsig : sigma a (x 1) (x 2) ≠ 0) (_hdel : delta M a (x 1) ≠ 0) (_hs : Real.sin (x 2) ≠ 0)
    (k i j : Fin 4) :
    DifferentiableAt ℝ (fun s => kerrChristoffel M a (Function.update x 1 s) k i j) (x 1) := by
  have _ : DifferentiableAt ℝ (fun s => sigma a s (x 2)) (x 1) :=
    (hasDerivAt_sigma_r a (x 1) (x 2)).differentiableAt
  have _ : DifferentiableAt ℝ (fun s => delta M a s) (x 1) :=
    (hasDerivAt_delta_r M a (x 1)).differentiableAt
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp only [kerrChristoffel, Function.update_self,
      Function.update_of_ne (by decide : (2 : Fin 4) ≠ 1)] <;>
    norm_num
  all_goals fun_prop (disch := positivity)

private lemma differentiableAt_kerrG_th (M a : ℝ) (x : Fin 4 → ℝ)
    (_hsig : sigma a (x 1) (x 2) ≠ 0) (_hdel : delta M a (x 1) ≠ 0) (_hs : Real.sin (x 2) ≠ 0)
    (k i j : Fin 4) :
    DifferentiableAt ℝ (fun t => kerrChristoffel M a (Function.update x 2 t) k i j) (x 2) := by
  have _ : DifferentiableAt ℝ (fun t => sigma a (x 1) t) (x 2) :=
    (hasDerivAt_sigma_th a (x 1) (x 2)).differentiableAt
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp only [kerrChristoffel, Function.update_self,
      Function.update_of_ne (by decide : (1 : Fin 4) ≠ 2)] <;>
    norm_num
  all_goals fun_prop (disch := positivity)

/-- Partial derivative `∂_r (kerrChristoffelTrace a · 1)`. -/
lemma pd_kerrChristoffelTrace_11 (a : ℝ) (x : Fin 4 → ℝ) (hsig : sigma a (x 1) (x 2) ≠ 0) :
    pd 1 (fun y => kerrChristoffelTrace a y 1) x
      = -2 * (x 1 ^ 2 - a ^ 2 * Real.cos (x 2) ^ 2) / sigma a (x 1) (x 2) ^ 2 := by
  have hfun : (fun s => kerrChristoffelTrace a (Function.update x 1 s) 1)
      = fun s => 2 * s / sigma a s (x 2) := by funext s; simp [kerrChristoffelTrace]
  have hm : HasDerivAt (fun s : ℝ => 2 * s) 2 (x 1) :=
    ((hasDerivAt_const (x 1) 2).fun_mul (hasDerivAt_id (x 1))).congr_deriv (by ring)
  have hd := hm.fun_div (hasDerivAt_sigma_r a (x 1) (x 2)) hsig
  rw [pd, hfun, hd.deriv]
  field_simp [hsig]
  simp only [sigma]
  ring

/-- Partial derivative `∂_θ (kerrChristoffelTrace a · 1)`. -/
lemma pd_kerrChristoffelTrace_21 (a : ℝ) (x : Fin 4 → ℝ) (hsig : sigma a (x 1) (x 2) ≠ 0) :
    pd 2 (fun y => kerrChristoffelTrace a y 1) x
      = 4 * a ^ 2 * Real.cos (x 2) * x 1 * Real.sin (x 2) / sigma a (x 1) (x 2) ^ 2 := by
  have hfun : (fun t => kerrChristoffelTrace a (Function.update x 2 t) 1)
      = fun t => 2 * x 1 / sigma a (x 1) t := by funext t; simp [kerrChristoffelTrace]
  have hd := (hasDerivAt_const (x 2) (2 * x 1)).fun_div (hasDerivAt_sigma_th a (x 1) (x 2)) hsig
  rw [pd, hfun, hd.deriv]
  ring

/-- Partial derivative `∂_r (kerrChristoffelTrace a · 2)`. -/
lemma pd_kerrChristoffelTrace_12 (a : ℝ) (x : Fin 4 → ℝ) (hsig : sigma a (x 1) (x 2) ≠ 0) :
    pd 1 (fun y => kerrChristoffelTrace a y 2) x
      = 4 * a ^ 2 * Real.cos (x 2) * x 1 * Real.sin (x 2) / sigma a (x 1) (x 2) ^ 2 := by
  have hfun : (fun s => kerrChristoffelTrace a (Function.update x 1 s) 2)
      = fun s => Real.cos (x 2) / Real.sin (x 2)
        - 2 * a ^ 2 * Real.cos (x 2) * Real.sin (x 2) / sigma a s (x 2) := by
    funext s; simp [kerrChristoffelTrace]
  have hd1 := hasDerivAt_const (x 1) (Real.cos (x 2) / Real.sin (x 2))
  have hd2 := (hasDerivAt_const (x 1) (2 * a ^ 2 * Real.cos (x 2) * Real.sin (x 2))).fun_div
    (hasDerivAt_sigma_r a (x 1) (x 2)) hsig
  rw [pd, hfun, (hd1.fun_sub hd2).deriv]
  ring

/-- Partial derivative `∂_θ (kerrChristoffelTrace a · 2)`. -/
lemma pd_kerrChristoffelTrace_22 (a : ℝ) (x : Fin 4 → ℝ)
    (hsig : sigma a (x 1) (x 2) ≠ 0) (hs : Real.sin (x 2) ≠ 0) :
    pd 2 (fun y => kerrChristoffelTrace a y 2) x
      = -(1 / Real.sin (x 2) ^ 2)
        - 2 * a ^ 2 * ((Real.cos (x 2) ^ 2 - Real.sin (x 2) ^ 2) * sigma a (x 1) (x 2)
          + 2 * a ^ 2 * Real.cos (x 2) ^ 2 * Real.sin (x 2) ^ 2) / sigma a (x 1) (x 2) ^ 2 := by
  have hfun : (fun t => kerrChristoffelTrace a (Function.update x 2 t) 2)
      = fun t => Real.cos t / Real.sin t
        - 2 * a ^ 2 * (Real.cos t * Real.sin t) / sigma a (x 1) t := by
    funext t; simp only [kerrChristoffelTrace, Fin.isValue, Fin.reduceEq, ↓reduceIte,
      Function.update_self,
      Function.update_of_ne (by decide : (1 : Fin 4) ≠ 2)]; ring
  have hcot := (Real.hasDerivAt_cos (x 2)).fun_div (Real.hasDerivAt_sin (x 2)) hs
  have hnum := (hasDerivAt_cos_mul_sin (x 2)).const_mul (2 * a ^ 2)
  have hq := hnum.fun_div (hasDerivAt_sigma_th a (x 1) (x 2)) hsig
  rw [pd, hfun, (hcot.fun_sub hq).deriv]
  have hsc := Real.sin_sq_add_cos_sq (x 2)
  field_simp [hs, hsig]
  linear_combination -sigma a (x 1) (x 2) ^ 2 * hsc

private lemma hasDerivAt_num_1_00 (M a : ℝ) (x : Fin 4 → ℝ) :
    HasDerivAt (fun s => M * (s ^ 2 - a ^ 2 * Real.cos (x 2) ^ 2) * delta M a s)
      ((M * (2 * x 1)) * delta M a (x 1)
        + M * (x 1 ^ 2 - a ^ 2 * Real.cos (x 2) ^ 2) * (2 * x 1 - 2 * M)) (x 1) := by
  have h1 := (((hasDerivAt_pow 2 (x 1)).sub_const (a ^ 2 * Real.cos (x 2) ^ 2)).const_mul M)
  exact (h1.fun_mul (hasDerivAt_delta_r M a (x 1))).congr_deriv (by ring)

private lemma pd_kerrG_1_00 (M a : ℝ) (x : Fin 4 → ℝ)
    (hsig : sigma a (x 1) (x 2) ≠ 0) (_hdel : delta M a (x 1) ≠ 0) :
    pd 1 (fun y => kerrChristoffel M a y 1 0 0) x =
      (-2 * M * (-M * a ^ 4 * Real.cos (x 2) ^ 4 + 8 * M * a ^ 2 * Real.cos (x 2) ^ 2 * x 1 ^ 2
        - 3 * M * x 1 ^ 4 + a ^ 4 * Real.cos (x 2) ^ 4 * x 1 - 4 * a ^ 4 * Real.cos (x 2) ^ 2 * x 1
        - 4 * a ^ 2 * Real.cos (x 2) ^ 2 * x 1 ^ 3 + 2 * a ^ 2 * x 1 ^ 3 + x 1 ^ 5))
        / sigma a (x 1) (x 2) ^ 4 := by
  have hfun : (fun s => kerrChristoffel M a (Function.update x 1 s) 1 0 0)
      = fun s => (M * (s ^ 2 - a ^ 2 * Real.cos (x 2) ^ 2) * delta M a s)
        / sigma a s (x 2) ^ 3 := by funext s; simp [kerrChristoffel]
  have hd := (hasDerivAt_num_1_00 M a x).fun_div (hasDerivAt_sigma3_r a (x 1) (x 2))
    (pow_ne_zero 3 hsig)
  rw [pd, hfun, hd.deriv]
  field_simp [hsig]
  simp only [sigma, delta]
  ring

private lemma pd_kerrG_1_03 (M a : ℝ) (x : Fin 4 → ℝ) (hsig : sigma a (x 1) (x 2) ≠ 0) :
    pd 1 (fun y => kerrChristoffel M a y 1 0 3) x =
      (2 * M * a * Real.sin (x 2) ^ 2 * (-M * a ^ 4 * Real.cos (x 2) ^ 4
        + 8 * M * a ^ 2 * Real.cos (x 2) ^ 2 * x 1 ^ 2 - 3 * M * x 1 ^ 4
        + a ^ 4 * Real.cos (x 2) ^ 4 * x 1 - 4 * a ^ 4 * Real.cos (x 2) ^ 2 * x 1
        - 4 * a ^ 2 * Real.cos (x 2) ^ 2 * x 1 ^ 3 + 2 * a ^ 2 * x 1 ^ 3 + x 1 ^ 5))
        / sigma a (x 1) (x 2) ^ 4 := by
  have hfun : (fun s => kerrChristoffel M a (Function.update x 1 s) 1 0 3)
      = fun s => -(a * Real.sin (x 2) ^ 2)
        * ((M * (s ^ 2 - a ^ 2 * Real.cos (x 2) ^ 2) * delta M a s) / sigma a s (x 2) ^ 3) := by
    funext s
    simp only [kerrChristoffel, Function.update_self,
      Function.update_of_ne (by decide : (2 : Fin 4) ≠ 1)]
    norm_num
    ring
  have hd := ((hasDerivAt_num_1_00 M a x).fun_div (hasDerivAt_sigma3_r a (x 1) (x 2))
    (pow_ne_zero 3 hsig)).const_mul (-(a * Real.sin (x 2) ^ 2))
  rw [pd, hfun, hd.deriv]
  field_simp [hsig]
  simp only [sigma, delta]
  ring

private lemma pd_kerrG_1_11 (M a : ℝ) (x : Fin 4 → ℝ)
    (hsig : sigma a (x 1) (x 2) ≠ 0) (hdel : delta M a (x 1) ≠ 0) :
    pd 1 (fun y => kerrChristoffel M a y 1 1 1) x =
      (2 * M ^ 2 * a ^ 4 * Real.cos (x 2) ^ 4 + 8 * M ^ 2 * a ^ 2 * Real.cos (x 2) ^ 2 * x 1 ^ 2
        - 2 * M ^ 2 * x 1 ^ 4 - 2 * M * a ^ 4 * Real.cos (x 2) ^ 4 * x 1
        - 4 * M * a ^ 4 * Real.cos (x 2) ^ 2 * x 1 - 8 * M * a ^ 2 * Real.cos (x 2) ^ 2 * x 1 ^ 3
        + 4 * M * a ^ 2 * x 1 ^ 3 + 2 * M * x 1 ^ 5 - a ^ 6 * Real.cos (x 2) ^ 4
        + a ^ 6 * Real.cos (x 2) ^ 2 + a ^ 4 * Real.cos (x 2) ^ 4 * x 1 ^ 2 - a ^ 4 * x 1 ^ 2
        + 3 * a ^ 2 * Real.cos (x 2) ^ 2 * x 1 ^ 4 - 3 * a ^ 2 * x 1 ^ 4)
        / (sigma a (x 1) (x 2) ^ 2 * delta M a (x 1) ^ 2) := by
  let c0 : ℝ := -M * a ^ 2 * Real.cos (x 2) ^ 2
  let c1 : ℝ := a ^ 2 * Real.cos (x 2) ^ 2 - a ^ 2
  have hfun : (fun s => kerrChristoffel M a (Function.update x 1 s) 1 1 1)
      = fun s => (-(c0 + M * s ^ 2 + c1 * s)) / (sigma a s (x 2) * delta M a s) := by
    funext s
    simp only [kerrChristoffel, c0, c1, Function.update_self,
      Function.update_of_ne (by decide : (2 : Fin 4) ≠ 1)]
    norm_num
    ring
  have hnum : HasDerivAt (fun s => -(c0 + M * s ^ 2 + c1 * s)) (-(2 * M * x 1 + c1)) (x 1) := by
    have h1 := ((hasDerivAt_pow 2 (x 1)).const_mul M).const_add c0
    have h2 := (hasDerivAt_id' (x 1)).const_mul c1
    exact ((h1.fun_add h2).fun_neg).congr_deriv (by ring)
  have hden := (hasDerivAt_sigma_r a (x 1) (x 2)).fun_mul (hasDerivAt_delta_r M a (x 1))
  have hd := hnum.fun_div hden (mul_ne_zero hsig hdel)
  rw [pd, hfun, hd.deriv]
  field_simp [hsig, hdel]
  simp only [sigma, delta, c0, c1]
  ring

private lemma pd_kerrG_1_12 (M a : ℝ) (x : Fin 4 → ℝ) (hsig : sigma a (x 1) (x 2) ≠ 0) :
    pd 1 (fun y => kerrChristoffel M a y 1 1 2) x =
      2 * a ^ 2 * Real.cos (x 2) * x 1 * Real.sin (x 2) / sigma a (x 1) (x 2) ^ 2 := by
  have hfun : (fun s => kerrChristoffel M a (Function.update x 1 s) 1 1 2)
      = fun s => -a ^ 2 * Real.cos (x 2) * Real.sin (x 2) / sigma a s (x 2) := by
    funext s; simp [kerrChristoffel]
  have hd := (hasDerivAt_const (x 1) (-a ^ 2 * Real.cos (x 2) * Real.sin (x 2))).fun_div
    (hasDerivAt_sigma_r a (x 1) (x 2)) hsig
  rw [pd, hfun, hd.deriv]
  ring

private lemma pd_kerrG_1_22 (M a : ℝ) (x : Fin 4 → ℝ) (hsig : sigma a (x 1) (x 2) ≠ 0) :
    pd 1 (fun y => kerrChristoffel M a y 1 2 2) x =
      -(-4 * M * a ^ 2 * Real.cos (x 2) ^ 2 * x 1 + a ^ 4 * Real.cos (x 2) ^ 2
        + 3 * a ^ 2 * Real.cos (x 2) ^ 2 * x 1 ^ 2 - a ^ 2 * x 1 ^ 2 + x 1 ^ 4)
        / sigma a (x 1) (x 2) ^ 2 := by
  have hfun : (fun s => kerrChristoffel M a (Function.update x 1 s) 1 2 2)
      = fun s => (-s * delta M a s) / sigma a s (x 2) := by funext s; simp [kerrChristoffel]
  have hnum := (hasDerivAt_id' (x 1)).fun_neg.fun_mul (hasDerivAt_delta_r M a (x 1))
  have hd := hnum.fun_div (hasDerivAt_sigma_r a (x 1) (x 2)) hsig
  rw [pd, hfun, hd.deriv]
  field_simp [hsig]
  simp only [sigma, delta]
  ring

private lemma pd_kerrG_1_33 (M a : ℝ) (x : Fin 4 → ℝ) (hsig : sigma a (x 1) (x 2) ≠ 0) :
    pd 1 (fun y => kerrChristoffel M a y 1 3 3) x =
      (-Real.sin (x 2) ^ 2 * (2 * M ^ 2 * a ^ 6 * Real.cos (x 2) ^ 6
        - 2 * M ^ 2 * a ^ 6 * Real.cos (x 2) ^ 4
        - 16 * M ^ 2 * a ^ 4 * Real.cos (x 2) ^ 4 * x 1 ^ 2
        + 16 * M ^ 2 * a ^ 4 * Real.cos (x 2) ^ 2 * x 1 ^ 2
        + 6 * M ^ 2 * a ^ 2 * Real.cos (x 2) ^ 2 * x 1 ^ 4 - 6 * M ^ 2 * a ^ 2 * x 1 ^ 4
        - 6 * M * a ^ 6 * Real.cos (x 2) ^ 6 * x 1 + 10 * M * a ^ 6 * Real.cos (x 2) ^ 4 * x 1
        - 8 * M * a ^ 6 * Real.cos (x 2) ^ 2 * x 1
        - 12 * M * a ^ 4 * Real.cos (x 2) ^ 2 * x 1 ^ 3 + 4 * M * a ^ 4 * x 1 ^ 3
        - 6 * M * a ^ 2 * Real.cos (x 2) ^ 2 * x 1 ^ 5 + 2 * M * a ^ 2 * x 1 ^ 5
        + a ^ 8 * Real.cos (x 2) ^ 6 + 3 * a ^ 6 * Real.cos (x 2) ^ 6 * x 1 ^ 2
        + a ^ 6 * Real.cos (x 2) ^ 4 * x 1 ^ 2 + 7 * a ^ 4 * Real.cos (x 2) ^ 4 * x 1 ^ 4
        - a ^ 4 * Real.cos (x 2) ^ 2 * x 1 ^ 4 + 5 * a ^ 2 * Real.cos (x 2) ^ 2 * x 1 ^ 6
        - a ^ 2 * x 1 ^ 6 + x 1 ^ 8)) / sigma a (x 1) (x 2) ^ 4 := by
  let k0 : ℝ := -M * a ^ 4 * Real.cos (x 2) ^ 4 + M * a ^ 4 * Real.cos (x 2) ^ 2
  let k2 : ℝ := M * a ^ 2 * Real.cos (x 2) ^ 2 - M * a ^ 2
  let k1 : ℝ := a ^ 4 * Real.cos (x 2) ^ 4
  let k3 : ℝ := 2 * a ^ 2 * Real.cos (x 2) ^ 2
  let P : ℝ → ℝ := fun s => k0 + k1 * s + k2 * s ^ 2 + k3 * s ^ 3 + s ^ 5
  let P' : ℝ := k1 + 2 * k2 * x 1 + 3 * k3 * x 1 ^ 2 + 5 * x 1 ^ 4
  have hP : HasDerivAt P P' (x 1) := by
    have h1 := ((hasDerivAt_id' (x 1)).const_mul k1).const_add k0
    have h2 := ((hasDerivAt_pow 2 (x 1)).const_mul k2)
    have h3 := ((hasDerivAt_pow 3 (x 1)).const_mul k3)
    have h5 := hasDerivAt_pow 5 (x 1)
    exact (((h1.fun_add h2).fun_add h3).fun_add h5).congr_deriv (by simp only [P']; ring)
  have hfun : (fun s => kerrChristoffel M a (Function.update x 1 s) 1 3 3)
      = fun s => -(Real.sin (x 2) ^ 2) * (delta M a s * P s / sigma a s (x 2) ^ 3) := by
    funext s
    simp only [kerrChristoffel, P, k0, k1, k2, k3, Function.update_self,
      Function.update_of_ne (by decide : (2 : Fin 4) ≠ 1)]
    norm_num
    ring
  have hd := (((hasDerivAt_delta_r M a (x 1)).fun_mul hP).fun_div
    (hasDerivAt_sigma3_r a (x 1) (x 2)) (pow_ne_zero 3 hsig)).const_mul (-(Real.sin (x 2) ^ 2))
  rw [pd, hfun, hd.deriv]
  field_simp [hsig]
  simp only [sigma, delta, P, P', k0, k1, k2, k3]
  ring

private lemma pd_kerrG_2_00 (M a : ℝ) (x : Fin 4 → ℝ) (hsig : sigma a (x 1) (x 2) ≠ 0) :
    pd 2 (fun y => kerrChristoffel M a y 2 0 0) x =
      2 * M * a ^ 2 * x 1 * (-a ^ 2 * Real.cos (x 2) ^ 4
        - 5 * a ^ 2 * Real.cos (x 2) ^ 2 * Real.sin (x 2) ^ 2
        - Real.cos (x 2) ^ 2 * x 1 ^ 2 + x 1 ^ 2 * Real.sin (x 2) ^ 2)
        / sigma a (x 1) (x 2) ^ 4 := by
  have hfun : (fun t => kerrChristoffel M a (Function.update x 2 t) 2 0 0)
      = fun t => (-2 * M * a ^ 2 * x 1) * (Real.cos t * Real.sin t / sigma a (x 1) t ^ 3) := by
    funext t
    simp only [kerrChristoffel, Function.update_self,
      Function.update_of_ne (by decide : (1 : Fin 4) ≠ 2)]
    norm_num
    ring
  have hd := ((hasDerivAt_cos_mul_sin (x 2)).fun_div (hasDerivAt_sigma3_th a (x 1) (x 2))
    (pow_ne_zero 3 hsig)).const_mul (-2 * M * a ^ 2 * x 1)
  rw [pd, hfun, hd.deriv]
  field_simp [hsig]
  simp only [sigma]
  ring

private lemma pd_kerrG_2_03 (M a : ℝ) (x : Fin 4 → ℝ) (hsig : sigma a (x 1) (x 2) ≠ 0) :
    pd 2 (fun y => kerrChristoffel M a y 2 0 3) x =
      -2 * M * a * x 1 * (a ^ 2 + x 1 ^ 2) * (-a ^ 2 * Real.cos (x 2) ^ 4
        - 5 * a ^ 2 * Real.cos (x 2) ^ 2 * Real.sin (x 2) ^ 2
        - Real.cos (x 2) ^ 2 * x 1 ^ 2 + x 1 ^ 2 * Real.sin (x 2) ^ 2)
        / sigma a (x 1) (x 2) ^ 4 := by
  have hfun : (fun t => kerrChristoffel M a (Function.update x 2 t) 2 0 3)
      = fun t => (2 * M * a * x 1 * (a ^ 2 + x 1 ^ 2))
        * (Real.cos t * Real.sin t / sigma a (x 1) t ^ 3) := by
    funext t
    simp only [kerrChristoffel, Function.update_self,
      Function.update_of_ne (by decide : (1 : Fin 4) ≠ 2)]
    norm_num
    ring
  have hd := ((hasDerivAt_cos_mul_sin (x 2)).fun_div (hasDerivAt_sigma3_th a (x 1) (x 2))
    (pow_ne_zero 3 hsig)).const_mul (2 * M * a * x 1 * (a ^ 2 + x 1 ^ 2))
  rw [pd, hfun, hd.deriv]
  field_simp [hsig]
  simp only [sigma]
  ring

private lemma pd_kerrG_2_11 (M a : ℝ) (x : Fin 4 → ℝ)
    (hsig : sigma a (x 1) (x 2) ≠ 0) (hdel : delta M a (x 1) ≠ 0) :
    pd 2 (fun y => kerrChristoffel M a y 2 1 1) x =
      -a ^ 2 * (-a ^ 2 * Real.cos (x 2) ^ 4 - a ^ 2 * Real.cos (x 2) ^ 2 * Real.sin (x 2) ^ 2
        - Real.cos (x 2) ^ 2 * x 1 ^ 2 + x 1 ^ 2 * Real.sin (x 2) ^ 2)
        / (sigma a (x 1) (x 2) ^ 2 * delta M a (x 1)) := by
  have hfun : (fun t => kerrChristoffel M a (Function.update x 2 t) 2 1 1)
      = fun t => (a ^ 2 / delta M a (x 1)) * (Real.cos t * Real.sin t / sigma a (x 1) t) := by
    funext t
    simp only [kerrChristoffel, Function.update_self,
      Function.update_of_ne (by decide : (1 : Fin 4) ≠ 2)]
    norm_num
    ring
  have hd := ((hasDerivAt_cos_mul_sin (x 2)).fun_div (hasDerivAt_sigma_th a (x 1) (x 2))
    hsig).const_mul (a ^ 2 / delta M a (x 1))
  rw [pd, hfun, hd.deriv]
  field_simp [hsig, hdel]
  simp only [sigma]
  ring

private lemma pd_kerrG_2_12 (M a : ℝ) (x : Fin 4 → ℝ) (hsig : sigma a (x 1) (x 2) ≠ 0) :
    pd 2 (fun y => kerrChristoffel M a y 2 1 2) x =
      2 * a ^ 2 * Real.cos (x 2) * x 1 * Real.sin (x 2) / sigma a (x 1) (x 2) ^ 2 := by
  have hfun : (fun t => kerrChristoffel M a (Function.update x 2 t) 2 1 2)
      = fun t => x 1 / sigma a (x 1) t := by funext t; simp [kerrChristoffel]
  have hd := (hasDerivAt_const (x 2) (x 1)).fun_div (hasDerivAt_sigma_th a (x 1) (x 2)) hsig
  rw [pd, hfun, hd.deriv]
  ring

private lemma pd_kerrG_2_22 (M a : ℝ) (x : Fin 4 → ℝ) (hsig : sigma a (x 1) (x 2) ≠ 0) :
    pd 2 (fun y => kerrChristoffel M a y 2 2 2) x =
      a ^ 2 * (-a ^ 2 * Real.cos (x 2) ^ 4 - a ^ 2 * Real.cos (x 2) ^ 2 * Real.sin (x 2) ^ 2
        - Real.cos (x 2) ^ 2 * x 1 ^ 2 + x 1 ^ 2 * Real.sin (x 2) ^ 2)
        / sigma a (x 1) (x 2) ^ 2 := by
  have hfun : (fun t => kerrChristoffel M a (Function.update x 2 t) 2 2 2)
      = fun t => (-a ^ 2) * (Real.cos t * Real.sin t / sigma a (x 1) t) := by
    funext t
    simp only [kerrChristoffel, Function.update_self,
      Function.update_of_ne (by decide : (1 : Fin 4) ≠ 2)]
    norm_num
    ring
  have hd := ((hasDerivAt_cos_mul_sin (x 2)).fun_div (hasDerivAt_sigma_th a (x 1) (x 2))
    hsig).const_mul (-a ^ 2)
  rw [pd, hfun, hd.deriv]
  field_simp [hsig]
  simp only [sigma]
  ring

private lemma pd_kerrG_2_33 (M a : ℝ) (x : Fin 4 → ℝ) (hsig : sigma a (x 1) (x 2) ≠ 0) :
    pd 2 (fun y => kerrChristoffel M a y 2 3 3) x =
      (2 * M * a ^ 6 * Real.cos (x 2) ^ 8 * x 1
        + 2 * M * a ^ 6 * Real.cos (x 2) ^ 6 * x 1 * Real.sin (x 2) ^ 2
        - 2 * M * a ^ 6 * Real.cos (x 2) ^ 4 * x 1
        - 10 * M * a ^ 6 * Real.cos (x 2) ^ 2 * x 1 * Real.sin (x 2) ^ 2
        + 6 * M * a ^ 4 * Real.cos (x 2) ^ 6 * x 1 ^ 3
        + 2 * M * a ^ 4 * Real.cos (x 2) ^ 4 * x 1 ^ 3 * Real.sin (x 2) ^ 2
        - 4 * M * a ^ 4 * Real.cos (x 2) ^ 4 * x 1 ^ 3
        - 20 * M * a ^ 4 * Real.cos (x 2) ^ 2 * x 1 ^ 3 * Real.sin (x 2) ^ 2
        - 2 * M * a ^ 4 * Real.cos (x 2) ^ 2 * x 1 ^ 3
        + 2 * M * a ^ 4 * x 1 ^ 3 * Real.sin (x 2) ^ 2
        + 4 * M * a ^ 2 * Real.cos (x 2) ^ 4 * x 1 ^ 5
        - 12 * M * a ^ 2 * Real.cos (x 2) ^ 2 * x 1 ^ 5 * Real.sin (x 2) ^ 2
        - 4 * M * a ^ 2 * Real.cos (x 2) ^ 2 * x 1 ^ 5
        + 4 * M * a ^ 2 * x 1 ^ 5 * Real.sin (x 2) ^ 2
        - a ^ 8 * Real.cos (x 2) ^ 8 - a ^ 8 * Real.cos (x 2) ^ 6 * Real.sin (x 2) ^ 2
        - a ^ 6 * Real.cos (x 2) ^ 8 * x 1 ^ 2
        - a ^ 6 * Real.cos (x 2) ^ 6 * x 1 ^ 2 * Real.sin (x 2) ^ 2
        - 3 * a ^ 6 * Real.cos (x 2) ^ 6 * x 1 ^ 2
        - a ^ 6 * Real.cos (x 2) ^ 4 * x 1 ^ 2 * Real.sin (x 2) ^ 2
        - 3 * a ^ 4 * Real.cos (x 2) ^ 6 * x 1 ^ 4
        - a ^ 4 * Real.cos (x 2) ^ 4 * x 1 ^ 4 * Real.sin (x 2) ^ 2
        - 3 * a ^ 4 * Real.cos (x 2) ^ 4 * x 1 ^ 4
        + a ^ 4 * Real.cos (x 2) ^ 2 * x 1 ^ 4 * Real.sin (x 2) ^ 2
        - 3 * a ^ 2 * Real.cos (x 2) ^ 4 * x 1 ^ 6
        + a ^ 2 * Real.cos (x 2) ^ 2 * x 1 ^ 6 * Real.sin (x 2) ^ 2
        - a ^ 2 * Real.cos (x 2) ^ 2 * x 1 ^ 6
        + a ^ 2 * x 1 ^ 6 * Real.sin (x 2) ^ 2
        - Real.cos (x 2) ^ 2 * x 1 ^ 8 + x 1 ^ 8 * Real.sin (x 2) ^ 2)
        / sigma a (x 1) (x 2) ^ 4 := by
  let c4 : ℝ := -2 * M * a ^ 4 * x 1 + a ^ 6 + a ^ 4 * x 1 ^ 2
  let c2 : ℝ := -4 * M * a ^ 2 * x 1 ^ 3 + 2 * a ^ 4 * x 1 ^ 2 + 2 * a ^ 2 * x 1 ^ 4
  let c0 : ℝ := 2 * M * a ^ 4 * x 1 + 4 * M * a ^ 2 * x 1 ^ 3 + a ^ 2 * x 1 ^ 4 + x 1 ^ 6
  let Q : ℝ → ℝ := fun t => c4 * Real.cos t ^ 4 + c2 * Real.cos t ^ 2 + c0
  have hQ : HasDerivAt Q
      (4 * c4 * Real.cos (x 2) ^ 3 * (-Real.sin (x 2))
        + 2 * c2 * Real.cos (x 2) * (-Real.sin (x 2))) (x 2) := by
    have hc4 : HasDerivAt (fun t => c4 * Real.cos t ^ 4)
        (c4 * (4 * Real.cos (x 2) ^ (4 - 1) * (-Real.sin (x 2)))) (x 2) :=
      ((Real.hasDerivAt_cos (x 2)).pow 4).const_mul c4
    have hc2 := (hasDerivAt_cos_sq (x 2)).const_mul c2
    exact ((hc4.fun_add hc2).add_const c0).congr_deriv (by ring)
  have hfun : (fun t => kerrChristoffel M a (Function.update x 2 t) 2 3 3)
      = fun t => -((Real.cos t * Real.sin t * Q t) / sigma a (x 1) t ^ 3) := by
    funext t
    simp only [kerrChristoffel, Q, c4, c2, c0]
    norm_num
    ring
  have hd := (((hasDerivAt_cos_mul_sin (x 2)).fun_mul hQ).fun_div
    (hasDerivAt_sigma3_th a (x 1) (x 2)) (pow_ne_zero 3 hsig)).fun_neg
  rw [pd, hfun, hd.deriv]
  field_simp [hsig]
  simp only [sigma, Q, c4, c2, c0]
  ring

/-!

## B. Ricci flatness through the coordinate pipeline

-/

private lemma sum_pd_kerrChristoffel_diag (M a : ℝ) (x : Fin 4 → ℝ)
    (hsig : sigma a (x 1) (x 2) ≠ 0) (hdel : delta M a (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0)
    (σ ν : Fin 4) :
    (∑ ρ : Fin 4, pd ν (fun y => kerrChristoffel M a y ρ ρ σ) x)
      = if ν = 1 ∨ ν = 2 then pd ν (fun y => kerrChristoffelTrace a y σ) x else 0 := by
  have hcongrTr : (fun y => ∑ ρ : Fin 4, kerrChristoffel M a y ρ ρ σ) =ᶠ[nhds x]
      fun y => kerrChristoffelTrace a y σ := by
    have hcSig : Continuous (fun y : Fin 4 → ℝ => sigma a (y 1) (y 2)) := by
      simp only [sigma]; fun_prop
    have hcDel : Continuous (fun y : Fin 4 → ℝ => delta M a (y 1)) := by
      simp only [delta]; fun_prop
    have hcS : Continuous (fun y : Fin 4 → ℝ => Real.sin (y 2)) := by fun_prop
    filter_upwards [(hcSig.continuousAt.eventually_ne hsig).and
      ((hcDel.continuousAt.eventually_ne hdel).and (hcS.continuousAt.eventually_ne hs))]
      with y ⟨h1, h2, h3⟩
    exact sum_kerrChristoffel_trace M a y h1 h2 h3 σ
  have hν : ν = 0 ∨ ν = 1 ∨ ν = 2 ∨ ν = 3 := by fin_cases ν <;> decide
  rcases hν with rfl | rfl | rfl | rfl
  · simp [pd_kerrG_const_03 M a x 0 (Or.inl rfl)]
  · simp only [Fin.isValue, true_or, ↓reduceIte]
    rw [← pd_sum 1 (fun ρ y => kerrChristoffel M a y ρ ρ σ) x
      (fun ρ => differentiableAt_kerrG_r' M a x hsig hdel hs ρ ρ σ)]
    exact pd_congr_nhds 1 x hcongrTr
  · simp only [Fin.isValue, or_true, ↓reduceIte]
    rw [← pd_sum 2 (fun ρ y => kerrChristoffel M a y ρ ρ σ) x
      (fun ρ => differentiableAt_kerrG_th M a x hsig hdel hs ρ ρ σ)]
    exact pd_congr_nhds 2 x hcongrTr
  · simp [pd_kerrG_const_03 M a x 3 (Or.inr rfl)]

private lemma ricciOf_kerr_eq_sum (M a : ℝ) (x : Fin 4 → ℝ)
    (hsig : sigma a (x 1) (x 2) ≠ 0) (hdel : delta M a (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0)
    (σ ν : Fin 4) :
    ricciTensorOf (kerrMetric M a) (kerrMetricInv M a) x σ ν
      = pd 1 (fun y => kerrChristoffel M a y 1 ν σ) x
        + pd 2 (fun y => kerrChristoffel M a y 2 ν σ) x
        - (if ν = 1 ∨ ν = 2 then pd ν (fun y => kerrChristoffelTrace a y σ) x else 0)
        + ∑ lam : Fin 4, kerrChristoffelTrace a x lam * kerrChristoffel M a x lam ν σ
        - ∑ ρ : Fin 4, ∑ lam : Fin 4,
          kerrChristoffel M a x ρ ν lam * kerrChristoffel M a x lam ρ σ := by
  have hev : ∀ k i j,
      (fun y => christoffel (kerrMetric M a) (kerrMetricInv M a) y k i j)
        =ᶠ[nhds x] fun y => kerrChristoffel M a y k i j :=
    eventually_christoffel_kerr_eq M a x hsig hdel hs
  have hpt : ∀ k i j,
      christoffel (kerrMetric M a) (kerrMetricInv M a) x k i j = kerrChristoffel M a x k i j :=
    christoffel_kerr_eq M a x hsig hdel hs
  have hpd : ∀ μ k i j,
      pd μ (fun y => christoffel (kerrMetric M a) (kerrMetricInv M a) y k i j) x
        = pd μ (fun y => kerrChristoffel M a y k i j) x :=
    fun μ k i j => pd_congr_nhds μ x (hev k i j)
  have hsumG : ∀ lam, (∑ ρ : Fin 4, kerrChristoffel M a x ρ ρ lam) = kerrChristoffelTrace a x lam :=
    sum_kerrChristoffel_trace M a x hsig hdel hs
  have htr_pd := sum_pd_kerrChristoffel_diag M a x hsig hdel hs σ ν
  simp only [ricciTensorOf, riemann, hpd, hpt, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have h1 : (∑ ρ : Fin 4, pd ρ (fun y => kerrChristoffel M a y ρ ν σ) x)
      = pd 1 (fun y => kerrChristoffel M a y 1 ν σ) x
        + pd 2 (fun y => kerrChristoffel M a y 2 ν σ) x := by
    simp [Fin.sum_univ_four, pd_kerrG_const_03 M a x 0 (Or.inl rfl),
      pd_kerrG_const_03 M a x 3 (Or.inr rfl)]
  have h3 : (∑ ρ : Fin 4, ∑ lam : Fin 4,
    kerrChristoffel M a x ρ ρ lam * kerrChristoffel M a x lam ν σ)
      = ∑ lam : Fin 4, kerrChristoffelTrace a x lam * kerrChristoffel M a x lam ν σ := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun lam _ => ?_
    rw [← Finset.sum_mul, hsumG lam]
  rw [h1, htr_pd, h3]
  ring

private lemma ricciOf_kerr_00 (M a : ℝ) (x : Fin 4 → ℝ)
    (hsig : sigma a (x 1) (x 2) ≠ 0) (hdel : delta M a (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0) :
    ricciTensorOf (kerrMetric M a) (kerrMetricInv M a) x 0 0 = 0 := by
  have hs2 : Real.sin (x 2) ^ 2 = 1 - Real.cos (x 2) ^ 2 := Real.sin_sq (x 2)
  rw [ricciOf_kerr_eq_sum M a x hsig hdel hs 0 0, pd_kerrG_1_00 M a x hsig hdel,
    pd_kerrG_2_00 M a x hsig]
  simp only [Fin.sum_univ_four, kerrChristoffelTrace, kerrChristoffel]
  norm_num
  field_simp [hsig, hdel, hs]
  simp -failIfUnchanged only [sigma, delta, hs2]
  ring

private lemma ricciOf_kerr_03 (M a : ℝ) (x : Fin 4 → ℝ)
    (hsig : sigma a (x 1) (x 2) ≠ 0) (hdel : delta M a (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0) :
    ricciTensorOf (kerrMetric M a) (kerrMetricInv M a) x 0 3 = 0 := by
  have hs2 : Real.sin (x 2) ^ 2 = 1 - Real.cos (x 2) ^ 2 := Real.sin_sq (x 2)
  rw [ricciOf_kerr_eq_sum M a x hsig hdel hs 0 3]
  have hsym1 : (fun y => kerrChristoffel M a y 1 3 0) = fun y => kerrChristoffel M a y 1 0 3 := by
    funext y; exact kerrChristoffel_symm M a y 1 3 0
  have hsym2 : (fun y => kerrChristoffel M a y 2 3 0) = fun y => kerrChristoffel M a y 2 0 3 := by
    funext y; exact kerrChristoffel_symm M a y 2 3 0
  rw [hsym1, hsym2, pd_kerrG_1_03 M a x hsig, pd_kerrG_2_03 M a x hsig]
  simp only [Fin.sum_univ_four, kerrChristoffelTrace, kerrChristoffel]
  norm_num
  field_simp [hsig, hdel, hs]
  simp -failIfUnchanged only [sigma, delta, hs2]
  ring

private lemma ricciOf_kerr_30 (M a : ℝ) (x : Fin 4 → ℝ)
    (hsig : sigma a (x 1) (x 2) ≠ 0) (hdel : delta M a (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0) :
    ricciTensorOf (kerrMetric M a) (kerrMetricInv M a) x 3 0 = 0 := by
  have hs2 : Real.sin (x 2) ^ 2 = 1 - Real.cos (x 2) ^ 2 := Real.sin_sq (x 2)
  have hs4 : Real.sin (x 2) ^ 4 = (1 - Real.cos (x 2) ^ 2) ^ 2 := by
    rw [show Real.sin (x 2) ^ 4 = (Real.sin (x 2) ^ 2) ^ 2 by ring, hs2]
  rw [ricciOf_kerr_eq_sum M a x hsig hdel hs 3 0, pd_kerrG_1_03 M a x hsig,
    pd_kerrG_2_03 M a x hsig]
  simp only [Fin.sum_univ_four, kerrChristoffelTrace, kerrChristoffel]
  norm_num
  field_simp [hsig, hdel, hs]
  simp -failIfUnchanged only [sigma, delta, hs4, hs2]
  ring

private lemma ricciOf_kerr_11 (M a : ℝ) (x : Fin 4 → ℝ)
    (hsig : sigma a (x 1) (x 2) ≠ 0) (hdel : delta M a (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0) :
    ricciTensorOf (kerrMetric M a) (kerrMetricInv M a) x 1 1 = 0 := by
  have hs2 : Real.sin (x 2) ^ 2 = 1 - Real.cos (x 2) ^ 2 := Real.sin_sq (x 2)
  rw [ricciOf_kerr_eq_sum M a x hsig hdel hs 1 1, pd_kerrG_1_11 M a x hsig hdel,
    pd_kerrG_2_11 M a x hsig hdel]
  simp only [Fin.isValue, ↓reduceIte, true_or]
  rw [pd_kerrChristoffelTrace_11 a x hsig]
  simp only [Fin.sum_univ_four, kerrChristoffelTrace, kerrChristoffel]
  norm_num
  field_simp [hsig, hdel, hs]
  simp -failIfUnchanged only [sigma, delta, hs2]
  ring

private lemma ricciOf_kerr_12 (M a : ℝ) (x : Fin 4 → ℝ)
    (hsig : sigma a (x 1) (x 2) ≠ 0) (hdel : delta M a (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0) :
    ricciTensorOf (kerrMetric M a) (kerrMetricInv M a) x 1 2 = 0 := by
  have hs2 : Real.sin (x 2) ^ 2 = 1 - Real.cos (x 2) ^ 2 := Real.sin_sq (x 2)
  rw [ricciOf_kerr_eq_sum M a x hsig hdel hs 1 2]
  have hsym1 : (fun y => kerrChristoffel M a y 1 2 1) = fun y => kerrChristoffel M a y 1 1 2 := by
    funext y; exact kerrChristoffel_symm M a y 1 2 1
  have hsym2 : (fun y => kerrChristoffel M a y 2 2 1) = fun y => kerrChristoffel M a y 2 1 2 := by
    funext y; exact kerrChristoffel_symm M a y 2 2 1
  rw [hsym1, hsym2, pd_kerrG_1_12 M a x hsig, pd_kerrG_2_12 M a x hsig]
  simp only [Fin.isValue, ↓reduceIte, or_true]
  rw [pd_kerrChristoffelTrace_21 a x hsig]
  simp only [Fin.sum_univ_four, kerrChristoffelTrace, kerrChristoffel]
  norm_num
  field_simp [hsig, hdel, hs]
  simp -failIfUnchanged only [sigma, delta, hs2]
  ring

private lemma ricciOf_kerr_21 (M a : ℝ) (x : Fin 4 → ℝ)
    (hsig : sigma a (x 1) (x 2) ≠ 0) (hdel : delta M a (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0) :
    ricciTensorOf (kerrMetric M a) (kerrMetricInv M a) x 2 1 = 0 := by
  have hs2 : Real.sin (x 2) ^ 2 = 1 - Real.cos (x 2) ^ 2 := Real.sin_sq (x 2)
  have hs4 : Real.sin (x 2) ^ 4 = (1 - Real.cos (x 2) ^ 2) ^ 2 := by
    rw [show Real.sin (x 2) ^ 4 = (Real.sin (x 2) ^ 2) ^ 2 by ring, hs2]
  rw [ricciOf_kerr_eq_sum M a x hsig hdel hs 2 1, pd_kerrG_1_12 M a x hsig,
    pd_kerrG_2_12 M a x hsig]
  simp only [Fin.isValue, ↓reduceIte, true_or]
  rw [pd_kerrChristoffelTrace_12 a x hsig]
  simp only [Fin.sum_univ_four, kerrChristoffelTrace, kerrChristoffel]
  norm_num
  field_simp [hsig, hdel, hs]
  simp -failIfUnchanged only [sigma, delta, hs4, hs2]
  ring

private lemma ricciOf_kerr_22 (M a : ℝ) (x : Fin 4 → ℝ)
    (hsig : sigma a (x 1) (x 2) ≠ 0) (hdel : delta M a (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0) :
    ricciTensorOf (kerrMetric M a) (kerrMetricInv M a) x 2 2 = 0 := by
  have hs2 : Real.sin (x 2) ^ 2 = 1 - Real.cos (x 2) ^ 2 := Real.sin_sq (x 2)
  have hs4 : Real.sin (x 2) ^ 4 = (1 - Real.cos (x 2) ^ 2) ^ 2 := by
    rw [show Real.sin (x 2) ^ 4 = (Real.sin (x 2) ^ 2) ^ 2 by ring, hs2]
  rw [ricciOf_kerr_eq_sum M a x hsig hdel hs 2 2, pd_kerrG_1_22 M a x hsig,
    pd_kerrG_2_22 M a x hsig]
  simp only [Fin.isValue, ↓reduceIte, or_true]
  rw [pd_kerrChristoffelTrace_22 a x hsig hs]
  simp only [Fin.sum_univ_four, kerrChristoffelTrace, kerrChristoffel]
  norm_num
  field_simp [hsig, hdel, hs]
  simp -failIfUnchanged only [sigma, delta, hs4, hs2]
  ring

private lemma ricciOf_kerr_33 (M a : ℝ) (x : Fin 4 → ℝ)
    (hsig : sigma a (x 1) (x 2) ≠ 0) (hdel : delta M a (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0) :
    ricciTensorOf (kerrMetric M a) (kerrMetricInv M a) x 3 3 = 0 := by
  have hs2 : Real.sin (x 2) ^ 2 = 1 - Real.cos (x 2) ^ 2 := Real.sin_sq (x 2)
  have hs4 : Real.sin (x 2) ^ 4 = (1 - Real.cos (x 2) ^ 2) ^ 2 := by
    rw [show Real.sin (x 2) ^ 4 = (Real.sin (x 2) ^ 2) ^ 2 by ring, hs2]
  rw [ricciOf_kerr_eq_sum M a x hsig hdel hs 3 3, pd_kerrG_1_33 M a x hsig,
    pd_kerrG_2_33 M a x hsig]
  simp only [Fin.sum_univ_four, kerrChristoffelTrace, kerrChristoffel]
  norm_num
  field_simp [hsig, hdel, hs]
  simp -failIfUnchanged only [sigma, delta, hs4, hs2]
  ring

private lemma pd_kerrG_zero_of_const (M a : ℝ) (x : Fin 4 → ℝ) (μ k i j : Fin 4)
    (h : ∀ s, kerrChristoffel M a (Function.update x μ s) k i j = 0) :
    pd μ (fun y => kerrChristoffel M a y k i j) x = 0 :=
  pd_eq_zero_of μ _ x 0 h

private lemma pd_kerrTr_zero_of_const (a : ℝ) (x : Fin 4 → ℝ) (μ σ : Fin 4)
    (h : ∀ s, kerrChristoffelTrace a (Function.update x μ s) σ = 0) :
    pd μ (fun y => kerrChristoffelTrace a y σ) x = 0 :=
  pd_eq_zero_of μ _ x 0 h

private lemma ricciOf_kerr_offblock (M a : ℝ) (x : Fin 4 → ℝ)
    (hsig : sigma a (x 1) (x 2) ≠ 0) (hdel : delta M a (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0)
    (σ ν : Fin 4)
    (hoff : (σ = 0 ∧ (ν = 1 ∨ ν = 2)) ∨ ((σ = 1 ∨ σ = 2) ∧ (ν = 0 ∨ ν = 3))
      ∨ (σ = 3 ∧ (ν = 1 ∨ ν = 2))) :
    ricciTensorOf (kerrMetric M a) (kerrMetricInv M a) x σ ν = 0 := by
  rw [ricciOf_kerr_eq_sum M a x hsig hdel hs σ ν]
  rcases hoff with ⟨rfl, rfl | rfl⟩ | ⟨rfl | rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩
  all_goals
    rw [pd_kerrG_zero_of_const M a x 1 1 _ _ (fun _ => by simp [kerrChristoffel]),
      pd_kerrG_zero_of_const M a x 2 2 _ _ (fun _ => by simp [kerrChristoffel])]
    simp only [Fin.isValue, Fin.reduceEq, or_self, true_or, or_true, ↓reduceIte]
    try rw [pd_kerrTr_zero_of_const a x _ _ (fun _ => by simp [kerrChristoffelTrace])]
    simp only [Fin.sum_univ_four, kerrChristoffelTrace, kerrChristoffel]
    norm_num

/-- The Boyer–Lindquist Kerr metric has identically vanishing Ricci tensor at every regular
coordinate point (`Σ ≠ 0`, `Δ ≠ 0`, `sin θ ≠ 0`) through `GeneralRelativity.Pipeline`. -/
lemma ricciTensorOf_kerr_eq_zero (M a : ℝ) (x : Fin 4 → ℝ)
    (hsig : sigma a (x 1) (x 2) ≠ 0) (hdel : delta M a (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0)
    (σ ν : Fin 4) :
    ricciTensorOf (kerrMetric M a) (kerrMetricInv M a) x σ ν = 0 := by
  fin_cases σ <;> fin_cases ν
  · exact ricciOf_kerr_00 M a x hsig hdel hs
  · exact ricciOf_kerr_offblock M a x hsig hdel hs 0 1 (by simp)
  · exact ricciOf_kerr_offblock M a x hsig hdel hs 0 2 (by simp)
  · exact ricciOf_kerr_03 M a x hsig hdel hs
  · exact ricciOf_kerr_offblock M a x hsig hdel hs 1 0 (by simp)
  · exact ricciOf_kerr_11 M a x hsig hdel hs
  · exact ricciOf_kerr_12 M a x hsig hdel hs
  · exact ricciOf_kerr_offblock M a x hsig hdel hs 1 3 (by simp)
  · exact ricciOf_kerr_offblock M a x hsig hdel hs 2 0 (by simp)
  · exact ricciOf_kerr_21 M a x hsig hdel hs
  · exact ricciOf_kerr_22 M a x hsig hdel hs
  · exact ricciOf_kerr_offblock M a x hsig hdel hs 2 3 (by simp)
  · exact ricciOf_kerr_30 M a x hsig hdel hs
  · exact ricciOf_kerr_offblock M a x hsig hdel hs 3 1 (by simp)
  · exact ricciOf_kerr_offblock M a x hsig hdel hs 3 2 (by simp)
  · exact ricciOf_kerr_33 M a x hsig hdel hs

/-!

## C. Scalar curvature and vacuum Einstein equations

-/

/-- The Boyer–Lindquist Kerr metric has identically vanishing scalar curvature `S = 0`. -/
lemma ricciScalarOf_kerr_eq_zero (M a : ℝ) (x : Fin 4 → ℝ)
    (hsig : sigma a (x 1) (x 2) ≠ 0) (hdel : delta M a (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0) :
    ricciScalarOf (kerrMetric M a) (kerrMetricInv M a) x = 0 := by
  simp [ricciScalarOf, ricciTensorOf_kerr_eq_zero M a x hsig hdel hs]

/-- Vacuum Einstein equations for the Kerr black hole through `GeneralRelativity.Pipeline`:
`G_{i j} = 0` for all `i, j : Fin 4`. -/
lemma einsteinTensorOf_kerr_eq_zero (M a : ℝ) (x : Fin 4 → ℝ)
    (hsig : sigma a (x 1) (x 2) ≠ 0) (hdel : delta M a (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0)
    (i j : Fin 4) :
    einsteinTensorOf (kerrMetric M a) (kerrMetricInv M a) x i j = 0 := by
  simp [einsteinTensorOf, ricciTensorOf_kerr_eq_zero M a x hsig hdel hs,
    ricciScalarOf_kerr_eq_zero M a x hsig hdel hs]

end Kerr

end GeneralRelativity
