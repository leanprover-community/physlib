/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import PhyslibAlpha.Cosmology.FLRW.Basic
public import PhyslibAlpha.Relativity.Metrics.CoordinateMetric
public import PhyslibAlpha.Relativity.Tensors.EinsteinTensor
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!

# FLRW Christoffel symbols and curvature tensors

Closed-form Levi-Civita Christoffel symbols, partial-derivative tables, and Riemann, Ricci,
scalar, and Einstein curvature tensors computed from the FLRW coordinate metric.

## i. Overview

For an FLRW spacetime in comoving coordinates `(t, r, θ, φ)`, this module derives the Levi-Civita
connection and curvature tensors directly from the metric components:

1. Defines closed-form tables `FLRWSpacetime.christoffel` and `FLRWSpacetime.christoffelDeriv`.
2. Proves all 64 Christoffel symbols and all 256 partial derivatives match the general coordinate
   expressions (`christoffel_eq`, `eventually_christoffel_eq`, `pd_christoffel_eq_deriv`).
3. Identifies the coordinate Riemann tensor with `riemannFromData` (`riemann_eq_data`) and derives
   closed-form expressions for the Ricci tensor, scalar curvature, and Einstein tensor.

## ii. Key results

- `FLRWSpacetime.christoffel`, `FLRWSpacetime.christoffelDeriv` : closed-form Christoffel and
  partial-derivative tables.
- `FLRWSpacetime.christoffel_eq`, `FLRWSpacetime.eventually_christoffel_eq`,
  `FLRWSpacetime.pd_christoffel_eq_deriv` : coordinate-metric connection identities.
- `FLRWSpacetime.riemann_eq_data`, `FLRWSpacetime.ricciTensorOf`, `FLRWSpacetime.ricciScalarOf`,
  `FLRWSpacetime.einsteinTensorOf` : curvature tensors computed from the FLRW metric.

## iii. Table of contents

- A. Christoffel symbols and derivative tables
- B. Metric-level Ricci, scalar, and Einstein tensors

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 5 (Sec. 5.1-5.2). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 27.
  [ref: mtw_1973_gravitation]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 8
  (https://arxiv.org/pdf/gr-qc/9712019#page=201). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

namespace FLRW

open GeneralRelativity.Pipeline

namespace FLRWSpacetime

/-!

## A. Christoffel symbols and derivative tables

Evaluating the coordinate Christoffel symbols and their partial derivatives isolates the
Hubble-rate terms `a' / a`, spatial curvature factor `1 - k r²`, and angular factors across all
256 index combinations.

-/

-- Factored out separately from `Pipeline.christoffel` so symbolic time derivatives of `S.a(t)`
-- remain isolated from metric-inverse index sums.
/-- Closed-form Levi-Civita Christoffel symbols `Γ^m_{ij}` of an FLRW spacetime in comoving
coordinates `(t, r, θ, φ)`. -/
noncomputable def christoffel (S : FLRWSpacetime) (x : Fin 4 → ℝ) (m i j : Fin 4) : ℝ :=
  if m = 0 then
    (if i = 1 ∧ j = 1 then S.a (x 0) * deriv S.a (x 0) / (1 - S.k * (x 1) ^ 2)
     else if i = 2 ∧ j = 2 then S.a (x 0) * deriv S.a (x 0) * (x 1) ^ 2
     else if i = 3 ∧ j = 3 then S.a (x 0) * deriv S.a (x 0) * (x 1) ^ 2 * Real.sin (x 2) ^ 2
     else 0)
  else if m = 1 then
    (if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then deriv S.a (x 0) / S.a (x 0)
     else if i = 1 ∧ j = 1 then S.k * x 1 / (1 - S.k * (x 1) ^ 2)
     else if i = 2 ∧ j = 2 then -(x 1 * (1 - S.k * (x 1) ^ 2))
     else if i = 3 ∧ j = 3 then -(x 1 * (1 - S.k * (x 1) ^ 2) * Real.sin (x 2) ^ 2)
     else 0)
  else if m = 2 then
    (if (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) then deriv S.a (x 0) / S.a (x 0)
     else if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then 1 / x 1
     else if i = 3 ∧ j = 3 then -(Real.sin (x 2) * Real.cos (x 2))
     else 0)
  else
    (if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then deriv S.a (x 0) / S.a (x 0)
     else if (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) then 1 / x 1
     else if (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) then Real.cos (x 2) / Real.sin (x 2)
     else 0)

-- Decouples scalar derivative evaluation from `Pipeline.riemann` assembly.
/-- Complete partial-derivative table `∂_μ Γ^m_{ij}` of the FLRW Christoffel symbols across all
256 coordinate and connection index tuples. -/
noncomputable def christoffelDeriv (S : FLRWSpacetime) (μ : Fin 4) (x : Fin 4 → ℝ)
    (m i j : Fin 4) : ℝ :=
  if μ = 0 then
    (if m = 0 ∧ i = 1 ∧ j = 1 then
       ((deriv S.a (x 0)) ^ 2 + S.a (x 0) * deriv (deriv S.a) (x 0)) / (1 - S.k * (x 1) ^ 2)
     else if m = 0 ∧ i = 2 ∧ j = 2 then
       ((deriv S.a (x 0)) ^ 2 + S.a (x 0) * deriv (deriv S.a) (x 0)) * (x 1) ^ 2
     else if m = 0 ∧ i = 3 ∧ j = 3 then
       ((deriv S.a (x 0)) ^ 2 + S.a (x 0) * deriv (deriv S.a) (x 0)) * (x 1) ^ 2
         * Real.sin (x 2) ^ 2
     else if (m = 1 ∧ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)))
         ∨ (m = 2 ∧ ((i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0)))
         ∨ (m = 3 ∧ ((i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0))) then
       (deriv (deriv S.a) (x 0) * S.a (x 0) - (deriv S.a (x 0)) ^ 2) / (S.a (x 0)) ^ 2
     else 0)
  else if μ = 1 then
    (if m = 0 ∧ i = 1 ∧ j = 1 then
       2 * S.k * x 1 * S.a (x 0) * deriv S.a (x 0) / (1 - S.k * (x 1) ^ 2) ^ 2
     else if m = 0 ∧ i = 2 ∧ j = 2 then
       2 * x 1 * S.a (x 0) * deriv S.a (x 0)
     else if m = 0 ∧ i = 3 ∧ j = 3 then
       2 * x 1 * S.a (x 0) * deriv S.a (x 0) * Real.sin (x 2) ^ 2
     else if m = 1 ∧ i = 1 ∧ j = 1 then
       S.k * (1 + S.k * (x 1) ^ 2) / (1 - S.k * (x 1) ^ 2) ^ 2
     else if m = 1 ∧ i = 2 ∧ j = 2 then
       -(1 - 3 * S.k * (x 1) ^ 2)
     else if m = 1 ∧ i = 3 ∧ j = 3 then
       -(1 - 3 * S.k * (x 1) ^ 2) * Real.sin (x 2) ^ 2
     else if (m = 2 ∧ ((i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)))
         ∨ (m = 3 ∧ ((i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1))) then
       -1 / (x 1) ^ 2
     else 0)
  else if μ = 2 then
    (if m = 0 ∧ i = 3 ∧ j = 3 then
       S.a (x 0) * deriv S.a (x 0) * (x 1) ^ 2 * (2 * Real.sin (x 2) * Real.cos (x 2))
     else if m = 1 ∧ i = 3 ∧ j = 3 then
       -(x 1 * (1 - S.k * (x 1) ^ 2) * (2 * Real.sin (x 2) * Real.cos (x 2)))
     else if m = 2 ∧ i = 3 ∧ j = 3 then
       Real.sin (x 2) ^ 2 - Real.cos (x 2) ^ 2
     else if m = 3 ∧ ((i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)) then
       -1 / Real.sin (x 2) ^ 2
     else 0)
  else 0

@[simp]
private lemma metricDeriv_phi_eq_zero (S : FLRWSpacetime) (x : Fin 4 → ℝ) (c d : Fin 4) :
    coordDeriv 3 (fun y => S.metric y c d) x = 0 :=
  coordDeriv_const_slice 3 (S.metric x c d) fun _ => by simp [metric]

private lemma pd_t_11 (S : FLRWSpacetime) (x : Fin 4 → ℝ)
    (ha_diff : DifferentiableAt ℝ S.a (x 0)) :
    coordDeriv 0 (fun y => S.metric y 1 1) x
      = 2 * S.a (x 0) * deriv S.a (x 0) / (1 - S.k * (x 1) ^ 2) := by
  have haSq : HasDerivAt (fun s : ℝ => S.a s ^ 2) (2 * S.a (x 0) * deriv S.a (x 0)) (x 0) := by
    convert ha_diff.hasDerivAt.pow 2 using 1; ring
  have hfun : (fun s : ℝ => S.metric (Function.update x 0 s) 1 1)
      = fun s : ℝ => S.a s ^ 2 / (1 - S.k * (x 1) ^ 2) := by
    funext s; simp [metric]
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ (haSq.div_const (1 - S.k * (x 1) ^ 2)))]

private lemma pd_t_22 (S : FLRWSpacetime) (x : Fin 4 → ℝ)
    (ha_diff : DifferentiableAt ℝ S.a (x 0)) :
    coordDeriv 0 (fun y => S.metric y 2 2) x = 2 * S.a (x 0) * deriv S.a (x 0) * (x 1) ^ 2 := by
  have haSq : HasDerivAt (fun s : ℝ => S.a s ^ 2) (2 * S.a (x 0) * deriv S.a (x 0)) (x 0) := by
    convert ha_diff.hasDerivAt.pow 2 using 1; ring
  have hfun : (fun s : ℝ => S.metric (Function.update x 0 s) 2 2)
      = fun s : ℝ => S.a s ^ 2 * (x 1) ^ 2 := by
    funext s; simp [metric]
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ (haSq.mul_const ((x 1) ^ 2)))]

private lemma pd_t_33 (S : FLRWSpacetime) (x : Fin 4 → ℝ)
    (ha_diff : DifferentiableAt ℝ S.a (x 0)) :
    coordDeriv 0 (fun y => S.metric y 3 3) x
      = 2 * S.a (x 0) * deriv S.a (x 0) * (x 1) ^ 2 * Real.sin (x 2) ^ 2 := by
  have haSq : HasDerivAt (fun s : ℝ => S.a s ^ 2) (2 * S.a (x 0) * deriv S.a (x 0)) (x 0) := by
    convert ha_diff.hasDerivAt.pow 2 using 1; ring
  have hfun : (fun s : ℝ => S.metric (Function.update x 0 s) 3 3)
      = fun s : ℝ => S.a s ^ 2 * ((x 1) ^ 2 * Real.sin (x 2) ^ 2) := by
    funext s; simp [metric, mul_assoc]
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ (haSq.mul_const ((x 1) ^ 2 * Real.sin (x 2) ^ 2)))]
  ring

private lemma pd_t (S : FLRWSpacetime) (x : Fin 4 → ℝ) (ha_diff : DifferentiableAt ℝ S.a (x 0))
    (c d : Fin 4) :
    coordDeriv 0 (fun y => S.metric y c d) x
      = if c = 1 ∧ d = 1 then 2 * S.a (x 0) * deriv S.a (x 0) / (1 - S.k * (x 1) ^ 2)
        else if c = 2 ∧ d = 2 then 2 * S.a (x 0) * deriv S.a (x 0) * (x 1) ^ 2
        else if c = 3 ∧ d = 3 then
          2 * S.a (x 0) * deriv S.a (x 0) * (x 1) ^ 2 * Real.sin (x 2) ^ 2
        else 0 := by
  fin_cases c <;> fin_cases d <;>
    first
    | exact pd_t_11 S x ha_diff
    | exact pd_t_22 S x ha_diff
    | exact pd_t_33 S x ha_diff
    | simp [coordDeriv, metric]

private lemma pd_r_11 (S : FLRWSpacetime) (x : Fin 4 → ℝ) (hkr : 1 - S.k * (x 1) ^ 2 ≠ 0) :
    coordDeriv 1 (fun y => S.metric y 1 1) x
      = (S.a (x 0)) ^ 2 * (2 * S.k * x 1) / (1 - S.k * (x 1) ^ 2) ^ 2 := by
  have hfun : (fun s : ℝ => S.metric (Function.update x 1 s) 1 1)
      = fun s : ℝ => S.a (x 0) ^ 2 * (1 - S.k * s ^ 2)⁻¹ := by
    funext s; simp [metric, div_eq_mul_inv]
  have hden : HasDerivAt (fun s : ℝ => 1 - S.k * s ^ 2) (-2 * S.k * x 1) (x 1) := by
    convert (hasDerivAt_const (x 1) 1).sub ((hasDerivAt_pow 2 (x 1)).const_mul S.k) using 1
    ring
  have hd : HasDerivAt (fun s : ℝ => S.a (x 0) ^ 2 * (1 - S.k * s ^ 2)⁻¹)
      (S.a (x 0) ^ 2 * (-(-2 * S.k * x 1) / (1 - S.k * (x 1) ^ 2) ^ 2)) (x 1) := by
    convert (hden.inv hkr).const_mul (S.a (x 0) ^ 2) using 1
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hd)]
  ring

private lemma pd_r_22 (S : FLRWSpacetime) (x : Fin 4 → ℝ) :
    coordDeriv 1 (fun y => S.metric y 2 2) x = 2 * (S.a (x 0)) ^ 2 * x 1 := by
  have hfun : (fun s : ℝ => S.metric (Function.update x 1 s) 2 2)
      = fun s : ℝ => S.a (x 0) ^ 2 * s ^ 2 := by
    funext s; simp [metric]
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ ((hasDerivAt_pow 2 (x 1)).const_mul (S.a (x 0) ^ 2)))]
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  ring

private lemma pd_r_33 (S : FLRWSpacetime) (x : Fin 4 → ℝ) :
    coordDeriv 1 (fun y => S.metric y 3 3) x =
      2 * (S.a (x 0)) ^ 2 * x 1 * Real.sin (x 2) ^ 2 := by
  have hfun : (fun s : ℝ => S.metric (Function.update x 1 s) 3 3)
      = fun s : ℝ => s ^ 2 * (S.a (x 0) ^ 2 * Real.sin (x 2) ^ 2) := by
    funext s; simp [metric]; ring
  have hd := (hasDerivAt_pow 2 (x 1)).mul_const (S.a (x 0) ^ 2 * Real.sin (x 2) ^ 2)
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hd)]
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  ring

private lemma pd_r (S : FLRWSpacetime) (x : Fin 4 → ℝ) (hkr : 1 - S.k * (x 1) ^ 2 ≠ 0)
    (c d : Fin 4) :
    coordDeriv 1 (fun y => S.metric y c d) x
      = if c = 1 ∧ d = 1 then
          (S.a (x 0)) ^ 2 * (2 * S.k * x 1) / (1 - S.k * (x 1) ^ 2) ^ 2
        else if c = 2 ∧ d = 2 then 2 * (S.a (x 0)) ^ 2 * x 1
        else if c = 3 ∧ d = 3 then 2 * (S.a (x 0)) ^ 2 * x 1 * Real.sin (x 2) ^ 2
        else 0 := by
  fin_cases c <;> fin_cases d <;>
    first
    | exact pd_r_11 S x hkr
    | exact pd_r_22 S x
    | exact pd_r_33 S x
    | simp [coordDeriv, metric]

private lemma pd_theta_33 (S : FLRWSpacetime) (x : Fin 4 → ℝ) :
    coordDeriv 2 (fun y => S.metric y 3 3) x
      = 2 * (S.a (x 0)) ^ 2 * (x 1) ^ 2 * Real.sin (x 2) * Real.cos (x 2) := by
  have hfun : (fun s : ℝ => S.metric (Function.update x 2 s) 3 3)
      = fun s : ℝ => (S.a (x 0) ^ 2 * (x 1) ^ 2) * Real.sin s ^ 2 := by
    funext s; simp [metric, mul_assoc]
  have hsinSq : HasDerivAt (fun s : ℝ => Real.sin s ^ 2)
      (2 * Real.sin (x 2) * Real.cos (x 2)) (x 2) :=
    ((hasDerivAt_pow 2 (Real.sin (x 2))).comp (x 2)
      (Real.hasDerivAt_sin (x 2))).congr_deriv (by ring)
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ (hsinSq.const_mul (S.a (x 0) ^ 2 * (x 1) ^ 2)))]
  ring

private lemma pd_theta (S : FLRWSpacetime) (x : Fin 4 → ℝ) (c d : Fin 4) :
    coordDeriv 2 (fun y => S.metric y c d) x
      = if c = 3 ∧ d = 3 then
          2 * (S.a (x 0)) ^ 2 * (x 1) ^ 2 * Real.sin (x 2) * Real.cos (x 2)
        else 0 := by
  fin_cases c <;> fin_cases d <;>
    first
    | exact pd_theta_33 S x
    | simp [coordDeriv, metric]

/-- All 64 Christoffel symbols computed from the FLRW coordinate metric match
`FLRWSpacetime.christoffel`. -/
lemma christoffel_eq (S : FLRWSpacetime) (x : Fin 4 → ℝ) (ha : S.a (x 0) ≠ 0)
    (hr : x 1 ≠ 0) (hkr : 1 - S.k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : DifferentiableAt ℝ S.a (x 0)) :
    ∀ m i j, Pipeline.christoffel S.metric S.metricInv x m i j = S.christoffel x m i j := by
  intro m i j
  fin_cases m
  · fin_cases i <;> fin_cases j <;>
      simp [Pipeline.christoffel, christoffel, metricInv, pd_t S x ha_diff,
        pd_r S x hkr, pd_theta S x]
    all_goals field_simp [ha, hr, hkr, hsin]
  · fin_cases i <;> fin_cases j <;>
      simp [Pipeline.christoffel, christoffel, metricInv, pd_t S x ha_diff,
        pd_r S x hkr, pd_theta S x]
    all_goals field_simp [ha, hr, hkr, hsin]
  · fin_cases i <;> fin_cases j <;>
      simp [Pipeline.christoffel, christoffel, metricInv, pd_t S x ha_diff,
        pd_r S x hkr, pd_theta S x]
    all_goals field_simp [ha, hr, hkr, hsin]
  · fin_cases i <;> fin_cases j <;>
      simp [Pipeline.christoffel, christoffel, metricInv, pd_t S x ha_diff,
        pd_r S x hkr, pd_theta S x]
    all_goals field_simp [ha, hr, hkr, hsin]

/-- Neighbourhood equality between the coordinate Christoffel symbols and the closed-form
`FLRWSpacetime.christoffel` around a regular chart point `x`. -/
lemma eventually_christoffel_eq (S : FLRWSpacetime) (x : Fin 4 → ℝ)
    (ha : S.a (x 0) ≠ 0) (hr : x 1 ≠ 0) (hkr : 1 - S.k * (x 1) ^ 2 ≠ 0)
    (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ S.a t) (m i j : Fin 4) :
    (fun y => Pipeline.christoffel S.metric S.metricInv y m i j)
      =ᶠ[nhds x] fun y => S.christoffel y m i j := by
  have hc0 : Continuous (fun y : Fin 4 → ℝ => y 0) := continuous_apply 0
  have hc1 : Continuous (fun y : Fin 4 → ℝ => y 1) := continuous_apply 1
  have hc2 : Continuous (fun y : Fin 4 → ℝ => y 2) := continuous_apply 2
  have ha_cont : ContinuousAt S.a (x 0) := ha_diff.self_of_nhds.continuousAt
  have ha' : ∀ᶠ y in nhds x, S.a (y 0) ≠ 0 :=
    (hc0.continuousAt (x := x)).tendsto.eventually (ha_cont.eventually_ne ha)
  have hr' : ∀ᶠ y in nhds x, y 1 ≠ 0 := hc1.continuousAt.eventually_ne hr
  have hkr_cont : Continuous (fun y : Fin 4 → ℝ => 1 - S.k * (y 1) ^ 2) :=
    continuous_const.sub (continuous_const.mul (hc1.pow 2))
  have hkr' : ∀ᶠ y in nhds x, 1 - S.k * (y 1) ^ 2 ≠ 0 := hkr_cont.continuousAt.eventually_ne hkr
  have hsin' : ∀ᶠ y in nhds x, Real.sin (y 2) ≠ 0 :=
    (hc2.continuousAt (x := x)).tendsto.eventually
      (Real.continuous_sin.continuousAt.eventually_ne hsin)
  have hdiff' : ∀ᶠ y in nhds x, DifferentiableAt ℝ S.a (y 0) :=
    hc0.continuousAt.tendsto.eventually ha_diff
  filter_upwards [ha', hr', hkr', hsin', hdiff'] with y hya hyr hykr hysin hydiff
  exact S.christoffel_eq y hya hyr hykr hysin hydiff m i j

/-- Neighbourhood equality promotes `christoffel_eq` to partial derivatives along every coordinate
axis `μ`. -/
lemma pd_christoffel_eq (S : FLRWSpacetime) (x : Fin 4 → ℝ) (ha : S.a (x 0) ≠ 0)
    (hr : x 1 ≠ 0) (hkr : 1 - S.k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ S.a t) (μ m i j : Fin 4) :
    coordDeriv μ (fun y => Pipeline.christoffel S.metric S.metricInv y m i j) x
      = coordDeriv μ (fun y => S.christoffel y m i j) x :=
  coordDeriv_congr_nhds μ x (S.eventually_christoffel_eq x ha hr hkr hsin ha_diff m i j)

private lemma pd_G_0_011 (S : FLRWSpacetime) (x : Fin 4 → ℝ)
    (ha1 : DifferentiableAt ℝ S.a (x 0)) (ha2 : DifferentiableAt ℝ (deriv S.a) (x 0)) :
    coordDeriv 0 (fun y => S.christoffel y 0 1 1) x = S.christoffelDeriv 0 x 0 1 1 := by
  have hfun : (fun s : ℝ => S.christoffel (Function.update x 0 s) 0 1 1)
      = fun s : ℝ => (S.a s * deriv S.a s) / (1 - S.k * (x 1) ^ 2) := by
    funext s; simp [christoffel]
  have haa' : HasDerivAt (fun s : ℝ => S.a s * deriv S.a s)
      ((deriv S.a (x 0)) ^ 2 + S.a (x 0) * deriv (deriv S.a) (x 0)) (x 0) := by
    convert ha1.hasDerivAt.mul ha2.hasDerivAt using 1; ring
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ (haa'.div_const (1 - S.k * (x 1) ^ 2)))]
  simp [christoffelDeriv]

private lemma pd_G_0_022 (S : FLRWSpacetime) (x : Fin 4 → ℝ)
    (ha1 : DifferentiableAt ℝ S.a (x 0)) (ha2 : DifferentiableAt ℝ (deriv S.a) (x 0)) :
    coordDeriv 0 (fun y => S.christoffel y 0 2 2) x = S.christoffelDeriv 0 x 0 2 2 := by
  have hfun : (fun s : ℝ => S.christoffel (Function.update x 0 s) 0 2 2)
      = fun s : ℝ => (S.a s * deriv S.a s) * (x 1) ^ 2 := by
    funext s; simp [christoffel]
  have haa' : HasDerivAt (fun s : ℝ => S.a s * deriv S.a s)
      ((deriv S.a (x 0)) ^ 2 + S.a (x 0) * deriv (deriv S.a) (x 0)) (x 0) := by
    convert ha1.hasDerivAt.mul ha2.hasDerivAt using 1; ring
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ (haa'.mul_const ((x 1) ^ 2)))]
  simp [christoffelDeriv]

private lemma pd_G_0_033 (S : FLRWSpacetime) (x : Fin 4 → ℝ)
    (ha1 : DifferentiableAt ℝ S.a (x 0)) (ha2 : DifferentiableAt ℝ (deriv S.a) (x 0)) :
    coordDeriv 0 (fun y => S.christoffel y 0 3 3) x = S.christoffelDeriv 0 x 0 3 3 := by
  have hfun : (fun s : ℝ => S.christoffel (Function.update x 0 s) 0 3 3)
      = fun s : ℝ => (S.a s * deriv S.a s) * ((x 1) ^ 2 * Real.sin (x 2) ^ 2) := by
    funext s; simp [christoffel, mul_assoc]
  have haa' : HasDerivAt (fun s : ℝ => S.a s * deriv S.a s)
      ((deriv S.a (x 0)) ^ 2 + S.a (x 0) * deriv (deriv S.a) (x 0)) (x 0) := by
    convert ha1.hasDerivAt.mul ha2.hasDerivAt using 1; ring
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ (haa'.mul_const ((x 1) ^ 2 * Real.sin (x 2) ^ 2)))]
  have hval : S.christoffelDeriv 0 x 0 3 3 =
      ((deriv S.a (x 0)) ^ 2 + S.a (x 0) * deriv (deriv S.a) (x 0)) *
        (x 1) ^ 2 * Real.sin (x 2) ^ 2 := by
    simp [christoffelDeriv]
  rw [hval]
  ring

private lemma pd_G_0_H (S : FLRWSpacetime) (x : Fin 4 → ℝ) (ha : S.a (x 0) ≠ 0)
    (ha1 : DifferentiableAt ℝ S.a (x 0)) (ha2 : DifferentiableAt ℝ (deriv S.a) (x 0))
    (m i j : Fin 4)
    (hmatch : (m = 1 ∧ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)))
      ∨ (m = 2 ∧ ((i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0)))
      ∨ (m = 3 ∧ ((i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0)))) :
    coordDeriv 0 (fun y => S.christoffel y m i j) x = S.christoffelDeriv 0 x m i j := by
  have hH' : deriv (fun s : ℝ => deriv S.a s / S.a s) (x 0)
      = (deriv (deriv S.a) (x 0) * S.a (x 0) - (deriv S.a (x 0)) ^ 2) / (S.a (x 0)) ^ 2 := by
    convert (ha2.hasDerivAt.div ha1.hasDerivAt ha).deriv using 2
    ring
  rcases hmatch with ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ |
      ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · have hfun : (fun s => S.christoffel (Function.update x 0 s) 1 0 1)
      = fun s => deriv S.a s / S.a s := funext fun s => by simp [christoffel]
    rw [coordDeriv, hfun, hH']; simp [christoffelDeriv]
  · have hfun : (fun s => S.christoffel (Function.update x 0 s) 1 1 0)
      = fun s => deriv S.a s / S.a s := funext fun s => by simp [christoffel]
    rw [coordDeriv, hfun, hH']; simp [christoffelDeriv]
  · have hfun : (fun s => S.christoffel (Function.update x 0 s) 2 0 2)
      = fun s => deriv S.a s / S.a s := funext fun s => by simp [christoffel]
    rw [coordDeriv, hfun, hH']; simp [christoffelDeriv]
  · have hfun : (fun s => S.christoffel (Function.update x 0 s) 2 2 0)
      = fun s => deriv S.a s / S.a s := funext fun s => by simp [christoffel]
    rw [coordDeriv, hfun, hH']; simp [christoffelDeriv]
  · have hfun : (fun s => S.christoffel (Function.update x 0 s) 3 0 3)
      = fun s => deriv S.a s / S.a s := funext fun s => by simp [christoffel]
    rw [coordDeriv, hfun, hH']; simp [christoffelDeriv]
  · have hfun : (fun s => S.christoffel (Function.update x 0 s) 3 3 0)
      = fun s => deriv S.a s / S.a s := funext fun s => by simp [christoffel]
    rw [coordDeriv, hfun, hH']; simp [christoffelDeriv]

private lemma pd_G_eq_0 (S : FLRWSpacetime) (x : Fin 4 → ℝ) (ha : S.a (x 0) ≠ 0)
    (ha1 : DifferentiableAt ℝ S.a (x 0)) (ha2 : DifferentiableAt ℝ (deriv S.a) (x 0))
    (m i j : Fin 4) :
    coordDeriv 0 (fun y => S.christoffel y m i j) x = S.christoffelDeriv 0 x m i j := by
  fin_cases m <;>
    (fin_cases i <;> fin_cases j <;>
      first
      | exact pd_G_0_011 S x ha1 ha2
      | exact pd_G_0_022 S x ha1 ha2
      | exact pd_G_0_033 S x ha1 ha2
      | exact pd_G_0_H S x ha ha1 ha2 _ _ _ (by decide)
      | simp [coordDeriv, christoffel, christoffelDeriv])

private lemma pd_G_1_011 (S : FLRWSpacetime) (x : Fin 4 → ℝ) (hkr : 1 - S.k * (x 1) ^ 2 ≠ 0) :
    coordDeriv 1 (fun y => S.christoffel y 0 1 1) x = S.christoffelDeriv 1 x 0 1 1 := by
  have hfun : (fun s => S.christoffel (Function.update x 1 s) 0 1 1)
      = fun s => (S.a (x 0) * deriv S.a (x 0)) * (1 - S.k * s ^ 2)⁻¹ := by
    funext s; simp [christoffel, div_eq_mul_inv]
  have hden : HasDerivAt (fun s : ℝ => 1 - S.k * s ^ 2) (-2 * S.k * x 1) (x 1) := by
    convert (hasDerivAt_const (x 1) 1).sub ((hasDerivAt_pow 2 (x 1)).const_mul S.k) using 1
    ring
  have hd : HasDerivAt (fun s : ℝ => (S.a (x 0) * deriv S.a (x 0)) * (1 - S.k * s ^ 2)⁻¹)
      ((S.a (x 0) * deriv S.a (x 0)) * (-(-2 * S.k * x 1) / (1 - S.k * (x 1) ^ 2) ^ 2)) (x 1) := by
    convert (hden.inv hkr).const_mul (S.a (x 0) * deriv S.a (x 0)) using 1
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hd)]
  simp [christoffelDeriv]
  ring

private lemma pd_G_1_022 (S : FLRWSpacetime) (x : Fin 4 → ℝ) :
    coordDeriv 1 (fun y => S.christoffel y 0 2 2) x = S.christoffelDeriv 1 x 0 2 2 := by
  have hfun : (fun s => S.christoffel (Function.update x 1 s) 0 2 2)
      = fun s => (S.a (x 0) * deriv S.a (x 0)) * s ^ 2 := by
    funext s; simp [christoffel]
  rw [coordDeriv_of_hasDerivAt _
    (hfun ▸ ((hasDerivAt_pow 2 (x 1)).const_mul (S.a (x 0) * deriv S.a (x 0))))]
  simp [christoffelDeriv]
  ring

private lemma pd_G_1_033 (S : FLRWSpacetime) (x : Fin 4 → ℝ) :
    coordDeriv 1 (fun y => S.christoffel y 0 3 3) x = S.christoffelDeriv 1 x 0 3 3 := by
  have hfun : (fun s => S.christoffel (Function.update x 1 s) 0 3 3)
      = fun s => s ^ 2 * (S.a (x 0) * deriv S.a (x 0) * Real.sin (x 2) ^ 2) := by
    funext s; simp [christoffel]; ring
  rw [coordDeriv, hfun,
    ((hasDerivAt_pow 2 (x 1)).mul_const (S.a (x 0) * deriv S.a (x 0) * Real.sin (x 2) ^ 2)).deriv]
  simp [christoffelDeriv]
  ring

private lemma pd_G_1_111 (S : FLRWSpacetime) (x : Fin 4 → ℝ) (hkr : 1 - S.k * (x 1) ^ 2 ≠ 0) :
    coordDeriv 1 (fun y => S.christoffel y 1 1 1) x = S.christoffelDeriv 1 x 1 1 1 := by
  have hfun : (fun s => S.christoffel (Function.update x 1 s) 1 1 1)
      = fun s => S.k * s / (1 - S.k * s ^ 2) := by
    funext s; simp [christoffel]
  have hden : HasDerivAt (fun s : ℝ => 1 - S.k * s ^ 2) (-2 * S.k * x 1) (x 1) := by
    convert (hasDerivAt_const (x 1) 1).sub ((hasDerivAt_pow 2 (x 1)).const_mul S.k) using 1
    ring
  have hnum : HasDerivAt (fun s : ℝ => S.k * s) S.k (x 1) := by
    convert (hasDerivAt_id (x 1)).const_mul S.k using 2 <;> simp
  have hd : HasDerivAt (fun s : ℝ => S.k * s / (1 - S.k * s ^ 2))
      ((S.k * (1 - S.k * (x 1) ^ 2) - (S.k * x 1) * (-2 * S.k * x 1)) /
        (1 - S.k * (x 1) ^ 2) ^ 2) (x 1) := by
    convert hnum.div hden hkr using 1
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hd)]
  simp [christoffelDeriv]
  ring

private lemma pd_G_1_122 (S : FLRWSpacetime) (x : Fin 4 → ℝ) :
    coordDeriv 1 (fun y => S.christoffel y 1 2 2) x = S.christoffelDeriv 1 x 1 2 2 := by
  have hfun : (fun s => S.christoffel (Function.update x 1 s) 1 2 2)
      = fun s => -(s * (1 - S.k * s ^ 2)) := by
    funext s; simp [christoffel]
  have hden : HasDerivAt (fun s : ℝ => 1 - S.k * s ^ 2) (-2 * S.k * x 1) (x 1) := by
    convert (hasDerivAt_const (x 1) 1).sub ((hasDerivAt_pow 2 (x 1)).const_mul S.k) using 1
    ring
  have hd : HasDerivAt (fun s : ℝ => -(s * (1 - S.k * s ^ 2)))
      (-(1 * (1 - S.k * (x 1) ^ 2) + x 1 * (-2 * S.k * x 1))) (x 1) := by
    convert ((hasDerivAt_id (x 1)).mul hden).neg using 2 <;> simp
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hd)]
  simp [christoffelDeriv]
  ring

private lemma pd_G_1_133 (S : FLRWSpacetime) (x : Fin 4 → ℝ) :
    coordDeriv 1 (fun y => S.christoffel y 1 3 3) x = S.christoffelDeriv 1 x 1 3 3 := by
  have hfun : (fun s => S.christoffel (Function.update x 1 s) 1 3 3)
      = fun s => -(s * (1 - S.k * s ^ 2)) * Real.sin (x 2) ^ 2 := by
    funext s; simp [christoffel]
  have hden : HasDerivAt (fun s : ℝ => 1 - S.k * s ^ 2) (-2 * S.k * x 1) (x 1) := by
    convert (hasDerivAt_const (x 1) 1).sub ((hasDerivAt_pow 2 (x 1)).const_mul S.k) using 1
    ring
  have hd : HasDerivAt (fun s : ℝ => -(s * (1 - S.k * s ^ 2)) * Real.sin (x 2) ^ 2)
      ((-(1 * (1 - S.k * (x 1) ^ 2) + x 1 * (-2 * S.k * x 1))) * Real.sin (x 2) ^ 2) (x 1) := by
    convert ((hasDerivAt_id (x 1)).mul hden).neg.mul_const (Real.sin (x 2) ^ 2) using 2 <;> simp
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hd)]
  have hval : S.christoffelDeriv 1 x 1 3 3
    = -(1 - 3 * S.k * (x 1) ^ 2) * Real.sin (x 2) ^ 2 := by
    simp [christoffelDeriv]
  rw [hval]
  ring

private lemma pd_G_1_inv (S : FLRWSpacetime) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (m i j : Fin 4)
    (hmatch : (m = 2 ∧ ((i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)))
      ∨ (m = 3 ∧ ((i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1)))) :
    coordDeriv 1 (fun y => S.christoffel y m i j) x = S.christoffelDeriv 1 x m i j := by
  have hinv : deriv (fun s : ℝ => 1 / s) (x 1) = -1 / (x 1) ^ 2 := by
    rw [show (fun s : ℝ => 1 / s) = fun s : ℝ => s⁻¹ by funext s; simp [one_div]]
    rw [(hasDerivAt_inv hr).deriv]
    ring
  rcases hmatch with ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · have hfun : (fun s => S.christoffel (Function.update x 1 s) 2 1 2) = fun s => 1 / s :=
      funext fun s => by simp [christoffel]
    rw [coordDeriv, hfun, hinv]; simp [christoffelDeriv]
  · have hfun : (fun s => S.christoffel (Function.update x 1 s) 2 2 1) = fun s => 1 / s :=
      funext fun s => by simp [christoffel]
    rw [coordDeriv, hfun, hinv]; simp [christoffelDeriv]
  · have hfun : (fun s => S.christoffel (Function.update x 1 s) 3 1 3) = fun s => 1 / s :=
      funext fun s => by simp [christoffel]
    rw [coordDeriv, hfun, hinv]; simp [christoffelDeriv]
  · have hfun : (fun s => S.christoffel (Function.update x 1 s) 3 3 1) = fun s => 1 / s :=
      funext fun s => by simp [christoffel]
    rw [coordDeriv, hfun, hinv]; simp [christoffelDeriv]

private lemma pd_G_eq_1 (S : FLRWSpacetime) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hkr : 1 - S.k * (x 1) ^ 2 ≠ 0) (m i j : Fin 4) :
    coordDeriv 1 (fun y => S.christoffel y m i j) x = S.christoffelDeriv 1 x m i j := by
  fin_cases m <;>
    (fin_cases i <;> fin_cases j <;>
      first
      | exact pd_G_1_011 S x hkr
      | exact pd_G_1_022 S x
      | exact pd_G_1_033 S x
      | exact pd_G_1_111 S x hkr
      | exact pd_G_1_122 S x
      | exact pd_G_1_133 S x
      | exact pd_G_1_inv S x hr _ _ _ (by decide)
      | simp [coordDeriv, christoffel, christoffelDeriv])

private lemma pd_G_2_033 (S : FLRWSpacetime) (x : Fin 4 → ℝ) :
    coordDeriv 2 (fun y => S.christoffel y 0 3 3) x = S.christoffelDeriv 2 x 0 3 3 := by
  have hfun : (fun s => S.christoffel (Function.update x 2 s) 0 3 3)
      = fun s => (S.a (x 0) * deriv S.a (x 0) * (x 1) ^ 2) * Real.sin s ^ 2 := by
    funext s; simp [christoffel]
  have hsinSq : HasDerivAt (fun s : ℝ => Real.sin s ^ 2)
      (2 * Real.sin (x 2) * Real.cos (x 2)) (x 2) :=
    ((hasDerivAt_pow 2 (Real.sin (x 2))).comp (x 2)
      (Real.hasDerivAt_sin (x 2))).congr_deriv (by ring)
  rw [coordDeriv_of_hasDerivAt _
    (hfun ▸ (hsinSq.const_mul (S.a (x 0) * deriv S.a (x 0) * (x 1) ^ 2)))]
  simp [christoffelDeriv]

private lemma pd_G_2_133 (S : FLRWSpacetime) (x : Fin 4 → ℝ) :
    coordDeriv 2 (fun y => S.christoffel y 1 3 3) x = S.christoffelDeriv 2 x 1 3 3 := by
  have hfun : (fun s => S.christoffel (Function.update x 2 s) 1 3 3)
      = fun s => -(x 1 * (1 - S.k * (x 1) ^ 2) * Real.sin s ^ 2) := by
    funext s; simp [christoffel]
  have hsinSq : HasDerivAt (fun s : ℝ => Real.sin s ^ 2)
      (2 * Real.sin (x 2) * Real.cos (x 2)) (x 2) :=
    ((hasDerivAt_pow 2 (Real.sin (x 2))).comp (x 2)
      (Real.hasDerivAt_sin (x 2))).congr_deriv (by ring)
  have hd : HasDerivAt (fun s : ℝ => -(x 1 * (1 - S.k * (x 1) ^ 2) * Real.sin s ^ 2))
      (-(x 1 * (1 - S.k * (x 1) ^ 2) * (2 * Real.sin (x 2) * Real.cos (x 2)))) (x 2) := by
    convert (hsinSq.const_mul (x 1 * (1 - S.k * (x 1) ^ 2))).neg using 1
  rw [coordDeriv_of_hasDerivAt _ (hfun ▸ hd)]
  simp [christoffelDeriv]

private lemma pd_G_2_233 (S : FLRWSpacetime) (x : Fin 4 → ℝ) :
    coordDeriv 2 (fun y => S.christoffel y 2 3 3) x = S.christoffelDeriv 2 x 2 3 3 := by
  have hfun : (fun s => S.christoffel (Function.update x 2 s) 2 3 3)
      = fun s => -(Real.sin s * Real.cos s) := by
    funext s; simp [christoffel]
  have h := ((Real.hasDerivAt_sin (x 2)).mul (Real.hasDerivAt_cos (x 2))).neg
  have hderiv : deriv (fun s => -(Real.sin s * Real.cos s)) (x 2)
      = Real.sin (x 2) ^ 2 - Real.cos (x 2) ^ 2 := by
    convert h.deriv using 1
    ring
  rw [coordDeriv, hfun, hderiv]
  simp [christoffelDeriv]

private lemma pd_G_2_323 (S : FLRWSpacetime) (x : Fin 4 → ℝ)
    (hsin : Real.sin (x 2) ≠ 0) :
    coordDeriv 2 (fun y => S.christoffel y 3 2 3) x = S.christoffelDeriv 2 x 3 2 3 := by
  have hfun : (fun s => S.christoffel (Function.update x 2 s) 3 2 3)
      = fun s => Real.cos s / Real.sin s := by
    funext s; simp [christoffel]
  have hsc : Real.sin (x 2) ^ 2 + Real.cos (x 2) ^ 2 = 1 := Real.sin_sq_add_cos_sq (x 2)
  have h := (Real.hasDerivAt_cos (x 2)).div (Real.hasDerivAt_sin (x 2)) hsin
  have h1 : -Real.sin (x 2) * Real.sin (x 2) - Real.cos (x 2) * Real.cos (x 2) = -1 := by
    linear_combination -hsc
  have hderiv : deriv (fun s => Real.cos s / Real.sin s) (x 2) = -1 / Real.sin (x 2) ^ 2 := by
    convert h.deriv using 1
    rw [h1]
  rw [coordDeriv, hfun, hderiv]
  simp [christoffelDeriv]

private lemma pd_G_eq_2 (S : FLRWSpacetime) (x : Fin 4 → ℝ) (hsin : Real.sin (x 2) ≠ 0)
    (m i j : Fin 4) :
    coordDeriv 2 (fun y => S.christoffel y m i j) x = S.christoffelDeriv 2 x m i j := by
  fin_cases m <;>
    (fin_cases i <;> fin_cases j <;> dsimp only <;>
      first
      | exact pd_G_2_033 S x
      | exact pd_G_2_133 S x
      | exact pd_G_2_233 S x
      | exact pd_G_2_323 S x hsin
      | simp [coordDeriv, christoffel, christoffelDeriv])

/-- All 256 partial derivatives of `FLRWSpacetime.christoffel` match
`FLRWSpacetime.christoffelDeriv`. -/
lemma pd_christoffel_eq_deriv (S : FLRWSpacetime) (x : Fin 4 → ℝ) (ha : S.a (x 0) ≠ 0)
    (hr : x 1 ≠ 0) (hkr : 1 - S.k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha1 : DifferentiableAt ℝ S.a (x 0)) (ha2 : DifferentiableAt ℝ (deriv S.a) (x 0))
    (μ m i j : Fin 4) :
    coordDeriv μ (fun y => S.christoffel y m i j) x = S.christoffelDeriv μ x m i j := by
  fin_cases μ
  · exact pd_G_eq_0 S x ha ha1 ha2 m i j
  · exact pd_G_eq_1 S x hr hkr m i j
  · exact pd_G_eq_2 S x hsin m i j
  · have hc : coordDeriv 3 (fun y => S.christoffel y m i j) x = 0 :=
      coordDeriv_const_slice 3 (S.christoffel x m i j) fun _ => by simp [christoffel]
    simp [hc, christoffelDeriv]

/-- The coordinate Riemann tensor of an FLRW spacetime equals
`riemannFromData S.christoffel S.christoffelDeriv`. -/
lemma riemann_eq_data (S : FLRWSpacetime) (x : Fin 4 → ℝ) (ha : S.a (x 0) ≠ 0)
    (hr : x 1 ≠ 0) (hkr : 1 - S.k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ S.a t)
    (ha2 : DifferentiableAt ℝ (deriv S.a) (x 0)) (ρ σ μ ν : Fin 4) :
    Pipeline.riemann S.metric S.metricInv x ρ σ μ ν
      = riemannFromData S.christoffel S.christoffelDeriv x ρ σ μ ν := by
  rw [riemann_eq_riemannFromData]
  have ha1 := ha_diff.self_of_nhds
  have h1 := (S.pd_christoffel_eq x ha hr hkr hsin ha_diff μ ρ ν σ).trans
    (S.pd_christoffel_eq_deriv x ha hr hkr hsin ha1 ha2 μ ρ ν σ)
  have h2 := (S.pd_christoffel_eq x ha hr hkr hsin ha_diff ν ρ μ σ).trans
    (S.pd_christoffel_eq_deriv x ha hr hkr hsin ha1 ha2 ν ρ μ σ)
  simp only [riemannFromData, h1, h2, S.christoffel_eq x ha hr hkr hsin ha1]

/-!

## B. Metric-level Ricci, scalar, and Einstein tensors

Contracting the closed-form FLRW Riemann tensor yields the diagonal Ricci components, scalar
curvature `R = 6 (a''/a + (a'/a)² + k/a²)`, and Einstein tensor directly from the metric.

-/

private lemma ricci_00 (S : FLRWSpacetime) (x : Fin 4 → ℝ) (ha : S.a (x 0) ≠ 0)
    (hr : x 1 ≠ 0) (hkr : 1 - S.k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ S.a t)
    (ha2 : DifferentiableAt ℝ (deriv S.a) (x 0)) :
    Pipeline.ricciTensorOf S.metric S.metricInv x 0 0
      = -3 * deriv (deriv S.a) (x 0) / S.a (x 0) := by
  simp [Pipeline.ricciTensorOf, Fin.sum_univ_four, S.riemann_eq_data x ha hr hkr hsin ha_diff ha2,
    riemannFromData, christoffel, christoffelDeriv]
  field_simp [ha]
  ring

private lemma ricci_11 (S : FLRWSpacetime) (x : Fin 4 → ℝ) (ha : S.a (x 0) ≠ 0)
    (hr : x 1 ≠ 0) (hkr : 1 - S.k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ S.a t)
    (ha2 : DifferentiableAt ℝ (deriv S.a) (x 0)) :
    Pipeline.ricciTensorOf S.metric S.metricInv x 1 1
      = (S.a (x 0) * deriv (deriv S.a) (x 0) + 2 * (deriv S.a (x 0)) ^ 2 + 2 * S.k)
          / (1 - S.k * (x 1) ^ 2) := by
  simp [Pipeline.ricciTensorOf, Fin.sum_univ_four, S.riemann_eq_data x ha hr hkr hsin ha_diff ha2,
    riemannFromData, christoffel, christoffelDeriv]
  field_simp [ha, hr, hkr]
  ring

private lemma ricci_22 (S : FLRWSpacetime) (x : Fin 4 → ℝ) (ha : S.a (x 0) ≠ 0)
    (hr : x 1 ≠ 0) (hkr : 1 - S.k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ S.a t)
    (ha2 : DifferentiableAt ℝ (deriv S.a) (x 0)) :
    Pipeline.ricciTensorOf S.metric S.metricInv x 2 2
      = (S.a (x 0) * deriv (deriv S.a) (x 0) + 2 * (deriv S.a (x 0)) ^ 2 + 2 * S.k)
          * (x 1) ^ 2 := by
  have hkr' : 1 - (x 1) ^ 2 * S.k ≠ 0 := by rwa [mul_comm]
  simp [Pipeline.ricciTensorOf, Fin.sum_univ_four, S.riemann_eq_data x ha hr hkr hsin ha_diff ha2,
    riemannFromData, christoffel, christoffelDeriv]
  field_simp [ha, hr, hkr, hkr', hsin]
  rw [Real.sin_sq (x 2)]
  ring

private lemma ricci_33 (S : FLRWSpacetime) (x : Fin 4 → ℝ) (ha : S.a (x 0) ≠ 0)
    (hr : x 1 ≠ 0) (hkr : 1 - S.k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ S.a t)
    (ha2 : DifferentiableAt ℝ (deriv S.a) (x 0)) :
    Pipeline.ricciTensorOf S.metric S.metricInv x 3 3
      = (S.a (x 0) * deriv (deriv S.a) (x 0) + 2 * (deriv S.a (x 0)) ^ 2 + 2 * S.k) * (x 1) ^ 2
          * Real.sin (x 2) ^ 2 := by
  have hkr' : 1 - (x 1) ^ 2 * S.k ≠ 0 := by rwa [mul_comm]
  simp [Pipeline.ricciTensorOf, Fin.sum_univ_four, S.riemann_eq_data x ha hr hkr hsin ha_diff ha2,
    riemannFromData, christoffel, christoffelDeriv]
  field_simp [ha, hr, hkr, hkr', hsin]
  ring

private lemma ricci_offdiag (S : FLRWSpacetime) (x : Fin 4 → ℝ) (ha : S.a (x 0) ≠ 0)
    (hr : x 1 ≠ 0) (hkr : 1 - S.k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ S.a t)
    (ha2 : DifferentiableAt ℝ (deriv S.a) (x 0)) {σ ν : Fin 4} (h : σ ≠ ν) :
    Pipeline.ricciTensorOf S.metric S.metricInv x σ ν = 0 := by
  fin_cases σ <;> fin_cases ν <;> try exact absurd rfl h
  all_goals
    simp [Pipeline.ricciTensorOf, Fin.sum_univ_four, S.riemann_eq_data x ha hr hkr hsin ha_diff ha2,
      riemannFromData, christoffel, christoffelDeriv]
  all_goals ring

/-- Complete coordinate Ricci tensor of an FLRW spacetime. -/
lemma ricciTensorOf (S : FLRWSpacetime) (x : Fin 4 → ℝ) (ha : S.a (x 0) ≠ 0)
    (hr : x 1 ≠ 0) (hkr : 1 - S.k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ S.a t)
    (ha2 : DifferentiableAt ℝ (deriv S.a) (x 0)) (σ ν : Fin 4) :
    Pipeline.ricciTensorOf S.metric S.metricInv x σ ν
      = if σ = ν then
          if σ = 0 then -3 * deriv (deriv S.a) (x 0) / S.a (x 0)
          else if σ = 1 then
            (S.a (x 0) * deriv (deriv S.a) (x 0) + 2 * (deriv S.a (x 0)) ^ 2 + 2 * S.k)
              / (1 - S.k * (x 1) ^ 2)
          else if σ = 2 then
            (S.a (x 0) * deriv (deriv S.a) (x 0) + 2 * (deriv S.a (x 0)) ^ 2 + 2 * S.k)
              * (x 1) ^ 2
          else
            (S.a (x 0) * deriv (deriv S.a) (x 0) + 2 * (deriv S.a (x 0)) ^ 2 + 2 * S.k)
              * (x 1) ^ 2 * Real.sin (x 2) ^ 2
        else 0 := by
  by_cases h : σ = ν
  · subst h
    fin_cases σ
    · simpa using ricci_00 S x ha hr hkr hsin ha_diff ha2
    · simpa using ricci_11 S x ha hr hkr hsin ha_diff ha2
    · simpa using ricci_22 S x ha hr hkr hsin ha_diff ha2
    · simpa using ricci_33 S x ha hr hkr hsin ha_diff ha2
  · simp [h, ricci_offdiag S x ha hr hkr hsin ha_diff ha2 h]

/-- FLRW scalar curvature `R = 6 (a'' / a + (a' / a)² + k / a²)`. -/
lemma ricciScalarOf (S : FLRWSpacetime) (x : Fin 4 → ℝ) (ha : S.a (x 0) ≠ 0)
    (hr : x 1 ≠ 0) (hkr : 1 - S.k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ S.a t)
    (ha2 : DifferentiableAt ℝ (deriv S.a) (x 0)) :
    Pipeline.ricciScalarOf S.metric S.metricInv x
      = 6 * (deriv (deriv S.a) (x 0) / S.a (x 0) + (deriv S.a (x 0) / S.a (x 0)) ^ 2
          + S.k / (S.a (x 0)) ^ 2) := by
  simp only [Pipeline.ricciScalarOf, S.ricciTensorOf x ha hr hkr hsin ha_diff ha2]
  simp only [Fin.sum_univ_four, metricInv, Matrix.of_apply, Fin.reduceEq, ↓reduceIte,
    Fin.isValue, mul_zero, add_zero, zero_add]
  field_simp [ha, hr, hkr, hsin]
  ring

/-- Complete FLRW Einstein tensor: `G_{00} = 3 ((a'/a)² + k/a²)` and
`G_{ii} = -(2 a''/a + (a'/a)² + k/a²) g_{ii}` for spatial indices `i = 1, 2, 3`. -/
lemma einsteinTensorOf (S : FLRWSpacetime) (x : Fin 4 → ℝ) (ha : S.a (x 0) ≠ 0)
    (hr : x 1 ≠ 0) (hkr : 1 - S.k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ S.a t)
    (ha2 : DifferentiableAt ℝ (deriv S.a) (x 0)) (i j : Fin 4) :
    Pipeline.einsteinTensorOf S.metric S.metricInv x i j
      = if i = j then
          if i = 0 then 3 * ((deriv S.a (x 0) / S.a (x 0)) ^ 2 + S.k / (S.a (x 0)) ^ 2)
          else -(2 * (deriv (deriv S.a) (x 0) / S.a (x 0))
            + (deriv S.a (x 0) / S.a (x 0)) ^ 2 + S.k / (S.a (x 0)) ^ 2) * S.metric x i j
        else 0 := by
  simp only [Pipeline.einsteinTensorOf, S.ricciTensorOf x ha hr hkr hsin ha_diff ha2,
    S.ricciScalarOf x ha hr hkr hsin ha_diff ha2, metric]
  fin_cases i <;> fin_cases j <;> simp
  · field_simp [ha]; ring
  · field_simp [ha, hkr]; ring
  · field_simp [ha]; ring
  · field_simp [ha]; ring

end FLRWSpacetime

end FLRW

end GeneralRelativity
