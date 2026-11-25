/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Physlib.Cosmology.FLRW.Basic
public import Physlib.Cosmology.FLRW.MatterContent
public import PhyslibAlpha.Relativity.General.GravitationalConstant
public import PhyslibAlpha.Relativity.Metrics.CoordinateMetric
public import PhyslibAlpha.Relativity.Tensors.EinsteinTensor
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

# FLRW cosmology through the metric pipeline

Full derivation of the Friedmann equations and cosmic-fluid continuity equation from the
four-dimensional FLRW metric through `GeneralRelativity.Pipeline`, bridged directly to
`Physlib.Cosmology.FLRW`.

## i. Overview

The homogeneous, isotropic Friedmann–Lemaître–Robertson–Walker (FLRW) spacetime in comoving
spherical coordinates `x = (t, r, θ, φ)` has metric:

`g = diag(-1, a(t)² / (1 - k r²), a(t)² r², a(t)² r² sin²θ)`.

Whereas `Physlib.Cosmology.FLRW` takes the two Friedmann equations as postulated ODEs for
`U : Cosmology.FLRW`, this module **derives** them directly from the Einstein tensor
`einsteinTensorOf (flrwMetric a k) (flrwMetricInv a k)`:

1. Computes all 64 Christoffel symbols and all 256 Christoffel partial derivatives through
   `GeneralRelativity.Pipeline` (`christoffel_eq_flrwChristoffel`, `pd_flrwChristoffel_eq_deriv`).
2. Obtains exact closed-form `ricciTensorOf_flrw`, `ricciScalarOf_flrw`, and
`einsteinTensorOf_flrw`.
3. Proves equivalence between `G_{ij} + Λ g_{ij} = 8 π G T_{ij}` (for a comoving perfect fluid `T`)
   and the two Friedmann equations in geometric units `c = 1`
   (`einsteinTensorOf_flrw_iff_friedmann`).
4. Bridges `U : Cosmology.FLRW` to `flrwScaleFn U := fun τ => U.a ⟨τ⟩` via
   `Time.hasDerivAt_mk_of_differentiableAt`, deducing `U.FriedmannSolution F Λ G 1` (and
   consequently covariant energy-momentum conservation `continuityEquation`) directly from the
   Einstein tensor.

## ii. Key results

- `FLRWSpacetime`, `flrwMetric`, `flrwMetricInv`, `flrwMetricTensor` : FLRW spacetime
  structure, coordinate metric, inverse, and `MetricTensor 4`.
- `flrwChristoffel`, `flrwChristoffelDeriv`, `riemann_flrw_eq_data` : Christoffel and
  partial-derivative bridge.
- `ricciTensorOf_flrw`, `ricciScalarOf_flrw`, `einsteinTensorOf_flrw` : metric-pipeline curvature
  tensors.
- `perfectFluidT`, `einsteinTensorOf_flrw_iff_friedmann` : Einstein–Friedmann equivalence (`c = 1`).
- `flrwScaleFn`, `einsteinTensorOf_flrw_iff_cosmology_friedmann`,
  `friedmannSolution_of_einsteinTensorOf_flrw` :
  direct bridge to `Physlib.Cosmology.FLRW`.

## iii. Table of contents

- A. Metric, inverse, and MetricTensor bundle
- B. Christoffel symbols and derivative tables
- C. Metric-level Ricci, scalar, and Einstein tensors
- D. Equivalence with the Friedmann equations and Physlib Cosmology

## iv. References

* R. M. Wald, *General Relativity* (1984). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973). [ref: mtw_1973_gravitation]

-/

@[expose] public section

namespace GeneralRelativity

namespace FLRW

open GeneralRelativity.Pipeline

/-!

## A. Metric, inverse, and MetricTensor bundle

In comoving coordinates `(t, r, θ, φ)`, the spatially homogeneous and isotropic FLRW line element
is diagonal, invertible whenever the scale factor `a(t)`, radius `r`, `1 - k r²`, and `sin θ` are
non-zero.

-/

/-- Comoving Friedmann–Lemaître–Robertson–Walker (FLRW) spacetime parameterized by a scale
factor `a(t)` and spatial curvature `k`. -/
structure FLRWSpacetime where
  /-- Scale factor `a(t)` as a function of comoving coordinate time. -/
  a : ℝ → ℝ
  /-- Normalized spatial curvature parameter `k`. -/
  k : ℝ

/-- Construct an `FLRWSpacetime` directly from `U : Cosmology.FLRW`. -/
noncomputable def FLRWSpacetime.ofCosmology (U : Cosmology.FLRW) : FLRWSpacetime where
  a := fun τ => U.a ⟨τ⟩
  k := U.geometry.curvature

/-- The FLRW metric in comoving coordinates `(t, r, θ, φ)` with scale factor `a(t)` and spatial
curvature parameter `k`. -/
noncomputable def flrwMetric (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ) : Tensor2 4 :=
  fun i j =>
    if i = j then
      if i = 0 then -1
      else if i = 1 then (a (x 0)) ^ 2 / (1 - k * (x 1) ^ 2)
      else if i = 2 then (a (x 0)) ^ 2 * (x 1) ^ 2
      else (a (x 0)) ^ 2 * (x 1) ^ 2 * Real.sin (x 2) ^ 2
    else 0

/-- The inverse of the FLRW metric in `(t, r, θ, φ)` coordinates. -/
noncomputable def flrwMetricInv (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ) : Tensor2 4 :=
  fun i j =>
    if i = j then
      if i = 0 then -1
      else if i = 1 then (1 - k * (x 1) ^ 2) / (a (x 0)) ^ 2
      else if i = 2 then ((a (x 0)) ^ 2 * (x 1) ^ 2)⁻¹
      else ((a (x 0)) ^ 2 * (x 1) ^ 2 * Real.sin (x 2) ^ 2)⁻¹
    else 0

/-- Symmetry of `flrwMetric`. -/
lemma flrwMetric_symm (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ) : IsSymm (flrwMetric a k x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply, flrwMetric]

/-- `flrwMetric * flrwMetricInv = 1` on the regular coordinate domain. -/
lemma flrwMetric_mul_inv (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ) (ha : a (x 0) ≠ 0)
    (hr : x 1 ≠ 0) (hkr : 1 - k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0) :
    flrwMetric a k x * flrwMetricInv a k x = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [flrwMetric, flrwMetricInv, Matrix.mul_apply]
  · field_simp [ha, hkr]
  · field_simp [ha, hr]
  · field_simp [ha, hr, hsin]

/-- `flrwMetricInv * flrwMetric = 1` on the regular coordinate domain. -/
lemma flrwMetricInv_mul (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ) (ha : a (x 0) ≠ 0)
    (hr : x 1 ≠ 0) (hkr : 1 - k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0) :
    flrwMetricInv a k x * flrwMetric a k x = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [flrwMetric, flrwMetricInv, Matrix.mul_apply]
  · field_simp [ha, hkr]
  · field_simp [ha, hr]
  · field_simp [ha, hr, hsin]

/-- Bundled `MetricTensor 4` for the FLRW metric on the regular coordinate domain. -/
noncomputable def flrwMetricTensor (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ) (ha : a (x 0) ≠ 0)
    (hr : x 1 ≠ 0) (hkr : 1 - k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0) :
    MetricTensor 4 where
  g := flrwMetric a k x
  ginv := flrwMetricInv a k x
  symm := flrwMetric_symm a k x
  inv_left := flrwMetric_mul_inv a k x ha hr hkr hsin
  inv_right := flrwMetricInv_mul a k x ha hr hkr hsin

/-!

## B. Christoffel symbols and derivative tables

Evaluating `Pipeline.christoffel` and its partial derivatives isolates the Hubble-rate terms
`a' / a`, spatial curvature factor `1 - k r²`, and angular factors across all 256 index
combinations.

-/

/-- Closed-form Christoffel symbols `Γ^m_{ij}` of the FLRW metric, factored out from
`Pipeline.christoffel` so symbolic time derivatives of `a(t)` remain isolated from index sums. -/
noncomputable def flrwChristoffel (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ) (m i j : Fin 4) : ℝ :=
  if m = 0 then
    (if i = 1 ∧ j = 1 then a (x 0) * deriv a (x 0) / (1 - k * (x 1) ^ 2)
     else if i = 2 ∧ j = 2 then a (x 0) * deriv a (x 0) * (x 1) ^ 2
     else if i = 3 ∧ j = 3 then a (x 0) * deriv a (x 0) * (x 1) ^ 2 * Real.sin (x 2) ^ 2
     else 0)
  else if m = 1 then
    (if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then deriv a (x 0) / a (x 0)
     else if i = 1 ∧ j = 1 then k * x 1 / (1 - k * (x 1) ^ 2)
     else if i = 2 ∧ j = 2 then -(x 1 * (1 - k * (x 1) ^ 2))
     else if i = 3 ∧ j = 3 then -(x 1 * (1 - k * (x 1) ^ 2) * Real.sin (x 2) ^ 2)
     else 0)
  else if m = 2 then
    (if (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) then deriv a (x 0) / a (x 0)
     else if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then 1 / x 1
     else if i = 3 ∧ j = 3 then -(Real.sin (x 2) * Real.cos (x 2))
     else 0)
  else
    (if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then deriv a (x 0) / a (x 0)
     else if (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) then 1 / x 1
     else if (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) then Real.cos (x 2) / Real.sin (x 2)
     else 0)

/-- Complete partial-derivative table `∂_μ flrwChristoffel^m_{ij}` across all 256 index tuples,
decoupling scalar derivative evaluation from `Pipeline.riemann` assembly. -/
noncomputable def flrwChristoffelDeriv (a : ℝ → ℝ) (k : ℝ) (μ : Fin 4) (x : Fin 4 → ℝ)
    (m i j : Fin 4) : ℝ :=
  if μ = 0 then
    (if m = 0 ∧ i = 1 ∧ j = 1 then
       ((deriv a (x 0)) ^ 2 + a (x 0) * deriv (deriv a) (x 0)) / (1 - k * (x 1) ^ 2)
     else if m = 0 ∧ i = 2 ∧ j = 2 then
       ((deriv a (x 0)) ^ 2 + a (x 0) * deriv (deriv a) (x 0)) * (x 1) ^ 2
     else if m = 0 ∧ i = 3 ∧ j = 3 then
       ((deriv a (x 0)) ^ 2 + a (x 0) * deriv (deriv a) (x 0)) * (x 1) ^ 2
         * Real.sin (x 2) ^ 2
     else if (m = 1 ∧ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)))
         ∨ (m = 2 ∧ ((i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0)))
         ∨ (m = 3 ∧ ((i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0))) then
       (deriv (deriv a) (x 0) * a (x 0) - (deriv a (x 0)) ^ 2) / (a (x 0)) ^ 2
     else 0)
  else if μ = 1 then
    (if m = 0 ∧ i = 1 ∧ j = 1 then
       2 * k * x 1 * a (x 0) * deriv a (x 0) / (1 - k * (x 1) ^ 2) ^ 2
     else if m = 0 ∧ i = 2 ∧ j = 2 then
       2 * x 1 * a (x 0) * deriv a (x 0)
     else if m = 0 ∧ i = 3 ∧ j = 3 then
       2 * x 1 * a (x 0) * deriv a (x 0) * Real.sin (x 2) ^ 2
     else if m = 1 ∧ i = 1 ∧ j = 1 then
       k * (1 + k * (x 1) ^ 2) / (1 - k * (x 1) ^ 2) ^ 2
     else if m = 1 ∧ i = 2 ∧ j = 2 then
       -(1 - 3 * k * (x 1) ^ 2)
     else if m = 1 ∧ i = 3 ∧ j = 3 then
       -(1 - 3 * k * (x 1) ^ 2) * Real.sin (x 2) ^ 2
     else if (m = 2 ∧ ((i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)))
         ∨ (m = 3 ∧ ((i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1))) then
       -1 / (x 1) ^ 2
     else 0)
  else if μ = 2 then
    (if m = 0 ∧ i = 3 ∧ j = 3 then
       a (x 0) * deriv a (x 0) * (x 1) ^ 2 * (2 * Real.sin (x 2) * Real.cos (x 2))
     else if m = 1 ∧ i = 3 ∧ j = 3 then
       -(x 1 * (1 - k * (x 1) ^ 2) * (2 * Real.sin (x 2) * Real.cos (x 2)))
     else if m = 2 ∧ i = 3 ∧ j = 3 then
       Real.sin (x 2) ^ 2 - Real.cos (x 2) ^ 2
     else if m = 3 ∧ ((i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)) then
       -1 / Real.sin (x 2) ^ 2
     else 0)
  else 0

@[simp]
private lemma pd_flrw_phi (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ) (c d : Fin 4) :
    pd 3 (fun y => flrwMetric a k y c d) x = 0 := by
  fin_cases c <;> fin_cases d <;> simp [pd, flrwMetric]

private lemma pd_flrw_t_11 (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ)
    (ha_diff : DifferentiableAt ℝ a (x 0)) :
    pd 0 (fun y => flrwMetric a k y 1 1) x
      = 2 * a (x 0) * deriv a (x 0) / (1 - k * (x 1) ^ 2) := by
  have haSq : HasDerivAt (fun s : ℝ => a s ^ 2) (2 * a (x 0) * deriv a (x 0)) (x 0) := by
    convert ha_diff.hasDerivAt.pow 2 using 1; ring
  have hfun : (fun s : ℝ => flrwMetric a k (Function.update x 0 s) 1 1)
      = fun s : ℝ => a s ^ 2 / (1 - k * (x 1) ^ 2) := by
    funext s; simp [flrwMetric]
  rw [pd, hfun, (haSq.div_const (1 - k * (x 1) ^ 2)).deriv]

private lemma pd_flrw_t_22 (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ)
    (ha_diff : DifferentiableAt ℝ a (x 0)) :
    pd 0 (fun y => flrwMetric a k y 2 2) x = 2 * a (x 0) * deriv a (x 0) * (x 1) ^ 2 := by
  have haSq : HasDerivAt (fun s : ℝ => a s ^ 2) (2 * a (x 0) * deriv a (x 0)) (x 0) := by
    convert ha_diff.hasDerivAt.pow 2 using 1; ring
  have hfun : (fun s : ℝ => flrwMetric a k (Function.update x 0 s) 2 2)
      = fun s : ℝ => a s ^ 2 * (x 1) ^ 2 := by
    funext s; simp [flrwMetric]
  rw [pd, hfun, (haSq.mul_const ((x 1) ^ 2)).deriv]

private lemma pd_flrw_t_33 (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ)
    (ha_diff : DifferentiableAt ℝ a (x 0)) :
    pd 0 (fun y => flrwMetric a k y 3 3) x
      = 2 * a (x 0) * deriv a (x 0) * (x 1) ^ 2 * Real.sin (x 2) ^ 2 := by
  have haSq : HasDerivAt (fun s : ℝ => a s ^ 2) (2 * a (x 0) * deriv a (x 0)) (x 0) := by
    convert ha_diff.hasDerivAt.pow 2 using 1; ring
  have hfun : (fun s : ℝ => flrwMetric a k (Function.update x 0 s) 3 3)
      = fun s : ℝ => a s ^ 2 * ((x 1) ^ 2 * Real.sin (x 2) ^ 2) := by
    funext s; simp [flrwMetric, mul_assoc]
  rw [pd, hfun, (haSq.mul_const ((x 1) ^ 2 * Real.sin (x 2) ^ 2)).deriv]
  ring

private lemma pd_flrw_t (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ) (ha_diff : DifferentiableAt ℝ a (x 0))
    (c d : Fin 4) :
    pd 0 (fun y => flrwMetric a k y c d) x
      = if c = 1 ∧ d = 1 then 2 * a (x 0) * deriv a (x 0) / (1 - k * (x 1) ^ 2)
        else if c = 2 ∧ d = 2 then 2 * a (x 0) * deriv a (x 0) * (x 1) ^ 2
        else if c = 3 ∧ d = 3 then 2 * a (x 0) * deriv a (x 0) * (x 1) ^ 2 * Real.sin (x 2) ^ 2
        else 0 := by
  fin_cases c <;> fin_cases d <;>
    first
    | exact pd_flrw_t_11 a k x ha_diff
    | exact pd_flrw_t_22 a k x ha_diff
    | exact pd_flrw_t_33 a k x ha_diff
    | simp [pd, flrwMetric]

private lemma pd_flrw_r_11 (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ) (hkr : 1 - k * (x 1) ^ 2 ≠ 0) :
    pd 1 (fun y => flrwMetric a k y 1 1) x
      = (a (x 0)) ^ 2 * (2 * k * x 1) / (1 - k * (x 1) ^ 2) ^ 2 := by
  have hfun : (fun s : ℝ => flrwMetric a k (Function.update x 1 s) 1 1)
      = fun s : ℝ => a (x 0) ^ 2 * (1 - k * s ^ 2)⁻¹ := by
    funext s; simp [flrwMetric, div_eq_mul_inv]
  have hden : HasDerivAt (fun s : ℝ => 1 - k * s ^ 2) (-2 * k * x 1) (x 1) := by
    convert (hasDerivAt_const (x 1) 1).sub ((hasDerivAt_pow 2 (x 1)).const_mul k) using 1
    ring
  have hd : HasDerivAt (fun s : ℝ => a (x 0) ^ 2 * (1 - k * s ^ 2)⁻¹)
      (a (x 0) ^ 2 * (-(-2 * k * x 1) / (1 - k * (x 1) ^ 2) ^ 2)) (x 1) := by
    convert (hden.inv hkr).const_mul (a (x 0) ^ 2) using 1
  rw [pd, hfun, hd.deriv]
  ring

private lemma pd_flrw_r_22 (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ) :
    pd 1 (fun y => flrwMetric a k y 2 2) x = 2 * (a (x 0)) ^ 2 * x 1 := by
  have hfun : (fun s : ℝ => flrwMetric a k (Function.update x 1 s) 2 2)
      = fun s : ℝ => a (x 0) ^ 2 * s ^ 2 := by
    funext s; simp [flrwMetric]
  rw [pd, hfun, ((hasDerivAt_pow 2 (x 1)).const_mul (a (x 0) ^ 2)).deriv]
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  ring

private lemma pd_flrw_r_33 (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ) :
    pd 1 (fun y => flrwMetric a k y 3 3) x = 2 * (a (x 0)) ^ 2 * x 1 * Real.sin (x 2) ^ 2 := by
  have hfun : (fun s : ℝ => flrwMetric a k (Function.update x 1 s) 3 3)
      = fun s : ℝ => s ^ 2 * (a (x 0) ^ 2 * Real.sin (x 2) ^ 2) := by
    funext s; simp [flrwMetric]; ring
  rw [pd, hfun, ((hasDerivAt_pow 2 (x 1)).mul_const (a (x 0) ^ 2 * Real.sin (x 2) ^ 2)).deriv]
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  ring

private lemma pd_flrw_r (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ) (hkr : 1 - k * (x 1) ^ 2 ≠ 0)
    (c d : Fin 4) :
    pd 1 (fun y => flrwMetric a k y c d) x
      = if c = 1 ∧ d = 1 then
          (a (x 0)) ^ 2 * (2 * k * x 1) / (1 - k * (x 1) ^ 2) ^ 2
        else if c = 2 ∧ d = 2 then 2 * (a (x 0)) ^ 2 * x 1
        else if c = 3 ∧ d = 3 then 2 * (a (x 0)) ^ 2 * x 1 * Real.sin (x 2) ^ 2
        else 0 := by
  fin_cases c <;> fin_cases d <;>
    first
    | exact pd_flrw_r_11 a k x hkr
    | exact pd_flrw_r_22 a k x
    | exact pd_flrw_r_33 a k x
    | simp [pd, flrwMetric]

private lemma pd_flrw_theta_33 (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ) :
    pd 2 (fun y => flrwMetric a k y 3 3) x
      = 2 * (a (x 0)) ^ 2 * (x 1) ^ 2 * Real.sin (x 2) * Real.cos (x 2) := by
  have hfun : (fun s : ℝ => flrwMetric a k (Function.update x 2 s) 3 3)
      = fun s : ℝ => (a (x 0) ^ 2 * (x 1) ^ 2) * Real.sin s ^ 2 := by
    funext s; simp [flrwMetric, mul_assoc]
  have hsinSq : HasDerivAt (fun s : ℝ => Real.sin s ^ 2)
      (2 * Real.sin (x 2) * Real.cos (x 2)) (x 2) := hasDerivAt_sin_sq (x 2)
  rw [pd, hfun, (hsinSq.const_mul (a (x 0) ^ 2 * (x 1) ^ 2)).deriv]
  ring

private lemma pd_flrw_theta (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ) (c d : Fin 4) :
    pd 2 (fun y => flrwMetric a k y c d) x
      = if c = 3 ∧ d = 3 then
          2 * (a (x 0)) ^ 2 * (x 1) ^ 2 * Real.sin (x 2) * Real.cos (x 2)
        else 0 := by
  fin_cases c <;> fin_cases d <;>
    first
    | exact pd_flrw_theta_33 a k x
    | simp [pd, flrwMetric]

/-- All 64 Christoffel symbols computed by `christoffel` match `flrwChristoffel`. -/
lemma christoffel_eq_flrwChristoffel (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ) (ha : a (x 0) ≠ 0)
    (hr : x 1 ≠ 0) (hkr : 1 - k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : DifferentiableAt ℝ a (x 0)) :
    ∀ m i j, christoffel (flrwMetric a k) (flrwMetricInv a k) x m i j
      = flrwChristoffel a k x m i j := by
  intro m i j
  fin_cases m <;> fin_cases i <;> fin_cases j <;>
    simp [christoffel, flrwChristoffel, flrwMetricInv, pd_flrw_t a k x ha_diff,
      pd_flrw_r a k x hkr, pd_flrw_theta a k x]
  all_goals field_simp [ha, hr, hkr, hsin]

/-- Neighbourhood equality promotes `christoffel = flrwChristoffel` to partial derivatives along
every
coordinate axis `μ`. -/
lemma pd_christoffel_eq_pd_flrwG (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ) (ha : a (x 0) ≠ 0)
    (hr : x 1 ≠ 0) (hkr : 1 - k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ a t) (μ m i j : Fin 4) :
    pd μ (fun y => christoffel (flrwMetric a k) (flrwMetricInv a k) y m i j) x
      = pd μ (fun y => flrwChristoffel a k y m i j) x := by
  fin_cases μ
  · have ha_cont : ContinuousAt a (x 0) := ha_diff.self_of_nhds.continuousAt
    have ha' : ∀ᶠ t in nhds (x 0), a t ≠ 0 := ha_cont.eventually_ne ha
    have heq : (fun s : ℝ =>
        christoffel (flrwMetric a k) (flrwMetricInv a k) (Function.update x 0 s) m i j)
        =ᶠ[nhds (x 0)] (fun s : ℝ => flrwChristoffel a k (Function.update x 0 s) m i j) := by
      filter_upwards [ha', ha_diff] with s hs1 hs2
      exact christoffel_eq_flrwChristoffel a k (Function.update x 0 s)
        (by simpa using hs1) (by simpa using hr) (by simpa using hkr) (by simpa using hsin)
        (by simpa using hs2) m i j
    exact Filter.EventuallyEq.deriv_eq heq
  · have hr' : ∀ᶠ s in nhds (x 1), s ≠ 0 := eventually_ne_nhds hr
    have hkr_cont : ContinuousAt (fun s : ℝ => 1 - k * s ^ 2) (x 1) := by fun_prop
    have hkr' : ∀ᶠ s in nhds (x 1), 1 - k * s ^ 2 ≠ 0 := hkr_cont.eventually_ne hkr
    have heq : (fun s : ℝ =>
        christoffel (flrwMetric a k) (flrwMetricInv a k) (Function.update x 1 s) m i j)
        =ᶠ[nhds (x 1)] (fun s : ℝ => flrwChristoffel a k (Function.update x 1 s) m i j) := by
      filter_upwards [hr', hkr'] with s hs1 hs2
      exact christoffel_eq_flrwChristoffel a k (Function.update x 1 s)
        (by simpa using ha) (by simpa using hs1) (by simpa using hs2) (by simpa using hsin)
        (by simpa using ha_diff.self_of_nhds) m i j
    exact Filter.EventuallyEq.deriv_eq heq
  · have hsin' : ∀ᶠ s in nhds (x 2), Real.sin s ≠ 0 :=
      Real.continuous_sin.continuousAt.eventually_ne hsin
    have heq : (fun s : ℝ =>
        christoffel (flrwMetric a k) (flrwMetricInv a k) (Function.update x 2 s) m i j)
        =ᶠ[nhds (x 2)] (fun s : ℝ => flrwChristoffel a k (Function.update x 2 s) m i j) := by
      filter_upwards [hsin'] with s hs
      exact christoffel_eq_flrwChristoffel a k (Function.update x 2 s)
        (by simpa using ha) (by simpa using hr) (by simpa using hkr) (by simpa using hs)
        (by simpa using ha_diff.self_of_nhds) m i j
    exact Filter.EventuallyEq.deriv_eq heq
  · have heq : (fun s : ℝ =>
        christoffel (flrwMetric a k) (flrwMetricInv a k) (Function.update x 3 s) m i j)
        =ᶠ[nhds (x 3)] (fun s : ℝ => flrwChristoffel a k (Function.update x 3 s) m i j) :=
      Filter.Eventually.of_forall (fun s =>
        christoffel_eq_flrwChristoffel a k (Function.update x 3 s) ha hr hkr hsin
            ha_diff.self_of_nhds
          m i j)
    exact Filter.EventuallyEq.deriv_eq heq

private lemma pd_flrwG_0_011 (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ)
    (ha1 : DifferentiableAt ℝ a (x 0)) (ha2 : DifferentiableAt ℝ (deriv a) (x 0)) :
    pd 0 (fun y => flrwChristoffel a k y 0 1 1) x = flrwChristoffelDeriv a k 0 x 0 1 1 := by
  have hfun : (fun s : ℝ => flrwChristoffel a k (Function.update x 0 s) 0 1 1)
      = fun s : ℝ => (a s * deriv a s) / (1 - k * (x 1) ^ 2) := by
    funext s; simp [flrwChristoffel]
  have haa' : HasDerivAt (fun s : ℝ => a s * deriv a s)
      ((deriv a (x 0)) ^ 2 + a (x 0) * deriv (deriv a) (x 0)) (x 0) := by
    convert ha1.hasDerivAt.mul ha2.hasDerivAt using 1; ring
  rw [pd, hfun, (haa'.div_const (1 - k * (x 1) ^ 2)).deriv]
  simp [flrwChristoffelDeriv]

private lemma pd_flrwG_0_022 (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ)
    (ha1 : DifferentiableAt ℝ a (x 0)) (ha2 : DifferentiableAt ℝ (deriv a) (x 0)) :
    pd 0 (fun y => flrwChristoffel a k y 0 2 2) x = flrwChristoffelDeriv a k 0 x 0 2 2 := by
  have hfun : (fun s : ℝ => flrwChristoffel a k (Function.update x 0 s) 0 2 2)
      = fun s : ℝ => (a s * deriv a s) * (x 1) ^ 2 := by
    funext s; simp [flrwChristoffel]
  have haa' : HasDerivAt (fun s : ℝ => a s * deriv a s)
      ((deriv a (x 0)) ^ 2 + a (x 0) * deriv (deriv a) (x 0)) (x 0) := by
    convert ha1.hasDerivAt.mul ha2.hasDerivAt using 1; ring
  rw [pd, hfun, (haa'.mul_const ((x 1) ^ 2)).deriv]
  simp [flrwChristoffelDeriv]

private lemma pd_flrwG_0_033 (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ)
    (ha1 : DifferentiableAt ℝ a (x 0)) (ha2 : DifferentiableAt ℝ (deriv a) (x 0)) :
    pd 0 (fun y => flrwChristoffel a k y 0 3 3) x = flrwChristoffelDeriv a k 0 x 0 3 3 := by
  have hfun : (fun s : ℝ => flrwChristoffel a k (Function.update x 0 s) 0 3 3)
      = fun s : ℝ => (a s * deriv a s) * ((x 1) ^ 2 * Real.sin (x 2) ^ 2) := by
    funext s; simp [flrwChristoffel, mul_assoc]
  have haa' : HasDerivAt (fun s : ℝ => a s * deriv a s)
      ((deriv a (x 0)) ^ 2 + a (x 0) * deriv (deriv a) (x 0)) (x 0) := by
    convert ha1.hasDerivAt.mul ha2.hasDerivAt using 1; ring
  rw [pd, hfun, (haa'.mul_const ((x 1) ^ 2 * Real.sin (x 2) ^ 2)).deriv]
  have hval : flrwChristoffelDeriv a k 0 x 0 3 3 =
      ((deriv a (x 0)) ^ 2 + a (x 0) * deriv (deriv a) (x 0)) *
        (x 1) ^ 2 * Real.sin (x 2) ^ 2 := by
    simp [flrwChristoffelDeriv]
  rw [hval]
  ring

private lemma pd_flrwG_0_H (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ) (ha : a (x 0) ≠ 0)
    (ha1 : DifferentiableAt ℝ a (x 0)) (ha2 : DifferentiableAt ℝ (deriv a) (x 0))
    (m i j : Fin 4)
    (hmatch : (m = 1 ∧ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)))
      ∨ (m = 2 ∧ ((i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0)))
      ∨ (m = 3 ∧ ((i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0)))) :
    pd 0 (fun y => flrwChristoffel a k y m i j) x = flrwChristoffelDeriv a k 0 x m i j := by
  have hH' : deriv (fun s : ℝ => deriv a s / a s) (x 0)
      = (deriv (deriv a) (x 0) * a (x 0) - (deriv a (x 0)) ^ 2) / (a (x 0)) ^ 2 := by
    convert (ha2.hasDerivAt.div ha1.hasDerivAt ha).deriv using 2
    ring
  rcases hmatch with ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ |
      ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · have hfun : (fun s => flrwChristoffel a k (Function.update x 0 s) 1 0 1)
    = fun s => deriv a s / a s :=
      funext fun s => by simp [flrwChristoffel]
    rw [pd, hfun, hH']; simp [flrwChristoffelDeriv]
  · have hfun : (fun s => flrwChristoffel a k (Function.update x 0 s) 1 1 0)
    = fun s => deriv a s / a s :=
      funext fun s => by simp [flrwChristoffel]
    rw [pd, hfun, hH']; simp [flrwChristoffelDeriv]
  · have hfun : (fun s => flrwChristoffel a k (Function.update x 0 s) 2 0 2)
    = fun s => deriv a s / a s :=
      funext fun s => by simp [flrwChristoffel]
    rw [pd, hfun, hH']; simp [flrwChristoffelDeriv]
  · have hfun : (fun s => flrwChristoffel a k (Function.update x 0 s) 2 2 0)
    = fun s => deriv a s / a s :=
      funext fun s => by simp [flrwChristoffel]
    rw [pd, hfun, hH']; simp [flrwChristoffelDeriv]
  · have hfun : (fun s => flrwChristoffel a k (Function.update x 0 s) 3 0 3)
    = fun s => deriv a s / a s :=
      funext fun s => by simp [flrwChristoffel]
    rw [pd, hfun, hH']; simp [flrwChristoffelDeriv]
  · have hfun : (fun s => flrwChristoffel a k (Function.update x 0 s) 3 3 0)
    = fun s => deriv a s / a s :=
      funext fun s => by simp [flrwChristoffel]
    rw [pd, hfun, hH']; simp [flrwChristoffelDeriv]

private lemma pd_flrwG_eq_0 (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ) (ha : a (x 0) ≠ 0)
    (ha1 : DifferentiableAt ℝ a (x 0)) (ha2 : DifferentiableAt ℝ (deriv a) (x 0))
    (m i j : Fin 4) :
    pd 0 (fun y => flrwChristoffel a k y m i j) x = flrwChristoffelDeriv a k 0 x m i j := by
  fin_cases m <;> fin_cases i <;> fin_cases j <;>
    first
    | exact pd_flrwG_0_011 a k x ha1 ha2
    | exact pd_flrwG_0_022 a k x ha1 ha2
    | exact pd_flrwG_0_033 a k x ha1 ha2
    | exact pd_flrwG_0_H a k x ha ha1 ha2 _ _ _ (by decide)
    | simp [pd, flrwChristoffel, flrwChristoffelDeriv]

private lemma pd_flrwG_1_011 (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ) (hkr : 1 - k * (x 1) ^ 2 ≠ 0) :
    pd 1 (fun y => flrwChristoffel a k y 0 1 1) x = flrwChristoffelDeriv a k 1 x 0 1 1 := by
  have hfun : (fun s => flrwChristoffel a k (Function.update x 1 s) 0 1 1)
      = fun s => (a (x 0) * deriv a (x 0)) * (1 - k * s ^ 2)⁻¹ := by
    funext s; simp [flrwChristoffel, div_eq_mul_inv]
  have hden : HasDerivAt (fun s : ℝ => 1 - k * s ^ 2) (-2 * k * x 1) (x 1) := by
    convert (hasDerivAt_const (x 1) 1).sub ((hasDerivAt_pow 2 (x 1)).const_mul k) using 1
    ring
  have hd : HasDerivAt (fun s : ℝ => (a (x 0) * deriv a (x 0)) * (1 - k * s ^ 2)⁻¹)
      ((a (x 0) * deriv a (x 0)) * (-(-2 * k * x 1) / (1 - k * (x 1) ^ 2) ^ 2)) (x 1) := by
    convert (hden.inv hkr).const_mul (a (x 0) * deriv a (x 0)) using 1
  rw [pd, hfun, hd.deriv]
  simp [flrwChristoffelDeriv]
  ring

private lemma pd_flrwG_1_022 (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ) :
    pd 1 (fun y => flrwChristoffel a k y 0 2 2) x = flrwChristoffelDeriv a k 1 x 0 2 2 := by
  have hfun : (fun s => flrwChristoffel a k (Function.update x 1 s) 0 2 2)
      = fun s => (a (x 0) * deriv a (x 0)) * s ^ 2 := by
    funext s; simp [flrwChristoffel]
  rw [pd, hfun, ((hasDerivAt_pow 2 (x 1)).const_mul (a (x 0) * deriv a (x 0))).deriv]
  simp [flrwChristoffelDeriv]
  ring

private lemma pd_flrwG_1_033 (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ) :
    pd 1 (fun y => flrwChristoffel a k y 0 3 3) x = flrwChristoffelDeriv a k 1 x 0 3 3 := by
  have hfun : (fun s => flrwChristoffel a k (Function.update x 1 s) 0 3 3)
      = fun s => s ^ 2 * (a (x 0) * deriv a (x 0) * Real.sin (x 2) ^ 2) := by
    funext s; simp [flrwChristoffel]; ring
  rw [pd, hfun,
    ((hasDerivAt_pow 2 (x 1)).mul_const (a (x 0) * deriv a (x 0) * Real.sin (x 2) ^ 2)).deriv]
  simp [flrwChristoffelDeriv]
  ring

private lemma pd_flrwG_1_111 (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ) (hkr : 1 - k * (x 1) ^ 2 ≠ 0) :
    pd 1 (fun y => flrwChristoffel a k y 1 1 1) x = flrwChristoffelDeriv a k 1 x 1 1 1 := by
  have hfun : (fun s => flrwChristoffel a k (Function.update x 1 s) 1 1 1)
      = fun s => k * s / (1 - k * s ^ 2) := by
    funext s; simp [flrwChristoffel]
  have hden : HasDerivAt (fun s : ℝ => 1 - k * s ^ 2) (-2 * k * x 1) (x 1) := by
    convert (hasDerivAt_const (x 1) 1).sub ((hasDerivAt_pow 2 (x 1)).const_mul k) using 1
    ring
  have hnum : HasDerivAt (fun s : ℝ => k * s) k (x 1) := by
    convert (hasDerivAt_id (x 1)).const_mul k using 2 <;> simp
  have hd : HasDerivAt (fun s : ℝ => k * s / (1 - k * s ^ 2))
      ((k * (1 - k * (x 1) ^ 2) - (k * x 1) * (-2 * k * x 1)) / (1 - k * (x 1) ^ 2) ^ 2)
      (x 1) := by
    convert hnum.div hden hkr using 1
  rw [pd, hfun, hd.deriv]
  simp [flrwChristoffelDeriv]
  ring

private lemma pd_flrwG_1_122 (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ) :
    pd 1 (fun y => flrwChristoffel a k y 1 2 2) x = flrwChristoffelDeriv a k 1 x 1 2 2 := by
  have hfun : (fun s => flrwChristoffel a k (Function.update x 1 s) 1 2 2)
      = fun s => -(s * (1 - k * s ^ 2)) := by
    funext s; simp [flrwChristoffel]
  have hden : HasDerivAt (fun s : ℝ => 1 - k * s ^ 2) (-2 * k * x 1) (x 1) := by
    convert (hasDerivAt_const (x 1) 1).sub ((hasDerivAt_pow 2 (x 1)).const_mul k) using 1
    ring
  have hd : HasDerivAt (fun s : ℝ => -(s * (1 - k * s ^ 2)))
      (-(1 * (1 - k * (x 1) ^ 2) + x 1 * (-2 * k * x 1))) (x 1) := by
    convert ((hasDerivAt_id (x 1)).mul hden).neg using 2 <;> simp
  rw [pd, hfun, hd.deriv]
  simp [flrwChristoffelDeriv]
  ring

private lemma pd_flrwG_1_133 (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ) :
    pd 1 (fun y => flrwChristoffel a k y 1 3 3) x = flrwChristoffelDeriv a k 1 x 1 3 3 := by
  have hfun : (fun s => flrwChristoffel a k (Function.update x 1 s) 1 3 3)
      = fun s => -(s * (1 - k * s ^ 2)) * Real.sin (x 2) ^ 2 := by
    funext s; simp [flrwChristoffel]
  have hden : HasDerivAt (fun s : ℝ => 1 - k * s ^ 2) (-2 * k * x 1) (x 1) := by
    convert (hasDerivAt_const (x 1) 1).sub ((hasDerivAt_pow 2 (x 1)).const_mul k) using 1
    ring
  have hd : HasDerivAt (fun s : ℝ => -(s * (1 - k * s ^ 2)) * Real.sin (x 2) ^ 2)
      ((-(1 * (1 - k * (x 1) ^ 2) + x 1 * (-2 * k * x 1))) * Real.sin (x 2) ^ 2) (x 1) := by
    convert ((hasDerivAt_id (x 1)).mul hden).neg.mul_const (Real.sin (x 2) ^ 2) using 2 <;> simp
  rw [pd, hfun, hd.deriv]
  have hval : flrwChristoffelDeriv a k 1 x 1 3 3
    = -(1 - 3 * k * (x 1) ^ 2) * Real.sin (x 2) ^ 2 := by
    simp [flrwChristoffelDeriv]
  rw [hval]
  ring

private lemma pd_flrwG_1_inv (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (m i j : Fin 4)
    (hmatch : (m = 2 ∧ ((i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)))
      ∨ (m = 3 ∧ ((i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1)))) :
    pd 1 (fun y => flrwChristoffel a k y m i j) x = flrwChristoffelDeriv a k 1 x m i j := by
  have hinv : deriv (fun s : ℝ => 1 / s) (x 1) = -1 / (x 1) ^ 2 := by
    rw [show (fun s : ℝ => 1 / s) = fun s : ℝ => s⁻¹ by funext s; simp [one_div]]
    rw [(hasDerivAt_inv hr).deriv]
    ring
  rcases hmatch with ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · have hfun : (fun s => flrwChristoffel a k (Function.update x 1 s) 2 1 2) = fun s => 1 / s :=
      funext fun s => by simp [flrwChristoffel]
    rw [pd, hfun, hinv]; simp [flrwChristoffelDeriv]
  · have hfun : (fun s => flrwChristoffel a k (Function.update x 1 s) 2 2 1) = fun s => 1 / s :=
      funext fun s => by simp [flrwChristoffel]
    rw [pd, hfun, hinv]; simp [flrwChristoffelDeriv]
  · have hfun : (fun s => flrwChristoffel a k (Function.update x 1 s) 3 1 3) = fun s => 1 / s :=
      funext fun s => by simp [flrwChristoffel]
    rw [pd, hfun, hinv]; simp [flrwChristoffelDeriv]
  · have hfun : (fun s => flrwChristoffel a k (Function.update x 1 s) 3 3 1) = fun s => 1 / s :=
      funext fun s => by simp [flrwChristoffel]
    rw [pd, hfun, hinv]; simp [flrwChristoffelDeriv]

private lemma pd_flrwG_eq_1 (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hkr : 1 - k * (x 1) ^ 2 ≠ 0) (m i j : Fin 4) :
    pd 1 (fun y => flrwChristoffel a k y m i j) x = flrwChristoffelDeriv a k 1 x m i j := by
  fin_cases m <;> fin_cases i <;> fin_cases j <;>
    first
    | exact pd_flrwG_1_011 a k x hkr
    | exact pd_flrwG_1_022 a k x
    | exact pd_flrwG_1_033 a k x
    | exact pd_flrwG_1_111 a k x hkr
    | exact pd_flrwG_1_122 a k x
    | exact pd_flrwG_1_133 a k x
    | exact pd_flrwG_1_inv a k x hr _ _ _ (by decide)
    | simp [pd, flrwChristoffel, flrwChristoffelDeriv]

private lemma pd_flrwG_2_033 (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ) :
    pd 2 (fun y => flrwChristoffel a k y 0 3 3) x = flrwChristoffelDeriv a k 2 x 0 3 3 := by
  have hfun : (fun s => flrwChristoffel a k (Function.update x 2 s) 0 3 3)
      = fun s => (a (x 0) * deriv a (x 0) * (x 1) ^ 2) * Real.sin s ^ 2 := by
    funext s; simp [flrwChristoffel]
  have hsinSq : HasDerivAt (fun s : ℝ => Real.sin s ^ 2)
      (2 * Real.sin (x 2) * Real.cos (x 2)) (x 2) := hasDerivAt_sin_sq (x 2)
  rw [pd, hfun, (hsinSq.const_mul (a (x 0) * deriv a (x 0) * (x 1) ^ 2)).deriv]
  simp [flrwChristoffelDeriv]

private lemma pd_flrwG_2_133 (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ) :
    pd 2 (fun y => flrwChristoffel a k y 1 3 3) x = flrwChristoffelDeriv a k 2 x 1 3 3 := by
  have hfun : (fun s => flrwChristoffel a k (Function.update x 2 s) 1 3 3)
      = fun s => -(x 1 * (1 - k * (x 1) ^ 2) * Real.sin s ^ 2) := by
    funext s; simp [flrwChristoffel]
  have hsinSq : HasDerivAt (fun s : ℝ => Real.sin s ^ 2)
      (2 * Real.sin (x 2) * Real.cos (x 2)) (x 2) := hasDerivAt_sin_sq (x 2)
  have hd : HasDerivAt (fun s : ℝ => -(x 1 * (1 - k * (x 1) ^ 2) * Real.sin s ^ 2))
      (-(x 1 * (1 - k * (x 1) ^ 2) * (2 * Real.sin (x 2) * Real.cos (x 2)))) (x 2) := by
    convert (hsinSq.const_mul (x 1 * (1 - k * (x 1) ^ 2))).neg using 1
  rw [pd, hfun, hd.deriv]
  simp [flrwChristoffelDeriv]

private lemma pd_flrwG_2_233 (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ) :
    pd 2 (fun y => flrwChristoffel a k y 2 3 3) x = flrwChristoffelDeriv a k 2 x 2 3 3 := by
  have hfun : (fun s => flrwChristoffel a k (Function.update x 2 s) 2 3 3)
      = fun s => -(Real.sin s * Real.cos s) := by
    funext s; simp [flrwChristoffel]
  have h := ((Real.hasDerivAt_sin (x 2)).mul (Real.hasDerivAt_cos (x 2))).neg
  have hderiv : deriv (fun s => -(Real.sin s * Real.cos s)) (x 2)
      = Real.sin (x 2) ^ 2 - Real.cos (x 2) ^ 2 := by
    convert h.deriv using 1
    ring
  rw [pd, hfun, hderiv]
  simp [flrwChristoffelDeriv]

private lemma pd_flrwG_2_323 (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ)
    (hsin : Real.sin (x 2) ≠ 0) :
    pd 2 (fun y => flrwChristoffel a k y 3 2 3) x = flrwChristoffelDeriv a k 2 x 3 2 3 := by
  have hfun : (fun s => flrwChristoffel a k (Function.update x 2 s) 3 2 3)
      = fun s => Real.cos s / Real.sin s := by
    funext s; simp [flrwChristoffel]
  have hsc : Real.sin (x 2) ^ 2 + Real.cos (x 2) ^ 2 = 1 := Real.sin_sq_add_cos_sq (x 2)
  have h := (Real.hasDerivAt_cos (x 2)).div (Real.hasDerivAt_sin (x 2)) hsin
  have h1 : -Real.sin (x 2) * Real.sin (x 2) - Real.cos (x 2) * Real.cos (x 2) = -1 := by
    linear_combination -hsc
  have hderiv : deriv (fun s => Real.cos s / Real.sin s) (x 2) = -1 / Real.sin (x 2) ^ 2 := by
    convert h.deriv using 1
    rw [h1]
  rw [pd, hfun, hderiv]
  simp [flrwChristoffelDeriv]

private lemma pd_flrwG_eq_2 (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ) (hsin : Real.sin (x 2) ≠ 0)
    (m i j : Fin 4) :
    pd 2 (fun y => flrwChristoffel a k y m i j) x = flrwChristoffelDeriv a k 2 x m i j := by
  fin_cases m <;> fin_cases i <;> fin_cases j <;> dsimp only <;>
    first
    | exact pd_flrwG_2_033 a k x
    | exact pd_flrwG_2_133 a k x
    | exact pd_flrwG_2_233 a k x
    | exact pd_flrwG_2_323 a k x hsin
    | simp [pd, flrwChristoffel, flrwChristoffelDeriv]

/-- All 256 partial derivatives of `flrwChristoffel` match `flrwChristoffelDeriv`. -/
lemma pd_flrwChristoffel_eq_deriv (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ) (ha : a (x 0) ≠ 0)
    (hr : x 1 ≠ 0) (hkr : 1 - k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha1 : DifferentiableAt ℝ a (x 0)) (ha2 : DifferentiableAt ℝ (deriv a) (x 0))
    (μ m i j : Fin 4) :
    pd μ (fun y => flrwChristoffel a k y m i j) x = flrwChristoffelDeriv a k μ x m i j := by
  fin_cases μ
  · exact pd_flrwG_eq_0 a k x ha ha1 ha2 m i j
  · exact pd_flrwG_eq_1 a k x hr hkr m i j
  · exact pd_flrwG_eq_2 a k x hsin m i j
  · fin_cases m <;> fin_cases i <;> fin_cases j <;> simp [pd, flrwChristoffel, flrwChristoffelDeriv]

/-- The pipeline Riemann tensor of `flrwMetric` equals `riemannFromData flrwChristoffel
flrwChristoffelDeriv`. -/
lemma riemann_flrw_eq_data (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ) (ha : a (x 0) ≠ 0)
    (hr : x 1 ≠ 0) (hkr : 1 - k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ a t)
    (ha2 : DifferentiableAt ℝ (deriv a) (x 0)) (ρ σ μ ν : Fin 4) :
    riemann (flrwMetric a k) (flrwMetricInv a k) x ρ σ μ ν
      = riemannFromData (flrwChristoffel a k) (flrwChristoffelDeriv a k) x ρ σ μ ν := by
  rw [riemann_eq_riemannFromData]
  have ha1 := ha_diff.self_of_nhds
  have h1 := (pd_christoffel_eq_pd_flrwG a k x ha hr hkr hsin ha_diff μ ρ ν σ).trans
    (pd_flrwChristoffel_eq_deriv a k x ha hr hkr hsin ha1 ha2 μ ρ ν σ)
  have h2 := (pd_christoffel_eq_pd_flrwG a k x ha hr hkr hsin ha_diff ν ρ μ σ).trans
    (pd_flrwChristoffel_eq_deriv a k x ha hr hkr hsin ha1 ha2 ν ρ μ σ)
  simp only [riemannFromData, h1, h2, christoffel_eq_flrwChristoffel a k x ha hr hkr hsin ha1]

/-!

## C. Metric-level Ricci, scalar, and Einstein tensors

Contracting the closed-form FLRW Riemann tensor yields the diagonal Ricci components, scalar
curvature `S = 6 (a''/a + (a'/a)² + k/a²)`, and Einstein tensor directly from the metric.

-/

private lemma ricci_flrw_00 (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ) (ha : a (x 0) ≠ 0)
    (hr : x 1 ≠ 0) (hkr : 1 - k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ a t)
    (ha2 : DifferentiableAt ℝ (deriv a) (x 0)) :
    ricciTensorOf (flrwMetric a k) (flrwMetricInv a k) x 0 0
      = -3 * deriv (deriv a) (x 0) / a (x 0) := by
  simp [ricciTensorOf, Fin.sum_univ_four, riemann_flrw_eq_data a k x ha hr hkr hsin ha_diff ha2,
    riemannFromData, flrwChristoffel, flrwChristoffelDeriv]
  field_simp [ha]
  ring

private lemma ricci_flrw_11 (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ) (ha : a (x 0) ≠ 0)
    (hr : x 1 ≠ 0) (hkr : 1 - k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ a t)
    (ha2 : DifferentiableAt ℝ (deriv a) (x 0)) :
    ricciTensorOf (flrwMetric a k) (flrwMetricInv a k) x 1 1
      = (a (x 0) * deriv (deriv a) (x 0) + 2 * (deriv a (x 0)) ^ 2 + 2 * k)
          / (1 - k * (x 1) ^ 2) := by
  simp [ricciTensorOf, Fin.sum_univ_four, riemann_flrw_eq_data a k x ha hr hkr hsin ha_diff ha2,
    riemannFromData, flrwChristoffel, flrwChristoffelDeriv]
  field_simp [ha, hr, hkr]
  ring

private lemma ricci_flrw_22 (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ) (ha : a (x 0) ≠ 0)
    (hr : x 1 ≠ 0) (hkr : 1 - k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ a t)
    (ha2 : DifferentiableAt ℝ (deriv a) (x 0)) :
    ricciTensorOf (flrwMetric a k) (flrwMetricInv a k) x 2 2
      = (a (x 0) * deriv (deriv a) (x 0) + 2 * (deriv a (x 0)) ^ 2 + 2 * k) * (x 1) ^ 2 := by
  have hkr' : 1 - (x 1) ^ 2 * k ≠ 0 := by rwa [mul_comm]
  simp [ricciTensorOf, Fin.sum_univ_four, riemann_flrw_eq_data a k x ha hr hkr hsin ha_diff ha2,
    riemannFromData, flrwChristoffel, flrwChristoffelDeriv]
  field_simp [ha, hr, hkr, hkr', hsin]
  rw [Real.sin_sq (x 2)]
  ring

private lemma ricci_flrw_33 (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ) (ha : a (x 0) ≠ 0)
    (hr : x 1 ≠ 0) (hkr : 1 - k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ a t)
    (ha2 : DifferentiableAt ℝ (deriv a) (x 0)) :
    ricciTensorOf (flrwMetric a k) (flrwMetricInv a k) x 3 3
      = (a (x 0) * deriv (deriv a) (x 0) + 2 * (deriv a (x 0)) ^ 2 + 2 * k) * (x 1) ^ 2
          * Real.sin (x 2) ^ 2 := by
  have hkr' : 1 - (x 1) ^ 2 * k ≠ 0 := by rwa [mul_comm]
  simp [ricciTensorOf, Fin.sum_univ_four, riemann_flrw_eq_data a k x ha hr hkr hsin ha_diff ha2,
    riemannFromData, flrwChristoffel, flrwChristoffelDeriv]
  field_simp [ha, hr, hkr, hkr', hsin]
  ring

private lemma ricci_flrw_offdiag (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ) (ha : a (x 0) ≠ 0)
    (hr : x 1 ≠ 0) (hkr : 1 - k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ a t)
    (ha2 : DifferentiableAt ℝ (deriv a) (x 0)) {σ ν : Fin 4} (h : σ ≠ ν) :
    ricciTensorOf (flrwMetric a k) (flrwMetricInv a k) x σ ν = 0 := by
  fin_cases σ <;> fin_cases ν <;> try exact absurd rfl h
  all_goals
    simp [ricciTensorOf, Fin.sum_univ_four, riemann_flrw_eq_data a k x ha hr hkr hsin ha_diff ha2,
      riemannFromData, flrwChristoffel, flrwChristoffelDeriv]
  all_goals ring

/-- Complete coordinate-pipeline Ricci tensor of the FLRW metric. -/
lemma ricciTensorOf_flrw (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ) (ha : a (x 0) ≠ 0)
    (hr : x 1 ≠ 0) (hkr : 1 - k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ a t)
    (ha2 : DifferentiableAt ℝ (deriv a) (x 0)) (σ ν : Fin 4) :
    ricciTensorOf (flrwMetric a k) (flrwMetricInv a k) x σ ν
      = if σ = ν then
          if σ = 0 then -3 * deriv (deriv a) (x 0) / a (x 0)
          else if σ = 1 then
            (a (x 0) * deriv (deriv a) (x 0) + 2 * (deriv a (x 0)) ^ 2 + 2 * k)
              / (1 - k * (x 1) ^ 2)
          else if σ = 2 then
            (a (x 0) * deriv (deriv a) (x 0) + 2 * (deriv a (x 0)) ^ 2 + 2 * k) * (x 1) ^ 2
          else
            (a (x 0) * deriv (deriv a) (x 0) + 2 * (deriv a (x 0)) ^ 2 + 2 * k) * (x 1) ^ 2
              * Real.sin (x 2) ^ 2
        else 0 := by
  fin_cases σ <;> fin_cases ν <;> dsimp only
  · exact ricci_flrw_00 a k x ha hr hkr hsin ha_diff ha2
  · exact ricci_flrw_offdiag a k x ha hr hkr hsin ha_diff ha2 (by decide)
  · exact ricci_flrw_offdiag a k x ha hr hkr hsin ha_diff ha2 (by decide)
  · exact ricci_flrw_offdiag a k x ha hr hkr hsin ha_diff ha2 (by decide)
  · exact ricci_flrw_offdiag a k x ha hr hkr hsin ha_diff ha2 (by decide)
  · exact ricci_flrw_11 a k x ha hr hkr hsin ha_diff ha2
  · exact ricci_flrw_offdiag a k x ha hr hkr hsin ha_diff ha2 (by decide)
  · exact ricci_flrw_offdiag a k x ha hr hkr hsin ha_diff ha2 (by decide)
  · exact ricci_flrw_offdiag a k x ha hr hkr hsin ha_diff ha2 (by decide)
  · exact ricci_flrw_offdiag a k x ha hr hkr hsin ha_diff ha2 (by decide)
  · exact ricci_flrw_22 a k x ha hr hkr hsin ha_diff ha2
  · exact ricci_flrw_offdiag a k x ha hr hkr hsin ha_diff ha2 (by decide)
  · exact ricci_flrw_offdiag a k x ha hr hkr hsin ha_diff ha2 (by decide)
  · exact ricci_flrw_offdiag a k x ha hr hkr hsin ha_diff ha2 (by decide)
  · exact ricci_flrw_offdiag a k x ha hr hkr hsin ha_diff ha2 (by decide)
  · exact ricci_flrw_33 a k x ha hr hkr hsin ha_diff ha2

/-- FLRW scalar curvature `S = 6 (a'' / a + (a' / a)² + k / a²)`. -/
lemma ricciScalarOf_flrw (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ) (ha : a (x 0) ≠ 0)
    (hr : x 1 ≠ 0) (hkr : 1 - k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ a t)
    (ha2 : DifferentiableAt ℝ (deriv a) (x 0)) :
    ricciScalarOf (flrwMetric a k) (flrwMetricInv a k) x
      = 6 * (deriv (deriv a) (x 0) / a (x 0) + (deriv a (x 0) / a (x 0)) ^ 2
          + k / (a (x 0)) ^ 2) := by
  simp only [ricciScalarOf, ricciTensorOf_flrw a k x ha hr hkr hsin ha_diff ha2, flrwMetricInv,
    Fin.sum_univ_four, Fin.reduceEq, ↓reduceIte, Fin.isValue, mul_zero, add_zero, zero_add]
  field_simp [ha, hr, hkr, hsin]
  ring

/-- Complete FLRW Einstein tensor: `G_{00} = 3 ((a'/a)² + k/a²)` and
`G_{ii} = -(2 a''/a + (a'/a)² + k/a²) g_{ii}` for spatial indices `i = 1, 2, 3`. -/
lemma einsteinTensorOf_flrw (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ) (ha : a (x 0) ≠ 0)
    (hr : x 1 ≠ 0) (hkr : 1 - k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ a t)
    (ha2 : DifferentiableAt ℝ (deriv a) (x 0)) (i j : Fin 4) :
    einsteinTensorOf (flrwMetric a k) (flrwMetricInv a k) x i j
      = if i = j then
          if i = 0 then 3 * ((deriv a (x 0) / a (x 0)) ^ 2 + k / (a (x 0)) ^ 2)
          else -(2 * (deriv (deriv a) (x 0) / a (x 0))
            + (deriv a (x 0) / a (x 0)) ^ 2 + k / (a (x 0)) ^ 2) * flrwMetric a k x i j
        else 0 := by
  simp only [einsteinTensorOf, ricciTensorOf_flrw a k x ha hr hkr hsin ha_diff ha2,
    ricciScalarOf_flrw a k x ha hr hkr hsin ha_diff ha2, flrwMetric]
  fin_cases i <;> fin_cases j <;> simp
  · field_simp [ha]; ring
  · field_simp [ha, hkr]; ring
  · field_simp [ha]; ring
  · field_simp [ha]; ring

/-!

## D. Equivalence with the Friedmann equations and Physlib Cosmology

Equating the pipeline Einstein tensor with comoving perfect-fluid stress-energy directly recovers
the first and second Friedmann equations of `Cosmology.FLRW`.

-/

/-- Comoving perfect-fluid stress-energy tensor `T_{ij} = (ρ + p) u_i u_j + p g_{ij}` for a
comoving observer `u = (-1, 0, 0, 0)` (units `c = 1`). -/
def perfectFluidT (ρ p : ℝ) (g : Tensor2 4) : Tensor2 4 :=
  fun i j => (ρ + p) * (if i = 0 ∧ j = 0 then 1 else 0) + p * g i j

/-- Einstein's equation `G_{ij} + Λ g_{ij} = 8 π G T_{ij}` for the FLRW metric and a comoving
perfect fluid is equivalent to the first- and second-order Friedmann equations (`c = 1`). -/
lemma einsteinTensorOf_flrw_iff_friedmann (a : ℝ → ℝ) (k Λ G ρ p : ℝ) (x : Fin 4 → ℝ)
    (ha : a (x 0) ≠ 0) (hr : x 1 ≠ 0) (hkr : 1 - k * (x 1) ^ 2 ≠ 0)
    (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ a t)
    (ha2 : DifferentiableAt ℝ (deriv a) (x 0)) :
    (∀ i j, einsteinTensorOf (flrwMetric a k) (flrwMetricInv a k) x i j + Λ * flrwMetric a k x i j
        = 8 * Real.pi * G * perfectFluidT ρ p (flrwMetric a k x) i j)
      ↔ ((deriv a (x 0) / a (x 0)) ^ 2
            = (8 * Real.pi * G / 3) * ρ - k / (a (x 0)) ^ 2 + Λ / 3)
          ∧ (deriv (deriv a) (x 0) / a (x 0)
              = -(4 * Real.pi * G / 3) * (ρ + 3 * p) + Λ / 3) := by
  have hg11 : flrwMetric a k x 1 1 ≠ 0 := by
    simp [flrwMetric, ha, hkr]
  constructor
  · intro h
    have h00 := h 0 0
    have h11 := h 1 1
    rw [einsteinTensorOf_flrw a k x ha hr hkr hsin ha_diff ha2 0 0] at h00
    rw [einsteinTensorOf_flrw a k x ha hr hkr hsin ha_diff ha2 1 1] at h11
    simp [flrwMetric, perfectFluidT] at h00 h11
    have hf1 : (deriv a (x 0) / a (x 0)) ^ 2
        = (8 * Real.pi * G / 3) * ρ - k / (a (x 0)) ^ 2 + Λ / 3 := by
      linarith
    have h2 : -(2 * (deriv (deriv a) (x 0) / a (x 0))
          + (deriv a (x 0) / a (x 0)) ^ 2 + k / (a (x 0)) ^ 2) + Λ
        = 8 * Real.pi * G * p := by
      apply mul_right_cancel₀ hg11
      have h11' : -(2 * (deriv (deriv a) (x 0) / a (x 0))
            + (deriv a (x 0) / a (x 0)) ^ 2 + k / (a (x 0)) ^ 2) * (a (x 0) ^ 2 / (1 - k * x 1 ^ 2))
            + Λ * (a (x 0) ^ 2 / (1 - k * x 1 ^ 2))
          = 8 * Real.pi * G * p * (a (x 0) ^ 2 / (1 - k * x 1 ^ 2)) := by
        linear_combination h11
      have hg11' : a (x 0) ^ 2 / (1 - k * x 1 ^ 2) = flrwMetric a k x 1 1 := by
        simp [flrwMetric]
      rw [hg11'] at h11'
      linear_combination h11'
    refine ⟨hf1, ?_⟩
    linarith
  · rintro ⟨hf1, hf2⟩ i j
    rw [einsteinTensorOf_flrw a k x ha hr hkr hsin ha_diff ha2 i j]
    have hcoef : -(2 * (deriv (deriv a) (x 0) / a (x 0))
        + (deriv a (x 0) / a (x 0)) ^ 2 + k / (a (x 0)) ^ 2) + Λ = 8 * Real.pi * G * p := by
      linarith
    fin_cases i <;> fin_cases j <;> simp [flrwMetric, perfectFluidT]
    · linarith
    · linear_combination (a (x 0) ^ 2 / (1 - k * x 1 ^ 2)) * hcoef
    · linear_combination (a (x 0) ^ 2 * x 1 ^ 2) * hcoef
    · linear_combination (a (x 0) ^ 2 * x 1 ^ 2 * Real.sin (x 2) ^ 2) * hcoef

/-- The real-coordinate scale factor `τ ↦ U.a ⟨τ⟩` extracted from `U : Cosmology.FLRW`. -/
noncomputable def flrwScaleFn (U : Cosmology.FLRW) : ℝ → ℝ := fun τ => U.a ⟨τ⟩

/-- Neighbourhood differentiability of `flrwScaleFn U` at any time `t ∈ U.I`. -/
lemma eventually_differentiableAt_flrwScaleFn (U : Cosmology.FLRW) {t : Time} (ht : t ∈ U.I) :
    ∀ᶠ τ in nhds t.val, DifferentiableAt ℝ (flrwScaleFn U) τ := by
  have hmem : ∀ᶠ τ in nhds t.val, (⟨τ⟩ : Time) ∈ U.I :=
    (Time.toRealCLE.symm.continuous.tendsto t.val).eventually (U.isOpen_I.mem_nhds ht)
  filter_upwards [hmem] with τ hτ
  exact (Time.hasDerivAt_mk_of_differentiableAt (U.differentiableAt_a hτ)).differentiableAt

/-- First derivative of `flrwScaleFn U` equals `Time.deriv U.a`. -/
lemma deriv_flrwScaleFn_eq (U : Cosmology.FLRW) {t : Time} (ht : t ∈ U.I) :
    deriv (flrwScaleFn U) t.val = Time.deriv U.a t :=
  (Time.hasDerivAt_mk_of_differentiableAt (U.differentiableAt_a ht)).deriv

/-- `flrwScaleFn U` is twice differentiable at `t.val` with second derivative
`Time.deriv (Time.deriv U.a) t`. -/
lemma hasDerivAt_deriv_flrwScaleFn (U : Cosmology.FLRW) {t : Time} (ht : t ∈ U.I) :
    HasDerivAt (deriv (flrwScaleFn U)) (Time.deriv (Time.deriv U.a) t) t.val := by
  have hmem : ∀ᶠ τ in nhds t.val, (⟨τ⟩ : Time) ∈ U.I :=
    (Time.toRealCLE.symm.continuous.tendsto t.val).eventually (U.isOpen_I.mem_nhds ht)
  have heq : deriv (flrwScaleFn U) =ᶠ[nhds t.val] fun τ => Time.deriv U.a ⟨τ⟩ := by
    filter_upwards [hmem] with τ hτ
    exact (Time.hasDerivAt_mk_of_differentiableAt (U.differentiableAt_a hτ)).deriv
  have hderiv := Time.hasDerivAt_mk_of_differentiableAt (U.differentiableAt_deriv_a ht)
  exact hderiv.congr_of_eventuallyEq heq

/-- Bridge to `Physlib.Cosmology.FLRW`: the coordinate-pipeline Einstein equation for
`flrwMetric (flrwScaleFn U) U.geometry.curvature` is equivalent to `FirstOrderFriedmann` and
`SecondOrderFriedmann` (`c = 1`) at `t ∈ U.I`. -/
lemma einsteinTensorOf_flrw_iff_cosmology_friedmann (U : Cosmology.FLRW) (F : Cosmology.CosmicFluid)
    (Λ G : ℝ) {t : Time} (ht : t ∈ U.I) (x : Fin 4 → ℝ) (hx0 : x 0 = t.val) (hr : x 1 ≠ 0)
    (hkr : 1 - U.geometry.curvature * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0) :
    (∀ i j, einsteinTensorOf (flrwMetric (flrwScaleFn U) U.geometry.curvature)
          (flrwMetricInv (flrwScaleFn U) U.geometry.curvature) x i j
          + Λ * flrwMetric (flrwScaleFn U) U.geometry.curvature x i j
        = 8 * Real.pi * G * perfectFluidT (F.ρ t) (F.p t)
            (flrwMetric (flrwScaleFn U) U.geometry.curvature x) i j)
      ↔ Cosmology.FLRW.FriedmannEquation.FirstOrderFriedmann U.a F.ρ U.geometry.curvature Λ G 1 t
          ∧ Cosmology.FLRW.FriedmannEquation.SecondOrderFriedmann U.a F.ρ F.p Λ G 1 t := by
  have ha : flrwScaleFn U (x 0) ≠ 0 := by
    rw [hx0]
    exact U.a_ne_zero ht
  have ha_diff : ∀ᶠ τ in nhds (x 0), DifferentiableAt ℝ (flrwScaleFn U) τ := by
    rw [hx0]
    exact eventually_differentiableAt_flrwScaleFn U ht
  have hd2 := hasDerivAt_deriv_flrwScaleFn U ht
  have ha2 : DifferentiableAt ℝ (deriv (flrwScaleFn U)) (x 0) := by
    rw [hx0]
    exact hd2.differentiableAt
  have hd1_eq : deriv (flrwScaleFn U) (x 0) = Time.deriv U.a t := by
    rw [hx0]
    exact deriv_flrwScaleFn_eq U ht
  have hd2_eq : deriv (deriv (flrwScaleFn U)) (x 0) = Time.deriv (Time.deriv U.a) t := by
    rw [hx0]
    exact hd2.deriv
  have ha0_eq : flrwScaleFn U (x 0) = U.a t := by
    rw [hx0]
    rfl
  rw [einsteinTensorOf_flrw_iff_friedmann (flrwScaleFn U) U.geometry.curvature Λ G (F.ρ t) (F.p t) x
    ha hr hkr hsin ha_diff ha2]
  simp only [Cosmology.FLRW.FriedmannEquation.FirstOrderFriedmann,
    Cosmology.FLRW.FriedmannEquation.SecondOrderFriedmann, SpeedOfLight.val_one, one_pow,
    mul_one, div_one, ha0_eq, hd1_eq, hd2_eq]

/-- If the FLRW Einstein equation holds across `U.I` (say at a spatial chart point `r₀, θ₀`),
then `U` and `F` form a `Cosmology.FLRW.FriedmannSolution F Λ G 1` (and hence automatically satisfy
the fluid continuity equation by `Cosmology.FLRW.FriedmannSolution.continuityEquation`). -/
lemma friedmannSolution_of_einsteinTensorOf_flrw (U : Cosmology.FLRW) (F : Cosmology.CosmicFluid)
    (Λ G r₀ θ₀ : ℝ) (hr : r₀ ≠ 0) (hkr : 1 - U.geometry.curvature * r₀ ^ 2 ≠ 0)
    (hsin : Real.sin θ₀ ≠ 0)
    (heinst : ∀ t ∈ U.I, ∀ i j,
      let x : Fin 4 → ℝ := ![t.val, r₀, θ₀, 0]
      einsteinTensorOf (flrwMetric (flrwScaleFn U) U.geometry.curvature)
          (flrwMetricInv (flrwScaleFn U) U.geometry.curvature) x i j
          + Λ * flrwMetric (flrwScaleFn U) U.geometry.curvature x i j
        = 8 * Real.pi * G * perfectFluidT (F.ρ t) (F.p t)
            (flrwMetric (flrwScaleFn U) U.geometry.curvature x) i j) :
    U.FriedmannSolution F Λ G 1 := by
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · exact ((einsteinTensorOf_flrw_iff_cosmology_friedmann U F Λ G ht ![t.val, r₀, θ₀, 0]
      rfl hr hkr hsin).mp (heinst t ht)).1
  · exact ((einsteinTensorOf_flrw_iff_cosmology_friedmann U F Λ G ht ![t.val, r₀, θ₀, 0]
      rfl hr hkr hsin).mp (heinst t ht)).2

/-- Overload of `friedmannSolution_of_einsteinTensorOf_flrw` taking the Newtonian constant as a
`GravitationalConstant`. -/
lemma friedmannSolution_of_einsteinTensorOf_flrw_G (U : Cosmology.FLRW) (F : Cosmology.CosmicFluid)
    (Λ : ℝ) (G : GravitationalConstant) (r₀ θ₀ : ℝ) (hr : r₀ ≠ 0)
    (hkr : 1 - U.geometry.curvature * r₀ ^ 2 ≠ 0)
    (hsin : Real.sin θ₀ ≠ 0)
    (heinst : ∀ t ∈ U.I, ∀ i j,
      let x : Fin 4 → ℝ := ![t.val, r₀, θ₀, 0]
      einsteinTensorOf (flrwMetric (flrwScaleFn U) U.geometry.curvature)
          (flrwMetricInv (flrwScaleFn U) U.geometry.curvature) x i j
          + Λ * flrwMetric (flrwScaleFn U) U.geometry.curvature x i j
        = 8 * Real.pi * G.val * perfectFluidT (F.ρ t) (F.p t)
            (flrwMetric (flrwScaleFn U) U.geometry.curvature x) i j) :
    U.FriedmannSolution F Λ G.val 1 :=
  friedmannSolution_of_einsteinTensorOf_flrw U F Λ G.val r₀ θ₀ hr hkr hsin heinst

/-- The coordinate metric of an FLRW spacetime. -/
noncomputable def FLRWSpacetime.metric (S : FLRWSpacetime) (x : Fin 4 → ℝ) : Tensor2 4 :=
  flrwMetric S.a S.k x

/-- The inverse coordinate metric of an FLRW spacetime. -/
noncomputable def FLRWSpacetime.metricInv (S : FLRWSpacetime) (x : Fin 4 → ℝ) : Tensor2 4 :=
  flrwMetricInv S.a S.k x

end FLRW

end GeneralRelativity
