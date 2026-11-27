/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.General.SchwarzschildDeSitter.Basic
public import PhyslibAlpha.Relativity.Metrics.StaticSphericalMetric.RicciCurvature
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!

# Schwarzschild and Schwarzschild–de Sitter coordinate curvature

Coordinate verification of `SchwarzschildDeSitterSpacetime` and Schwarzschild (`Λ = 0`) metrics
from `g ↦ ∂g ↦ Γ ↦ ∂Γ ↦ R^ρ_{σμν} ↦ Ric ↦ R ↦ G`.

## i. Overview

This module connects `SchwarzschildDeSitterSpacetime.metric` and
`SchwarzschildDeSitterSpacetime.metricInv` to the general static spherically symmetric curvature
formulas in `GeneralRelativity.StaticSpherical`:

1. Equates `S.christoffel` and `S.christoffelDeriv` with `S.toStaticSpherical.christoffel` and
   `S.toStaticSpherical.christoffelDeriv`.
2. Delegates `christoffel_eq`, `pd_christoffel_eq`, `pd_christoffel_eq_deriv`, `ricciTensor`, and
   `ricciScalar` directly to `GeneralRelativity.StaticSpherical`.
3. Obtains `riemann_eq_data`, all six independent Riemann components
   `riemann_components_from_metric`, `G_{ij} = -Λ g_{ij}` (`einsteinTensor`), and frame agreement
   `frameScale * Ric = Λ η` (`ricciTensor_frame`).

## ii. Key results

- `SchwarzschildDeSitterSpacetime.christoffel`,
  `SchwarzschildDeSitterSpacetime.christoffelDeriv` : Christoffel table and complete 256-entry
  derivative table.
- `SchwarzschildDeSitterSpacetime.christoffel_eq`,
  `SchwarzschildDeSitterSpacetime.pd_christoffel_eq_deriv`,
  `SchwarzschildDeSitterSpacetime.riemann_eq_data` : metric-to-Riemann bridge via
  `StaticSpherical`.
- `SchwarzschildDeSitterSpacetime.riemann_components_from_metric`,
  `SchwarzschildDeSitterSpacetime.ricciTensor`, `SchwarzschildDeSitterSpacetime.ricciScalar`,
  `SchwarzschildDeSitterSpacetime.einsteinTensor`,
  `SchwarzschildDeSitterSpacetime.ricciTensor_frame` : general-`Λ` metric-level solution
  theorems.

## iii. Table of contents

- A. Christoffel and derivative tables
- B. Static-spherical reduction and Christoffel identification
- C. Metric-level Riemann, Ricci, scalar, and Einstein tensors

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 6 (Sec. 6.1) & Sec. 4.2.
  [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 23 & Ch. 27.
  [ref: mtw_1973_gravitation]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 7
  (https://arxiv.org/pdf/gr-qc/9712019#page=168). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

namespace SchwarzschildDeSitter

open GeneralRelativity.CoordinateCurvature
open GeneralRelativity.StaticSpherical

namespace SchwarzschildDeSitterSpacetime

/-!

## A. Christoffel and derivative tables

Explicit tables for the Schwarzschild–de Sitter Christoffel connection and its partial derivatives
isolate rational algebra in `S.metricFn` and `S.metricFnHalfDeriv` from generic summation loops.

-/

/-- Closed-form Schwarzschild–de Sitter Christoffel symbols in `(t, r, θ, φ)` coordinates. -/
noncomputable def christoffel (S : SchwarzschildDeSitterSpacetime) (x : Fin 4 → ℝ)
    (k i j : Fin 4) : ℝ :=
  if k = 0 then
    (if (i = 1 ∧ j = 0) ∨ (i = 0 ∧ j = 1) then
      S.metricFnHalfDeriv (x 1) / S.metricFn (x 1)
     else 0)
  else if k = 1 then
    (if i = 0 ∧ j = 0 then S.metricFn (x 1) * S.metricFnHalfDeriv (x 1)
     else if i = 1 ∧ j = 1 then -(S.metricFnHalfDeriv (x 1) / S.metricFn (x 1))
     else if i = 2 ∧ j = 2 then -(x 1 * S.metricFn (x 1))
     else if i = 3 ∧ j = 3 then -(x 1 * Real.sin (x 2) ^ 2 * S.metricFn (x 1))
     else 0)
  else if k = 2 then
    (if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then 1 / (x 1)
     else if i = 3 ∧ j = 3 then -(Real.sin (x 2) * Real.cos (x 2)) else 0)
  else
    (if (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) then 1 / (x 1)
     else if (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) then
       Real.cos (x 2) / Real.sin (x 2) else 0)

/-- Complete partial-derivative table `∂_μ christoffel^k_{ij}` across all 256 index tuples
`(μ, k, i, j)` for Schwarzschild–de Sitter spacetime. -/
noncomputable def christoffelDeriv (S : SchwarzschildDeSitterSpacetime) (μ : Fin 4)
    (x : Fin 4 → ℝ) (k i j : Fin 4) : ℝ :=
  if μ = 1 then
    (if k = 0 ∧ ((i = 1 ∧ j = 0) ∨ (i = 0 ∧ j = 1)) then
       (-2 * S.M / (x 1) ^ 3 - S.Λ / 3) / S.metricFn (x 1)
         - S.metricFnHalfDeriv (x 1) * (2 * S.metricFnHalfDeriv (x 1)) /
             (S.metricFn (x 1)) ^ 2
     else if k = 1 ∧ i = 0 ∧ j = 0 then
       (2 * S.metricFnHalfDeriv (x 1)) * S.metricFnHalfDeriv (x 1)
         + S.metricFn (x 1) * (-2 * S.M / (x 1) ^ 3 - S.Λ / 3)
     else if k = 1 ∧ i = 1 ∧ j = 1 then
       -((-2 * S.M / (x 1) ^ 3 - S.Λ / 3) / S.metricFn (x 1)
         - S.metricFnHalfDeriv (x 1) * (2 * S.metricFnHalfDeriv (x 1)) /
             (S.metricFn (x 1)) ^ 2)
     else if k = 1 ∧ i = 2 ∧ j = 2 then
       -(S.metricFn (x 1)) - (x 1) * (2 * S.metricFnHalfDeriv (x 1))
     else if k = 1 ∧ i = 3 ∧ j = 3 then
       (-(S.metricFn (x 1)) - (x 1) * (2 * S.metricFnHalfDeriv (x 1))) * Real.sin (x 2) ^ 2
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

/-!

## B. Static-spherical reduction and Christoffel identification

Recognizing `S.metric` via `S.toStaticSpherical` delegates the coordinate Christoffel and Ricci
computations directly to `GeneralRelativity.StaticSpherical`.

-/

private lemma eventually_differentiableAt_metricFn (S : SchwarzschildDeSitterSpacetime) (r : ℝ)
    (hr : r ≠ 0) :
    ∀ᶠ s in nhds r, DifferentiableAt ℝ S.metricFn s := by
  filter_upwards [eventually_ne_nhds hr] with s hs
  exact (S.hasDerivAt_metricFn s hs).differentiableAt

private lemma hasDerivAt_deriv_metricFn (S : SchwarzschildDeSitterSpacetime) (r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (deriv S.metricFn) (-4 * S.M / r ^ 3 - 2 * S.Λ / 3) r := by
  have heq : deriv S.metricFn =ᶠ[nhds r] fun s => 2 * S.metricFnHalfDeriv s := by
    filter_upwards [eventually_ne_nhds hr] with s hs
    exact S.deriv_metricFn s hs
  have hd : HasDerivAt (fun s : ℝ => 2 * S.metricFnHalfDeriv s)
      (-4 * S.M / r ^ 3 - 2 * S.Λ / 3) r := by
    convert (S.hasDerivAt_metricFnHalfDeriv r hr).const_mul 2 using 1
    ring
  exact hd.congr_of_eventuallyEq heq

private lemma christoffel_eq_staticSpherical (S : SchwarzschildDeSitterSpacetime)
    (x : Fin 4 → ℝ) (hr : x 1 ≠ 0) :
    ∀ k i j, S.christoffel x k i j = S.toStaticSpherical.christoffel x k i j := by
  intro k i j
  have hd1 := S.deriv_metricFn (x 1) hr
  fin_cases k <;> fin_cases i <;> fin_cases j <;> simp [christoffel,
    StaticSphericalMetric.christoffel, toStaticSpherical, hd1] <;> ring

private lemma christoffelDeriv_eq_staticSpherical (S : SchwarzschildDeSitterSpacetime)
    (x : Fin 4 → ℝ) (hr : x 1 ≠ 0) (hf : S.metricFn (x 1) ≠ 0) (μ k i j : Fin 4) :
    S.christoffelDeriv μ x k i j =
      S.toStaticSpherical.christoffelDeriv μ x k i j := by
  have hd1 := S.deriv_metricFn (x 1) hr
  have hd2 := (S.hasDerivAt_deriv_metricFn (x 1) hr).deriv
  fin_cases μ
  · simp [christoffelDeriv, StaticSphericalMetric.christoffelDeriv]
  · fin_cases k <;> fin_cases i <;> fin_cases j <;>
      simp [christoffelDeriv, StaticSphericalMetric.christoffelDeriv, toStaticSpherical, hd1, hd2]
    all_goals field_simp [hf]; ring
  · fin_cases k <;> fin_cases i <;> fin_cases j <;>
      simp [christoffelDeriv, StaticSphericalMetric.christoffelDeriv, toStaticSpherical]
  · simp [christoffelDeriv, StaticSphericalMetric.christoffelDeriv]

/-- All 64 Christoffel symbols computed from the coordinate metric equal
`SchwarzschildDeSitterSpacetime.christoffel`, for every `Λ`. -/
lemma christoffel_eq (S : SchwarzschildDeSitterSpacetime) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.metricFn (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) :
    ∀ k i j, CoordinateCurvature.christoffel S.metric S.metricInv x k i j
      = S.christoffel x k i j := by
  intro k i j
  have hm : S.metric = S.toStaticSpherical.metric := rfl
  have hmi : S.metricInv = S.toStaticSpherical.metricInv := rfl
  rw [hm, hmi, S.toStaticSpherical.christoffel_eq x hr hf hsin
      (S.hasDerivAt_metricFn (x 1) hr).differentiableAt k i j,
    S.christoffel_eq_staticSpherical x hr k i j]

/-- Away from the central singularity (`r ≠ 0`), event and cosmological horizons (`f ≠ 0`), and
polar axis (`sin θ ≠ 0`), every spacetime point has a regular neighborhood where the coordinate
Christoffel symbols and `S.christoffel` agree, so their coordinate partial derivatives match
along every axis. -/
lemma pd_christoffel_eq (S : SchwarzschildDeSitterSpacetime) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.metricFn (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) (μ a b c : Fin 4) :
    coordDeriv μ (fun y => CoordinateCurvature.christoffel S.metric S.metricInv y a b c) x
      = coordDeriv μ (fun y => S.christoffel y a b c) x := by
  have hm : S.metric = S.toStaticSpherical.metric := rfl
  have hmi : S.metricInv = S.toStaticSpherical.metricInv := rfl
  rw [hm, hmi, S.toStaticSpherical.pd_christoffel_eq x hr hf hsin
      (S.eventually_differentiableAt_metricFn (x 1) hr) μ a b c]
  have hr_nhds : ∀ᶠ y in nhds x, y 1 ≠ 0 :=
    (continuous_apply (1 : Fin 4)).continuousAt.eventually_ne hr
  have heq : (fun y => S.toStaticSpherical.christoffel y a b c) =ᶠ[nhds x]
      fun y => S.christoffel y a b c := by
    filter_upwards [hr_nhds] with y hy
    exact (S.christoffel_eq_staticSpherical y hy a b c).symm
  exact coordDeriv_congr_nhds μ x heq

/-- Every partial derivative of `S.christoffel` equals `S.christoffelDeriv`, across all 256
index tuples `(μ, k, i, j)`. -/
lemma pd_christoffel_eq_deriv (S : SchwarzschildDeSitterSpacetime) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.metricFn (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) (μ k i j : Fin 4) :
    coordDeriv μ (fun y => S.christoffel y k i j) x = S.christoffelDeriv μ x k i j := by
  have hr_nhds : ∀ᶠ y in nhds x, y 1 ≠ 0 :=
    (continuous_apply (1 : Fin 4)).continuousAt.eventually_ne hr
  have heq : (fun y => S.christoffel y k i j) =ᶠ[nhds x]
      fun y => S.toStaticSpherical.christoffel y k i j := by
    filter_upwards [hr_nhds] with y hy
    exact S.christoffel_eq_staticSpherical y hy k i j
  rw [coordDeriv_congr_nhds μ x heq,
    S.toStaticSpherical.pd_christoffel_eq_deriv x hr hf hsin
      (S.hasDerivAt_metricFn (x 1) hr).differentiableAt
      (S.hasDerivAt_deriv_metricFn (x 1) hr).differentiableAt μ k i j,
    S.christoffelDeriv_eq_staticSpherical x hr hf μ k i j]

/-!

## C. Metric-level Riemann, Ricci, scalar, and Einstein tensors

Evaluating `riemann`, `ricciTensor`, `ricciScalar`, and `einsteinTensor` in the regular region
verifies the cosmological Einstein-space equations `Ric_{ij} = Λ g_{ij}` and `G_{ij} = -Λ g_{ij}`.

-/

/-- The coordinate Riemann tensor of `S.metric` equals
`riemannFromData S.christoffel S.christoffelDeriv` at every 4-tuple `(ρ, σ, μ, ν)`, for general
`Λ`. -/
lemma riemann_eq_data (S : SchwarzschildDeSitterSpacetime) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.metricFn (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) (ρ σ μ ν : Fin 4) :
    CoordinateCurvature.riemann S.metric S.metricInv x ρ σ μ ν
      = riemannFromData S.christoffel S.christoffelDeriv x ρ σ μ ν := by
  rw [riemann_eq_riemannFromData]
  have h1 : coordDeriv μ (fun z => CoordinateCurvature.christoffel S.metric S.metricInv z ρ ν σ) x
      = S.christoffelDeriv μ x ρ ν σ :=
    (S.pd_christoffel_eq x hr hf hsin μ ρ ν σ).trans
      (S.pd_christoffel_eq_deriv x hr hf hsin μ ρ ν σ)
  have h2 : coordDeriv ν (fun z => CoordinateCurvature.christoffel S.metric S.metricInv z ρ μ σ) x
      = S.christoffelDeriv ν x ρ μ σ :=
    (S.pd_christoffel_eq x hr hf hsin ν ρ μ σ).trans
      (S.pd_christoffel_eq_deriv x hr hf hsin ν ρ μ σ)
  simp only [riemannFromData, h1, h2, S.christoffel_eq x hr hf hsin]

/-- All six independent Schwarzschild–de Sitter Riemann components computed directly from the
coordinate metric, for general `Λ`. -/
lemma riemann_components_from_metric (S : SchwarzschildDeSitterSpacetime) (x : Fin 4 → ℝ)
    (hr : x 1 ≠ 0) (hf : S.metricFn (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) :
    (CoordinateCurvature.riemann S.metric S.metricInv x 0 1 0 1
        = (2 * S.M / (x 1) ^ 3 + S.Λ / 3) / S.metricFn (x 1))
      ∧ (CoordinateCurvature.riemann S.metric S.metricInv x 0 2 0 2 = S.Λ * (x 1) ^ 2 / 3 - S.M / (x 1))
      ∧ (CoordinateCurvature.riemann S.metric S.metricInv x 0 3 0 3
          = (S.Λ * (x 1) ^ 2 / 3 - S.M / (x 1)) * Real.sin (x 2) ^ 2)
      ∧ (CoordinateCurvature.riemann S.metric S.metricInv x 1 2 1 2 = S.Λ * (x 1) ^ 2 / 3 - S.M / (x 1))
      ∧ (CoordinateCurvature.riemann S.metric S.metricInv x 1 3 1 3
          = (S.Λ * (x 1) ^ 2 / 3 - S.M / (x 1)) * Real.sin (x 2) ^ 2)
      ∧ (CoordinateCurvature.riemann S.metric S.metricInv x 2 3 2 3
          = (2 * S.M / (x 1) + S.Λ * (x 1) ^ 2 / 3) * Real.sin (x 2) ^ 2) := by
  have hd := S.deriv_metricFnHalfDeriv_div_metricFn (x 1) hr hf
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := S.riemann_t_rtr (x 1) hr hf
    simp [S.riemann_eq_data x hr hf hsin, riemannFromData, christoffel,
      christoffelDeriv, Fin.sum_univ_four, hd, add_assoc, sub_eq_add_neg, pow_two] at h ⊢
    linear_combination h
  · simpa [S.riemann_eq_data x hr hf hsin, riemannFromData, christoffel,
      christoffelDeriv, Fin.sum_univ_four, add_assoc, sub_eq_add_neg, pow_two] using
      S.riemann_t_thetatheta (x 1) hr hf
  · simpa [S.riemann_eq_data x hr hf hsin, riemannFromData, christoffel,
      christoffelDeriv, Fin.sum_univ_four, add_assoc, sub_eq_add_neg, pow_two] using
      S.riemann_t_phitphi (x 1) (x 2) hr hf
  · have h := S.riemann_r_thetar (x 1) hr hf
    simp [S.riemann_eq_data x hr hf hsin, riemannFromData, christoffel,
      christoffelDeriv, Fin.sum_univ_four, add_assoc, sub_eq_add_neg, pow_two] at h ⊢
    linear_combination h
  · have h := S.riemann_r_phirphi (x 1) (x 2) hr hf
    simp [S.riemann_eq_data x hr hf hsin, riemannFromData, christoffel,
      christoffelDeriv, Fin.sum_univ_four, add_assoc, sub_eq_add_neg, pow_two] at h ⊢
    linear_combination h
  · simpa [S.riemann_eq_data x hr hf hsin, riemannFromData, christoffel,
      christoffelDeriv, Fin.sum_univ_four, add_assoc, sub_eq_add_neg, pow_two] using
      S.riemann_theta_phitheta (x 1) (x 2) hr hsin

/-- Metric-level Ricci tensor for Schwarzschild–de Sitter: `Ric_{σν} = Λ g_{σν}`, computed directly
from the coordinate metric. -/
lemma ricciTensor (S : SchwarzschildDeSitterSpacetime) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.metricFn (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) (σ ν : Fin 4) :
    CoordinateCurvature.ricciTensor S.metric S.metricInv x σ ν = S.Λ * S.metric x σ ν := by
  have hm : S.metric = S.toStaticSpherical.metric := rfl
  have hmi : S.metricInv = S.toStaticSpherical.metricInv := rfl
  have hf1 := S.deriv_metricFn (x 1) hr
  have hf2 := (S.hasDerivAt_deriv_metricFn (x 1) hr).deriv
  have hfdiff := S.eventually_differentiableAt_metricFn (x 1) hr
  have hf2diff := (S.hasDerivAt_deriv_metricFn (x 1) hr).differentiableAt
  rw [hm, hmi, S.toStaticSpherical.ricciTensor x hr hf hsin hfdiff hf2diff σ ν]
  simp only [toStaticSpherical_metricFn] at *
  rw [hf1, hf2]
  fin_cases σ <;> fin_cases ν <;>
    simp [StaticSphericalMetric.metric, metricFn, metricFnHalfDeriv]
  · field_simp [hr]; ring
  · field_simp [hr, hf]; ring
  · field_simp [hr]; ring
  · field_simp [hr]; ring

/-- Metric-level scalar curvature for Schwarzschild–de Sitter: `R = 4 Λ`. -/
lemma ricciScalar (S : SchwarzschildDeSitterSpacetime) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.metricFn (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) :
    CoordinateCurvature.ricciScalar S.metric S.metricInv x = 4 * S.Λ := by
  have hm : S.metric = S.toStaticSpherical.metric := rfl
  have hmi : S.metricInv = S.toStaticSpherical.metricInv := rfl
  have hf1 := S.deriv_metricFn (x 1) hr
  have hf2 := (S.hasDerivAt_deriv_metricFn (x 1) hr).deriv
  have hfdiff := S.eventually_differentiableAt_metricFn (x 1) hr
  have hf2diff := (S.hasDerivAt_deriv_metricFn (x 1) hr).differentiableAt
  rw [hm, hmi, S.toStaticSpherical.ricciScalar x hr hf hsin hfdiff hf2diff]
  simp only [toStaticSpherical_metricFn] at *
  rw [hf1, hf2]
  simp only [metricFn, metricFnHalfDeriv]
  field_simp [hr]
  ring

/-- Metric-level Einstein tensor for Schwarzschild–de Sitter: `G_{ij} = -Λ g_{ij}`, so
`G_{ij} + Λ g_{ij} = 0`. -/
lemma einsteinTensor (S : SchwarzschildDeSitterSpacetime) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.metricFn (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) (i j : Fin 4) :
    CoordinateCurvature.einsteinTensor S.metric S.metricInv x i j = -(S.Λ * S.metric x i j) := by
  simp only [CoordinateCurvature.einsteinTensor, S.ricciTensor x hr hf hsin,
    S.ricciScalar x hr hf hsin]
  ring

/-- The inverse diagonal scale `|g_{aa}|⁻¹` relating coordinate Ricci components of `S.metric`
to the orthonormal frame `η`. -/
noncomputable def frameScale (S : SchwarzschildDeSitterSpacetime) (x : Fin 4 → ℝ)
    (a : Fin 4) : ℝ :=
  if a = 0 then (S.metricFn (x 1))⁻¹
  else if a = 1 then S.metricFn (x 1)
  else if a = 2 then ((x 1) ^ 2)⁻¹
  else ((x 1) ^ 2 * Real.sin (x 2) ^ 2)⁻¹

/-- Scaling `S.ricciTensor` by `S.frameScale` reproduces `Λ η` in the orthonormal frame. -/
lemma ricciTensor_frame (S : SchwarzschildDeSitterSpacetime) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.metricFn (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) (σ ν : Fin 4) :
    S.frameScale x σ * CoordinateCurvature.ricciTensor S.metric S.metricInv x σ ν
      = S.Λ * minkowskiMetric4 σ ν := by
  rw [S.ricciTensor x hr hf hsin]
  fin_cases σ <;> fin_cases ν <;>
    simp [frameScale, metric, toStaticSpherical, StaticSphericalMetric.metric]
  · field_simp [hf]
  · field_simp [hf]
  · field_simp [hr]
  · field_simp [hr, hsin]

end SchwarzschildDeSitterSpacetime

end SchwarzschildDeSitter

end GeneralRelativity
