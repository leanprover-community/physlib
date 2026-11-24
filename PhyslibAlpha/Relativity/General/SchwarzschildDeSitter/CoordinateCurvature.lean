/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.General.SchwarzschildDeSitter.Basic
public import PhyslibAlpha.Relativity.Metrics.CoordinateMetric
public import PhyslibAlpha.Relativity.Metrics.StaticSphericalMetric
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!

# Schwarzschild and Schwarzschild–de Sitter through the metric pipeline

End-to-end verification of the Schwarzschild–de Sitter and Schwarzschild (`Λ = 0`) metrics
through the coordinate pipeline `g ↦ ∂g ↦ Γ ↦ ∂Γ ↦ R^ρ_{σμν} ↦ Ric ↦ S ↦ G`.

## i. Overview

This module connects the coordinate metric fields `sdsMetric` and `sdsMetricInv` directly to the
general static spherically symmetric curvature engine in `GeneralRelativity.StaticSpherical` and
`GeneralRelativity.Pipeline`:

1. Identifies `sdsMetric M Λ` and `sdsMetricInv M Λ` with `staticSphericalMetric (sdsF M Λ)` and
   `staticSphericalMetricInv (sdsF M Λ)`, and equates `sdsG` and `sdsDGFull` with
   `staticSphericalG` and `staticSphericalDG`.
2. Delegates `christoffel_eq_sdsG`, `pd_christoffel_eq_pd_sdsG`, `pd_sdsG_eq_sdsDGFull`,
   `ricciOf_sds`, and `scalarOf_sds` directly to `GeneralRelativity.StaticSpherical`.
3. Obtains `riemann_sds_eq_data`, all six independent Riemann components `riemann_sds_components`,
   `G_{ij} = -Λ g_{ij}` (`einsteinOf_sds`), and frame agreement `sdsFrameScale * Ric = Λ η`
   (`ricciOf_sds_frame`).

## ii. Key results

- `sdsG`, `sdsDGFull` : Christoffel table and complete 256-entry derivative table.
- `christoffel_eq_sdsG`, `pd_sdsG_eq_sdsDGFull`, `riemann_sds_eq_data` : metric-to-Riemann
  bridge via `StaticSpherical`.
- `riemann_sds_components`, `ricciOf_sds`, `scalarOf_sds`, `einsteinOf_sds`,
  `ricciOf_sds_frame` : general-`Λ` metric-level solution theorems.

## iii. Table of contents

- A. Christoffel and derivative tables
- B. Static-spherical reduction and Christoffel identification
- C. Metric-level Riemann, Ricci, scalar, and Einstein tensors

## iv. References

* R. M. Wald, *General Relativity* (1984). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973). [ref: mtw_1973_gravitation]

-/

@[expose] public section

namespace GeneralRelativity

namespace SchwarzschildDeSitter

open GeneralRelativity.Pipeline
open GeneralRelativity.StaticSpherical

/-!

## A. Christoffel and derivative tables

-/

/-- The closed-form Schwarzschild–de Sitter Christoffel symbols in `(t, r, θ, φ)` coordinates. -/
noncomputable def sdsG (M Λ : ℝ) (x : Fin 4 → ℝ) (k i j : Fin 4) : ℝ :=
  if k = 0 then
    (if (i = 1 ∧ j = 0) ∨ (i = 0 ∧ j = 1) then
      sdsHalf M Λ (x 1) / sdsF M Λ (x 1)
     else 0)
  else if k = 1 then
    (if i = 0 ∧ j = 0 then sdsF M Λ (x 1) * sdsHalf M Λ (x 1)
     else if i = 1 ∧ j = 1 then -(sdsHalf M Λ (x 1) / sdsF M Λ (x 1))
     else if i = 2 ∧ j = 2 then -(x 1 * sdsF M Λ (x 1))
     else if i = 3 ∧ j = 3 then -(x 1 * Real.sin (x 2) ^ 2 * sdsF M Λ (x 1))
     else 0)
  else if k = 2 then
    (if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then 1 / (x 1)
     else if i = 3 ∧ j = 3 then -(Real.sin (x 2) * Real.cos (x 2)) else 0)
  else
    (if (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) then 1 / (x 1)
     else if (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) then
       Real.cos (x 2) / Real.sin (x 2) else 0)

/-- The complete partial-derivative table `∂_μ sdsG^k_{ij}` across all 256 index tuples
`(μ, k, i, j)`. -/
noncomputable def sdsDGFull (M Λ : ℝ) (μ : Fin 4) (x : Fin 4 → ℝ)
    (k i j : Fin 4) : ℝ :=
  if μ = 1 then
    (if k = 0 ∧ ((i = 1 ∧ j = 0) ∨ (i = 0 ∧ j = 1)) then
       (-2 * M / (x 1) ^ 3 - Λ / 3) / sdsF M Λ (x 1)
         - sdsHalf M Λ (x 1) * (2 * sdsHalf M Λ (x 1)) / (sdsF M Λ (x 1)) ^ 2
     else if k = 1 ∧ i = 0 ∧ j = 0 then
       (2 * sdsHalf M Λ (x 1)) * sdsHalf M Λ (x 1)
         + sdsF M Λ (x 1) * (-2 * M / (x 1) ^ 3 - Λ / 3)
     else if k = 1 ∧ i = 1 ∧ j = 1 then
       -((-2 * M / (x 1) ^ 3 - Λ / 3) / sdsF M Λ (x 1)
         - sdsHalf M Λ (x 1) * (2 * sdsHalf M Λ (x 1)) / (sdsF M Λ (x 1)) ^ 2)
     else if k = 1 ∧ i = 2 ∧ j = 2 then
       -(sdsF M Λ (x 1)) - (x 1) * (2 * sdsHalf M Λ (x 1))
     else if k = 1 ∧ i = 3 ∧ j = 3 then
       (-(sdsF M Λ (x 1)) - (x 1) * (2 * sdsHalf M Λ (x 1))) * Real.sin (x 2) ^ 2
     else if (k = 2 ∧ ((i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)))
         ∨ (k = 3 ∧ ((i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1))) then
       -1 / (x 1) ^ 2
     else 0)
  else if μ = 2 then
    (if k = 1 ∧ i = 3 ∧ j = 3 then
       -(x 1 * (2 * Real.sin (x 2) * Real.cos (x 2)) * sdsF M Λ (x 1))
     else if k = 2 ∧ i = 3 ∧ j = 3 then
       Real.sin (x 2) ^ 2 - Real.cos (x 2) ^ 2
     else if k = 3 ∧ ((i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)) then
       -1 / Real.sin (x 2) ^ 2
     else 0)
  else 0

/-!

## B. Static-spherical reduction and Christoffel identification

-/

private lemma sdsMetric_eq_staticSpherical (M Λ : ℝ) :
    sdsMetric M Λ = staticSphericalMetric (sdsF M Λ) := by
  funext x i j
  rfl

private lemma sdsMetricInv_eq_staticSpherical (M Λ : ℝ) :
    sdsMetricInv M Λ = staticSphericalMetricInv (sdsF M Λ) := by
  funext x i j
  rfl

private lemma eventually_differentiableAt_sdsF (M Λ r : ℝ) (hr : r ≠ 0) :
    ∀ᶠ s in nhds r, DifferentiableAt ℝ (sdsF M Λ) s := by
  filter_upwards [eventually_ne_nhds hr] with s hs
  exact (hasDerivAt_sdsF M Λ s hs).differentiableAt

private lemma hasDerivAt_deriv_sdsF (M Λ r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (deriv (sdsF M Λ)) (-4 * M / r ^ 3 - 2 * Λ / 3) r := by
  have heq : deriv (sdsF M Λ) =ᶠ[nhds r] fun s => 2 * sdsHalf M Λ s := by
    filter_upwards [eventually_ne_nhds hr] with s hs
    exact deriv_sdsF M Λ s hs
  have hd : HasDerivAt (fun s : ℝ => 2 * sdsHalf M Λ s)
      (-4 * M / r ^ 3 - 2 * Λ / 3) r := by
    convert (hasDerivAt_sdsHalf M Λ r hr).const_mul 2 using 1
    ring
  exact hd.congr_of_eventuallyEq heq

private lemma sdsG_eq_staticSphericalG (M Λ : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0) :
    ∀ k i j, sdsG M Λ x k i j = staticSphericalG (sdsF M Λ) x k i j := by
  intro k i j
  have hd1 := deriv_sdsF M Λ (x 1) hr
  fin_cases k <;> fin_cases i <;> fin_cases j <;> simp [sdsG, staticSphericalG, hd1] <;> ring

private lemma sdsDGFull_eq_staticSphericalDG (M Λ : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : sdsF M Λ (x 1) ≠ 0) (μ k i j : Fin 4) :
    sdsDGFull M Λ μ x k i j = staticSphericalDG (sdsF M Λ) μ x k i j := by
  have hd1 := deriv_sdsF M Λ (x 1) hr
  have hd2 := (hasDerivAt_deriv_sdsF M Λ (x 1) hr).deriv
  fin_cases μ <;> fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [sdsDGFull, staticSphericalDG, hd1, hd2]
  all_goals field_simp [hf]; ring

/-- All 64 Christoffel symbols computed by `christoffel` equal `sdsG`, for every `Λ`. -/
lemma christoffel_eq_sdsG (M Λ : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : sdsF M Λ (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) :
    ∀ k i j, christoffel (sdsMetric M Λ) (sdsMetricInv M Λ) x k i j = sdsG M Λ x k i j := by
  intro k i j
  rw [sdsMetric_eq_staticSpherical, sdsMetricInv_eq_staticSpherical,
    christoffel_eq_staticSphericalG (sdsF M Λ) x hr hf hsin
      (hasDerivAt_sdsF M Λ (x 1) hr).differentiableAt k i j,
    sdsG_eq_staticSphericalG M Λ x hr k i j]

/-- Because `r ≠ 0`, `f ≠ 0`, and `sin θ ≠ 0` are open conditions, `christoffel` and `sdsG`
have the same coordinate partial derivatives along every coordinate axis. -/
lemma pd_christoffel_eq_pd_sdsG (M Λ : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : sdsF M Λ (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) (μ a b c : Fin 4) :
    pd μ (fun y => christoffel (sdsMetric M Λ) (sdsMetricInv M Λ) y a b c) x
      = pd μ (fun y => sdsG M Λ y a b c) x := by
  rw [sdsMetric_eq_staticSpherical, sdsMetricInv_eq_staticSpherical,
    pd_christoffel_eq_pd_staticSphericalG (sdsF M Λ) x hr hf hsin
      (eventually_differentiableAt_sdsF M Λ (x 1) hr) μ a b c]
  have hr_nhds : ∀ᶠ y in nhds x, y 1 ≠ 0 :=
    (continuous_apply (1 : Fin 4)).continuousAt.eventually_ne hr
  have heq : (fun y => staticSphericalG (sdsF M Λ) y a b c) =ᶠ[nhds x]
      fun y => sdsG M Λ y a b c := by
    filter_upwards [hr_nhds] with y hy
    exact (sdsG_eq_staticSphericalG M Λ y hy a b c).symm
  exact pd_congr_nhds μ x heq

/-- Every partial derivative of `sdsG` equals `sdsDGFull`, across all 256 index tuples
`(μ, k, i, j)`. -/
lemma pd_sdsG_eq_sdsDGFull (M Λ : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : sdsF M Λ (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) (μ k i j : Fin 4) :
    pd μ (fun y => sdsG M Λ y k i j) x = sdsDGFull M Λ μ x k i j := by
  have hr_nhds : ∀ᶠ y in nhds x, y 1 ≠ 0 :=
    (continuous_apply (1 : Fin 4)).continuousAt.eventually_ne hr
  have heq : (fun y => sdsG M Λ y k i j) =ᶠ[nhds x]
      fun y => staticSphericalG (sdsF M Λ) y k i j := by
    filter_upwards [hr_nhds] with y hy
    exact sdsG_eq_staticSphericalG M Λ y hy k i j
  rw [pd_congr_nhds μ x heq,
    pd_staticSphericalG_eq_staticSphericalDG (sdsF M Λ) x hr hf hsin
      (hasDerivAt_sdsF M Λ (x 1) hr).differentiableAt
      (hasDerivAt_deriv_sdsF M Λ (x 1) hr).differentiableAt μ k i j,
    sdsDGFull_eq_staticSphericalDG M Λ x hr hf μ k i j]

/-!

## C. Metric-level Riemann, Ricci, scalar, and Einstein tensors

-/

/-- The pipeline Riemann tensor of `sdsMetric` equals `riemannFromData sdsG sdsDGFull` at every
4-tuple `(ρ, σ, μ, ν)`, for general `Λ`. -/
lemma riemann_sds_eq_data (M Λ : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : sdsF M Λ (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) (ρ σ μ ν : Fin 4) :
    riemann (sdsMetric M Λ) (sdsMetricInv M Λ) x ρ σ μ ν
      = riemannFromData (sdsG M Λ) (sdsDGFull M Λ) x ρ σ μ ν := by
  rw [riemann_eq_riemannFromData]
  have h1 : pd μ (fun z => christoffel (sdsMetric M Λ) (sdsMetricInv M Λ) z ρ ν σ) x
      = sdsDGFull M Λ μ x ρ ν σ :=
    (pd_christoffel_eq_pd_sdsG M Λ x hr hf hsin μ ρ ν σ).trans
      (pd_sdsG_eq_sdsDGFull M Λ x hr hf hsin μ ρ ν σ)
  have h2 : pd ν (fun z => christoffel (sdsMetric M Λ) (sdsMetricInv M Λ) z ρ μ σ) x
      = sdsDGFull M Λ ν x ρ μ σ :=
    (pd_christoffel_eq_pd_sdsG M Λ x hr hf hsin ν ρ μ σ).trans
      (pd_sdsG_eq_sdsDGFull M Λ x hr hf hsin ν ρ μ σ)
  simp only [riemannFromData, h1, h2, christoffel_eq_sdsG M Λ x hr hf hsin]

/-- All six independent Schwarzschild–de Sitter Riemann components directly from the metric
pipeline, for general `Λ`. -/
lemma riemann_sds_components (M Λ : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : sdsF M Λ (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) :
    (riemann (sdsMetric M Λ) (sdsMetricInv M Λ) x 0 1 0 1
        = (2 * M / (x 1) ^ 3 + Λ / 3) / sdsF M Λ (x 1))
      ∧ (riemann (sdsMetric M Λ) (sdsMetricInv M Λ) x 0 2 0 2 = Λ * (x 1) ^ 2 / 3 - M / (x 1))
      ∧ (riemann (sdsMetric M Λ) (sdsMetricInv M Λ) x 0 3 0 3
          = (Λ * (x 1) ^ 2 / 3 - M / (x 1)) * Real.sin (x 2) ^ 2)
      ∧ (riemann (sdsMetric M Λ) (sdsMetricInv M Λ) x 1 2 1 2 = Λ * (x 1) ^ 2 / 3 - M / (x 1))
      ∧ (riemann (sdsMetric M Λ) (sdsMetricInv M Λ) x 1 3 1 3
          = (Λ * (x 1) ^ 2 / 3 - M / (x 1)) * Real.sin (x 2) ^ 2)
      ∧ (riemann (sdsMetric M Λ) (sdsMetricInv M Λ) x 2 3 2 3
          = (2 * M / (x 1) + Λ * (x 1) ^ 2 / 3) * Real.sin (x 2) ^ 2) := by
  have hd : deriv (fun s : ℝ => sdsHalf M Λ s / sdsF M Λ s) (x 1)
      = (-2 * M / (x 1) ^ 3 - Λ / 3) / sdsF M Λ (x 1)
        - sdsHalf M Λ (x 1) * (2 * sdsHalf M Λ (x 1)) / (sdsF M Λ (x 1)) ^ 2 := by
    have h := (hasDerivAt_sdsHalf M Λ (x 1) hr).div (hasDerivAt_sdsF M Λ (x 1) hr) hf
    have hfun : (fun s : ℝ => sdsHalf M Λ s / sdsF M Λ s)
        = (fun s : ℝ => sdsHalf M Λ s) / fun s : ℝ => sdsF M Λ s := rfl
    rw [hfun, h.deriv]
    field_simp [hf]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := riemann_t_rtr_sds M Λ (x 1) hr hf
    simp [riemann_sds_eq_data M Λ x hr hf hsin, riemannFromData, sdsG, sdsDGFull,
      Fin.sum_univ_four, hd, add_assoc, sub_eq_add_neg, pow_two] at h ⊢
    linear_combination h
  · simpa [riemann_sds_eq_data M Λ x hr hf hsin, riemannFromData, sdsG, sdsDGFull,
      Fin.sum_univ_four, add_assoc, sub_eq_add_neg, pow_two] using
      riemann_t_thetatheta_sds M Λ (x 1) hr hf
  · simpa [riemann_sds_eq_data M Λ x hr hf hsin, riemannFromData, sdsG, sdsDGFull,
      Fin.sum_univ_four, add_assoc, sub_eq_add_neg, pow_two] using
      riemann_t_phitphi_sds M Λ (x 1) (x 2) hr hf
  · have h := riemann_r_thetar_sds M Λ (x 1) hr hf
    simp [riemann_sds_eq_data M Λ x hr hf hsin, riemannFromData, sdsG, sdsDGFull,
      Fin.sum_univ_four, add_assoc, sub_eq_add_neg, pow_two] at h ⊢
    linear_combination h
  · have h := riemann_r_phirphi_sds M Λ (x 1) (x 2) hr hf
    simp [riemann_sds_eq_data M Λ x hr hf hsin, riemannFromData, sdsG, sdsDGFull,
      Fin.sum_univ_four, add_assoc, sub_eq_add_neg, pow_two] at h ⊢
    linear_combination h
  · simpa [riemann_sds_eq_data M Λ x hr hf hsin, riemannFromData, sdsG, sdsDGFull,
      Fin.sum_univ_four, add_assoc, sub_eq_add_neg, pow_two] using
      riemann_theta_phitheta_sds M Λ (x 1) (x 2) hr hsin

/-- Metric-level Ricci tensor for Schwarzschild–de Sitter: `Ric_{σν} = Λ g_{σν}` directly from
`ricciOf (sdsMetric M Λ) (sdsMetricInv M Λ)`. -/
lemma ricciOf_sds (M Λ : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : sdsF M Λ (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) (σ ν : Fin 4) :
    ricciOf (sdsMetric M Λ) (sdsMetricInv M Λ) x σ ν = Λ * sdsMetric M Λ x σ ν := by
  have hf1 := deriv_sdsF M Λ (x 1) hr
  have hf2 := (hasDerivAt_deriv_sdsF M Λ (x 1) hr).deriv
  have hfdiff := eventually_differentiableAt_sdsF M Λ (x 1) hr
  have hf2diff := (hasDerivAt_deriv_sdsF M Λ (x 1) hr).differentiableAt
  rw [sdsMetric_eq_staticSpherical, sdsMetricInv_eq_staticSpherical,
    ricciOf_staticSpherical (sdsF M Λ) x hr hf hsin hfdiff hf2diff σ ν, hf1, hf2]
  fin_cases σ <;> fin_cases ν <;> simp [staticSphericalMetric, sdsF, sdsHalf]
  · field_simp [hr]; ring
  · field_simp [hr, hf]; ring
  · field_simp [hr]; ring
  · field_simp [hr]; ring

/-- Metric-level scalar curvature for Schwarzschild–de Sitter: `S = 4 Λ`. -/
lemma scalarOf_sds (M Λ : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : sdsF M Λ (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) :
    scalarOf (sdsMetric M Λ) (sdsMetricInv M Λ) x = 4 * Λ := by
  have hf1 := deriv_sdsF M Λ (x 1) hr
  have hf2 := (hasDerivAt_deriv_sdsF M Λ (x 1) hr).deriv
  have hfdiff := eventually_differentiableAt_sdsF M Λ (x 1) hr
  have hf2diff := (hasDerivAt_deriv_sdsF M Λ (x 1) hr).differentiableAt
  rw [sdsMetric_eq_staticSpherical, sdsMetricInv_eq_staticSpherical,
    scalarOf_staticSpherical (sdsF M Λ) x hr hf hsin hfdiff hf2diff, hf1, hf2, sdsF, sdsHalf]
  field_simp [hr]
  ring

/-- Metric-level Einstein tensor for Schwarzschild–de Sitter: `G_{ij} = -Λ g_{ij}`, so
`G_{ij} + Λ g_{ij} = 0`. -/
lemma einsteinOf_sds (M Λ : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : sdsF M Λ (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) (i j : Fin 4) :
    einsteinOf (sdsMetric M Λ) (sdsMetricInv M Λ) x i j = -(Λ * sdsMetric M Λ x i j) := by
  simp only [einsteinOf, ricciOf_sds M Λ x hr hf hsin, scalarOf_sds M Λ x hr hf hsin]
  ring

/-- The inverse diagonal scale `|g_{aa}|⁻¹` relating coordinate Ricci components of `sdsMetric`
to the orthonormal frame `η`. -/
noncomputable def sdsFrameScale (M Λ : ℝ) (x : Fin 4 → ℝ) (a : Fin 4) : ℝ :=
  if a = 0 then (sdsF M Λ (x 1))⁻¹
  else if a = 1 then sdsF M Λ (x 1)
  else if a = 2 then ((x 1) ^ 2)⁻¹
  else ((x 1) ^ 2 * Real.sin (x 2) ^ 2)⁻¹

/-- Scaling `ricciOf (sdsMetric M Λ)` by `sdsFrameScale` reproduces `Λ η` in the orthonormal
frame. -/
lemma ricciOf_sds_frame (M Λ : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : sdsF M Λ (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) (σ ν : Fin 4) :
    sdsFrameScale M Λ x σ * ricciOf (sdsMetric M Λ) (sdsMetricInv M Λ) x σ ν
      = Λ * eta4 σ ν := by
  rw [ricciOf_sds M Λ x hr hf hsin]
  fin_cases σ <;> fin_cases ν <;> simp [sdsFrameScale, sdsMetric]
  · field_simp [hf]
  · field_simp [hf]
  · field_simp [hr]
  · field_simp [hr, hsin]

end SchwarzschildDeSitter

end GeneralRelativity
