/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.Metrics.CoordinateMetric
public import PhyslibAlpha.Relativity.General.SchwarzschildDeSitter.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!

# Schwarzschild and Schwarzschild–de Sitter through the metric pipeline

End-to-end verification of the Schwarzschild–de Sitter and Schwarzschild (`Λ = 0`) metrics
through the coordinate pipeline `g ↦ ∂g ↦ Γ ↦ ∂Γ ↦ R^ρ_{σμν} ↦ Ric ↦ S ↦ G`.

## i. Overview

This module connects the coordinate metric fields `sdsMetric` and `sdsMetricInv` directly to the
metric pipeline `GeneralRelativity.Pipeline`:

1. Computes all coordinate partial derivatives of `sdsMetric` and identifies all 64 Christoffel
   symbols with the closed-form table `sdsG` (`christoffel_eq_sdsG`).
2. Promotes `christoffel = sdsG` across neighbourhoods to equate their partial derivatives
   (`pd_christoffel_eq_pd_sdsG`) and computes every one of the 256 partial derivatives of `sdsG`
   in `sdsDGFull` (`pd_sdsG_eq_sdsDGFull`).
3. Proves that `riemann (sdsMetric M Λ) (sdsMetricInv M Λ)` equals `riemannFromData sdsG
   sdsDGFull` everywhere (`riemann_sds_eq_data`), yielding all six independent Riemann
   components, metric-level `Ric_{σν} = Λ g_{σν}` (`ricciOf_sds`), `S = 4 Λ` (`scalarOf_sds`),
   `G_{ij} = -Λ g_{ij}` (`einsteinOf_sds`), and frame agreement `sdsFrameScale * Ric = Λ η`
   (`ricciOf_sds_frame`).
4. Specialises at `Λ = 0` to `schwarzschildG` / `schwarzschildGinv`, obtaining all six
   Schwarzschild Riemann components, metric-level Ricci flatness (`ricciOf_schwarzschild`),
   vanishing scalar curvature, and the vacuum Einstein equation (`einsteinOf_schwarzschild`).

## ii. Key results

- `sdsG`, `sdsDGFull` : Christoffel table and complete 256-entry derivative table.
- `christoffel_eq_sdsG`, `pd_sdsG_eq_sdsDGFull`, `riemann_sds_eq_data` : metric-to-Riemann
  bridge without unverified derivative tables.
- `riemann_sds_components`, `ricciOf_sds`, `scalarOf_sds`, `einsteinOf_sds`,
  `ricciOf_sds_frame` : general-`Λ` metric-level solution theorems.

## iii. Table of contents

- A. Christoffel and derivative tables
- B. Metric partial derivatives and Christoffel identification
- C. Complete partial-derivative table of `sdsG`
- D. Metric-level Riemann, Ricci, scalar, and Einstein tensors

## iv. References

* R. M. Wald, *General Relativity* (1984). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973). [ref: mtw_1973_gravitation]

-/

@[expose] public section

namespace GeneralRelativity

namespace SchwarzschildDeSitter

open GeneralRelativity.Pipeline

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

## B. Metric partial derivatives and Christoffel identification

-/

/-- The Schwarzschild–de Sitter metric does not depend on `t`. -/
@[simp]
lemma pd_sds_t (M Λ : ℝ) (x : Fin 4 → ℝ) (a b : Fin 4) :
    pd 0 (fun y => sdsMetric M Λ y a b) x = 0 := by
  fin_cases a <;> fin_cases b <;> simp [pd, sdsMetric]

/-- The Schwarzschild–de Sitter metric does not depend on `φ`. -/
@[simp]
lemma pd_sds_phi (M Λ : ℝ) (x : Fin 4 → ℝ) (a b : Fin 4) :
    pd 3 (fun y => sdsMetric M Λ y a b) x = 0 := by
  fin_cases a <;> fin_cases b <;> simp [pd, sdsMetric]

/-- `∂_r g_rr = -2n / f²`. -/
lemma pd_sds_rr (M Λ : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0) (hf : sdsF M Λ (x 1) ≠ 0) :
    pd 1 (fun y => sdsMetric M Λ y 1 1) x = -(2 * sdsHalf M Λ (x 1)) / (sdsF M Λ (x 1)) ^ 2 := by
  have hfun : (fun s : ℝ => sdsMetric M Λ (Function.update x 1 s) 1 1)
      = fun s : ℝ => (sdsF M Λ s)⁻¹ := by
    funext s
    simp [sdsMetric]
  rw [pd, hfun, deriv_sdsF_inv M Λ (x 1) hr hf]

/-- `∂_r g_tt = -2n`. -/
lemma pd_sds_tt (M Λ : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0) :
    pd 1 (fun y => sdsMetric M Λ y 0 0) x = -(2 * sdsHalf M Λ (x 1)) := by
  have hfun : (fun s : ℝ => sdsMetric M Λ (Function.update x 1 s) 0 0)
      = -fun s : ℝ => sdsF M Λ s := by
    funext s
    simp [sdsMetric]
  have h := (hasDerivAt_sdsF M Λ (x 1) hr).neg
  rw [pd, hfun, h.deriv]

/-- `∂_r g_θθ = 2 r`. -/
lemma pd_sds_thetatheta (M Λ : ℝ) (x : Fin 4 → ℝ) :
    pd 1 (fun y => sdsMetric M Λ y 2 2) x = 2 * (x 1) := by
  have hfun : (fun s : ℝ => sdsMetric M Λ (Function.update x 1 s) 2 2)
      = fun s : ℝ => s ^ 2 := by
    funext s
    simp [sdsMetric]
  rw [pd, hfun]
  simp

/-- `∂_r g_φφ = 2 r sin²θ`. -/
lemma pd_sds_phiphi_r (M Λ : ℝ) (x : Fin 4 → ℝ) :
    pd 1 (fun y => sdsMetric M Λ y 3 3) x = 2 * (x 1) * Real.sin (x 2) ^ 2 := by
  have hfun : (fun s : ℝ => sdsMetric M Λ (Function.update x 1 s) 3 3)
      = fun s : ℝ => s ^ 2 * Real.sin (x 2) ^ 2 := by
    funext s
    simp [sdsMetric]
  have h := (hasDerivAt_pow 2 (x 1)).mul_const (Real.sin (x 2) ^ 2)
  rw [pd, hfun, h.deriv]
  ring

/-- `∂_θ g_φφ = 2 r² sin θ cos θ`. -/
lemma pd_sds_phiphi_theta (M Λ : ℝ) (x : Fin 4 → ℝ) :
    pd 2 (fun y => sdsMetric M Λ y 3 3) x = 2 * (x 1) ^ 2 * Real.sin (x 2) * Real.cos (x 2) := by
  have hfun : (fun s : ℝ => sdsMetric M Λ (Function.update x 2 s) 3 3)
      = fun s : ℝ => (x 1) ^ 2 * Real.sin s ^ 2 := by
    funext s
    simp [sdsMetric]
  have h := (Schwarzschild.hasDerivAt_sinSq (x 2)).const_mul ((x 1) ^ 2)
  rw [pd, hfun, h.deriv]
  ring

/-- `θ` derivatives of `sdsMetric`: only `g_φφ` contributes. -/
@[simp]
lemma pd_sds_theta (M Λ : ℝ) (x : Fin 4 → ℝ) (a b : Fin 4) :
    pd 2 (fun y => sdsMetric M Λ y a b) x
      = if a = 3 ∧ b = 3 then 2 * (x 1) ^ 2 * Real.sin (x 2) * Real.cos (x 2) else 0 := by
  fin_cases a <;> fin_cases b <;>
    first
    | exact pd_sds_phiphi_theta M Λ x
    | simp [pd, sdsMetric]

/-- Radial `r` derivatives of all `sdsMetric` components. -/
lemma pd_sds_r (M Λ : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0) (hf : sdsF M Λ (x 1) ≠ 0)
    (a b : Fin 4) :
    pd 1 (fun y => sdsMetric M Λ y a b) x
      = if a = 0 ∧ b = 0 then -(2 * sdsHalf M Λ (x 1))
        else if a = 1 ∧ b = 1 then -(2 * sdsHalf M Λ (x 1)) / (sdsF M Λ (x 1)) ^ 2
        else if a = 2 ∧ b = 2 then 2 * (x 1)
        else if a = 3 ∧ b = 3 then 2 * (x 1) * Real.sin (x 2) ^ 2
        else 0 := by
  fin_cases a <;> fin_cases b <;>
    first
    | exact pd_sds_tt M Λ x hr
    | exact pd_sds_rr M Λ x hr hf
    | exact pd_sds_thetatheta M Λ x
    | exact pd_sds_phiphi_r M Λ x
    | simp [pd, sdsMetric]

/-- All 64 Christoffel symbols computed by `christoffel` equal `sdsG`, for every `Λ`. -/
lemma christoffel_eq_sdsG (M Λ : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : sdsF M Λ (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) :
    ∀ k i j, christoffel (sdsMetric M Λ) (sdsMetricInv M Λ) x k i j = sdsG M Λ x k i j := by
  intro k i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [christoffel, sdsG, sdsMetricInv, pd_sds_r M Λ x hr hf]
  all_goals field_simp [hr, hf]

/-- Because `r ≠ 0`, `f ≠ 0`, and `sin θ ≠ 0` are open conditions, `christoffel` and `sdsG`
have the same coordinate partial derivatives along every coordinate axis. -/
lemma pd_christoffel_eq_pd_sdsG (M Λ : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : sdsF M Λ (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) (μ a b c : Fin 4) :
    pd μ (fun y => christoffel (sdsMetric M Λ) (sdsMetricInv M Λ) y a b c) x
      = pd μ (fun y => sdsG M Λ y a b c) x := by
  fin_cases μ
  · have heq : (fun s : ℝ =>
        christoffel (sdsMetric M Λ) (sdsMetricInv M Λ) (Function.update x 0 s) a b c)
        =ᶠ[nhds (x 0)] (fun s : ℝ => sdsG M Λ (Function.update x 0 s) a b c) :=
      Filter.Eventually.of_forall (fun s =>
        christoffel_eq_sdsG M Λ (Function.update x 0 s) hr hf hsin a b c)
    exact Filter.EventuallyEq.deriv_eq heq
  · have hr' : ∀ᶠ s in nhds (x 1), s ≠ 0 := eventually_ne_nhds hr
    have hcont : ContinuousAt (sdsF M Λ) (x 1) :=
      (hasDerivAt_sdsF M Λ (x 1) hr).continuousAt
    have hf' : ∀ᶠ s in nhds (x 1), sdsF M Λ s ≠ 0 := hcont.eventually_ne hf
    have heq : (fun s : ℝ =>
        christoffel (sdsMetric M Λ) (sdsMetricInv M Λ) (Function.update x 1 s) a b c)
        =ᶠ[nhds (x 1)] (fun s : ℝ => sdsG M Λ (Function.update x 1 s) a b c) := by
      filter_upwards [hr', hf'] with s hs1 hs2
      exact christoffel_eq_sdsG M Λ (Function.update x 1 s)
        (by simpa using hs1) (by simpa using hs2) (by simpa using hsin) a b c
    exact Filter.EventuallyEq.deriv_eq heq
  · have hsin' : ∀ᶠ s in nhds (x 2), Real.sin s ≠ 0 :=
      Real.continuous_sin.continuousAt.eventually_ne hsin
    have heq : (fun s : ℝ =>
        christoffel (sdsMetric M Λ) (sdsMetricInv M Λ) (Function.update x 2 s) a b c)
        =ᶠ[nhds (x 2)] (fun s : ℝ => sdsG M Λ (Function.update x 2 s) a b c) := by
      filter_upwards [hsin'] with s hs
      exact christoffel_eq_sdsG M Λ (Function.update x 2 s)
        (by simpa using hr) (by simpa using hf) (by simpa using hs) a b c
    exact Filter.EventuallyEq.deriv_eq heq
  · have heq : (fun s : ℝ =>
        christoffel (sdsMetric M Λ) (sdsMetricInv M Λ) (Function.update x 3 s) a b c)
        =ᶠ[nhds (x 3)] (fun s : ℝ => sdsG M Λ (Function.update x 3 s) a b c) :=
      Filter.Eventually.of_forall (fun s =>
        christoffel_eq_sdsG M Λ (Function.update x 3 s) hr hf hsin a b c)
    exact Filter.EventuallyEq.deriv_eq heq

/-!

## C. Complete partial-derivative table of `sdsG`

-/

/-- `∂_r(n/f) = n'/f - 2n²/f²` at `(0, 0, 1)`. -/
lemma pd_sdsG_r_tr (M Λ : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0) (hf : sdsF M Λ (x 1) ≠ 0) :
    pd 1 (fun y => sdsG M Λ y 0 0 1) x = sdsDGFull M Λ 1 x 0 0 1 := by
  have hfun : (fun s : ℝ => sdsG M Λ (Function.update x 1 s) 0 0 1)
      = fun s : ℝ => sdsHalf M Λ s / sdsF M Λ s := by
    funext s
    simp [sdsG]
  have hd : deriv (fun s : ℝ => sdsHalf M Λ s / sdsF M Λ s) (x 1)
      = (-2 * M / (x 1) ^ 3 - Λ / 3) / sdsF M Λ (x 1)
        - sdsHalf M Λ (x 1) * (2 * sdsHalf M Λ (x 1)) / (sdsF M Λ (x 1)) ^ 2 := by
    have h := (hasDerivAt_sdsHalf M Λ (x 1) hr).div (hasDerivAt_sdsF M Λ (x 1) hr) hf
    have hfun2 : (fun s : ℝ => sdsHalf M Λ s / sdsF M Λ s)
        = (fun s : ℝ => sdsHalf M Λ s) / fun s : ℝ => sdsF M Λ s := rfl
    rw [hfun2, h.deriv]
    field_simp [hf]
  rw [pd, hfun, hd, sdsDGFull]
  simp

/-- `∂_r Γ^r_{tt} = (2n)n + f n'`. -/
lemma pd_sdsG_r_tt (M Λ : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0) :
    pd 1 (fun y => sdsG M Λ y 1 0 0) x = sdsDGFull M Λ 1 x 1 0 0 := by
  have hfun : (fun s : ℝ => sdsG M Λ (Function.update x 1 s) 1 0 0)
      = fun s : ℝ => sdsF M Λ s * sdsHalf M Λ s := by
    funext s
    simp [sdsG]
  have hd : HasDerivAt (fun s : ℝ => sdsF M Λ s * sdsHalf M Λ s)
      ((2 * sdsHalf M Λ (x 1)) * sdsHalf M Λ (x 1)
        + sdsF M Λ (x 1) * (-2 * M / (x 1) ^ 3 - Λ / 3)) (x 1) :=
    (hasDerivAt_sdsF M Λ (x 1) hr).mul (hasDerivAt_sdsHalf M Λ (x 1) hr)
  have hderiv : deriv (fun s : ℝ => sdsF M Λ s * sdsHalf M Λ s) (x 1)
      = (2 * sdsHalf M Λ (x 1)) * sdsHalf M Λ (x 1)
        + sdsF M Λ (x 1) * (-2 * M / (x 1) ^ 3 - Λ / 3) := hd.deriv
  rw [pd, hfun, hderiv, sdsDGFull]
  simp

/-- `∂_r Γ^r_{rr} = -∂_r(n/f)`. -/
lemma pd_sdsG_r_rr (M Λ : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0) (hf : sdsF M Λ (x 1) ≠ 0) :
    pd 1 (fun y => sdsG M Λ y 1 1 1) x = sdsDGFull M Λ 1 x 1 1 1 := by
  have hfun : (fun s : ℝ => sdsG M Λ (Function.update x 1 s) 1 1 1)
      = fun s : ℝ => -(sdsHalf M Λ s / sdsF M Λ s) := by
    funext s
    simp [sdsG]
  have hd : HasDerivAt (fun s : ℝ => -(sdsHalf M Λ s / sdsF M Λ s))
      (-((-2 * M / (x 1) ^ 3 - Λ / 3) * sdsF M Λ (x 1)
        - sdsHalf M Λ (x 1) * (2 * sdsHalf M Λ (x 1))) / (sdsF M Λ (x 1)) ^ 2) (x 1) := by
    have h := ((hasDerivAt_sdsHalf M Λ (x 1) hr).div (hasDerivAt_sdsF M Λ (x 1) hr) hf).neg
    convert h using 1
    ring
  have hderiv : deriv (fun s : ℝ => -(sdsHalf M Λ s / sdsF M Λ s)) (x 1)
      = -((-2 * M / (x 1) ^ 3 - Λ / 3) * sdsF M Λ (x 1)
        - sdsHalf M Λ (x 1) * (2 * sdsHalf M Λ (x 1))) / (sdsF M Λ (x 1)) ^ 2 := hd.deriv
  rw [pd, hfun, hderiv]
  simp [sdsDGFull]
  field_simp [hf]

/-- `∂_r Γ^r_{θθ} = -f - 2rn`. -/
lemma pd_sdsG_r_thetatheta (M Λ : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0) :
    pd 1 (fun y => sdsG M Λ y 1 2 2) x = sdsDGFull M Λ 1 x 1 2 2 := by
  have hfun : (fun s : ℝ => sdsG M Λ (Function.update x 1 s) 1 2 2)
      = fun s : ℝ => -(s * sdsF M Λ s) := by
    funext s
    simp [sdsG]
  have hd : HasDerivAt (fun s : ℝ => -(s * sdsF M Λ s))
      (-(1 * sdsF M Λ (x 1) + (x 1) * (2 * sdsHalf M Λ (x 1)))) (x 1) :=
    ((hasDerivAt_id (x 1)).mul (hasDerivAt_sdsF M Λ (x 1) hr)).neg
  have hderiv : deriv (fun s : ℝ => -(s * sdsF M Λ s)) (x 1)
      = -(1 * sdsF M Λ (x 1) + (x 1) * (2 * sdsHalf M Λ (x 1))) := hd.deriv
  have hval : sdsDGFull M Λ 1 x 1 2 2
      = -(sdsF M Λ (x 1)) - x 1 * (2 * sdsHalf M Λ (x 1)) := by
    simp [sdsDGFull]
  rw [pd, hfun, hderiv, hval]
  ring

/-- `∂_r Γ^r_{φφ} = (-f - 2rn) sin²θ`. -/
lemma pd_sdsG_r_phiphi (M Λ : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0) :
    pd 1 (fun y => sdsG M Λ y 1 3 3) x = sdsDGFull M Λ 1 x 1 3 3 := by
  have hfun : (fun s : ℝ => sdsG M Λ (Function.update x 1 s) 1 3 3)
      = fun s : ℝ => -(s * (Real.sin (x 2) ^ 2 * sdsF M Λ s)) := by
    funext s
    simp [sdsG]
    ring
  have hd : HasDerivAt (fun s : ℝ => -(s * (Real.sin (x 2) ^ 2 * sdsF M Λ s)))
      (-(1 * (Real.sin (x 2) ^ 2 * sdsF M Λ (x 1))
        + (x 1) * (Real.sin (x 2) ^ 2 * (2 * sdsHalf M Λ (x 1))))) (x 1) :=
    ((hasDerivAt_id (x 1)).mul ((hasDerivAt_sdsF M Λ (x 1) hr).const_mul (Real.sin (x 2) ^ 2))).neg
  have hderiv : deriv (fun s : ℝ => -(s * (Real.sin (x 2) ^ 2 * sdsF M Λ s))) (x 1)
      = -(1 * (Real.sin (x 2) ^ 2 * sdsF M Λ (x 1))
        + (x 1) * (Real.sin (x 2) ^ 2 * (2 * sdsHalf M Λ (x 1)))) := hd.deriv
  have hval : sdsDGFull M Λ 1 x 1 3 3
      = (-(sdsF M Λ (x 1)) - x 1 * (2 * sdsHalf M Λ (x 1))) * Real.sin (x 2) ^ 2 := by
    simp [sdsDGFull]
  rw [pd, hfun, hderiv, hval]
  ring

/-- `∂_r (1 / r) = -1 / r²`. -/
lemma deriv_one_div_eq (r : ℝ) (hr : r ≠ 0) :
    deriv (fun s : ℝ => 1 / s) r = -1 / r ^ 2 := by
  have hfun : (fun s : ℝ => 1 / s) = fun s : ℝ => s⁻¹ := by
    funext s
    simp [one_div]
  have h := hasDerivAt_inv hr
  rw [hfun, h.deriv]
  ring

/-- `∂_θ Γ^r_{φφ} = -2 r sin θ cos θ f`. -/
lemma pd_sdsG_theta_r_phiphi (M Λ : ℝ) (x : Fin 4 → ℝ) :
    pd 2 (fun y => sdsG M Λ y 1 3 3) x = sdsDGFull M Λ 2 x 1 3 3 := by
  have hfun : (fun s : ℝ => sdsG M Λ (Function.update x 2 s) 1 3 3)
      = fun s : ℝ => -(x 1 * Real.sin s ^ 2 * sdsF M Λ (x 1)) := by
    funext s
    simp [sdsG]
  have hd : HasDerivAt (fun s : ℝ => -(x 1 * Real.sin s ^ 2 * sdsF M Λ (x 1)))
      (-(x 1 * (2 * Real.sin (x 2) * Real.cos (x 2)) * sdsF M Λ (x 1))) (x 2) := by
    have h := (((Schwarzschild.hasDerivAt_sinSq (x 2)).const_mul (x 1)).mul_const
      (sdsF M Λ (x 1))).neg
    convert h using 1
  have hderiv : deriv (fun s : ℝ => -(x 1 * Real.sin s ^ 2 * sdsF M Λ (x 1))) (x 2)
      = -(x 1 * (2 * Real.sin (x 2) * Real.cos (x 2)) * sdsF M Λ (x 1)) := hd.deriv
  rw [pd, hfun, hderiv, sdsDGFull]
  simp

/-- `∂_θ Γ^θ_{φφ} = sin²θ - cos²θ`. -/
lemma pd_sdsG_theta_phiphi (M Λ : ℝ) (x : Fin 4 → ℝ) :
    pd 2 (fun y => sdsG M Λ y 2 3 3) x = sdsDGFull M Λ 2 x 2 3 3 := by
  have hfun : (fun s : ℝ => sdsG M Λ (Function.update x 2 s) 2 3 3)
      = fun s : ℝ => -(Real.sin s * Real.cos s) := by
    funext s
    simp [sdsG]
  have hd : HasDerivAt (fun s : ℝ => -(Real.sin s * Real.cos s))
      (Real.sin (x 2) ^ 2 - Real.cos (x 2) ^ 2) (x 2) := by
    have h := ((Real.hasDerivAt_sin (x 2)).mul (Real.hasDerivAt_cos (x 2))).neg
    convert h using 1
    ring
  have hderiv : deriv (fun s : ℝ => -(Real.sin s * Real.cos s)) (x 2)
      = Real.sin (x 2) ^ 2 - Real.cos (x 2) ^ 2 := hd.deriv
  rw [pd, hfun, hderiv, sdsDGFull]
  simp

/-- `∂_θ (cos θ / sin θ) = -1 / sin²θ`. -/
lemma deriv_cos_div_sin (th : ℝ) (hsin : Real.sin th ≠ 0) :
    deriv (fun s : ℝ => Real.cos s / Real.sin s) th = -1 / Real.sin th ^ 2 := by
  have h := (Real.hasDerivAt_cos th).div (Real.hasDerivAt_sin th) hsin
  have hsc : Real.sin th ^ 2 + Real.cos th ^ 2 = 1 := Real.sin_sq_add_cos_sq th
  have hnum : (-Real.sin th * Real.sin th - Real.cos th * Real.cos th) / Real.sin th ^ 2
      = -1 / Real.sin th ^ 2 := by
    have h1 : -Real.sin th * Real.sin th - Real.cos th * Real.cos th = -1 := by
      linear_combination -hsc
    rw [h1]
  rw [hnum] at h
  exact h.deriv

private lemma pd_sdsG_eq_sdsDGFull_0 (M Λ : ℝ) (x : Fin 4 → ℝ) (k i j : Fin 4) :
    pd 0 (fun y => sdsG M Λ y k i j) x = sdsDGFull M Λ 0 x k i j := by
  fin_cases k <;> fin_cases i <;> fin_cases j <;> simp [pd, sdsG, sdsDGFull]

private lemma pd_sdsG_eq_sdsDGFull_1_0 (M Λ : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : sdsF M Λ (x 1) ≠ 0) (i j : Fin 4) :
    pd 1 (fun y => sdsG M Λ y 0 i j) x = sdsDGFull M Λ 1 x 0 i j := by
  have h01 := pd_sdsG_r_tr M Λ x hr hf
  fin_cases i <;> fin_cases j <;> simp [pd, sdsG, sdsDGFull]
  · simpa [pd, sdsG, sdsDGFull] using h01
  · simpa [pd, sdsG, sdsDGFull] using h01

private lemma pd_sdsG_eq_sdsDGFull_1_1 (M Λ : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : sdsF M Λ (x 1) ≠ 0) (i j : Fin 4) :
    pd 1 (fun y => sdsG M Λ y 1 i j) x = sdsDGFull M Λ 1 x 1 i j := by
  have h00 := pd_sdsG_r_tt M Λ x hr
  have h11 := pd_sdsG_r_rr M Λ x hr hf
  have h22 := pd_sdsG_r_thetatheta M Λ x hr
  have h33 := pd_sdsG_r_phiphi M Λ x hr
  fin_cases i <;> fin_cases j
  all_goals first | exact h00 | exact h11 | exact h22 | exact h33 | simp [pd, sdsG, sdsDGFull]

private lemma pd_sdsG_eq_sdsDGFull_1_2 (M Λ : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (i j : Fin 4) :
    pd 1 (fun y => sdsG M Λ y 2 i j) x = sdsDGFull M Λ 1 x 2 i j := by
  have hinv := deriv_one_div_eq (x 1) hr
  fin_cases i <;> fin_cases j <;> simp [pd, sdsG, sdsDGFull]
  · simpa [one_div] using hinv
  · simpa [one_div] using hinv

private lemma pd_sdsG_eq_sdsDGFull_1_3 (M Λ : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (i j : Fin 4) :
    pd 1 (fun y => sdsG M Λ y 3 i j) x = sdsDGFull M Λ 1 x 3 i j := by
  have hinv := deriv_one_div_eq (x 1) hr
  fin_cases i <;> fin_cases j <;> simp [pd, sdsG, sdsDGFull]
  · simpa [one_div] using hinv
  · simpa [one_div] using hinv

private lemma pd_sdsG_eq_sdsDGFull_1 (M Λ : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : sdsF M Λ (x 1) ≠ 0) (k i j : Fin 4) :
    pd 1 (fun y => sdsG M Λ y k i j) x = sdsDGFull M Λ 1 x k i j := by
  fin_cases k
  · exact pd_sdsG_eq_sdsDGFull_1_0 M Λ x hr hf i j
  · exact pd_sdsG_eq_sdsDGFull_1_1 M Λ x hr hf i j
  · exact pd_sdsG_eq_sdsDGFull_1_2 M Λ x hr i j
  · exact pd_sdsG_eq_sdsDGFull_1_3 M Λ x hr i j

private lemma pd_sdsG_eq_sdsDGFull_2 (M Λ : ℝ) (x : Fin 4 → ℝ)
    (hsin : Real.sin (x 2) ≠ 0) (k i j : Fin 4) :
    pd 2 (fun y => sdsG M Λ y k i j) x = sdsDGFull M Λ 2 x k i j := by
  have hcot := deriv_cos_div_sin (x 2) hsin
  fin_cases k <;> fin_cases i <;> fin_cases j <;> simp [pd, sdsG, sdsDGFull]
  · ring
  · exact hcot
  · exact hcot

private lemma pd_sdsG_eq_sdsDGFull_3 (M Λ : ℝ) (x : Fin 4 → ℝ) (k i j : Fin 4) :
    pd 3 (fun y => sdsG M Λ y k i j) x = sdsDGFull M Λ 3 x k i j := by
  fin_cases k <;> fin_cases i <;> fin_cases j <;> simp [pd, sdsG, sdsDGFull]

/-- Every partial derivative of `sdsG` equals `sdsDGFull`, across all 256 index tuples
`(μ, k, i, j)`. -/
lemma pd_sdsG_eq_sdsDGFull (M Λ : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : sdsF M Λ (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) (μ k i j : Fin 4) :
    pd μ (fun y => sdsG M Λ y k i j) x = sdsDGFull M Λ μ x k i j := by
  fin_cases μ
  · exact pd_sdsG_eq_sdsDGFull_0 M Λ x k i j
  · exact pd_sdsG_eq_sdsDGFull_1 M Λ x hr hf k i j
  · exact pd_sdsG_eq_sdsDGFull_2 M Λ x hsin k i j
  · exact pd_sdsG_eq_sdsDGFull_3 M Λ x k i j

/-!

## D. Metric-level Riemann, Ricci, scalar, and Einstein tensors

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

private lemma ricciOf_sds_00 (M Λ : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : sdsF M Λ (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) :
    ricciOf (sdsMetric M Λ) (sdsMetricInv M Λ) x 0 0 = Λ * sdsMetric M Λ x 0 0 := by
  simp [ricciOf, Fin.sum_univ_four, riemann_sds_eq_data M Λ x hr hf hsin,
    riemannFromData, sdsG, sdsDGFull, sdsMetric]
  field_simp [hr, hf]
  simp only [sdsF, sdsHalf]
  field_simp [hr]
  ring

private lemma ricciOf_sds_11 (M Λ : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : sdsF M Λ (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) :
    ricciOf (sdsMetric M Λ) (sdsMetricInv M Λ) x 1 1 = Λ * sdsMetric M Λ x 1 1 := by
  simp [ricciOf, Fin.sum_univ_four, riemann_sds_eq_data M Λ x hr hf hsin,
    riemannFromData, sdsG, sdsDGFull, sdsMetric]
  field_simp [hr, hf]
  simp only [sdsF, sdsHalf]
  field_simp [hr]
  ring

private lemma ricciOf_sds_22 (M Λ : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : sdsF M Λ (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) :
    ricciOf (sdsMetric M Λ) (sdsMetricInv M Λ) x 2 2 = Λ * sdsMetric M Λ x 2 2 := by
  have hsc : Real.sin (x 2) ^ 2 + Real.cos (x 2) ^ 2 = 1 := Real.sin_sq_add_cos_sq (x 2)
  simp [ricciOf, Fin.sum_univ_four, riemann_sds_eq_data M Λ x hr hf hsin,
    riemannFromData, sdsG, sdsDGFull, sdsMetric]
  field_simp [hr, hf, hsin]
  simp only [sdsF, sdsHalf]
  field_simp [hr]
  linear_combination -(3 * x 1) * hsc

private lemma ricciOf_sds_33 (M Λ : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : sdsF M Λ (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) :
    ricciOf (sdsMetric M Λ) (sdsMetricInv M Λ) x 3 3 = Λ * sdsMetric M Λ x 3 3 := by
  simp [ricciOf, Fin.sum_univ_four, riemann_sds_eq_data M Λ x hr hf hsin,
    riemannFromData, sdsG, sdsDGFull, sdsMetric]
  field_simp [hr, hf, hsin]
  simp only [sdsF, sdsHalf]
  field_simp [hr]
  ring

/-- Metric-level Ricci tensor for Schwarzschild–de Sitter: `Ric_{σν} = Λ g_{σν}` directly from
`ricciOf (sdsMetric M Λ) (sdsMetricInv M Λ)`. -/
lemma ricciOf_sds (M Λ : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : sdsF M Λ (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) (σ ν : Fin 4) :
    ricciOf (sdsMetric M Λ) (sdsMetricInv M Λ) x σ ν = Λ * sdsMetric M Λ x σ ν := by
  fin_cases σ <;> fin_cases ν
  · exact ricciOf_sds_00 M Λ x hr hf hsin
  · simp [ricciOf, Fin.sum_univ_four, riemann_sds_eq_data M Λ x hr hf hsin,
      riemannFromData, sdsG, sdsDGFull, sdsMetric]
  · simp [ricciOf, Fin.sum_univ_four, riemann_sds_eq_data M Λ x hr hf hsin,
      riemannFromData, sdsG, sdsDGFull, sdsMetric]
  · simp [ricciOf, Fin.sum_univ_four, riemann_sds_eq_data M Λ x hr hf hsin,
      riemannFromData, sdsG, sdsDGFull, sdsMetric]
  · simp [ricciOf, Fin.sum_univ_four, riemann_sds_eq_data M Λ x hr hf hsin,
      riemannFromData, sdsG, sdsDGFull, sdsMetric]
  · exact ricciOf_sds_11 M Λ x hr hf hsin
  · simp [ricciOf, Fin.sum_univ_four, riemann_sds_eq_data M Λ x hr hf hsin,
      riemannFromData, sdsG, sdsDGFull, sdsMetric]
  · simp [ricciOf, Fin.sum_univ_four, riemann_sds_eq_data M Λ x hr hf hsin,
      riemannFromData, sdsG, sdsDGFull, sdsMetric]
  · simp [ricciOf, Fin.sum_univ_four, riemann_sds_eq_data M Λ x hr hf hsin,
      riemannFromData, sdsG, sdsDGFull, sdsMetric]
  · simp [ricciOf, Fin.sum_univ_four, riemann_sds_eq_data M Λ x hr hf hsin,
      riemannFromData, sdsG, sdsDGFull, sdsMetric]
    ring
  · exact ricciOf_sds_22 M Λ x hr hf hsin
  · simp [ricciOf, Fin.sum_univ_four, riemann_sds_eq_data M Λ x hr hf hsin,
      riemannFromData, sdsG, sdsDGFull, sdsMetric]
  · simp [ricciOf, Fin.sum_univ_four, riemann_sds_eq_data M Λ x hr hf hsin,
      riemannFromData, sdsG, sdsDGFull, sdsMetric]
  · simp [ricciOf, Fin.sum_univ_four, riemann_sds_eq_data M Λ x hr hf hsin,
      riemannFromData, sdsG, sdsDGFull, sdsMetric]
  · simp [ricciOf, Fin.sum_univ_four, riemann_sds_eq_data M Λ x hr hf hsin,
      riemannFromData, sdsG, sdsDGFull, sdsMetric]
  · exact ricciOf_sds_33 M Λ x hr hf hsin

/-- Metric-level scalar curvature for Schwarzschild–de Sitter: `S = 4 Λ`. -/
lemma scalarOf_sds (M Λ : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : sdsF M Λ (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) :
    scalarOf (sdsMetric M Λ) (sdsMetricInv M Λ) x = 4 * Λ := by
  simp only [scalarOf, ricciOf_sds M Λ x hr hf hsin]
  simp only [Fin.sum_univ_four, sdsMetric, sdsMetricInv]
  simp only [Fin.reduceEq, ↓reduceIte, Fin.isValue, mul_zero, add_zero, zero_add]
  field_simp [hr, hf, hsin]
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
