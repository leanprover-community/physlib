/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import PhyslibAlpha.Relativity.General.Einstein
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!

# Kerr black hole spacetime

The rotating vacuum Boyer–Lindquist metric, event horizons, ergosphere, and ZAMO frame-dragging.

## i. Overview

This module defines the Boyer–Lindquist Kerr metric `kerrMetric` and its analytical inverse
`kerrMetricInv`, packages them as a `MetricTensor 4` (`kerrMetricTensor`) away from the ring
singularity `Σ = 0`, horizons `Δ = 0`, and polar axis `sin θ = 0`, and establishes the basic
causal and rotational properties of the Kerr geometry: outer/inner event horizons `r±`,
extremal coalescence `a² = M²`, stationary-limit surface (ergosphere) `g₀₀ = 0`,
zero-angular-momentum observer (ZAMO) frame-dragging angular velocity `ω = -g_{tφ}/g_{φφ}`, and
reduction to Schwarzschild at `a = 0`.

## ii. Key results

- `sigma`, `delta`, `bigB` : Boyer–Lindquist auxiliary functions `Σ`, `Δ`, and `B`.
- `kerrMetric`, `kerrMetricInv`, `kerrMetricTensor` : Kerr metric and inverse `MetricTensor 4`.
- `horizonPlus`, `horizonMinus`, `delta_horizonPlus`, `kerr_extremal` : event horizons `r±`.
- `ergosphereRadius`, `kerrMetric_00_ergosphere` : stationary-limit surface `g₀₀ = 0`.
- `frameDraggingOmega`, `frameDraggingOmega_horizonPlus` : ZAMO frame dragging and horizon speed.
- `kerrMetric_zero_spin` : Schwarzschild reduction `a = 0`.

## iii. Table of contents

- A. Boyer–Lindquist metric functions and inverse
- B. Event horizons, ergosphere, and frame dragging
- C. Schwarzschild limit

## iv. References

* None.

-/

@[expose] public section

namespace GeneralRelativity

namespace Kerr

/-!

## A. Boyer–Lindquist metric functions and inverse

-/

/-- Boyer–Lindquist radial-polar function `Σ = r² + a² cos² θ`. -/
noncomputable def sigma (a r θ : ℝ) : ℝ := r ^ 2 + a ^ 2 * Real.cos θ ^ 2

/-- Boyer–Lindquist horizon function `Δ = r² - 2 M r + a²`. -/
noncomputable def delta (M a r : ℝ) : ℝ := r ^ 2 - 2 * M * r + a ^ 2

/-- Boyer–Lindquist auxiliary function `B = (r² + a²)² - a² Δ sin² θ`. -/
noncomputable def bigB (M a r θ : ℝ) : ℝ :=
  (r ^ 2 + a ^ 2) ^ 2 - a ^ 2 * delta M a r * Real.sin θ ^ 2

/-- Alternative expansion of `B`: `B = Σ (r² + a²) + 2 M a² r sin² θ`. -/
lemma bigB_eq_sigma (M a r θ : ℝ) :
    bigB M a r θ = sigma a r θ * (r ^ 2 + a ^ 2) + 2 * M * a ^ 2 * r * Real.sin θ ^ 2 := by
  simp only [bigB, sigma, delta]
  rw [Real.sin_sq θ]
  ring

/-- Algebraic identity governing the determinant of the `(t, φ)` metric block:
`(Σ - 2 M r) B + 4 M² a² r² sin² θ = Σ² Δ`. -/
lemma kerr_tphi_det_id (M a r θ : ℝ) :
    (sigma a r θ - 2 * M * r) * bigB M a r θ + 4 * M ^ 2 * a ^ 2 * r ^ 2 * Real.sin θ ^ 2
      = sigma a r θ ^ 2 * delta M a r := by
  simp only [sigma, delta, bigB]
  rw [Real.sin_sq θ]
  ring

/-- Kerr spacetime metric in Boyer–Lindquist coordinates `x = (t, r, θ, φ)` with signature
`(-, +, +, +)` and geometrized units `G = c = 1`. -/
noncomputable def kerrMetric (M a : ℝ) (x : Fin 4 → ℝ) : Tensor2 4 :=
  let sig := sigma a (x 1) (x 2)
  let del := delta M a (x 1)
  let bval := bigB M a (x 1) (x 2)
  let s2 := Real.sin (x 2) ^ 2
  fun i j =>
    if i = 0 ∧ j = 0 then -(1 - 2 * M * x 1 / sig)
    else if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then -(2 * M * a * x 1 * s2 / sig)
    else if i = 1 ∧ j = 1 then sig / del
    else if i = 2 ∧ j = 2 then sig
    else if i = 3 ∧ j = 3 then bval * s2 / sig
    else 0

/-- Analytical inverse of the Boyer–Lindquist Kerr metric `kerrMetric M a x`. -/
noncomputable def kerrMetricInv (M a : ℝ) (x : Fin 4 → ℝ) : Tensor2 4 :=
  let sig := sigma a (x 1) (x 2)
  let del := delta M a (x 1)
  let bval := bigB M a (x 1) (x 2)
  let s2 := Real.sin (x 2) ^ 2
  fun i j =>
    if i = 0 ∧ j = 0 then -(bval / (sig * del))
    else if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then -(2 * M * a * x 1 / (sig * del))
    else if i = 1 ∧ j = 1 then del / sig
    else if i = 2 ∧ j = 2 then 1 / sig
    else if i = 3 ∧ j = 3 then (sig - 2 * M * x 1) / (sig * del * s2)
    else 0

/-- Symmetry of `kerrMetric M a x`. -/
lemma kerrMetric_symm (M a : ℝ) (x : Fin 4 → ℝ) : IsSymm (kerrMetric M a x) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [kerrMetric]

/-- Left-inverse verification `g⁻¹ * g = 1` for the Boyer–Lindquist Kerr metric. -/
lemma kerrMetricInv_mul_kerrMetric (M a : ℝ) (x : Fin 4 → ℝ)
    (hsig : sigma a (x 1) (x 2) ≠ 0) (hdel : delta M a (x 1) ≠ 0)
    (hs : Real.sin (x 2) ≠ 0) :
    kerrMetricInv M a x * kerrMetric M a x = 1 := by
  ext i j
  have hid := kerr_tphi_det_id M a (x 1) (x 2)
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.one_apply, Fin.sum_univ_four, kerrMetric, kerrMetricInv] <;>
    norm_num
  · field_simp [hsig, hdel]; linear_combination hid
  · field_simp [hsig, hdel]; ring
  · field_simp [hsig, hdel]
  · field_simp [hsig]
  · field_simp [hsig, hdel, hs]; ring
  · field_simp [hsig, hdel, hs]; linear_combination hid

/-- Right-inverse verification `g * g⁻¹ = 1` for the Boyer–Lindquist Kerr metric. -/
lemma kerrMetric_mul_kerrMetricInv (M a : ℝ) (x : Fin 4 → ℝ)
    (hsig : sigma a (x 1) (x 2) ≠ 0) (hdel : delta M a (x 1) ≠ 0)
    (hs : Real.sin (x 2) ≠ 0) :
    kerrMetric M a x * kerrMetricInv M a x = 1 := by
  ext i j
  have hid := kerr_tphi_det_id M a (x 1) (x 2)
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.one_apply, Fin.sum_univ_four, kerrMetric, kerrMetricInv] <;>
    norm_num
  · field_simp [hsig, hdel]; linear_combination hid
  · field_simp [hsig, hdel, hs]; ring
  · field_simp [hsig, hdel]
  · field_simp [hsig]
  · field_simp [hsig, hdel, hs]; ring
  · field_simp [hsig, hdel, hs]; linear_combination hid

/-- Package the Boyer–Lindquist Kerr metric at a regular point (`Σ ≠ 0`, `Δ ≠ 0`, `sin θ ≠ 0`) as a
`MetricTensor 4`. -/
noncomputable def kerrMetricTensor (M a : ℝ) (x : Fin 4 → ℝ)
    (hsig : sigma a (x 1) (x 2) ≠ 0) (hdel : delta M a (x 1) ≠ 0)
    (hs : Real.sin (x 2) ≠ 0) : MetricTensor 4 where
  g := kerrMetric M a x
  ginv := kerrMetricInv M a x
  symm := kerrMetric_symm M a x
  inv_left := kerrMetric_mul_kerrMetricInv M a x hsig hdel hs
  inv_right := kerrMetricInv_mul_kerrMetric M a x hsig hdel hs

/-!

## B. Event horizons, ergosphere, and frame dragging

-/

/-- Outer Kerr event horizon radius `r₊ = M + √(M² - a²)` for `|a| ≤ M`. -/
noncomputable def horizonPlus (M a : ℝ) : ℝ := M + Real.sqrt (M ^ 2 - a ^ 2)

/-- Inner Kerr Cauchy horizon radius `r₋ = M - √(M² - a²)` for `|a| ≤ M`. -/
noncomputable def horizonMinus (M a : ℝ) : ℝ := M - Real.sqrt (M ^ 2 - a ^ 2)

/-- Outer horizon `r₊` is a root of `Δ(r) = 0` when `a² ≤ M²`. -/
lemma delta_horizonPlus {M a : ℝ} (ha : a ^ 2 ≤ M ^ 2) : delta M a (horizonPlus M a) = 0 := by
  have hsq : Real.sqrt (M ^ 2 - a ^ 2) ^ 2 = M ^ 2 - a ^ 2 := Real.sq_sqrt (sub_nonneg.mpr ha)
  simp only [delta, horizonPlus]
  linear_combination hsq

/-- Inner horizon `r₋` is a root of `Δ(r) = 0` when `a² ≤ M²`. -/
lemma delta_horizonMinus {M a : ℝ} (ha : a ^ 2 ≤ M ^ 2) : delta M a (horizonMinus M a) = 0 := by
  have hsq : Real.sqrt (M ^ 2 - a ^ 2) ^ 2 = M ^ 2 - a ^ 2 := Real.sq_sqrt (sub_nonneg.mpr ha)
  simp only [delta, horizonMinus]
  linear_combination hsq

/-- Extremal Kerr limit (`a² = M²`): outer and inner horizons coalesce at `r = M` with a double
root of `Δ`. -/
lemma kerr_extremal {M a : ℝ} (ha : a ^ 2 = M ^ 2) :
    horizonPlus M a = M ∧ horizonMinus M a = M ∧ delta M a M = 0 := by
  have hsub : M ^ 2 - a ^ 2 = 0 := sub_eq_zero.mpr ha.symm
  refine ⟨?_, ?_, ?_⟩
  · simp [horizonPlus, hsub]
  · simp [horizonMinus, hsub]
  · simp [delta, ha]; ring

/-- Outer stationary-limit (ergosphere) radius `r_E(θ) = M + √(M² - a² cos² θ)`. -/
noncomputable def ergosphereRadius (M a θ : ℝ) : ℝ :=
  M + Real.sqrt (M ^ 2 - a ^ 2 * Real.cos θ ^ 2)

/-- At the ergosphere radius `r_E(θ)`, `g_{tt} = 0`, so static observers become null. -/
lemma kerrMetric_00_ergosphere {M a : ℝ} (x : Fin 4 → ℝ)
    (hx1 : x 1 = ergosphereRadius M a (x 2))
    (hcos : a ^ 2 * Real.cos (x 2) ^ 2 ≤ M ^ 2)
    (hsig : sigma a (x 1) (x 2) ≠ 0) :
    kerrMetric M a x 0 0 = 0 := by
  have hsq : Real.sqrt (M ^ 2 - a ^ 2 * Real.cos (x 2) ^ 2) ^ 2
      = M ^ 2 - a ^ 2 * Real.cos (x 2) ^ 2 := Real.sq_sqrt (sub_nonneg.mpr hcos)
  have hnum : sigma a (x 1) (x 2) - 2 * M * x 1 = 0 := by
    rw [hx1]
    simp only [sigma, ergosphereRadius]
    linear_combination hsq
  simp only [kerrMetric, Fin.isValue, and_self, ↓reduceIte]
  field_simp [hsig]
  linear_combination -hnum

/-- Zero-angular-momentum observer (ZAMO) frame-dragging angular velocity
`ω = -g_{tφ} / g_{φφ} = 2 M a r / B`. -/
noncomputable def frameDraggingOmega (M a r θ : ℝ) : ℝ := 2 * M * a * r / bigB M a r θ

/-- Agreement of `-g_{tφ} / g_{φφ}` with `frameDraggingOmega M a r θ`. -/
lemma kerr_zamo_omega_eq (M a : ℝ) (x : Fin 4 → ℝ)
    (hsig : sigma a (x 1) (x 2) ≠ 0) (hs : Real.sin (x 2) ≠ 0)
    (hB : bigB M a (x 1) (x 2) ≠ 0) :
    -(kerrMetric M a x 0 3 / kerrMetric M a x 3 3)
      = frameDraggingOmega M a (x 1) (x 2) := by
  simp only [kerrMetric, frameDraggingOmega, Fin.isValue, Fin.reduceEq, and_false, and_true,
    or_false, ↓reduceIte]
  field_simp [hsig, hs, hB]

/-- At the outer event horizon `r₊`, `B(r₊, θ) = (r₊² + a²)²`, giving the horizon angular
velocity `ω_H = 2 M a r₊ / (r₊² + a²)²`. -/
lemma frameDraggingOmega_horizonPlus {M a : ℝ} (ha : a ^ 2 ≤ M ^ 2) (θ : ℝ) :
    frameDraggingOmega M a (horizonPlus M a) θ
      = 2 * M * a * horizonPlus M a / (horizonPlus M a ^ 2 + a ^ 2) ^ 2 := by
  have hdel : delta M a (horizonPlus M a) = 0 := delta_horizonPlus ha
  simp [frameDraggingOmega, bigB, hdel]

/-!

## C. Schwarzschild limit

-/

/-- In the non-rotating limit `a = 0`, `kerrMetric M 0 x` reduces entrywise to the Schwarzschild
metric with `f(r) = 1 - 2 M / r`. -/
lemma kerrMetric_zero_spin (M : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (_hf : 1 - 2 * M / x 1 ≠ 0) :
    (kerrMetric M 0 x 0 0 = -(1 - 2 * M / x 1))
      ∧ (kerrMetric M 0 x 0 3 = 0)
      ∧ (kerrMetric M 0 x 1 1 = (1 - 2 * M / x 1)⁻¹)
      ∧ (kerrMetric M 0 x 2 2 = (x 1) ^ 2)
      ∧ (kerrMetric M 0 x 3 3 = (x 1) ^ 2 * Real.sin (x 2) ^ 2) := by
  have hr2 : (x 1) ^ 2 ≠ 0 := pow_ne_zero 2 hr
  have hs0 : sigma 0 (x 1) (x 2) = (x 1) ^ 2 := by simp [sigma]
  have hd0 : delta M 0 (x 1) = (x 1) ^ 2 * (1 - 2 * M / x 1) := by
    simp only [delta]; field_simp [hr]; ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [kerrMetric, hs0, Fin.isValue, and_self, ↓reduceIte]
    field_simp [hr]
  · simp [kerrMetric]
  · simp only [kerrMetric, hs0, hd0, Fin.isValue, Fin.reduceEq, ↓reduceIte,
      and_self, or_self]
    field_simp [hr2]
  · simp [kerrMetric, hs0]
  · simp only [kerrMetric, hs0, bigB, Fin.isValue]
    norm_num
    field_simp [hr2]

end Kerr

end GeneralRelativity
