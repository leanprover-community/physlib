/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import PhyslibAlpha.Relativity.Metrics.CoordinateMetric
public import PhyslibAlpha.Relativity.Tensors.EinsteinTensor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!

# Kerr black hole spacetime

The rotating vacuum Boyer–Lindquist metric, event horizons, ergosphere, and ZAMO frame-dragging
on `KerrSpacetime`.

## i. Overview

This module defines the Boyer–Lindquist Kerr metric `KerrSpacetime.metric` of a spin-`a` mass-`M`
black hole together with its analytical inverse `KerrSpacetime.metricInv`, and certifies them as a
`MetricTensor 4` at each point and as a `CoordinateMetric 4` on the chart away from the ring
singularity `Σ = 0`, horizons `Δ = 0`, and polar axis `sin θ = 0`, and establishes the basic causal
and rotational properties of the Kerr geometry: outer/inner event horizons `r±`, extremal
coalescence `a² = M²`, stationary-limit surface (ergosphere) `g₀₀ = 0`, zero-angular-momentum
observer (ZAMO) frame-dragging angular velocity `ω = -g_{tφ}/g_{φφ}`, and reduction to Schwarzschild
at `a = 0`.

## ii. Key results

- `KerrSpacetime`, `KerrSpacetime.sigma`, `KerrSpacetime.delta`, `KerrSpacetime.axialFactor` :
  Kerr spacetime structure and Boyer–Lindquist auxiliary functions `Σ`, `Δ`, and `axialFactor`.
- `KerrSpacetime.metric`, `KerrSpacetime.metricInv`, `KerrSpacetime.metricTensor`,
  `KerrSpacetime.toCoordinateMetric` : Kerr metric, its inverse, and the coordinate metric on the
  regular chart.
- `KerrSpacetime.horizonPlus`, `KerrSpacetime.horizonMinus`, `KerrSpacetime.delta_horizonPlus`,
  `KerrSpacetime.extremal` : event horizons `r±`.
- `KerrSpacetime.ergosphereRadius`, `KerrSpacetime.metric_00_ergosphere` : stationary-limit
  surface `g₀₀ = 0`.
- `KerrSpacetime.frameDraggingOmega`, `KerrSpacetime.frameDraggingOmega_horizonPlus` : ZAMO frame
  dragging and horizon speed.
- `KerrSpacetime.metric_zero_spin` : Schwarzschild reduction `a = 0`.

## iii. Table of contents

- A. Boyer–Lindquist metric functions and inverse
- B. Event horizons, ergosphere, and frame dragging
- C. Schwarzschild limit

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

/-!

## A. Boyer–Lindquist metric functions and inverse

In Boyer–Lindquist coordinates `(t, r, θ, φ)`, a rotating uncharged black hole of mass `M` and spin
`a` is governed by the auxiliary polynomials `Σ = r² + a² cos²θ`, `Δ = r² - 2Mr + a²`, and
`A = (r² + a²)² - a² Δ sin²θ`.

-/

/-- Rotating Boyer–Lindquist Kerr black hole spacetime parameterized by mass `M` and spin `a`. -/
structure KerrSpacetime where
  /-- Geometric mass parameter `M` (`G = c = 1`). -/
  M : ℝ
  /-- Spin parameter `a = J / M`. -/
  a : ℝ

namespace KerrSpacetime

/-- Boyer–Lindquist radial-polar function `Σ = r² + a² cos² θ`. -/
noncomputable def sigma (K : KerrSpacetime) (r θ : ℝ) : ℝ := r ^ 2 + K.a ^ 2 * Real.cos θ ^ 2

/-- Boyer–Lindquist horizon function `Δ = r² - 2 M r + a²`. -/
noncomputable def delta (K : KerrSpacetime) (r : ℝ) : ℝ := r ^ 2 - 2 * K.M * r + K.a ^ 2

/-- Boyer–Lindquist axial metric factor `(r² + a²)² - a² Δ sin² θ` (denoted `A` in
Misner–Thorne–Wheeler and Chandrasekhar), factored out because it governs both `g_{φφ}` and
`g^{tt}` and appears directly in the `(t, φ)` block determinant identity. -/
noncomputable def axialFactor (K : KerrSpacetime) (r θ : ℝ) : ℝ :=
  (r ^ 2 + K.a ^ 2) ^ 2 - K.a ^ 2 * K.delta r * Real.sin θ ^ 2

/-- Kerr spacetime metric in Boyer–Lindquist coordinates `x = (t, r, θ, φ)` with signature
`(-, +, +, +)` and geometrized units `G = c = 1`. -/
noncomputable def metric (K : KerrSpacetime) (x : Fin 4 → ℝ) : Tensor2 4 :=
  let sig := K.sigma (x 1) (x 2)
  let del := K.delta (x 1)
  let aval := K.axialFactor (x 1) (x 2)
  let s2 := Real.sin (x 2) ^ 2
  Matrix.of fun i j =>
    if i = 0 ∧ j = 0 then -(1 - 2 * K.M * x 1 / sig)
    else if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then -(2 * K.M * K.a * x 1 * s2 / sig)
    else if i = 1 ∧ j = 1 then sig / del
    else if i = 2 ∧ j = 2 then sig
    else if i = 3 ∧ j = 3 then aval * s2 / sig
    else 0

/-- Analytical inverse of the Boyer–Lindquist Kerr metric `K.metric x`. -/
noncomputable def metricInv (K : KerrSpacetime) (x : Fin 4 → ℝ) : Tensor2 4 :=
  let sig := K.sigma (x 1) (x 2)
  let del := K.delta (x 1)
  let aval := K.axialFactor (x 1) (x 2)
  let s2 := Real.sin (x 2) ^ 2
  Matrix.of fun i j =>
    if i = 0 ∧ j = 0 then -(aval / (sig * del))
    else if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then -(2 * K.M * K.a * x 1 / (sig * del))
    else if i = 1 ∧ j = 1 then del / sig
    else if i = 2 ∧ j = 2 then 1 / sig
    else if i = 3 ∧ j = 3 then (sig - 2 * K.M * x 1) / (sig * del * s2)
    else 0

/-- Alternative expansion of the Boyer–Lindquist axial metric factor:
`axialFactor = Σ (r² + a²) + 2 M a² r sin² θ`. -/
lemma axialFactor_eq_sigma (K : KerrSpacetime) (r θ : ℝ) :
    K.axialFactor r θ
      = K.sigma r θ * (r ^ 2 + K.a ^ 2) + 2 * K.M * K.a ^ 2 * r * Real.sin θ ^ 2 := by
  simp only [axialFactor, sigma, delta]
  rw [Real.sin_sq θ]
  ring

/-- Algebraic identity governing the determinant of the `(t, φ)` metric block:
`(Σ - 2 M r) axialFactor + 4 M² a² r² sin² θ = Σ² Δ`. -/
lemma tphi_det_id (K : KerrSpacetime) (r θ : ℝ) :
    (K.sigma r θ - 2 * K.M * r) * K.axialFactor r θ + 4 * K.M ^ 2 * K.a ^ 2 * r ^ 2 * Real.sin θ ^ 2
      = K.sigma r θ ^ 2 * K.delta r := by
  simp only [sigma, delta, axialFactor]
  rw [Real.sin_sq θ]
  ring

/-- Symmetry of the Boyer–Lindquist Kerr metric `K.metric`. -/
lemma metric_symm (K : KerrSpacetime) (x : Fin 4 → ℝ) : IsSymm (K.metric x) :=
  Matrix.IsSymm.ext fun i j => by
    fin_cases i <;> fin_cases j <;> simp [metric]

/-- Left-inverse verification `g⁻¹ * g = 1` for the Boyer–Lindquist Kerr metric. -/
lemma metricInv_mul_metric (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) (hdel : K.delta (x 1) ≠ 0)
    (hs : Real.sin (x 2) ≠ 0) :
    K.metricInv x * K.metric x = 1 := by
  ext i j
  have hid := K.tphi_det_id (x 1) (x 2)
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.one_apply, Fin.sum_univ_four, metric, metricInv, Matrix.of_apply] <;>
    norm_num
  · field_simp [hsig, hdel]; linear_combination hid
  · field_simp [hsig, hdel]; ring
  · field_simp [hsig, hdel]
  · field_simp [hsig]
  · field_simp [hsig, hdel, hs]; ring
  · field_simp [hsig, hdel, hs]; linear_combination hid

/-- Right-inverse verification `g * g⁻¹ = 1` for the Boyer–Lindquist Kerr metric. -/
lemma metric_mul_metricInv (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) (hdel : K.delta (x 1) ≠ 0)
    (hs : Real.sin (x 2) ≠ 0) :
    K.metric x * K.metricInv x = 1 :=
  mul_eq_one_of_isSymm_of_mul_eq_one (K.metric_symm x)
    (K.metricInv_mul_metric x hsig hdel hs)

/-- Package the Boyer–Lindquist Kerr metric at a regular point (`Σ ≠ 0`, `Δ ≠ 0`, `sin θ ≠ 0`) as a
`MetricTensor 4`. -/
noncomputable def metricTensor (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) (hdel : K.delta (x 1) ≠ 0)
    (hs : Real.sin (x 2) ≠ 0) : MetricTensor 4 where
  g := K.metric x
  ginv := K.metricInv x
  symm := K.metric_symm x
  inv_left := K.metric_mul_metricInv x hsig hdel hs
  inv_right := K.metricInv_mul_metric x hsig hdel hs

/-- The Boyer–Lindquist Kerr metric as a `CoordinateMetric 4` on the chart away from the ring
singularity `Σ = 0`, horizons `Δ = 0`, and polar axis `sin θ = 0`. -/
noncomputable def toCoordinateMetric (K : KerrSpacetime) : CoordinateMetric 4 where
  g := K.metric
  ginv := K.metricInv
  domain := {x | K.sigma (x 1) (x 2) ≠ 0 ∧ K.delta (x 1) ≠ 0 ∧ Real.sin (x 2) ≠ 0}
  symm := K.metric_symm
  inv_left x hx := K.metric_mul_metricInv x hx.1 hx.2.1 hx.2.2
  inv_right x hx := K.metricInv_mul_metric x hx.1 hx.2.1 hx.2.2

/-- The covariant field of `K.toCoordinateMetric` is `K.metric`. -/
@[simp] lemma toCoordinateMetric_g (K : KerrSpacetime) :
    K.toCoordinateMetric.g = K.metric := rfl

/-- The inverse field of `K.toCoordinateMetric` is `K.metricInv`. -/
@[simp] lemma toCoordinateMetric_ginv (K : KerrSpacetime) :
    K.toCoordinateMetric.ginv = K.metricInv := rfl

/-!

## B. Event horizons, ergosphere, and frame dragging

Because the rotating spacetime admits distinct horizon (`Δ = 0`) and static-limit (`g_{tt} = 0`)
surfaces, observers inside the ergosphere are dragged in the direction of the black hole spin.

-/

/-- Outer Kerr event horizon radius `r₊ = M + √(M² - a²)` for `|a| ≤ M`. -/
noncomputable def horizonPlus (K : KerrSpacetime) : ℝ := K.M + Real.sqrt (K.M ^ 2 - K.a ^ 2)

/-- Inner Kerr Cauchy horizon radius `r₋ = M - √(M² - a²)` for `|a| ≤ M`. -/
noncomputable def horizonMinus (K : KerrSpacetime) : ℝ := K.M - Real.sqrt (K.M ^ 2 - K.a ^ 2)

/-- Outer horizon `r₊` is a root of `Δ(r) = 0` when `a² ≤ M²`. -/
lemma delta_horizonPlus (K : KerrSpacetime) (ha : K.a ^ 2 ≤ K.M ^ 2) :
    K.delta K.horizonPlus = 0 := by
  have hsq : Real.sqrt (K.M ^ 2 - K.a ^ 2) ^ 2 = K.M ^ 2 - K.a ^ 2 :=
    Real.sq_sqrt (sub_nonneg.mpr ha)
  simp only [delta, horizonPlus]
  linear_combination hsq

/-- Inner horizon `r₋` is a root of `Δ(r) = 0` when `a² ≤ M²`. -/
lemma delta_horizonMinus (K : KerrSpacetime) (ha : K.a ^ 2 ≤ K.M ^ 2) :
    K.delta K.horizonMinus = 0 := by
  have hsq : Real.sqrt (K.M ^ 2 - K.a ^ 2) ^ 2 = K.M ^ 2 - K.a ^ 2 :=
    Real.sq_sqrt (sub_nonneg.mpr ha)
  simp only [delta, horizonMinus]
  linear_combination hsq

/-- Extremal Kerr limit (`a² = M²`): outer and inner horizons coalesce at `r = M` with a double
root of `Δ`. -/
lemma extremal (K : KerrSpacetime) (ha : K.a ^ 2 = K.M ^ 2) :
    K.horizonPlus = K.M ∧ K.horizonMinus = K.M ∧ K.delta K.M = 0 := by
  have hsub : K.M ^ 2 - K.a ^ 2 = 0 := sub_eq_zero.mpr ha.symm
  refine ⟨?_, ?_, ?_⟩
  · simp [horizonPlus, hsub]
  · simp [horizonMinus, hsub]
  · simp [delta, ha]; ring

/-- Outer stationary-limit (ergosphere) radius `r_E(θ) = M + √(M² - a² cos² θ)`. -/
noncomputable def ergosphereRadius (K : KerrSpacetime) (θ : ℝ) : ℝ :=
  K.M + Real.sqrt (K.M ^ 2 - K.a ^ 2 * Real.cos θ ^ 2)

/-- At the ergosphere radius `r_E(θ)`, `g_{tt} = 0`, so static observers become null. -/
lemma metric_00_ergosphere (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hx1 : x 1 = K.ergosphereRadius (x 2))
    (hcos : K.a ^ 2 * Real.cos (x 2) ^ 2 ≤ K.M ^ 2)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) :
    K.metric x 0 0 = 0 := by
  have hsq : Real.sqrt (K.M ^ 2 - K.a ^ 2 * Real.cos (x 2) ^ 2) ^ 2
      = K.M ^ 2 - K.a ^ 2 * Real.cos (x 2) ^ 2 := Real.sq_sqrt (sub_nonneg.mpr hcos)
  have hnum : K.sigma (x 1) (x 2) - 2 * K.M * x 1 = 0 := by
    rw [hx1]
    simp only [sigma, ergosphereRadius]
    linear_combination hsq
  simp only [metric, Matrix.of_apply, Fin.isValue, and_self, ↓reduceIte]
  field_simp [hsig]
  linear_combination -hnum

/-- Zero-angular-momentum observer (ZAMO) frame-dragging angular velocity
`ω = -g_{tφ} / g_{φφ} = 2 M a r / A`. -/
noncomputable def frameDraggingOmega (K : KerrSpacetime) (r θ : ℝ) : ℝ :=
  2 * K.M * K.a * r / K.axialFactor r θ

/-- Agreement of `-g_{tφ} / g_{φφ}` with `K.frameDraggingOmega r θ`. -/
lemma zamo_omega_eq (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) (hs : Real.sin (x 2) ≠ 0)
    (hA : K.axialFactor (x 1) (x 2) ≠ 0) :
    -(K.metric x 0 3 / K.metric x 3 3)
      = K.frameDraggingOmega (x 1) (x 2) := by
  simp only [metric, frameDraggingOmega, Matrix.of_apply, Fin.isValue, Fin.reduceEq, and_false,
    and_true, or_false, ↓reduceIte]
  field_simp [hsig, hs, hA]

/-- At the outer event horizon `r₊`, `A(r₊, θ) = (r₊² + a²)²`, giving the horizon angular
velocity `ω_H = 2 M a r₊ / (r₊² + a²)²`. -/
lemma frameDraggingOmega_horizonPlus (K : KerrSpacetime) (ha : K.a ^ 2 ≤ K.M ^ 2) (θ : ℝ) :
    K.frameDraggingOmega K.horizonPlus θ
      = 2 * K.M * K.a * K.horizonPlus / (K.horizonPlus ^ 2 + K.a ^ 2) ^ 2 := by
  have hdel : K.delta K.horizonPlus = 0 := K.delta_horizonPlus ha
  simp [frameDraggingOmega, axialFactor, hdel]

/-!

## C. Schwarzschild limit

Setting the spin parameter `a = 0` extinguishes frame dragging and reduces every component of the
Boyer–Lindquist metric to the static exterior Schwarzschild metric.

-/

/-- In the non-rotating limit `a = 0`, `metric` reduces entrywise to the Schwarzschild metric with
`f(r) = 1 - 2 M / r`. -/
lemma metric_zero_spin (M : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (_hf : 1 - 2 * M / x 1 ≠ 0) :
    ((KerrSpacetime.mk M 0).metric x 0 0 = -(1 - 2 * M / x 1))
      ∧ ((KerrSpacetime.mk M 0).metric x 0 3 = 0)
      ∧ ((KerrSpacetime.mk M 0).metric x 1 1 = (1 - 2 * M / x 1)⁻¹)
      ∧ ((KerrSpacetime.mk M 0).metric x 2 2 = (x 1) ^ 2)
      ∧ ((KerrSpacetime.mk M 0).metric x 3 3 = (x 1) ^ 2 * Real.sin (x 2) ^ 2) := by
  have hr2 : (x 1) ^ 2 ≠ 0 := pow_ne_zero 2 hr
  have hs0 : (KerrSpacetime.mk M 0).sigma (x 1) (x 2) = (x 1) ^ 2 := by simp [sigma]
  have hd0 : (KerrSpacetime.mk M 0).delta (x 1) = (x 1) ^ 2 * (1 - 2 * M / x 1) := by
    simp only [delta]; field_simp [hr]; ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [metric, Matrix.of_apply, hs0, Fin.isValue, and_self, ↓reduceIte]
    field_simp [hr]
  · simp [metric]
  · simp only [metric, Matrix.of_apply, hs0, hd0, Fin.isValue, Fin.reduceEq, ↓reduceIte,
      and_self, or_self]
    field_simp [hr2]
  · simp [metric, hs0]
  · simp only [metric, Matrix.of_apply, hs0, axialFactor, Fin.isValue]
    norm_num
    field_simp [hr2]

end KerrSpacetime

end Kerr

end GeneralRelativity
