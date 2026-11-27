/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.General.Linearized.MinkowskiDalembertian
public import PhyslibAlpha.Relativity.Metrics.ConformalMetric
public import PhyslibAlpha.Relativity.Metrics.CoordinateMetric
public import PhyslibAlpha.Relativity.Metrics.Minkowski
public import PhyslibAlpha.Relativity.Metrics.NullVector
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!

# Nordström scalar gravitation (Einstein–Fokker formulation)

Conformally flat Nordström spacetime `g = φ² η`, null-cone invariance (zero light bending), and
the 4D Einstein–Fokker scalar curvature identity `R = -6 □φ / φ³`.

## i. Overview

This module formalizes Nordström's second scalar theory of gravity in its geometric
Einstein–Fokker reformulation around `NordstromSpacetime`: the metric `g(x) = φ(x)² η` is
conformally flat around Minkowski spacetime, inducing a `CoordinateMetric 4` wherever `φ(x) ≠ 0`.
It proves conformal null-cone invariance (`vᵀ g v = 0 ↔ vᵀ η v = 0`, explaining the absence of
gravitational light bending), evaluates the exact conformal Christoffel symbols, derives the exact
four-dimensional Ricci scalar curvature `R = -6 □φ / φ³`, and establishes equivalence between the
Einstein–Fokker equation `R = 24 π T` and Nordström's nonlinear scalar wave equation
`□φ = -4 π φ³ T`.

## ii. Key results

- `NordstromSpacetime`, `NordstromSpacetime.metric`, `NordstromSpacetime.metricInv`,
  `NordstromSpacetime.metricTensor`, `NordstromSpacetime.toCoordinateMetric` : conformally flat
  Nordström spacetime metric, `MetricTensor 4`, and `CoordinateMetric 4`.
- `NordstromSpacetime.light_deflection_zero` : null cones coincide with Minkowski space via
  `nullVector_conformal_iff` (zero light bending).
- `NordstromSpacetime.christoffel_eq` : exact conformal Christoffel symbols.
- `NordstromSpacetime.ricciScalar` : exact 4D Einstein–Fokker identity `R = -6 □φ / φ³`.
- `NordstromSpacetime.einsteinFokker_iff` : equivalence between `R = 24 π T` and `□φ = -4 π φ³ T`.

## iii. Table of contents

- A. Conformally flat Nordström metric and zero light bending
- B. Conformal Christoffel symbols from the coordinate metric
- C. Four-dimensional Einstein–Fokker scalar curvature

## iv. References

* Gunnar Nordström, *Zur Theorie der Gravitation vom Standpunkt des Relativitätsprinzips*, *Annalen
  der Physik* 347, pp. 533-554 (1913). [ref: Nordstrom1913]
* Albert Einstein and Adriaan D. Fokker, *Die Nordströmsche Gravitationstheorie vom Standpunkt des
  absoluten Differentialkalküls*, *Annalen der Physik* 349, pp. 321-328 (1914).
  [ref: EinsteinFokker1914]
* Gunnar Nordström, *Relativitätsprinzip und Gravitation*, *Physikalische Zeitschrift* 13, pp.
  1126-1129 (1912). [ref: Nordstrom1912]
* John D. Norton, *Einstein, Nordström and the Early Demise of Scalar, Lorentz-Covariant Theories of
  Gravitation*, *Archive for History of Exact Sciences* 45, pp. 17-94 (1992), Sec. 2-4.
  [ref: Norton1992]
-/

@[expose] public section

namespace GeneralRelativity

namespace Modified

namespace Nordstrom

open CoordinateCurvature Linearized

/-!

## A. Conformally flat Nordström metric and zero light bending

Rescaling Minkowski spacetime by `N.φ(x)²` preserves null cones identically, immediately forcing
vanishing gravitational light deflection.

-/

/-- Conformally flat Nordström scalar-gravity spacetime parameterized by its conformal
factor `φ : (Fin 4 → ℝ) → ℝ`. -/
structure NordstromSpacetime where
  /-- Scalar conformal factor `φ(x)` in `g = φ² η`. -/
  φ : (Fin 4 → ℝ) → ℝ

/-- Conformally flat Nordström metric `g_{ij}(x) = φ(x)² η_{ij}` with Minkowski signature
`(-, +, +, +)`. -/
noncomputable def NordstromSpacetime.metric (N : NordstromSpacetime) (x : Fin 4 → ℝ) : Tensor2 4 :=
  conformalRescaleMetric minkowskiMetric4 (N.φ x ^ 2)

/-- Inverse Nordström metric `g^{ij}(x) = φ(x)⁻² η^{ij}`. -/
noncomputable def NordstromSpacetime.metricInv (N : NordstromSpacetime) (x : Fin 4 → ℝ) :
    Tensor2 4 :=
  conformalRescaleMetricInv minkowskiMetric4 (N.φ x ^ 2)

/-- Package `N.metric` and `N.metricInv` as a `MetricTensor 4` wherever `N.φ x ≠ 0`. -/
noncomputable def NordstromSpacetime.metricTensor (N : NordstromSpacetime) (x : Fin 4 → ℝ)
    (hφ : N.φ x ≠ 0) : MetricTensor 4 :=
  conformalMetric minkowski (N.φ x ^ 2) (pow_ne_zero 2 hφ)

/-- View a `NordstromSpacetime` as a `CoordinateMetric 4` on the regular domain
`{x | N.φ x ≠ 0}`. -/
noncomputable def NordstromSpacetime.toCoordinateMetric (N : NordstromSpacetime) :
    CoordinateMetric 4 where
  g := N.metric
  ginv := N.metricInv
  domain := {x | N.φ x ≠ 0}
  symm x := Matrix.IsSymm.ext fun i j => by
    simp only [NordstromSpacetime.metric, conformalRescaleMetric]
    exact congrArg (N.φ x ^ 2 * ·) (minkowskiMetric4_symm.apply i j)
  inv_left x hx := (N.metricTensor x hx).inv_left
  inv_right x hx := (N.metricTensor x hx).inv_right

/-- The covariant field of `N.toCoordinateMetric` is `N.metric`. -/
@[simp] lemma NordstromSpacetime.toCoordinateMetric_g (N : NordstromSpacetime) :
    N.toCoordinateMetric.g = N.metric := rfl

/-- The inverse field of `N.toCoordinateMetric` is `N.metricInv`. -/
@[simp] lemma NordstromSpacetime.toCoordinateMetric_ginv (N : NordstromSpacetime) :
    N.toCoordinateMetric.ginv = N.metricInv := rfl

/-- Zero light deflection in Nordström gravity: null tangent vectors of `φ² η` coincide with
unbent Minkowski null rays. -/
lemma NordstromSpacetime.light_deflection_zero (N : NordstromSpacetime) (x : Fin 4 → ℝ)
    (hφ : N.φ x ≠ 0) (v : Fin 4 → ℝ) :
    NullVector (N.metric x) v ↔ NullVector minkowskiMetric4 v :=
  nullVector_conformal_iff (N.φ x ^ 2) (pow_ne_zero 2 hφ) minkowskiMetric4 v

/-!

## B. Conformal Christoffel symbols from the coordinate metric

Evaluating the coordinate Christoffel symbols on `N.metric` produces the closed-form conformal Weyl
connection coefficients in terms of first partial derivatives of `N.φ`.

-/

/-- Closed-form Christoffel symbols `Γ^k_{ij} = (δ^k_i ∂_j φ + δ^k_j ∂_i φ - η_{ij} η^{kk} ∂_k φ)
/ φ` of the conformally flat metric `φ² η`, stated separately from the general coordinate
Christoffel formula so conformal Ricci computations stay tractable. -/
noncomputable def NordstromSpacetime.christoffel (N : NordstromSpacetime) (x : Fin 4 → ℝ)
    (k i j : Fin 4) : ℝ :=
  ((if k = i then coordDeriv j N.φ x else 0) + (if k = j then coordDeriv i N.φ x else 0)
    - minkowskiMetric4 i j * minkowskiMetric4 k k * coordDeriv k N.φ x) / N.φ x

private lemma pd_conformal_eta (N : NordstromSpacetime) (x : Fin 4 → ℝ)
    (hd : DifferentiableAt ℝ N.φ x) (μ i j : Fin 4) :
    coordDeriv μ (fun y => N.metric y i j) x =
      2 * N.φ x * coordDeriv μ N.φ x * minkowskiMetric4 i j := by
  have hs := hasDerivAt_update_slice μ hd
  have hsq : HasDerivAt (fun s => N.φ (Function.update x μ s) ^ 2 * minkowskiMetric4 i j)
      (2 * N.φ x * coordDeriv μ N.φ x * minkowskiMetric4 i j) (x μ) :=
    ((hs.pow 2).mul_const (minkowskiMetric4 i j)).congr_deriv
      (by simp only [Function.update_eq_self]; ring)
  have hfun : (fun s => N.metric (Function.update x μ s) i j)
      = fun s => N.φ (Function.update x μ s) ^ 2 * minkowskiMetric4 i j := by
    funext s; simp [NordstromSpacetime.metric, conformalRescaleMetric]
  rw [coordDeriv, hfun, hsq.deriv]

/-- Agreement of the coordinate Christoffel symbols of `N.metric` with `N.christoffel` at every
point where `N.φ x ≠ 0` and `N.φ` is differentiable. -/
lemma NordstromSpacetime.christoffel_eq (N : NordstromSpacetime) (x : Fin 4 → ℝ)
    (hφ : N.φ x ≠ 0) (hd : DifferentiableAt ℝ N.φ x) (k i j : Fin 4) :
    N.toCoordinateMetric.christoffel x k i j = N.christoffel x k i j := by
  rw [show N.toCoordinateMetric.christoffel x k i j =
      CoordinateCurvature.christoffel N.metric N.metricInv x k i j from rfl]
  simp only [CoordinateCurvature.christoffel, pd_conformal_eta N x hd, NordstromSpacetime.metricInv,
    conformalRescaleMetricInv, NordstromSpacetime.christoffel, Fin.sum_univ_four]
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp only [minkowskiMetric4_apply] <;> norm_num <;> field_simp [hφ]

/-!

## C. Four-dimensional Einstein–Fokker scalar curvature

Differentiating `N.christoffel` and taking the Minkowski trace identifies the 4D scalar curvature
of `φ² η` with `-6 □φ / φ³`, equating `R = 24 π T` to `□φ = -4 π φ³ T`.

-/

private lemma pd_div_phi (φ : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) (hφ : φ x ≠ 0)
    (h1 : DifferentiableAt ℝ φ x) (h2 : ∀ μ, DifferentiableAt ℝ (coordDeriv μ φ) x) (μ ν : Fin 4) :
    coordDeriv μ (fun y => coordDeriv ν φ y / φ y) x =
      (coordDeriv μ (coordDeriv ν φ) x * φ x - coordDeriv ν φ x * coordDeriv μ φ x) /
        φ x ^ 2 := by
  have hφ' : φ (Function.update x μ (x μ)) ≠ 0 := by
    simpa [Function.update_eq_self] using hφ
  have hq := (hasDerivAt_update_slice μ (h2 ν)).fun_div
    (hasDerivAt_update_slice μ h1) hφ'
  simpa [coordDeriv, Function.update_eq_self] using hq.deriv

private lemma differentiableAt_ite_div_phi (φ : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) (hφ : φ x ≠ 0)
    (h1 : DifferentiableAt ℝ φ x) (h2 : ∀ μ, DifferentiableAt ℝ (coordDeriv μ φ) x)
    (P : Prop) [Decidable P] (μ ν : Fin 4) :
    DifferentiableAt ℝ (fun s => if P then coordDeriv ν φ (Function.update x μ s)
      / φ (Function.update x μ s) else 0) (x μ) := by
  have hφ' : φ (Function.update x μ (x μ)) ≠ 0 := by
    simpa [Function.update_eq_self] using hφ
  split_ifs
  · exact ((hasDerivAt_update_slice μ (h2 ν)).fun_div
      (hasDerivAt_update_slice μ h1) hφ').differentiableAt
  · exact differentiableAt_const _

private lemma coordDeriv_ite_div_phi (φ : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) (hφ : φ x ≠ 0)
    (h1 : DifferentiableAt ℝ φ x) (h2 : ∀ μ, DifferentiableAt ℝ (coordDeriv μ φ) x)
    (P : Prop) [Decidable P] (μ ν : Fin 4) :
    coordDeriv μ (fun y => if P then coordDeriv ν φ y / φ y else 0) x =
      if P then (coordDeriv μ (coordDeriv ν φ) x * φ x - coordDeriv ν φ x * coordDeriv μ φ x) /
        φ x ^ 2 else 0 := by
  split_ifs
  · exact pd_div_phi φ x hφ h1 h2 μ ν
  · exact coordDeriv_const μ 0 x

private lemma pd_nordstromChristoffel (N : NordstromSpacetime) (x : Fin 4 → ℝ) (hφ : N.φ x ≠ 0)
    (hc2 : ContDiffAt ℝ 2 N.φ x) (μ k i j : Fin 4) :
    coordDeriv μ (fun y => N.christoffel y k i j) x =
      ((if k = i then (coordDeriv μ (coordDeriv j N.φ) x * N.φ x
          - coordDeriv j N.φ x * coordDeriv μ N.φ x) / N.φ x ^ 2 else 0)
        + (if k = j then (coordDeriv μ (coordDeriv i N.φ) x * N.φ x
          - coordDeriv i N.φ x * coordDeriv μ N.φ x) / N.φ x ^ 2 else 0)
        - minkowskiMetric4 i j * minkowskiMetric4 k k *
          ((coordDeriv μ (coordDeriv k N.φ) x * N.φ x
            - coordDeriv k N.φ x * coordDeriv μ N.φ x) / N.φ x ^ 2)) := by
  have h1 : DifferentiableAt ℝ N.φ x := hc2.differentiableAt (by norm_num)
  have h2 : ∀ ν, DifferentiableAt ℝ (coordDeriv ν N.φ) x :=
    fun ν => coordDeriv_differentiableAt ν hc2
  have hrew : (fun y => N.christoffel y k i j) = fun y =>
      (if k = i then coordDeriv j N.φ y / N.φ y else 0)
      + (if k = j then coordDeriv i N.φ y / N.φ y else 0)
      - minkowskiMetric4 i j * minkowskiMetric4 k k * (coordDeriv k N.φ y / N.φ y) := by
    funext y
    simp only [NordstromSpacetime.christoffel]
    split_ifs <;> ring
  have hφ' : N.φ (Function.update x μ (x μ)) ≠ 0 := by
    simpa [Function.update_eq_self] using hφ
  have hd_q : DifferentiableAt ℝ (fun s => coordDeriv k N.φ (Function.update x μ s)
      / N.φ (Function.update x μ s)) (x μ) :=
    ((hasDerivAt_update_slice μ (h2 k)).fun_div (hasDerivAt_update_slice μ h1) hφ').differentiableAt
  rw [hrew, coordDeriv_sub μ x
      ((differentiableAt_ite_div_phi N.φ x hφ h1 h2 (k = i) μ j).add
        (differentiableAt_ite_div_phi N.φ x hφ h1 h2 (k = j) μ i))
      (hd_q.const_mul _),
    coordDeriv_add μ x (differentiableAt_ite_div_phi N.φ x hφ h1 h2 (k = i) μ j)
      (differentiableAt_ite_div_phi N.φ x hφ h1 h2 (k = j) μ i),
    coordDeriv_const_mul,
    coordDeriv_ite_div_phi N.φ x hφ h1 h2 (k = i) μ j,
    coordDeriv_ite_div_phi N.φ x hφ h1 h2 (k = j) μ i,
    pd_div_phi N.φ x hφ h1 h2 μ k]

private lemma ricciTensor_nordstrom_diag (N : NordstromSpacetime) (x : Fin 4 → ℝ)
    (hφ : N.φ x ≠ 0) (hc2 : ContDiffAt ℝ 2 N.φ x) (s : Fin 4) :
    CoordinateCurvature.ricciTensor N.metric N.metricInv x s s =
      (-(2 : ℝ) * (coordDeriv s (coordDeriv s N.φ) x * N.φ x - 2 * coordDeriv s N.φ x ^ 2) /
          N.φ x ^ 2
        - minkowskiMetric4 s s * (∑ ρ : Fin 4, minkowskiMetric4 ρ ρ *
          (coordDeriv ρ (coordDeriv ρ N.φ) x * N.φ x + coordDeriv ρ N.φ x ^ 2)) / N.φ x ^ 2) := by
  have nh : ∀ᶠ y in nhds x, ContDiffAt ℝ 2 N.φ y := hc2.eventually (by simp)
  have hne : ∀ᶠ y in nhds x, N.φ y ≠ 0 := hc2.continuousAt.eventually_ne hφ
  have hconv : ∀ (y : Fin 4 → ℝ) (k i j : Fin 4),
      N.toCoordinateMetric.christoffel y k i j =
        CoordinateCurvature.christoffel N.metric N.metricInv y k i j :=
    fun _ _ _ _ => rfl
  have hev : ∀ k i j,
      (fun y => CoordinateCurvature.christoffel N.metric N.metricInv y k i j)
        =ᶠ[nhds x] fun y => N.christoffel y k i j := by
    intro k i j
    filter_upwards [nh, hne] with y hy hyne
    rw [← hconv y k i j]
    exact N.christoffel_eq y hyne (hy.differentiableAt (by norm_num)) k i j
  have hpt : ∀ k i j,
      CoordinateCurvature.christoffel N.metric N.metricInv x k i j = N.christoffel x k i j :=
    fun k i j => by
      rw [← hconv x k i j]
      exact N.christoffel_eq x hφ (hc2.differentiableAt (by norm_num)) k i j
  have hpd : ∀ μ k i j,
      coordDeriv μ (fun y => CoordinateCurvature.christoffel N.metric N.metricInv y k i j) x
        = coordDeriv μ (fun y => N.christoffel y k i j) x :=
    fun μ k i j => coordDeriv_congr_nhds μ x (hev k i j)
  simp only [CoordinateCurvature.ricciTensor, riemann, hpd, hpt, Fin.sum_univ_four]
  simp only [pd_nordstromChristoffel N x hφ hc2]
  simp only [NordstromSpacetime.christoffel]
  fin_cases s
  all_goals simp only [minkowskiMetric4_apply]; norm_num
  all_goals field_simp [hφ]
  all_goals ring

/-- Exact 4D Einstein–Fokker scalar curvature identity `R = -6 □φ / φ³` for a `NordstromSpacetime`,
obtained from the coordinate metric `N.metric`. -/
lemma NordstromSpacetime.ricciScalar (N : NordstromSpacetime) (x : Fin 4 → ℝ) (hφ : N.φ x ≠ 0)
    (hc2 : ContDiffAt ℝ 2 N.φ x) :
    N.toCoordinateMetric.ricciScalar x
      = -6 * minkowskiDalembertian N.φ x / N.φ x ^ 3 := by
  rw [show N.toCoordinateMetric.ricciScalar x =
      CoordinateCurvature.ricciScalar N.metric N.metricInv x from rfl]
  simp only [CoordinateCurvature.ricciScalar, Fin.sum_univ_four, NordstromSpacetime.metricInv,
    conformalRescaleMetricInv, minkowskiMetric4_apply]
  norm_num
  simp only [ricciTensor_nordstrom_diag N x hφ hc2, minkowskiDalembertian, Fin.sum_univ_four,
    minkowskiMetric4_apply]
  norm_num
  field_simp [hφ]
  ring

/-- Equivalence between the 4D Einstein–Fokker geometric equation `S = 24 π T` and Nordström's
scalar wave equation `□φ = -4 π φ³ T`. -/
lemma NordstromSpacetime.einsteinFokker_iff (N : NordstromSpacetime) (x : Fin 4 → ℝ)
    (hφ : N.φ x ≠ 0) (hc2 : ContDiffAt ℝ 2 N.φ x) (T : ℝ) :
    N.toCoordinateMetric.ricciScalar x = 24 * Real.pi * T
      ↔ minkowskiDalembertian N.φ x = -4 * Real.pi * N.φ x ^ 3 * T := by
  rw [N.ricciScalar x hφ hc2]
  have h3 : N.φ x ^ 3 ≠ 0 := pow_ne_zero 3 hφ
  constructor <;> intro h
  · field_simp [h3] at h; linarith
  · rw [h]; field_simp [h3]; ring

end Nordstrom

end Modified

end GeneralRelativity
