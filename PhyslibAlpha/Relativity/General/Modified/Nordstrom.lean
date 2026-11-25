/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.General.Linearized.TraceReversed
public import PhyslibAlpha.Relativity.Metrics.ConformalMetric
public import PhyslibAlpha.Relativity.Metrics.CoordinateMetric
public import PhyslibAlpha.Relativity.Metrics.Minkowski
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!

# Nordström scalar gravitation (Einstein–Fokker formulation)

Conformally flat Nordström spacetime `g = φ² η`, null-cone invariance (zero light bending), and
the 4D Einstein–Fokker scalar curvature identity `S = -6 □φ / φ³`.

## i. Overview

This module formalizes Nordström's second scalar theory of gravity in its geometric
Einstein–Fokker reformulation: the metric `nordstromMetric φ x = φ(x)² η` is conformally flat
around Minkowski spacetime `minkowskiMetric4`. It proves conformal null-cone invariance (`vᵀ g v =
0 ↔
vᵀ η v = 0`, explaining the absence of gravitational light bending), evaluates the exact
Christoffel symbols through `Pipeline.christoffel`, derives the exact four-dimensional Ricci scalar
curvature `ricciScalarOf = -6 □φ / φ³` through `Pipeline.ricciScalarOf`, and establishes
equivalence between
the Einstein–Fokker equation `S = 24 π T` and Nordström's nonlinear scalar wave equation
`□φ = -4 π φ³ T`.

## ii. Key results

- `NordstromSpacetime` : conformally flat Nordström spacetime bundled by its scalar field
  `φ`.
- `nordstromMetric`, `nordstromMetricInv`, `nordstromMetricTensor` : conformally flat Nordström
  spacetime metric and `MetricTensor 4`.
- `light_deflection_zero` : null cones coincide with Minkowski space via
  `nullVector_conformal_iff` (zero light bending).
- `christoffel_nordstrom_eq` : exact conformal Christoffel symbols via `Pipeline.christoffel`.
- `ricciScalarOf_nordstrom` : exact 4D Einstein–Fokker identity `S = -6 □φ / φ³`.
- `einsteinFokker_iff` : equivalence between `S = 24 π T` and `□φ = -4 π φ³ T`.

## iii. Table of contents

- A. Conformally flat Nordström metric and zero light bending
- B. Conformal Christoffel symbols via the coordinate pipeline
- C. Four-dimensional Einstein–Fokker scalar curvature

## iv. References

* Gunnar Nordström, *Zur Theorie der Gravitation vom Standpunkt des Relativitätsprinzips*,
  *Annalen der Physik* (1913). [ref: Nordstrom1913]
* Albert Einstein and Adriaan D. Fokker, *Die Nordströmsche Gravitationstheorie vom Standpunkt des
  absoluten Differentialkalküls*, *Annalen der Physik* (1914). [ref: EinsteinFokker1914]
* Gunnar Nordström, *Relativitätsprinzip und Gravitation*, *Physikalische Zeitschrift* (1912).
  [ref: Nordstrom1912]
* John D. Norton, *Einstein, Nordström and the Early Demise of Scalar, Lorentz-Covariant Theories
  of Gravitation*, *Archive for History of Exact Sciences* (1992). [ref: Norton1992]

-/

@[expose] public section

namespace GeneralRelativity

namespace Modified

namespace Nordstrom

open Pipeline Linearized

/-!

## A. Conformally flat Nordström metric and zero light bending

-/

/-- Conformally flat Nordström scalar-gravity spacetime parameterized by its conformal
factor `φ : (Fin 4 → ℝ) → ℝ`. -/
structure NordstromSpacetime where
  /-- Scalar conformal factor `φ(x)` in `g = φ² η`. -/
  φ : (Fin 4 → ℝ) → ℝ

/-- Conformally flat Nordström metric `g_{ij}(x) = φ(x)² η_{ij}` with Minkowski signature
`(-, +, +, +)`. -/
noncomputable def nordstromMetric (φ : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) : Tensor2 4 :=
  conformalRescaleMetric minkowskiMetric4 (φ x ^ 2)

/-- Inverse Nordström metric `g^{ij}(x) = φ(x)⁻² η^{ij}`. -/
noncomputable def nordstromMetricInv (φ : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) : Tensor2 4 :=
  conformalRescaleMetricInv minkowskiMetric4 (φ x ^ 2)

/-- Package `nordstromMetric` and `nordstromMetricInv` as a `MetricTensor 4` wherever `φ x ≠ 0`. -/
noncomputable def nordstromMetricTensor (φ : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) (hφ : φ x ≠ 0) :
    MetricTensor 4 :=
  conformalMetric minkowski (φ x ^ 2) (pow_ne_zero 2 hφ)

/-- Zero light deflection in Nordström gravity: null tangent vectors of `φ² η` coincide with
unbent Minkowski null rays. -/
lemma light_deflection_zero (φ : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) (hφ : φ x ≠ 0)
    (v : Fin 4 → ℝ) :
    NullVector (nordstromMetric φ x) v ↔ NullVector minkowskiMetric4 v :=
  nullVector_conformal_iff (φ x ^ 2) (pow_ne_zero 2 hφ) minkowskiMetric4 v

/-!

## B. Conformal Christoffel symbols via the coordinate pipeline

-/

/-- Closed-form Christoffel symbols `Γ^k_{ij} = (δ^k_i ∂_j φ + δ^k_j ∂_i φ - η_{ij} η^{kk} ∂_k φ)
/ φ` of the conformally flat metric `φ² η`, kept separate from `Pipeline.christoffel` so
conformal Ricci computations stay tractable. -/
noncomputable def nordstromChristoffel (φ : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ)
    (k i j : Fin 4) : ℝ :=
  ((if k = i then coordDeriv j φ x else 0) + (if k = j then coordDeriv i φ x else 0)
    - minkowskiMetric4 i j * minkowskiMetric4 k k * coordDeriv k φ x) / φ x

private lemma hasDerivAt_update_slice (g : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) (μ : Fin 4)
    (hg : DifferentiableAt ℝ g x) :
    HasDerivAt (fun s => g (Function.update x μ s)) (coordDeriv μ g x) (x μ) := by
  have hu : (fun s : ℝ => Function.update x μ s)
      = fun s => x + (s - x μ) • (Pi.single μ 1 : Fin 4 → ℝ) := by
    ext s k; by_cases hk : k = μ <;> simp [Function.update, hk]
  have hdu : HasDerivAt (fun s : ℝ => Function.update x μ s)
      (Pi.single μ 1 : Fin 4 → ℝ) (x μ) := by
    rw [hu]
    simpa using (((hasDerivAt_id (x μ)).sub_const (x μ)).smul_const
      (Pi.single μ 1 : Fin 4 → ℝ)).const_add x
  have hf' : HasFDerivAt g (fderiv ℝ g x) (Function.update x μ (x μ)) := by
    simpa [Function.update_eq_self] using hg.hasFDerivAt
  exact (hf'.comp_hasDerivAt (x μ) hdu).differentiableAt.hasDerivAt

private lemma pd_conformal_eta (φ : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ)
    (hd : DifferentiableAt ℝ φ x) (μ i j : Fin 4) :
    coordDeriv μ (fun y => nordstromMetric φ y i j) x =
      2 * φ x * coordDeriv μ φ x * minkowskiMetric4 i j := by
  have hs := hasDerivAt_update_slice φ x μ hd
  have hsq : HasDerivAt (fun s => φ (Function.update x μ s) ^ 2 * minkowskiMetric4 i j)
      (2 * φ x * coordDeriv μ φ x * minkowskiMetric4 i j) (x μ) :=
    ((hs.pow 2).mul_const (minkowskiMetric4 i j)).congr_deriv
      (by simp only [Function.update_eq_self]; ring)
  have hfun : (fun s => nordstromMetric φ (Function.update x μ s) i j)
      = fun s => φ (Function.update x μ s) ^ 2 * minkowskiMetric4 i j := by
    funext s; simp [nordstromMetric, conformalRescaleMetric]
  rw [coordDeriv, hfun, hsq.deriv]

/-- Agreement of `Pipeline.christoffel` for `nordstromMetric φ` with `nordstromChristoffel φ` at
every
point where `φ x ≠ 0` and `φ` is differentiable. -/
lemma christoffel_nordstrom_eq (φ : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) (hφ : φ x ≠ 0)
    (hd : DifferentiableAt ℝ φ x) (k i j : Fin 4) :
    christoffel (nordstromMetric φ) (nordstromMetricInv φ) x k i j
      = nordstromChristoffel φ x k i j := by
  simp only [christoffel, pd_conformal_eta φ x hd, nordstromMetricInv, conformalRescaleMetricInv,
    nordstromChristoffel, Fin.sum_univ_four]
  fin_cases k
  · fin_cases i <;> fin_cases j <;> simp only [minkowskiMetric4_apply] <;> norm_num <;>
      field_simp [hφ]
  · fin_cases i <;> fin_cases j <;> simp only [minkowskiMetric4_apply] <;> norm_num <;>
      field_simp [hφ]
  · fin_cases i <;> fin_cases j <;> simp only [minkowskiMetric4_apply] <;> norm_num <;>
      field_simp [hφ]
  · fin_cases i <;> fin_cases j <;> simp only [minkowskiMetric4_apply] <;> norm_num <;>
      field_simp [hφ]

/-!

## C. Four-dimensional Einstein–Fokker scalar curvature

-/

private lemma pd_div_phi (φ : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) (hφ : φ x ≠ 0)
    (h1 : DifferentiableAt ℝ φ x) (h2 : ∀ μ, DifferentiableAt ℝ (coordDeriv μ φ) x) (μ ν : Fin 4) :
    coordDeriv μ (fun y => coordDeriv ν φ y / φ y) x =
      (coordDeriv μ (coordDeriv ν φ) x * φ x - coordDeriv ν φ x * coordDeriv μ φ x) /
        φ x ^ 2 := by
  have hφ' : φ (Function.update x μ (x μ)) ≠ 0 := by
    simpa [Function.update_eq_self] using hφ
  have hq := (hasDerivAt_update_slice (coordDeriv ν φ) x μ (h2 ν)).fun_div
    (hasDerivAt_update_slice φ x μ h1) hφ'
  simpa [coordDeriv, Function.update_eq_self] using hq.deriv

private lemma pd_nordstromChristoffel (φ : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) (hφ : φ x ≠ 0)
    (hc2 : ContDiffAt ℝ 2 φ x) (μ k i j : Fin 4) :
    coordDeriv μ (fun y => nordstromChristoffel φ y k i j) x =
      ((if k = i then (coordDeriv μ (coordDeriv j φ) x * φ x
          - coordDeriv j φ x * coordDeriv μ φ x) / φ x ^ 2 else 0)
        + (if k = j then (coordDeriv μ (coordDeriv i φ) x * φ x
          - coordDeriv i φ x * coordDeriv μ φ x) / φ x ^ 2 else 0)
        - minkowskiMetric4 i j * minkowskiMetric4 k k * ((coordDeriv μ (coordDeriv k φ) x * φ x
          - coordDeriv k φ x * coordDeriv μ φ x) / φ x ^ 2)) := by
  have nh : ∀ᶠ y in nhds x, ContDiffAt ℝ 2 φ y := hc2.eventually (by simp)
  have h1 : DifferentiableAt ℝ φ x := hc2.differentiableAt (by norm_num)
  have h2 : ∀ ν, DifferentiableAt ℝ (coordDeriv ν φ) x := fun ν => coordDeriv_differentiableAt ν hc2
  have hrew : (fun y => nordstromChristoffel φ y k i j) = fun y =>
      (if k = i then coordDeriv j φ y / φ y else 0)
      + (if k = j then coordDeriv i φ y / φ y else 0)
      - minkowskiMetric4 i j * minkowskiMetric4 k k * (coordDeriv k φ y / φ y) := by
    funext y
    simp only [nordstromChristoffel]
    split_ifs <;> ring
  have hd_q : ∀ ν, DifferentiableAt ℝ (fun s => coordDeriv ν φ (Function.update x μ s)
      / φ (Function.update x μ s)) (x μ) := by
    intro ν
    have hφ' : φ (Function.update x μ (x μ)) ≠ 0 := by
      simpa [Function.update_eq_self] using hφ
    exact ((hasDerivAt_update_slice (coordDeriv ν φ) x μ (h2 ν)).fun_div
      (hasDerivAt_update_slice φ x μ h1) hφ').differentiableAt
  have hd_if1 : DifferentiableAt ℝ (fun s => if k = i then coordDeriv j φ (Function.update x μ s)
      / φ (Function.update x μ s) else 0) (x μ) := by
    split_ifs <;> first | exact hd_q j | exact differentiableAt_const _
  have hd_if2 : DifferentiableAt ℝ (fun s => if k = j then coordDeriv i φ (Function.update x μ s)
      / φ (Function.update x μ s) else 0) (x μ) := by
    split_ifs <;> first | exact hd_q i | exact differentiableAt_const _
  have hd_eta : DifferentiableAt ℝ (fun s => minkowskiMetric4 i j * minkowskiMetric4 k k *
      (coordDeriv k φ (Function.update x μ s) / φ (Function.update x μ s))) (x μ) :=
    (hd_q k).const_mul _
  rw [hrew, coordDeriv_sub μ x (hd_if1.add hd_if2) hd_eta, coordDeriv_add μ x hd_if1 hd_if2,
    coordDeriv_const_mul]
  have hdp1 : coordDeriv μ (fun y => if k = i then coordDeriv j φ y / φ y else 0) x =
      if k = i then (coordDeriv μ (coordDeriv j φ) x * φ x
        - coordDeriv j φ x * coordDeriv μ φ x) / φ x ^ 2 else 0 := by
    split_ifs
    · exact pd_div_phi φ x hφ h1 h2 μ j
    · exact coordDeriv_const μ 0 x
  have hdp2 : coordDeriv μ (fun y => if k = j then coordDeriv i φ y / φ y else 0) x =
      if k = j then (coordDeriv μ (coordDeriv i φ) x * φ x
        - coordDeriv i φ x * coordDeriv μ φ x) / φ x ^ 2 else 0 := by
    split_ifs
    · exact pd_div_phi φ x hφ h1 h2 μ i
    · exact coordDeriv_const μ 0 x
  rw [hdp1, hdp2, pd_div_phi φ x hφ h1 h2 μ k]

private lemma ricciTensorOf_nordstrom_diag (φ : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) (hφ : φ x ≠ 0)
    (hc2 : ContDiffAt ℝ 2 φ x) (s : Fin 4) :
    ricciTensorOf (nordstromMetric φ) (nordstromMetricInv φ) x s s =
      (-(2 : ℝ) * (coordDeriv s (coordDeriv s φ) x * φ x - 2 * coordDeriv s φ x ^ 2) / φ x ^ 2
        - minkowskiMetric4 s s * (∑ ρ : Fin 4, minkowskiMetric4 ρ ρ *
          (coordDeriv ρ (coordDeriv ρ φ) x * φ x + coordDeriv ρ φ x ^ 2)) / φ x ^ 2) := by
  have nh : ∀ᶠ y in nhds x, ContDiffAt ℝ 2 φ y := hc2.eventually (by simp)
  have hne : ∀ᶠ y in nhds x, φ y ≠ 0 := hc2.continuousAt.eventually_ne hφ
  have hev : ∀ k i j,
      (fun y => christoffel (nordstromMetric φ) (nordstromMetricInv φ) y k i j)
        =ᶠ[nhds x] fun y => nordstromChristoffel φ y k i j := by
    intro k i j
    filter_upwards [nh, hne] with y hy hyne
    exact christoffel_nordstrom_eq φ y hyne (hy.differentiableAt (by norm_num)) k i j
  have hpt : ∀ k i j,
      christoffel (nordstromMetric φ) (nordstromMetricInv φ) x k i j
        = nordstromChristoffel φ x k i j :=
    fun k i j => christoffel_nordstrom_eq φ x hφ (hc2.differentiableAt (by norm_num)) k i j
  have hpd : ∀ μ k i j,
      coordDeriv μ (fun y => christoffel (nordstromMetric φ) (nordstromMetricInv φ) y k i j) x
        = coordDeriv μ (fun y => nordstromChristoffel φ y k i j) x :=
    fun μ k i j => coordDeriv_congr_nhds μ x (hev k i j)
  simp only [ricciTensorOf, riemann, hpd, hpt, Fin.sum_univ_four]
  simp only [pd_nordstromChristoffel φ x hφ hc2]
  simp only [nordstromChristoffel]
  fin_cases s
  all_goals simp only [minkowskiMetric4_apply]; norm_num
  all_goals field_simp [hφ]
  all_goals ring

/-- Exact 4D Einstein–Fokker scalar curvature identity `S = -6 □φ / φ³` for Nordström's
conformally flat metric `φ² η` computed through `GeneralRelativity.Pipeline`. -/
lemma ricciScalarOf_nordstrom (φ : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) (hφ : φ x ≠ 0)
    (hc2 : ContDiffAt ℝ 2 φ x) :
    ricciScalarOf (nordstromMetric φ) (nordstromMetricInv φ) x
      = -6 * boxEta φ x / φ x ^ 3 := by
  simp only [ricciScalarOf, Fin.sum_univ_four, nordstromMetricInv, conformalRescaleMetricInv,
    minkowskiMetric4_apply]
  norm_num
  simp only [ricciTensorOf_nordstrom_diag φ x hφ hc2, boxEta, Fin.sum_univ_four,
    minkowskiMetric4_apply]
  norm_num
  field_simp [hφ]
  ring

/-- Equivalence between the 4D Einstein–Fokker geometric equation `S = 24 π T` and Nordström's
scalar wave equation `□φ = -4 π φ³ T`. -/
lemma einsteinFokker_iff (φ : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) (hφ : φ x ≠ 0)
    (hc2 : ContDiffAt ℝ 2 φ x) (T : ℝ) :
    ricciScalarOf (nordstromMetric φ) (nordstromMetricInv φ) x = 24 * Real.pi * T
      ↔ boxEta φ x = -4 * Real.pi * φ x ^ 3 * T := by
  rw [ricciScalarOf_nordstrom φ x hφ hc2]
  have h3 : φ x ^ 3 ≠ 0 := pow_ne_zero 3 hφ
  constructor <;> intro h
  · field_simp [h3] at h; linarith
  · rw [h]; field_simp [h3]; ring

end Nordstrom

end Modified

end GeneralRelativity
