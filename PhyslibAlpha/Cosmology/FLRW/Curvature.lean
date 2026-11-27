/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Cosmology.FLRW.Christoffel
public import PhyslibAlpha.Relativity.Metrics.RiemannFromData
public import PhyslibAlpha.Relativity.Metrics.CoordinateMetric
public import PhyslibAlpha.Relativity.Tensors.EinsteinTensor
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!

# FLRW metric-level curvature

Ricci, scalar, and Einstein tensors of an FLRW spacetime from the coordinate metric.

## i. Overview

Contracting the closed-form FLRW Riemann tensor yields the diagonal Ricci components, the scalar
curvature `R = 6 (a''/a + (a'/a)² + k/a²)`, and the Einstein tensor directly from the metric.

## ii. Key results

- `FLRWSpacetime.riemann_eq_data` : coordinate Riemann tensor from the Christoffel data.
- `FLRWSpacetime.ricciTensor`, `FLRWSpacetime.ricciScalar`,
  `FLRWSpacetime.einsteinTensor` : chart-level curvature operators.

## iii. Table of contents

- A. Metric-level Ricci, scalar, and Einstein tensors

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 5 (Sec. 5.1). [ref: wald_1984_general_relativity]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 8
  (https://arxiv.org/pdf/gr-qc/9712019#page=216). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

namespace FLRW

namespace FLRWSpacetime

open CoordinateCurvature

/-!

## A. Metric-level Ricci, scalar, and Einstein tensors

Contracting the closed-form FLRW Riemann tensor yields the diagonal Ricci components, scalar
curvature `R = 6 (a''/a + (a'/a)² + k/a²)`, and Einstein tensor directly from the metric.

-/

private lemma ricci_00 (S : FLRWSpacetime) (x : Fin 4 → ℝ) (ha : S.a (x 0) ≠ 0)
    (hr : x 1 ≠ 0) (hkr : 1 - S.k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ S.a t)
    (ha2 : DifferentiableAt ℝ (deriv S.a) (x 0)) :
    CoordinateCurvature.ricciTensor S.metric S.metricInv x 0 0
      = -3 * deriv (deriv S.a) (x 0) / S.a (x 0) := by
  simp [CoordinateCurvature.ricciTensor, Fin.sum_univ_four,
    S.riemann_eq_data_raw x ha hr hkr hsin ha_diff ha2,
    riemannFromData, christoffel, christoffelDeriv]
  field_simp [ha]
  ring

private lemma ricci_11 (S : FLRWSpacetime) (x : Fin 4 → ℝ) (ha : S.a (x 0) ≠ 0)
    (hr : x 1 ≠ 0) (hkr : 1 - S.k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ S.a t)
    (ha2 : DifferentiableAt ℝ (deriv S.a) (x 0)) :
    CoordinateCurvature.ricciTensor S.metric S.metricInv x 1 1
      = (S.a (x 0) * deriv (deriv S.a) (x 0) + 2 * (deriv S.a (x 0)) ^ 2 + 2 * S.k)
          / (1 - S.k * (x 1) ^ 2) := by
  simp [CoordinateCurvature.ricciTensor, Fin.sum_univ_four,
    S.riemann_eq_data_raw x ha hr hkr hsin ha_diff ha2,
    riemannFromData, christoffel, christoffelDeriv]
  field_simp [ha, hr, hkr]
  ring

private lemma ricci_22 (S : FLRWSpacetime) (x : Fin 4 → ℝ) (ha : S.a (x 0) ≠ 0)
    (hr : x 1 ≠ 0) (hkr : 1 - S.k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ S.a t)
    (ha2 : DifferentiableAt ℝ (deriv S.a) (x 0)) :
    CoordinateCurvature.ricciTensor S.metric S.metricInv x 2 2
      = (S.a (x 0) * deriv (deriv S.a) (x 0) + 2 * (deriv S.a (x 0)) ^ 2 + 2 * S.k)
          * (x 1) ^ 2 := by
  have hkr' : 1 - (x 1) ^ 2 * S.k ≠ 0 := by rwa [mul_comm]
  simp [CoordinateCurvature.ricciTensor, Fin.sum_univ_four,
    S.riemann_eq_data_raw x ha hr hkr hsin ha_diff ha2,
    riemannFromData, christoffel, christoffelDeriv]
  field_simp [ha, hr, hkr, hkr', hsin]
  rw [Real.sin_sq (x 2)]
  ring

private lemma ricci_33 (S : FLRWSpacetime) (x : Fin 4 → ℝ) (ha : S.a (x 0) ≠ 0)
    (hr : x 1 ≠ 0) (hkr : 1 - S.k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ S.a t)
    (ha2 : DifferentiableAt ℝ (deriv S.a) (x 0)) :
    CoordinateCurvature.ricciTensor S.metric S.metricInv x 3 3
      = (S.a (x 0) * deriv (deriv S.a) (x 0) + 2 * (deriv S.a (x 0)) ^ 2 + 2 * S.k) * (x 1) ^ 2
          * Real.sin (x 2) ^ 2 := by
  have hkr' : 1 - (x 1) ^ 2 * S.k ≠ 0 := by rwa [mul_comm]
  simp [CoordinateCurvature.ricciTensor, Fin.sum_univ_four,
    S.riemann_eq_data_raw x ha hr hkr hsin ha_diff ha2,
    riemannFromData, christoffel, christoffelDeriv]
  field_simp [ha, hr, hkr, hkr', hsin]
  ring

private lemma ricci_offdiag (S : FLRWSpacetime) (x : Fin 4 → ℝ) (ha : S.a (x 0) ≠ 0)
    (hr : x 1 ≠ 0) (hkr : 1 - S.k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ S.a t)
    (ha2 : DifferentiableAt ℝ (deriv S.a) (x 0)) {σ ν : Fin 4} (h : σ ≠ ν) :
    CoordinateCurvature.ricciTensor S.metric S.metricInv x σ ν = 0 := by
  fin_cases σ <;> fin_cases ν <;> try exact absurd rfl h
  all_goals
    simp [CoordinateCurvature.ricciTensor, Fin.sum_univ_four,
      S.riemann_eq_data_raw x ha hr hkr hsin ha_diff ha2,
      riemannFromData, christoffel, christoffelDeriv]
  all_goals ring

/-- Complete coordinate Ricci tensor of an FLRW spacetime. -/
private lemma ricciTensor_raw (S : FLRWSpacetime) (x : Fin 4 → ℝ) (ha : S.a (x 0) ≠ 0)
    (hr : x 1 ≠ 0) (hkr : 1 - S.k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ S.a t)
    (ha2 : DifferentiableAt ℝ (deriv S.a) (x 0)) (σ ν : Fin 4) :
    CoordinateCurvature.ricciTensor S.metric S.metricInv x σ ν
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
private lemma ricciScalar_raw (S : FLRWSpacetime) (x : Fin 4 → ℝ) (ha : S.a (x 0) ≠ 0)
    (hr : x 1 ≠ 0) (hkr : 1 - S.k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ S.a t)
    (ha2 : DifferentiableAt ℝ (deriv S.a) (x 0)) :
    CoordinateCurvature.ricciScalar S.metric S.metricInv x
      = 6 * (deriv (deriv S.a) (x 0) / S.a (x 0) + (deriv S.a (x 0) / S.a (x 0)) ^ 2
          + S.k / (S.a (x 0)) ^ 2) := by
  simp only [CoordinateCurvature.ricciScalar, S.ricciTensor_raw x ha hr hkr hsin ha_diff ha2]
  simp only [Fin.sum_univ_four, metricInv, Matrix.of_apply, Fin.reduceEq, ↓reduceIte,
    Fin.isValue, mul_zero, add_zero, zero_add]
  field_simp [ha, hr, hkr, hsin]
  ring

/-- Complete FLRW Einstein tensor: `G_{00} = 3 ((a'/a)² + k/a²)` and
`G_{ii} = -(2 a''/a + (a'/a)² + k/a²) g_{ii}` for spatial indices `i = 1, 2, 3`. -/
private lemma einsteinTensor_raw (S : FLRWSpacetime) (x : Fin 4 → ℝ) (ha : S.a (x 0) ≠ 0)
    (hr : x 1 ≠ 0) (hkr : 1 - S.k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ S.a t)
    (ha2 : DifferentiableAt ℝ (deriv S.a) (x 0)) (i j : Fin 4) :
    CoordinateCurvature.einsteinTensor S.metric S.metricInv x i j
      = if i = j then
          if i = 0 then 3 * ((deriv S.a (x 0) / S.a (x 0)) ^ 2 + S.k / (S.a (x 0)) ^ 2)
          else -(2 * (deriv (deriv S.a) (x 0) / S.a (x 0))
            + (deriv S.a (x 0) / S.a (x 0)) ^ 2 + S.k / (S.a (x 0)) ^ 2) * S.metric x i j
        else 0 := by
  simp only [CoordinateCurvature.einsteinTensor, S.ricciTensor_raw x ha hr hkr hsin ha_diff ha2,
    S.ricciScalar_raw x ha hr hkr hsin ha_diff ha2, metric]
  fin_cases i <;> fin_cases j <;> simp
  · field_simp [ha]; ring
  · field_simp [ha, hkr]; ring
  · field_simp [ha]; ring
  · field_simp [ha]; ring

/-- The FLRW coordinate Riemann tensor agrees with
`riemannFromData S.christoffel S.christoffelDeriv`. -/
lemma riemann_eq_data (S : FLRWSpacetime) (x : Fin 4 → ℝ) (ha : S.a (x 0) ≠ 0)
    (hr : x 1 ≠ 0) (hkr : 1 - S.k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ S.a t)
    (ha2 : DifferentiableAt ℝ (deriv S.a) (x 0)) (ρ σ μ ν : Fin 4) :
    S.toCoordinateMetric.riemann x ρ σ μ ν
      = riemannFromData S.christoffel S.christoffelDeriv x ρ σ μ ν := by
  simp only [CoordinateMetric.riemann_apply, S.toCoordinateMetric_g,
    S.toCoordinateMetric_ginv]
  exact S.riemann_eq_data_raw x ha hr hkr hsin ha_diff ha2 ρ σ μ ν

/-- The FLRW Ricci tensor, stated with the chart-level `CoordinateMetric` operator. -/
lemma ricciTensor (S : FLRWSpacetime) (x : Fin 4 → ℝ) (ha : S.a (x 0) ≠ 0)
    (hr : x 1 ≠ 0) (hkr : 1 - S.k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ S.a t)
    (ha2 : DifferentiableAt ℝ (deriv S.a) (x 0)) (σ ν : Fin 4) :
    S.toCoordinateMetric.ricciTensor x σ ν
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
  simp only [CoordinateMetric.ricciTensor_apply, S.toCoordinateMetric_g,
    S.toCoordinateMetric_ginv]
  exact S.ricciTensor_raw x ha hr hkr hsin ha_diff ha2 σ ν

/-- FLRW scalar curvature, stated with the chart-level `CoordinateMetric` operator. -/
lemma ricciScalar (S : FLRWSpacetime) (x : Fin 4 → ℝ) (ha : S.a (x 0) ≠ 0)
    (hr : x 1 ≠ 0) (hkr : 1 - S.k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ S.a t)
    (ha2 : DifferentiableAt ℝ (deriv S.a) (x 0)) :
    S.toCoordinateMetric.ricciScalar x
      = 6 * (deriv (deriv S.a) (x 0) / S.a (x 0) + (deriv S.a (x 0) / S.a (x 0)) ^ 2
          + S.k / (S.a (x 0)) ^ 2) := by
  simp only [CoordinateMetric.ricciScalar_apply, S.toCoordinateMetric_g,
    S.toCoordinateMetric_ginv]
  exact S.ricciScalar_raw x ha hr hkr hsin ha_diff ha2

/-- The FLRW Einstein tensor, stated with the chart-level `CoordinateMetric` operator. -/
lemma einsteinTensor (S : FLRWSpacetime) (x : Fin 4 → ℝ) (ha : S.a (x 0) ≠ 0)
    (hr : x 1 ≠ 0) (hkr : 1 - S.k * (x 1) ^ 2 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ S.a t)
    (ha2 : DifferentiableAt ℝ (deriv S.a) (x 0)) (i j : Fin 4) :
    S.toCoordinateMetric.einsteinTensor x i j
      = if i = j then
          if i = 0 then 3 * ((deriv S.a (x 0) / S.a (x 0)) ^ 2 + S.k / (S.a (x 0)) ^ 2)
          else -(2 * (deriv (deriv S.a) (x 0) / S.a (x 0))
            + (deriv S.a (x 0) / S.a (x 0)) ^ 2 + S.k / (S.a (x 0)) ^ 2) * S.metric x i j
        else 0 := by
  simp only [CoordinateMetric.einsteinTensor_apply, S.toCoordinateMetric_g,
    S.toCoordinateMetric_ginv]
  exact S.einsteinTensor_raw x ha hr hkr hsin ha_diff ha2 i j

end FLRWSpacetime

end FLRW

end GeneralRelativity
