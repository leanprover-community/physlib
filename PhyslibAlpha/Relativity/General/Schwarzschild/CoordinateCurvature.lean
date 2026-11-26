/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.General.SchwarzschildDeSitter.CoordinateCurvature
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!

# Schwarzschild curvature through the coordinate pipeline

Vacuum Schwarzschild Riemann, Ricci, scalar, and Einstein tensors obtained from the coordinate
differential pipeline by specializing Schwarzschild–de Sitter to `Λ = 0`.

## i. Overview

Specializing `sdsMetric M 0` and `sdsMetricInv M 0` to `Λ = 0` yields the Schwarzschild metric
field `schwarzschildMetricField` and inverse `schwarzschildMetricInv`, recovering all six
independent Riemann components, Ricci flatness `Ric = 0`, vanishing scalar curvature `S = 0`, and
vacuum Einstein equations `G = 0`.

## ii. Key results

- `schwarzschildMetricField`, `schwarzschildMetricInv` : Schwarzschild coordinate metric and
  inverse fields.
- `sdsMetric_zero_lambda`, `sdsMetricInv_zero_lambda` : reduction from `sdsMetric` at `Λ = 0`.
- `riemann_schwarzschild_components` : all six independent Schwarzschild Riemann components.
- `ricciTensorOf_schwarzschild`, `ricciScalarOf_schwarzschild`, `einsteinTensorOf_schwarzschild` :
  pipeline
  vacuum solution theorems.

## iii. Table of contents

- A. Schwarzschild pipeline specialization at `Λ = 0`

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 6 (Sec. 6.1-6.2). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 23 & Ch. 31.
  [ref: mtw_1973_gravitation]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 7
  (https://arxiv.org/pdf/gr-qc/9712019#page=168). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

namespace Schwarzschild

open GeneralRelativity.Pipeline GeneralRelativity.SchwarzschildDeSitter

/-!

## A. Schwarzschild pipeline specialization at `Λ = 0`

-/

/-- The Schwarzschild metric as a coordinate spacetime field `(Fin 4 → ℝ) → Tensor2 4` for the
differential curvature pipeline, wrapping `Schwarzschild.schwarzschildMetric` over `ℝ⁴`. -/
noncomputable def schwarzschildMetricField (M : ℝ) : (Fin 4 → ℝ) → Tensor2 4 :=
  fun x => Schwarzschild.schwarzschildMetric M x

/-- The inverse Schwarzschild metric as a coordinate spacetime field `(Fin 4 → ℝ) → Tensor2 4` for
the differential curvature pipeline. -/
noncomputable def schwarzschildMetricInv (M : ℝ) : (Fin 4 → ℝ) → Tensor2 4 :=
  StaticSpherical.StaticSphericalMetric.metricInv ⟨Schwarzschild.schwarzschildLapse M⟩

/-- At `Λ = 0`, `sdsMetric` reduces to `schwarzschildMetricField`. -/
lemma sdsMetric_zero_lambda (M : ℝ) : sdsMetric M 0 = schwarzschildMetricField M := by
  funext x i j
  simp [sdsMetric, StaticSpherical.StaticSphericalMetric.metric, schwarzschildMetricField,
    Schwarzschild.schwarzschildMetric, sdsLapse, Schwarzschild.schwarzschildLapse]

/-- At `Λ = 0`, `sdsMetricInv` reduces to `schwarzschildMetricInv`. -/
lemma sdsMetricInv_zero_lambda (M : ℝ) : sdsMetricInv M 0 = schwarzschildMetricInv M := by
  funext x i j
  simp [sdsMetricInv, StaticSpherical.StaticSphericalMetric.metricInv, schwarzschildMetricInv,
    sdsLapse, Schwarzschild.schwarzschildLapse]

/-- All six independent Schwarzschild Riemann components directly from the metric pipeline,
specialised from `riemann_sds_components` at `Λ = 0`. -/
lemma riemann_schwarzschild_components (M : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : Schwarzschild.schwarzschildLapse M (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) :
    (riemann (schwarzschildMetricField M) (schwarzschildMetricInv M) x 0 1 0 1
        = 2 * M / ((x 1) ^ 3 * Schwarzschild.schwarzschildLapse M (x 1)))
      ∧ (riemann (schwarzschildMetricField M) (schwarzschildMetricInv M) x 0 2 0 2 = -M / (x 1))
      ∧ (riemann (schwarzschildMetricField M) (schwarzschildMetricInv M) x 0 3 0 3
          = -(M / (x 1)) * Real.sin (x 2) ^ 2)
      ∧ (riemann (schwarzschildMetricField M) (schwarzschildMetricInv M) x 1 2 1 2 = -M / (x 1))
      ∧ (riemann (schwarzschildMetricField M) (schwarzschildMetricInv M) x 1 3 1 3
          = -(M / (x 1)) * Real.sin (x 2) ^ 2)
      ∧ (riemann (schwarzschildMetricField M) (schwarzschildMetricInv M) x 2 3 2 3
          = (2 * M / (x 1)) * Real.sin (x 2) ^ 2) := by
  have hf0 : sdsLapse M 0 (x 1) ≠ 0 := by
    rwa [sdsLapse_zero_lambda]
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := riemann_sds_components M 0 x hr hf0 hsin
  rw [sdsMetric_zero_lambda, sdsMetricInv_zero_lambda] at c1 c2 c3 c4 c5 c6
  rw [sdsLapse_zero_lambda] at c1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [c1]
    field_simp [hr, hf]
    ring
  · rw [c2]
    ring
  · simpa using c3
  · rw [c4]
    ring
  · simpa using c5
  · simpa using c6

/-- Metric-level Ricci flatness for Schwarzschild: `Ric = 0` directly from
`schwarzschildMetricField` and `schwarzschildMetricInv`. -/
lemma ricciTensorOf_schwarzschild (M : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : Schwarzschild.schwarzschildLapse M (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (σ ν : Fin 4) :
    ricciTensorOf (schwarzschildMetricField M) (schwarzschildMetricInv M) x σ ν = 0 := by
  have hf0 : sdsLapse M 0 (x 1) ≠ 0 := by
    rwa [sdsLapse_zero_lambda]
  have h := ricciTensorOf_sds M 0 x hr hf0 hsin σ ν
  rw [sdsMetric_zero_lambda, sdsMetricInv_zero_lambda] at h
  simpa using h

/-- Metric-level vanishing scalar curvature for Schwarzschild: `S = 0`. -/
lemma ricciScalarOf_schwarzschild (M : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : Schwarzschild.schwarzschildLapse M (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) :
    ricciScalarOf (schwarzschildMetricField M) (schwarzschildMetricInv M) x = 0 := by
  have hf0 : sdsLapse M 0 (x 1) ≠ 0 := by
    rwa [sdsLapse_zero_lambda]
  have h := ricciScalarOf_sds M 0 x hr hf0 hsin
  rw [sdsMetric_zero_lambda, sdsMetricInv_zero_lambda] at h
  simpa using h

/-- Metric-level vacuum Einstein equation for Schwarzschild: `G_{ij} = 0` directly from
`g = diag(-f, 1/f, r², r² sin²θ)`. -/
lemma einsteinTensorOf_schwarzschild (M : ℝ) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : Schwarzschild.schwarzschildLapse M (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (i j : Fin 4) :
    einsteinTensorOf (schwarzschildMetricField M) (schwarzschildMetricInv M) x i j = 0 := by
  have hf0 : sdsLapse M 0 (x 1) ≠ 0 := by
    rwa [sdsLapse_zero_lambda]
  have h := einsteinTensorOf_sds M 0 x hr hf0 hsin i j
  rw [sdsMetric_zero_lambda, sdsMetricInv_zero_lambda] at h
  simpa using h

end Schwarzschild

end GeneralRelativity
