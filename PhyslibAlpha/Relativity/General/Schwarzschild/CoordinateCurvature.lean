/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.General.SchwarzschildDeSitter.CoordinateCurvature
public import PhyslibAlpha.Relativity.General.SchwarzschildDeSitter.Embedding
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!

# Schwarzschild curvature from the coordinate metric

Vacuum Schwarzschild Riemann, Ricci, scalar, and Einstein tensors obtained from the coordinate
metric by specializing `SchwarzschildDeSitterSpacetime` to `Λ = 0`.

## i. Overview

The embedding `S.toDeSitter` (`⟨S.M, 0⟩ : SchwarzschildDeSitterSpacetime`, defined in
`SchwarzschildDeSitter/Basic.lean` with its `Λ = 0` reductions) matches `S.metric` and
`S.metricInv`, recovering all six independent Riemann components, Ricci flatness `Ric = 0`,
vanishing scalar curvature `R = 0`, and vacuum Einstein equations `G = 0`.

## ii. Key results

- `SchwarzschildSpacetime.riemann_components_from_coordinateMetric` : all six independent
  Schwarzschild Riemann components computed from the coordinate metric.
- `SchwarzschildSpacetime.ricciTensor_eq_zero`, `SchwarzschildSpacetime.ricciScalar_eq_zero`,
  `SchwarzschildSpacetime.einsteinTensor_eq_zero` : vacuum Einstein solution theorems.

## iii. Table of contents

- A. Schwarzschild specialization at `Λ = 0`

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

open GeneralRelativity.CoordinateCurvature GeneralRelativity.SchwarzschildDeSitter

namespace SchwarzschildSpacetime

/-!

## A. Schwarzschild specialization at `Λ = 0`

Because a Schwarzschild black hole is the zero-cosmological-constant limit of Schwarzschild–de
Sitter spacetime, its coordinate Riemann, Ricci, scalar, and Einstein tensors follow by evaluating
at `Λ = 0`.

-/

/-- All six independent Schwarzschild Riemann components computed from the coordinate metric,
specialized from `SchwarzschildDeSitterSpacetime.riemann_components_from_metric` at `Λ = 0`. -/
lemma riemann_components_from_coordinateMetric (S : SchwarzschildSpacetime)
    (p : S.toStaticSpherical.RegularPoint) :
    (S.toCoordinateMetric.riemann p.x 0 1 0 1
        = 2 * S.M / ((p.x 1) ^ 3 * S.metricFn (p.x 1)))
      ∧ (S.toCoordinateMetric.riemann p.x 0 2 0 2 = -S.M / (p.x 1))
      ∧ (S.toCoordinateMetric.riemann p.x 0 3 0 3
          = -(S.M / (p.x 1)) * Real.sin (p.x 2) ^ 2)
      ∧ (S.toCoordinateMetric.riemann p.x 1 2 1 2 = -S.M / (p.x 1))
      ∧ (S.toCoordinateMetric.riemann p.x 1 3 1 3
          = -(S.M / (p.x 1)) * Real.sin (p.x 2) ^ 2)
      ∧ (S.toCoordinateMetric.riemann p.x 2 3 2 3
          = (2 * S.M / (p.x 1)) * Real.sin (p.x 2) ^ 2) := by
  simp only [CoordinateMetric.riemann_apply, S.toCoordinateMetric_g, S.toCoordinateMetric_ginv]
  have hf0 : S.toDeSitter.toStaticSpherical.metricFn (p.x 1) ≠ 0 := by simpa using p.hf
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ :=
    S.toDeSitter.riemann_components_from_metric ⟨p.x, p.hr, hf0, p.hsin⟩
  simp only [CoordinateMetric.riemann_apply, S.toDeSitter.toCoordinateMetric_g,
    S.toDeSitter.toCoordinateMetric_ginv] at c1 c2 c3 c4 c5 c6
  rw [S.toDeSitter_metric, S.toDeSitter_metricInv] at c1 c2 c3 c4 c5 c6
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [toDeSitter_M, toDeSitter_Λ, toDeSitter_metricFn, zero_div, add_zero] at c1
    rw [c1]
    field_simp [p.hr, p.hf]
  · simpa [neg_div] using c2
  · simpa using c3
  · simpa [neg_div] using c4
  · simpa using c5
  · simpa using c6

/-- Metric-level Ricci flatness for Schwarzschild: `Ric = 0` directly from `S.metric` and
`S.metricInv`. -/
lemma ricciTensor_eq_zero (S : SchwarzschildSpacetime)
    (p : S.toStaticSpherical.RegularPoint) (σ ν : Fin 4) :
    S.toCoordinateMetric.ricciTensor p.x σ ν = 0 := by
  simp only [CoordinateMetric.ricciTensor_apply, S.toCoordinateMetric_g, S.toCoordinateMetric_ginv]
  have hf0 : S.toDeSitter.toStaticSpherical.metricFn (p.x 1) ≠ 0 := by simpa using p.hf
  have h := S.toDeSitter.ricciTensor_eq ⟨p.x, p.hr, hf0, p.hsin⟩ σ ν
  simp only [CoordinateMetric.ricciTensor_apply, S.toDeSitter.toCoordinateMetric_g,
    S.toDeSitter.toCoordinateMetric_ginv] at h
  rw [S.toDeSitter_metric, S.toDeSitter_metricInv] at h
  simpa using h

/-- Metric-level vanishing scalar curvature for Schwarzschild: `R = 0`. -/
lemma ricciScalar_eq_zero (S : SchwarzschildSpacetime) (p : S.toStaticSpherical.RegularPoint) :
    S.toCoordinateMetric.ricciScalar p.x = 0 := by
  simp only [CoordinateMetric.ricciScalar_apply, S.toCoordinateMetric_g, S.toCoordinateMetric_ginv]
  have hf0 : S.toDeSitter.toStaticSpherical.metricFn (p.x 1) ≠ 0 := by simpa using p.hf
  have h := S.toDeSitter.ricciScalar_eq ⟨p.x, p.hr, hf0, p.hsin⟩
  simp only [CoordinateMetric.ricciScalar_apply, S.toDeSitter.toCoordinateMetric_g,
    S.toDeSitter.toCoordinateMetric_ginv] at h
  rw [S.toDeSitter_metric, S.toDeSitter_metricInv] at h
  simpa using h

/-- Metric-level vacuum Einstein equation for Schwarzschild: `G_{ij} = 0` directly from
`g = diag(-f, 1/f, r², r² sin²θ)`. -/
lemma einsteinTensor_eq_zero (S : SchwarzschildSpacetime)
    (p : S.toStaticSpherical.RegularPoint) (i j : Fin 4) :
    S.toCoordinateMetric.einsteinTensor p.x i j = 0 := by
  simp only [CoordinateMetric.einsteinTensor_apply, S.toCoordinateMetric_g,
    S.toCoordinateMetric_ginv]
  have hf0 : S.toDeSitter.toStaticSpherical.metricFn (p.x 1) ≠ 0 := by simpa using p.hf
  have h := S.toDeSitter.einsteinTensor_eq ⟨p.x, p.hr, hf0, p.hsin⟩ i j
  simp only [CoordinateMetric.einsteinTensor_apply, S.toDeSitter.toCoordinateMetric_g,
    S.toDeSitter.toCoordinateMetric_ginv] at h
  rw [S.toDeSitter_metric, S.toDeSitter_metricInv] at h
  simpa using h

end SchwarzschildSpacetime

end Schwarzschild

end GeneralRelativity
