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
differential pipeline by specializing `SchwarzschildDeSitterSpacetime` to `Λ = 0`.

## i. Overview

Specializing `S.toDeSitter` (`⟨S.M, 0⟩ : SchwarzschildDeSitterSpacetime`) to `Λ = 0` matches
`S.metric` and `S.metricInv`, recovering all six independent Riemann components, Ricci flatness
`Ric = 0`, vanishing scalar curvature `R = 0`, and vacuum Einstein equations `G = 0`.

## ii. Key results

- `SchwarzschildSpacetime.toDeSitter` : Schwarzschild–de Sitter embedding at `Λ = 0`.
- `SchwarzschildSpacetime.toDeSitter_metric`, `SchwarzschildSpacetime.toDeSitter_metricInv` :
  reduction from `toDeSitter` at `Λ = 0`.
- `SchwarzschildSpacetime.riemann_components` : all six independent Schwarzschild Riemann
  components.
- `SchwarzschildSpacetime.ricciTensorOf`, `SchwarzschildSpacetime.ricciScalarOf`,
  `SchwarzschildSpacetime.einsteinTensorOf` : pipeline vacuum solution theorems.

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

namespace SchwarzschildSpacetime

/-!

## A. Schwarzschild pipeline specialization at `Λ = 0`

-/

/-- Embed a Schwarzschild spacetime into `SchwarzschildDeSitterSpacetime` at `Λ = 0`. -/
def toDeSitter (S : SchwarzschildSpacetime) : SchwarzschildDeSitterSpacetime :=
  ⟨S.M, 0⟩

/-- At `Λ = 0`, `S.toDeSitter.metric` reduces to `S.metric`. -/
lemma toDeSitter_metric (S : SchwarzschildSpacetime) : S.toDeSitter.metric = S.metric := by
  funext x i j
  simp [SchwarzschildDeSitterSpacetime.metric, SchwarzschildDeSitterSpacetime.toStaticSpherical,
    StaticSpherical.StaticSphericalMetric.metric, metric, toStaticSpherical,
    SchwarzschildDeSitterSpacetime.lapse, lapse, toDeSitter]

/-- At `Λ = 0`, `S.toDeSitter.metricInv` reduces to `S.metricInv`. -/
lemma toDeSitter_metricInv (S : SchwarzschildSpacetime) :
    S.toDeSitter.metricInv = S.metricInv := by
  funext x i j
  simp [SchwarzschildDeSitterSpacetime.metricInv, SchwarzschildDeSitterSpacetime.toStaticSpherical,
    StaticSpherical.StaticSphericalMetric.metricInv, metricInv, toStaticSpherical,
    SchwarzschildDeSitterSpacetime.lapse, lapse, toDeSitter]

/-- All six independent Schwarzschild Riemann components directly from the metric pipeline,
specialised from `SchwarzschildDeSitterSpacetime.riemann_components_pipeline` at `Λ = 0`. -/
lemma riemann_components (S : SchwarzschildSpacetime) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.lapse (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) :
    (Pipeline.riemann S.metric S.metricInv x 0 1 0 1
        = 2 * S.M / ((x 1) ^ 3 * S.lapse (x 1)))
      ∧ (Pipeline.riemann S.metric S.metricInv x 0 2 0 2 = -S.M / (x 1))
      ∧ (Pipeline.riemann S.metric S.metricInv x 0 3 0 3
          = -(S.M / (x 1)) * Real.sin (x 2) ^ 2)
      ∧ (Pipeline.riemann S.metric S.metricInv x 1 2 1 2 = -S.M / (x 1))
      ∧ (Pipeline.riemann S.metric S.metricInv x 1 3 1 3
          = -(S.M / (x 1)) * Real.sin (x 2) ^ 2)
      ∧ (Pipeline.riemann S.metric S.metricInv x 2 3 2 3
          = (2 * S.M / (x 1)) * Real.sin (x 2) ^ 2) := by
  have h0 : S.toDeSitter.lapse (x 1) = S.lapse (x 1) := by
    simpa [toDeSitter] using SchwarzschildDeSitterSpacetime.lapse_zero_lambda S.M (x 1)
  have hf0 : S.toDeSitter.lapse (x 1) ≠ 0 := by rwa [h0]
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := S.toDeSitter.riemann_components_pipeline x hr hf0 hsin
  rw [S.toDeSitter_metric, S.toDeSitter_metricInv] at c1 c2 c3 c4 c5 c6
  rw [h0] at c1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [c1]
    change (2 * S.M / x 1 ^ 3 + 0 / 3) / S.lapse (x 1) = 2 * S.M / (x 1 ^ 3 * S.lapse (x 1))
    field_simp [hr, hf]
    ring
  · rw [c2]
    change (0 : ℝ) * x 1 ^ 2 / 3 - S.M / x 1 = -S.M / x 1
    ring
  · simpa [toDeSitter] using c3
  · rw [c4]
    change (0 : ℝ) * x 1 ^ 2 / 3 - S.M / x 1 = -S.M / x 1
    ring
  · simpa [toDeSitter] using c5
  · simpa [toDeSitter] using c6

/-- Metric-level Ricci flatness for Schwarzschild: `Ric = 0` directly from `S.metric` and
`S.metricInv`. -/
lemma ricciTensorOf (S : SchwarzschildSpacetime) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.lapse (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) (σ ν : Fin 4) :
    Pipeline.ricciTensorOf S.metric S.metricInv x σ ν = 0 := by
  have hf0 : S.toDeSitter.lapse (x 1) ≠ 0 := by
    rw [show S.toDeSitter.lapse (x 1) = S.lapse (x 1) from by
      simpa [toDeSitter] using SchwarzschildDeSitterSpacetime.lapse_zero_lambda S.M (x 1)]
    exact hf
  have h := S.toDeSitter.ricciTensorOf x hr hf0 hsin σ ν
  rw [S.toDeSitter_metric, S.toDeSitter_metricInv] at h
  simpa [toDeSitter] using h

/-- Metric-level vanishing scalar curvature for Schwarzschild: `R = 0`. -/
lemma ricciScalarOf (S : SchwarzschildSpacetime) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.lapse (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) :
    Pipeline.ricciScalarOf S.metric S.metricInv x = 0 := by
  have hf0 : S.toDeSitter.lapse (x 1) ≠ 0 := by
    rw [show S.toDeSitter.lapse (x 1) = S.lapse (x 1) from by
      simpa [toDeSitter] using SchwarzschildDeSitterSpacetime.lapse_zero_lambda S.M (x 1)]
    exact hf
  have h := S.toDeSitter.ricciScalarOf x hr hf0 hsin
  rw [S.toDeSitter_metric, S.toDeSitter_metricInv] at h
  simpa [toDeSitter] using h

/-- Metric-level vacuum Einstein equation for Schwarzschild: `G_{ij} = 0` directly from
`g = diag(-f, 1/f, r², r² sin²θ)`. -/
lemma einsteinTensorOf (S : SchwarzschildSpacetime) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.lapse (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) (i j : Fin 4) :
    Pipeline.einsteinTensorOf S.metric S.metricInv x i j = 0 := by
  have hf0 : S.toDeSitter.lapse (x 1) ≠ 0 := by
    rw [show S.toDeSitter.lapse (x 1) = S.lapse (x 1) from by
      simpa [toDeSitter] using SchwarzschildDeSitterSpacetime.lapse_zero_lambda S.M (x 1)]
    exact hf
  have h := S.toDeSitter.einsteinTensorOf x hr hf0 hsin i j
  rw [S.toDeSitter_metric, S.toDeSitter_metricInv] at h
  simpa [toDeSitter] using h

end SchwarzschildSpacetime

end Schwarzschild

end GeneralRelativity
