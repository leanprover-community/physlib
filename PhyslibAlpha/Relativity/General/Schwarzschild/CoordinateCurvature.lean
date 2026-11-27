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

# Schwarzschild curvature from the coordinate metric

Vacuum Schwarzschild Riemann, Ricci, scalar, and Einstein tensors obtained from the coordinate
metric by specializing `SchwarzschildDeSitterSpacetime` to `Λ = 0`.

## i. Overview

Specializing `S.toDeSitter` (`⟨S.M, 0⟩ : SchwarzschildDeSitterSpacetime`) to `Λ = 0` matches
`S.metric` and `S.metricInv`, recovering all six independent Riemann components, Ricci flatness
`Ric = 0`, vanishing scalar curvature `R = 0`, and vacuum Einstein equations `G = 0`.

## ii. Key results

- `SchwarzschildSpacetime.toDeSitter` : Schwarzschild–de Sitter embedding at `Λ = 0`.
- `SchwarzschildSpacetime.toDeSitter_M`, `SchwarzschildSpacetime.toDeSitter_Λ`,
  `SchwarzschildSpacetime.toDeSitter_metricFn`, `SchwarzschildSpacetime.toDeSitter_metric`,
  `SchwarzschildSpacetime.toDeSitter_metricInv` : reduction from `toDeSitter` at `Λ = 0`.
- `SchwarzschildSpacetime.riemann_components` : all six independent Schwarzschild Riemann
  components.
- `SchwarzschildSpacetime.ricciTensor`, `SchwarzschildSpacetime.ricciScalar`,
  `SchwarzschildSpacetime.einsteinTensor` : vacuum Einstein solution theorems.

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

/-- Embed a Schwarzschild spacetime into `SchwarzschildDeSitterSpacetime` at `Λ = 0`. -/
def toDeSitter (S : SchwarzschildSpacetime) : SchwarzschildDeSitterSpacetime :=
  ⟨S.M, 0⟩

/-- Mass parameter of `S.toDeSitter` equals `S.M`. -/
@[simp]
lemma toDeSitter_M (S : SchwarzschildSpacetime) : S.toDeSitter.M = S.M := rfl

/-- Cosmological constant of `S.toDeSitter` vanishes. -/
@[simp]
lemma toDeSitter_Λ (S : SchwarzschildSpacetime) : S.toDeSitter.Λ = 0 := rfl

/-- At `Λ = 0`, `S.toDeSitter.metricFn` agrees pointwise with `S.metricFn`. -/
@[simp]
lemma toDeSitter_metricFn (S : SchwarzschildSpacetime) (r : ℝ) :
    S.toDeSitter.metricFn r = S.metricFn r :=
  SchwarzschildDeSitterSpacetime.metricFn_zero_lambda S.M r

/-- At `Λ = 0`, `S.toDeSitter.metric` reduces to `S.metric`. -/
lemma toDeSitter_metric (S : SchwarzschildSpacetime) : S.toDeSitter.metric = S.metric := by
  ext x i j
  simp [SchwarzschildDeSitterSpacetime.metric, SchwarzschildDeSitterSpacetime.toStaticSpherical,
    StaticSpherical.StaticSphericalMetric.metric, metric, toStaticSpherical]

/-- At `Λ = 0`, `S.toDeSitter.metricInv` reduces to `S.metricInv`. -/
lemma toDeSitter_metricInv (S : SchwarzschildSpacetime) :
    S.toDeSitter.metricInv = S.metricInv := by
  ext x i j
  simp [SchwarzschildDeSitterSpacetime.metricInv, SchwarzschildDeSitterSpacetime.toStaticSpherical,
    StaticSpherical.StaticSphericalMetric.metricInv, metricInv, toStaticSpherical]

/-- All six independent Schwarzschild Riemann components computed from the coordinate metric,
specialized from `SchwarzschildDeSitterSpacetime.riemann_components_from_metric` at `Λ = 0`. -/
lemma riemann_components_from_metric (S : SchwarzschildSpacetime) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.metricFn (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) :
    (CoordinateCurvature.riemann S.metric S.metricInv x 0 1 0 1
        = 2 * S.M / ((x 1) ^ 3 * S.metricFn (x 1)))
      ∧ (CoordinateCurvature.riemann S.metric S.metricInv x 0 2 0 2 = -S.M / (x 1))
      ∧ (CoordinateCurvature.riemann S.metric S.metricInv x 0 3 0 3
          = -(S.M / (x 1)) * Real.sin (x 2) ^ 2)
      ∧ (CoordinateCurvature.riemann S.metric S.metricInv x 1 2 1 2 = -S.M / (x 1))
      ∧ (CoordinateCurvature.riemann S.metric S.metricInv x 1 3 1 3
          = -(S.M / (x 1)) * Real.sin (x 2) ^ 2)
      ∧ (CoordinateCurvature.riemann S.metric S.metricInv x 2 3 2 3
          = (2 * S.M / (x 1)) * Real.sin (x 2) ^ 2) := by
  have hf0 : S.toDeSitter.metricFn (x 1) ≠ 0 := by simp [hf]
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := S.toDeSitter.riemann_components_from_metric x hr hf0 hsin
  rw [S.toDeSitter_metric, S.toDeSitter_metricInv] at c1 c2 c3 c4 c5 c6
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [toDeSitter_M, toDeSitter_Λ, toDeSitter_metricFn, zero_div, add_zero] at c1
    rw [c1]
    field_simp [hr, hf]
  · simpa [neg_div] using c2
  · simpa using c3
  · simpa [neg_div] using c4
  · simpa using c5
  · simpa using c6

/-- Metric-level Ricci flatness for Schwarzschild: `Ric = 0` directly from `S.metric` and
`S.metricInv`. -/
lemma ricciTensor (S : SchwarzschildSpacetime) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.metricFn (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) (σ ν : Fin 4) :
    CoordinateCurvature.ricciTensor S.metric S.metricInv x σ ν = 0 := by
  have hf0 : S.toDeSitter.metricFn (x 1) ≠ 0 := by simp [hf]
  have h := S.toDeSitter.ricciTensor x hr hf0 hsin σ ν
  rw [S.toDeSitter_metric, S.toDeSitter_metricInv] at h
  simpa using h

/-- Metric-level vanishing scalar curvature for Schwarzschild: `R = 0`. -/
lemma ricciScalar (S : SchwarzschildSpacetime) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.metricFn (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) :
    CoordinateCurvature.ricciScalar S.metric S.metricInv x = 0 := by
  have hf0 : S.toDeSitter.metricFn (x 1) ≠ 0 := by simp [hf]
  have h := S.toDeSitter.ricciScalar x hr hf0 hsin
  rw [S.toDeSitter_metric, S.toDeSitter_metricInv] at h
  simpa using h

/-- Metric-level vacuum Einstein equation for Schwarzschild: `G_{ij} = 0` directly from
`g = diag(-f, 1/f, r², r² sin²θ)`. -/
lemma einsteinTensor (S : SchwarzschildSpacetime) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.metricFn (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0) (i j : Fin 4) :
    CoordinateCurvature.einsteinTensor S.metric S.metricInv x i j = 0 := by
  have hf0 : S.toDeSitter.metricFn (x 1) ≠ 0 := by simp [hf]
  have h := S.toDeSitter.einsteinTensor x hr hf0 hsin i j
  rw [S.toDeSitter_metric, S.toDeSitter_metricInv] at h
  simpa using h

end SchwarzschildSpacetime

end Schwarzschild

end GeneralRelativity
