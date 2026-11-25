/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.LinearAlgebra.Matrix.Notation
public import PhyslibAlpha.Relativity.Metrics.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!

# Tensor–Vector–Scalar gravity (TeVeS)

Causal structure and inverse geometry of Bekenstein's disformal physical metric.

## i. Overview

TeVeS couples matter to a physical (Jordan) metric `g̃` built disformally from an Einstein
metric `g`, a scalar field `φ`, and a unit timelike vector field `U`:

`g̃ = e^{-2φ} (g + U ⊗ U) - e^{2φ} U ⊗ U`.

In an orthonormal frame where `g = η = diag(-1, 1, 1, 1)` and `U = ∂_t`, this reduces to
`diag(-e^{2φ}, e^{-2φ}, e^{-2φ}, e^{-2φ})`. This module proves that `g̃` remains symmetric
and Lorentzian (`g̃_{00} < 0`, `g̃_{ii} > 0`) for every `φ : ℝ`, preserves the conformal spatial
metric `e^{-2φ} δ`, and admits an explicit two-sided inverse bundled into `MetricTensor 4`.

## ii. Key results

- `TeVeSMetric` : TeVeS disformal metric data parameterized by the scalar field `φ`.
- `metric`, `metricInv` : the TeVeS physical metric and its inverse in the aether frame.
- `metric_symm`, `metric_lorentzian`, `metric_spatial` : symmetry, preserved Lorentzian
  signature, and spatial conformal rescaling.
- `metricTensor` : the TeVeS physical metric bundled as a `MetricTensor 4`.

## iii. Table of contents

- A. The TeVeS physical metric and its inverse
- B. Signature, spatial rescaling, and bundled metric tensor

## iv. References

* Jacob D. Bekenstein, *Relativistic Gravitation Theory for the Modified Newtonian Dynamics
  Paradigm*, *Physical Review D* (2004) (https://arxiv.org/abs/astro-ph/0403694). [ref:
  Bekenstein2004]

-/

@[expose] public section

namespace GeneralRelativity

namespace Modified

namespace TeVeS

/-!

## A. The TeVeS physical metric and its inverse

-/

/-- Data determining the TeVeS disformal physical (Jordan) metric in an aether rest frame
for scalar field value `φ`. -/
structure TeVeSMetric where
  /-- Scalar field value `φ`. -/
  φ : ℝ

/-- The TeVeS physical (Jordan) metric in a frame where the unit timelike vector is `∂_t` and
the Einstein metric is `η`:
`g̃ = e^{-2φ}(g + U ⊗ U) - e^{2φ} U ⊗ U = diag(-e^{2φ}, e^{-2φ}, e^{-2φ}, e^{-2φ})`. -/
noncomputable def metric (φ : ℝ) : Tensor2 4 :=
  !![(-Real.exp (2 * φ)), 0, 0, 0;
     0, Real.exp (-2 * φ), 0, 0;
     0, 0, Real.exp (-2 * φ), 0;
     0, 0, 0, Real.exp (-2 * φ)]

/-- The inverse TeVeS physical metric `diag(-e^{-2φ}, e^{2φ}, e^{2φ}, e^{2φ})`. -/
noncomputable def metricInv (φ : ℝ) : Tensor2 4 :=
  !![(-Real.exp (-2 * φ)), 0, 0, 0;
     0, Real.exp (2 * φ), 0, 0;
     0, 0, Real.exp (2 * φ), 0;
     0, 0, 0, Real.exp (2 * φ)]

/-- The TeVeS physical (Jordan) metric of a `TeVeSMetric` configuration. -/
noncomputable def TeVeSMetric.metric (T : TeVeSMetric) : Tensor2 4 := TeVeS.metric T.φ

/-- The inverse TeVeS physical metric of a `TeVeSMetric` configuration. -/
noncomputable def TeVeSMetric.metricInv (T : TeVeSMetric) : Tensor2 4 := TeVeS.metricInv T.φ

/-- Symmetry of the TeVeS physical metric. -/
lemma metric_symm (φ : ℝ) : IsSymm (metric φ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [metric]

/-!

## B. Signature, spatial rescaling, and bundled metric tensor

-/

/-- The TeVeS physical metric remains Lorentzian for every value of the scalar field `φ`: one
negative temporal entry and three positive spatial entries. -/
lemma metric_lorentzian (φ : ℝ) :
    metric φ 0 0 < 0 ∧ 0 < metric φ 1 1 ∧ 0 < metric φ 2 2 ∧
      0 < metric φ 3 3 := by
  have h1 : 0 < Real.exp (2 * φ) := Real.exp_pos _
  have h2 : 0 < Real.exp (-(2 * φ)) := Real.exp_pos _
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [metric] <;> linarith

/-- The spatial block of the TeVeS physical metric is the conformal rescaling `e^{-2φ} δ`. -/
lemma metric_spatial (φ : ℝ) :
    metric φ 1 1 = Real.exp (-2 * φ) ∧ metric φ 2 2 = Real.exp (-2 * φ) ∧
      metric φ 3 3 = Real.exp (-2 * φ) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [metric]

/-- `metric φ * metricInv φ = 1`. -/
lemma metric_mul_inv (φ : ℝ) : metric φ * metricInv φ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [metric, metricInv, Matrix.mul_apply, Fin.sum_univ_four, ← Real.exp_add]

/-- `metricInv φ * metric φ = 1`. -/
lemma metricInv_mul (φ : ℝ) : metricInv φ * metric φ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [metric, metricInv, Matrix.mul_apply, Fin.sum_univ_four, ← Real.exp_add]

/-- The TeVeS physical metric bundled as a `MetricTensor 4` with its certified inverse. -/
noncomputable def metricTensor (φ : ℝ) : MetricTensor 4 where
  g := metric φ
  ginv := metricInv φ
  symm := metric_symm φ
  inv_left := metric_mul_inv φ
  inv_right := metricInv_mul φ

/-- Bundled `MetricTensor 4` of a `TeVeSMetric` configuration. -/
noncomputable def TeVeSMetric.metricTensor (T : TeVeSMetric) : MetricTensor 4 :=
  TeVeS.metricTensor T.φ

end TeVeS

end Modified

end GeneralRelativity
