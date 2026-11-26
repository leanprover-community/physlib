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
`diag(-e^{2φ}, e^{-2φ}, e^{-2φ}, e^{-2φ})`. This module bundles that configuration into
`TeVeSMetric`, proves that `T.metric` remains symmetric and Lorentzian
(`g̃_{00} < 0`, `g̃_{ii} > 0`) for every `φ : ℝ`, preserves the conformal spatial metric `e^{-2φ} δ`,
and admits an explicit two-sided inverse bundled into `MetricTensor 4`.

## ii. Key results

- `TeVeSMetric`, `TeVeSMetric.metric`, `TeVeSMetric.metricInv` : TeVeS disformal metric data,
  physical metric, and inverse in the aether rest frame.
- `TeVeSMetric.symm`, `TeVeSMetric.lorentzian`, `TeVeSMetric.spatial` : symmetry, preserved
  Lorentzian signature, and spatial conformal rescaling.
- `TeVeSMetric.metricTensor` : the TeVeS physical metric bundled as a `MetricTensor 4`.

## iii. Table of contents

- A. The TeVeS physical metric and its inverse
- B. Signature, spatial rescaling, and bundled metric tensor

## iv. References

* Jacob D. Bekenstein, *Relativistic Gravitation Theory for the Modified Newtonian Dynamics
  Paradigm*, *Physical Review D* (2004), Sec. II-III
  (https://arxiv.org/pdf/astro-ph/0403694#page=2). [ref: Bekenstein2004]
* Benoit Famaey and Stacy S. McGaugh, *Modified Newtonian Dynamics (MOND): Observational
  Phenomenology and Relativistic Extensions*, *Living Reviews in Relativity* (2012), Sec. 7.
  [ref: FamaeyMcGaugh2012]
-/

@[expose] public section

namespace GeneralRelativity

namespace Modified

namespace TeVeS

/-!

## A. The TeVeS physical metric and its inverse

In the aether rest frame, the disformal coupling reverses the scalar conformal exponent between the
timelike aether direction and the orthogonal spatial hypersurface.

-/

/-- Data determining the TeVeS disformal physical (Jordan) metric in an aether rest frame
for scalar field value `φ`. -/
structure TeVeSMetric where
  /-- Scalar field value `φ`. -/
  φ : ℝ

/-- The TeVeS physical (Jordan) metric in a frame where the unit timelike vector is `∂_t` and
the Einstein metric is `η`:
`g̃ = e^{-2φ}(g + U ⊗ U) - e^{2φ} U ⊗ U = diag(-e^{2φ}, e^{-2φ}, e^{-2φ}, e^{-2φ})`. -/
noncomputable def TeVeSMetric.metric (T : TeVeSMetric) : Tensor2 4 :=
  !![(-Real.exp (2 * T.φ)), 0, 0, 0;
     0, Real.exp (-2 * T.φ), 0, 0;
     0, 0, Real.exp (-2 * T.φ), 0;
     0, 0, 0, Real.exp (-2 * T.φ)]

/-- The inverse TeVeS physical metric `diag(-e^{-2φ}, e^{2φ}, e^{2φ}, e^{2φ})`. -/
noncomputable def TeVeSMetric.metricInv (T : TeVeSMetric) : Tensor2 4 :=
  !![(-Real.exp (-2 * T.φ)), 0, 0, 0;
     0, Real.exp (2 * T.φ), 0, 0;
     0, 0, Real.exp (2 * T.φ), 0;
     0, 0, 0, Real.exp (2 * T.φ)]

/-- Symmetry of the TeVeS physical metric. -/
lemma TeVeSMetric.symm (T : TeVeSMetric) : IsSymm T.metric := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [TeVeSMetric.metric]

/-!

## B. Signature, spatial rescaling, and bundled metric tensor

Positivity of the real exponential guarantees preserved Lorentzian signature and exact invertibility
for every scalar field value `T.φ`.

-/

/-- The TeVeS physical metric remains Lorentzian for every value of the scalar field `T.φ`: one
negative temporal entry and three positive spatial entries. -/
lemma TeVeSMetric.lorentzian (T : TeVeSMetric) :
    T.metric 0 0 < 0 ∧ 0 < T.metric 1 1 ∧ 0 < T.metric 2 2 ∧
      0 < T.metric 3 3 := by
  have h1 : 0 < Real.exp (2 * T.φ) := Real.exp_pos _
  have h2 : 0 < Real.exp (-(2 * T.φ)) := Real.exp_pos _
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [TeVeSMetric.metric] <;> linarith

/-- The spatial block of the TeVeS physical metric is the conformal rescaling `e^{-2φ} δ`. -/
lemma TeVeSMetric.spatial (T : TeVeSMetric) :
    T.metric 1 1 = Real.exp (-2 * T.φ) ∧ T.metric 2 2 = Real.exp (-2 * T.φ) ∧
      T.metric 3 3 = Real.exp (-2 * T.φ) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [TeVeSMetric.metric]

/-- `T.metric * T.metricInv = 1`. -/
lemma TeVeSMetric.mul_inv (T : TeVeSMetric) : T.metric * T.metricInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [TeVeSMetric.metric, TeVeSMetric.metricInv, Matrix.mul_apply, Fin.sum_univ_four,
      ← Real.exp_add]

/-- `T.metricInv * T.metric = 1`. -/
lemma TeVeSMetric.inv_mul (T : TeVeSMetric) : T.metricInv * T.metric = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [TeVeSMetric.metric, TeVeSMetric.metricInv, Matrix.mul_apply, Fin.sum_univ_four,
      ← Real.exp_add]

/-- The TeVeS physical metric of `T` bundled as a `MetricTensor 4` with its certified inverse. -/
noncomputable def TeVeSMetric.metricTensor (T : TeVeSMetric) : MetricTensor 4 where
  g := T.metric
  ginv := T.metricInv
  symm := T.symm
  inv_left := T.mul_inv
  inv_right := T.inv_mul

end TeVeS

end Modified

end GeneralRelativity
