/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith

/-!

# Scalar–Tensor–Vector Gravity (MOG / STVG)

Structural properties of Moffat's Modified Gravity (MOG) Yukawa-enhanced potential.

## i. Overview

MOG (Scalar–Tensor–Vector Gravity) introduces a massive vector field mediating a repulsive
Yukawa correction whose net effect is a radius-dependent enhancement of Newton's constant:

`Φ(r) = -(G M / r) (1 + α (1 - e^{-μ r}))`.

This module formalises the enhancement factor `factor α μ r` and potential `potential G M α μ r`,
proving that the enhancement equals `1` at `r = 0`, reduces to Newtonian gravity at `α = 0` or
`μ = 0`, is strictly bounded in `[1, 1 + α)` for `α > 0` and `μ r ≥ 0`, and approaches `1 + α`
asymptotically at large radius when `μ > 0`.

## ii. Key results

- `factor`, `potential` : MOG enhancement factor and gravitational potential.
- `factor_zero`, `factor_alpha_zero`, `factor_mu_zero` : Newtonian reductions at `r = 0`,
  `α = 0`, and `μ = 0`.
- `factor_bounds` : for `α > 0` and `μ r ≥ 0`, `1 ≤ factor α μ r < 1 + α`.
- `factor_tendsto_atTop` : for `μ > 0`, `factor α μ r → 1 + α` as `r → ∞`.

## iii. Table of contents

- A. The MOG enhancement factor and potential
- B. Bounds, Newtonian limits, and asymptotic behaviour

## iv. References

* None.

-/

@[expose] public section

namespace GeneralRelativity

namespace MOG

/-!

## A. The MOG enhancement factor and potential

-/

/-- MOG enhancement factor `1 + α (1 - e^{-μ r})`. -/
noncomputable def factor (α μ r : ℝ) : ℝ := 1 + α * (1 - Real.exp (-(μ * r)))

/-- The MOG gravitational potential `-(G M / r) · factor α μ r`. -/
noncomputable def potential (G M α μ r : ℝ) : ℝ := -((G * M) / r) * factor α μ r

/-!

## B. Bounds, Newtonian limits, and asymptotic behaviour

-/

/-- At `r = 0`, the MOG enhancement factor is exactly `1`. -/
lemma factor_zero (α μ : ℝ) : factor α μ 0 = 1 := by
  simp [factor]

/-- At `α = 0`, MOG reduces to Newtonian gravity (`factor = 1`). -/
lemma factor_alpha_zero (μ r : ℝ) : factor 0 μ r = 1 := by
  simp [factor]

/-- At `μ = 0`, MOG reduces to Newtonian gravity (`factor = 1`). -/
lemma factor_mu_zero (α r : ℝ) : factor α 0 r = 1 := by
  simp [factor]

/-- For positive `α` and `μ r ≥ 0`, the MOG enhancement factor lies in `[1, 1 + α)`: a single
Yukawa vector cannot absorb a mass discrepancy larger than `1 + α`. -/
lemma factor_bounds (α μ r : ℝ) (hα : 0 < α) (hμr : 0 ≤ μ * r) :
    1 ≤ factor α μ r ∧ factor α μ r < 1 + α := by
  have hpos : 0 < Real.exp (-(μ * r)) := Real.exp_pos _
  have hle : Real.exp (-(μ * r)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  constructor
  · simp only [factor]
    nlinarith
  · simp only [factor]
    nlinarith

/-- For `μ > 0`, the MOG enhancement factor tends asymptotically to `1 + α` at large radius. -/
lemma factor_tendsto_atTop (α μ : ℝ) (hμ : 0 < μ) :
    Filter.Tendsto (fun r : ℝ => factor α μ r) Filter.atTop (nhds (1 + α)) := by
  have hmul : Filter.Tendsto (fun r : ℝ => μ * r) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hμ Filter.tendsto_id
  have hneg : Filter.Tendsto (fun r : ℝ => -(μ * r)) Filter.atTop Filter.atBot :=
    Filter.tendsto_neg_atTop_atBot.comp hmul
  have hexp : Filter.Tendsto (fun r : ℝ => Real.exp (-(μ * r))) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp hneg
  have h1 : Filter.Tendsto (fun r : ℝ => 1 + α * (1 - Real.exp (-(μ * r))))
      Filter.atTop (nhds (1 + α * (1 - 0))) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul (tendsto_const_nhds.sub hexp))
  simpa [factor] using h1

end MOG

end GeneralRelativity
