/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte, Emil Kuban
-/
module

public import Physlib.SpaceAndTime.Space.Derivatives.Basic
public import Physlib.Mathematics.ForMathlib.HasTemperateGrowth
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!

# Integration by parts on space

## i. Overview

For a function `g` of temperate growth and a Schwartz map `ψ` on `Space d`, the integral of
`g ∂ᵢψ` equals minus the integral of `(∂ᵢ g) ψ`. There are no boundary terms since `g ψ` decays
at infinity.

## ii. Key results

- `integral_mul_deriv_schwartzMap` : `∫ g ∂ᵢψ = -∫ (∂ᵢ g) ψ`.

## iii. Table of contents

- A. Integration by parts against a Schwartz map

## iv. References

* None.

-/

@[expose] public section

namespace Space

open MeasureTheory

/-!

## A. Integration by parts against a Schwartz map

-/

/-- Integration by parts for a space derivative of a Schwartz map against a function of
temperate growth: `∫ g ∂ᵢψ = -∫ (∂ᵢ g) ψ`. -/
lemma integral_mul_deriv_schwartzMap {d : ℕ} (i : Fin d) {g : Space d → ℂ}
    (hg : g.HasTemperateGrowth) (ψ : SchwartzMap (Space d) ℂ) :
    ∫ x, g x * ∂[i] ψ x = -∫ x, ∂[i] g x * ψ x :=
  integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.mul ℝ ℂ)
    ((deriv_hasTemperateGrowth i hg).integrable_mul_schwartzMap ψ)
    (hg.integrable_mul_schwartzMap
      (SchwartzMap.evalCLM ℝ (Space d) ℂ (basis i) (SchwartzMap.fderivCLM ℝ (Space d) ℂ ψ)))
    (hg.integrable_mul_schwartzMap ψ)
    (fun x _ => ((hg.1.differentiable (by simp)) x).hasFDerivAt.hasLineDerivAt (basis i))
    (fun x _ => ψ.differentiableAt.hasFDerivAt.hasLineDerivAt (basis i))

end Space
