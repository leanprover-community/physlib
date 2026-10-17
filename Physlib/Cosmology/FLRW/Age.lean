/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philippe Kevorkian, Jinzheng Li
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
/-!

# The age of the universe

## i. Overview

Integrating `dt = da / (a H)` from `a = 0` to the present value of the scale factor, with
`H = H₀ E(a / a₀)` for a reduced Hubble function `E` (for instance `reducedHubble` of
`Physlib.Cosmology.FLRW.ReducedHubble`), gives the age of the universe
`t₀ = H₀⁻¹ ∫₀¹ dx / (x E(x))`. It is proportional to `1 / H₀`: the dimensionless integral depends
only on the shape of `E`.

The age is defined here for an arbitrary function `E`, as an interval integral; no convergence
is asserted.

## ii. Key results

- `age`: `t₀ = H₀⁻¹ ∫₀¹ dx / (x E(x))`.
- `age_eq`: `t₀ ∝ 1 / H₀`.

## iii. Table of contents

- A. The age of the universe

## iv. References

* None.

-/

@[expose] public section

namespace Cosmology.FLRW.FriedmannEquation

/-!

## A. The age of the universe

-/

/-- The age of the universe `t₀ = H₀⁻¹ ∫₀¹ dx / (x E(x))` for a reduced Hubble function `E`:
  the time elapsed since `a = 0`, obtained by integrating `dt = da / (a H)` with
  `H = H₀ E(a / a₀)` (interval integral; no convergence is asserted here). -/
noncomputable def age (H₀ : ℝ) (E : ℝ → ℝ) : ℝ :=
  (1 / H₀) * ∫ x in (0 : ℝ)..1, 1 / (x * E x)

/-- The age is proportional to `1 / H₀`. -/
lemma age_eq (H₀ : ℝ) (E : ℝ → ℝ) : age H₀ E = (1 / H₀) * age 1 E := by
  unfold age
  ring

end Cosmology.FLRW.FriedmannEquation
