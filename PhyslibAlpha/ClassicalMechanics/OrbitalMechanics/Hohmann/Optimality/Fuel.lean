/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qianli Ma
-/
module

public import PhyslibAlpha.ClassicalMechanics.OrbitalMechanics.Hohmann.Optimality.Bielliptic
public import PhyslibAlpha.ClassicalMechanics.OrbitalMechanics.Hohmann.Optimality.KeplerConservation

/-!
# Hohmann optimality in the ideal rocket model

Fixed positive exhaust speed transfers the impulse bound to propellant fraction.

## i. Overview

The ideal rocket equation gives the fraction consumed as a function of total delta-v at fixed
exhaust speed. Monotonicity transfers the two-impulse bound to this model.

## ii. Key results

- `newton_arc_ideal_fuel_lower_bound` gives the main result of this module.

## iii. Table of contents

- A. The ideal propellant fraction

## iv. References

- [ref: hohmann_nasa_rocket]. NASA Glenn gives the ideal rocket equation.
-/

@[expose] public noncomputable section

namespace ClassicalMechanics.HohmannOptimality

/-!
## A. The ideal propellant fraction
-/

/-- The fraction of initial mass consumed at fixed exhaust speed. -/
def idealPropellantFraction (exhaustSpeed deltaV : ℝ) : ℝ :=
  1 - Real.exp (-deltaV/exhaustSpeed)

lemma idealPropellantFraction_mono {ve d₁ d₂ : ℝ} (hExhaustSpeed : 0 < ve) (hd : d₁ ≤ d₂) :
    idealPropellantFraction ve d₁ ≤ idealPropellantFraction ve d₂ := by
  have hdiv : -d₂/ve ≤ -d₁/ve :=
    (div_le_div_iff_of_pos_right hExhaustSpeed).2 (neg_le_neg hd)
  have he := Real.exp_le_exp.mpr hdiv
  dsimp [idealPropellantFraction]
  linarith

lemma idealPropellantFraction_strict {ve d₁ d₂ : ℝ} (hExhaustSpeed : 0 < ve) (hd : d₁ < d₂) :
    idealPropellantFraction ve d₁ < idealPropellantFraction ve d₂ := by
  have hdiv : -d₂/ve < -d₁/ve :=
    (div_lt_div_iff_of_pos_right hExhaustSpeed).2 (neg_lt_neg hd)
  have he := Real.exp_lt_exp.mpr hdiv
  dsimp [idealPropellantFraction]
  linarith

/-- Equal exhaust speed makes multiplying burn mass ratios equivalent to using
sum delta-v; this is the ONLY fuel interpretation used here. -/
lemma remaining_fraction_two_burns (ve d₁ d₂ : ℝ) :
    Real.exp (-d₁/ve)*Real.exp (-d₂/ve) = Real.exp (-(d₁+d₂)/ve) := by
  rw [← Real.exp_add]
  congr 1
  ring

lemma newton_arc_ideal_fuel_lower_bound (p : Units) (a : KeplerArc p.mu)
    (h₀ : (a.state a.t₀).radius=p.r₁) (h₁ : (a.state a.t₁).radius=p.r₂)
    {ve : ℝ} (hExhaustSpeed : 0 < ve) :
    idealPropellantFraction ve p.bound ≤ idealPropellantFraction ve
      ((a.state a.t₀).impulse p.speed+(a.state a.t₁).impulse p.circular₂) :=
  idealPropellantFraction_mono hExhaustSpeed (KeplerArc.newton_arc_lower_bound p a h₀ h₁)

end ClassicalMechanics.HohmannOptimality
