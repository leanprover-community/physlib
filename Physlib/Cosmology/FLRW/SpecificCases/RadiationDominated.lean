/-
Copyright (c) 2026 Philippe Kevorkian. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philippe Kevorkian
-/
module

public import Physlib.Cosmology.FLRW.SpecificCases.PowerLaw
/-!

# The radiation-dominated model

## i. Overview

The radiation-dominated solution `radiationScaleFactor t₀`, `a(t) = (t / t₀) ^ (1/2)`, of
`Physlib.Cosmology.FLRW.Solutions` as an FLRW model: the flat power-law model of
`Physlib.Cosmology.FLRW.SpecificCases.PowerLaw` with `n = 1/2`, on the interval `t > 0`. Filled
with its cosmic fluid `CosmicFluid.powerLaw (1/2) (1/3) G c`, radiation of density
`3 n² / (8 π G t²) = 3 / (32 π G t²)` with `n = 1/2` and pressure `ρ c² / 3`, it solves the
Friedmann equations without cosmological constant.

## ii. Key results

- `FLRW.radiationDominated`: the radiation-dominated model.
- `FLRW.radiationDominated_a`: its scale factor is `radiationScaleFactor t₀`.
- `FLRW.friedmannSolution_radiationDominated`: filled with radiation, it solves the Friedmann
  equations.

## iii. Table of contents

- A. The radiation-dominated model

## iv. References

* None.

-/

@[expose] public section

namespace Cosmology

open FLRW.FriedmannEquation

/-!

## A. The radiation-dominated model

-/

/-- The radiation-dominated model, the flat power-law model with `n = 1/2`. -/
noncomputable def FLRW.radiationDominated (t₀ : Time) (ht₀ : 0 < t₀.val) : FLRW :=
  FLRW.powerLaw t₀ ht₀ (1 / 2)

/-- The scale factor of the radiation-dominated model is `radiationScaleFactor t₀`. -/
lemma FLRW.radiationDominated_a {t₀ : Time} (ht₀ : 0 < t₀.val) :
    (FLRW.radiationDominated t₀ ht₀).a = radiationScaleFactor t₀ := rfl

/-- The radiation-dominated model, filled with radiation of density `3 n² / (8 π G t²)` with
  `n = 1/2`, that is `3 / (32 π G t²)`, and pressure `ρ c² / 3`, solves the Friedmann equations
  without cosmological constant on its interval. -/
lemma FLRW.friedmannSolution_radiationDominated {t₀ : Time} (ht₀ : 0 < t₀.val)
    {G c : ℝ} (hG : 0 < G) (hc : 0 < c) :
    (FLRW.radiationDominated t₀ ht₀).FriedmannSolution
      (CosmicFluid.powerLaw (1 / 2) (1 / 3) G c) 0 G c :=
  FLRW.friedmannSolution_powerLaw ht₀ hG hc (by norm_num) (by norm_num)

end Cosmology
