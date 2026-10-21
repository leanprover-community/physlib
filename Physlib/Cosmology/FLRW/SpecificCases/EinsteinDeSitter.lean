/-
Copyright (c) 2026 Philippe Kevorkian. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philippe Kevorkian
-/
module

public import Physlib.Cosmology.FLRW.SpecificCases.PowerLaw
/-!

# The Einstein-de Sitter model

## i. Overview

The Einstein-de Sitter solution `einsteinDeSitterScaleFactor t₀`, `a(t) = (t / t₀) ^ (2/3)`, of
`Physlib.Cosmology.FLRW.Solutions` as an FLRW model: the flat power-law model of
`Physlib.Cosmology.FLRW.SpecificCases.PowerLaw` with `n = 2/3`, on the interval `t > 0`. Filled
with its cosmic fluid `CosmicFluid.powerLaw (2/3) 0 G c`, dust of density
`3 n² / (8 π G t²) = 1 / (6 π G t²)` with `n = 2/3` and zero pressure, it solves the Friedmann
equations without cosmological constant.

## ii. Key results

- `FLRW.einsteinDeSitter`: the Einstein-de Sitter model.
- `FLRW.einsteinDeSitter_a`: its scale factor is `einsteinDeSitterScaleFactor t₀`.
- `FLRW.friedmannSolution_einsteinDeSitter`: filled with dust, it solves the Friedmann
  equations.

## iii. Table of contents

- A. The Einstein-de Sitter model

## iv. References

* None.

-/

@[expose] public section

namespace Cosmology

open FLRW.FriedmannEquation

/-!

## A. The Einstein-de Sitter model

-/

/-- The Einstein-de Sitter model, the flat power-law model with `n = 2/3`. -/
noncomputable def FLRW.einsteinDeSitter (t₀ : Time) (ht₀ : 0 < t₀.val) : FLRW :=
  FLRW.powerLaw t₀ ht₀ (2 / 3)

/-- The scale factor of the Einstein-de Sitter model is `einsteinDeSitterScaleFactor t₀`. -/
lemma FLRW.einsteinDeSitter_a {t₀ : Time} (ht₀ : 0 < t₀.val) :
    (FLRW.einsteinDeSitter t₀ ht₀).a = einsteinDeSitterScaleFactor t₀ := rfl

/-- The Einstein-de Sitter model, filled with dust of density `3 n² / (8 π G t²)` with `n = 2/3`,
  that is `1 / (6 π G t²)`, and zero pressure, solves the Friedmann equations without cosmological
  constant on its interval. -/
lemma FLRW.friedmannSolution_einsteinDeSitter {t₀ : Time} (ht₀ : 0 < t₀.val)
    {G c : ℝ} (hG : 0 < G) (hc : 0 < c) :
    (FLRW.einsteinDeSitter t₀ ht₀).FriedmannSolution
      (CosmicFluid.powerLaw (2 / 3) 0 G c) 0 G c :=
  FLRW.friedmannSolution_powerLaw ht₀ hG hc (by norm_num) (by norm_num)

end Cosmology
