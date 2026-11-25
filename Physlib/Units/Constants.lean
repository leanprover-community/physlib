/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.Relativity.SpeedOfLight
public import Physlib.StatisticalMechanics.BoltzmannConstant
/-!

# Physical constants

An index of the physical constants in Physlib, and the format of their files.

## i. Overview

Each constant has its own file, which this module imports. Use these constants instead of defining
new ones or writing out their values: a result in any units takes the type, such as
`c : SpeedOfLight`, and the value in our world is `speedOfLight`. A new constant gets a file in the
format of section A, an import above, a row in the table below and an `example` in section B.

## ii. Key results

| Constant | Dimension | Value in SI units |
|---|---|---|
| `speedOfLight` | `L T⁻¹` | `299792458 m s⁻¹`, exact |
| `boltzmannConstant` | `M L² T⁻² Θ⁻¹` | `1.380649 × 10⁻²³ J K⁻¹`, exact |

Not yet in this format: `Constants.h`, `Constants.ℏ` and `ChargeUnit.elementaryCharge`.

- `exists_units_constants_eq_one` : There are units in which the speed of light and the Boltzmann
  constant are `1`.

## iii. Table of contents

- A. The format of a constant
- B. Checked values
- C. Planck units

## iv. References

* The defining constants of the SI. [ref: bipm_si_brochure_2019]

## A. The format of a constant

The file of a constant with type `X` and value `x` has these sections, as in
`Physlib/Relativity/SpeedOfLight.lean`.

| Section | Contents |
|---|---|
| A. The type | `structure X` with fields `val : ℝ` and `pos : 0 < val` |
| B. Instances | `X.instPositiveRealUnitCore`, `Coe X ℝ`, `X.positiveRealUnitCore_val` |
| C. Positivity | `X.val_pos`, `X.val_nonneg`, `X.val_ne_zero` |
| D. The dimension | `X.instHasDim` |
| E. The value in our world | `x : Dimensionful X` and `x_in_SI` |
| F. Specific to this constant | Optional, for example `One` or other forms of the constant |

The value `x` is `X` in lower camel case, defined by `toDimensionful SI`, and `x_in_SI` is proved by
`toDimensionful_apply_self`. The docstring of `x` gives the number with its SI unit, followed by
`exact` or, for a measured constant, the CODATA edition.

-/

@[expose] public section

open NNReal Dimension LTMCTUnitChoices

/-!

## B. Checked values

One `example` for each row of the table, giving the dimension and the value in SI units. Lean
checks these against the definitions; it does not read the table.

-/

example : dim SpeedOfLight = L𝓭 * T𝓭⁻¹ ∧ (speedOfLight SI).val = 299792458 := ⟨rfl, by simp⟩

example : dim BoltzmannConstant = M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹ ∧
    (boltzmannConstant SI).val = 1.380649e-23 := ⟨rfl, by simp⟩

TODO "Define `SI` from the defining constants, as the SI itself has been defined since 2019: the
  units in which the caesium frequency, the speed of light, the Planck constant, the elementary
  charge and the Boltzmann constant take their exact values. The values in our world, such as
  `speedOfLight` and `boltzmannConstant`, are currently defined the other way round, from `SI`."

/-!

## C. Planck units

Planck units are units in which `c`, `ℏ`, `G` and `k_B` are all `1`; so far the lemma below covers
`c` and `k_B`. Constants with independent dimensions can always be `1` together, while constants
with dependent dimensions can only if their dimensionless ratios are `1`. So the lemma does not
extend to every constant: `h` cannot join `ℏ`, and the electron mass cannot join `c`, `ℏ` and `G`.

-/

/-- There are units in which the speed of light and the Boltzmann constant are `1`. -/
lemma exists_units_constants_eq_one : ∃ u : LTMCTUnitChoices,
    (speedOfLight u).val = 1 ∧ (boltzmannConstant u).val = 1 := by
  refine ⟨{SI with
    length := PositiveRealUnitCore.scale 299792458 LengthUnit.meters
    temperature := PositiveRealUnitCore.scale (299792458 ^ 2 / 1.380649e-23)
      TemperatureUnit.kelvin}, ?_, ?_⟩
  · change ((SI.dimScale _ (L𝓭 * T𝓭⁻¹) : ℝ≥0) : ℝ) * 299792458 = 1
    simp only [map_mul, map_inv, NNReal.coe_mul, NNReal.coe_inv, dimScale_L𝓭, dimScale_T𝓭]
    change (1 / (299792458 * 1) : ℝ) * (1 / 1)⁻¹ * 299792458 = 1
    norm_num
  · change ((SI.dimScale _ (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹) : ℝ≥0) : ℝ) * 1.380649e-23 = 1
    simp only [map_mul, map_inv, NNReal.coe_mul, NNReal.coe_inv, dimScale_L𝓭, dimScale_T𝓭,
      dimScale_M𝓭, dimScale_Θ𝓭]
    change (1 / 1 : ℝ) * (1 / (299792458 * 1)) * (1 / (299792458 * 1)) * (1 / 1)⁻¹ * (1 / 1)⁻¹ *
      (1 / ((299792458 ^ 2 / 1.380649e-23) * 1))⁻¹ * 1.380649e-23 = 1
    norm_num
