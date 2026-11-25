/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samyak Rai, Joseph Tooby-Smith
-/
module

public import Physlib.Units.WithDim.Basic
/-!

# The Speed of Light

The speed of light in a vacuum, in the format of `Physlib/Units/Constants.lean`.

## i. Overview

The speed of light has the dimension `L T⁻¹`, and its value in SI units is exact. Section F adds
the instance of one and the speed of light as a dimensioned quantity.

## ii. Key results

- `SpeedOfLight` : The speed of light in a chosen but arbitrary system of units.
- `speedOfLight` : The speed of light in our world, `299792458 m s⁻¹`.
- `SpeedOfLight.toWithDim` : The speed of light as a quantity with the dimension of
  length over time.
- `SpeedOfLight.toWithDim_scaleUnit` : The map `toWithDim` commutes with changes of units.

## iii. Table of contents

- A. The type
- B. Instances
- C. Positivity
- D. The dimension
- E. The value in our world
- F. Specific to the speed of light
  - F.1. The instance of one
  - F.2. As a dimensioned quantity

## iv. References

* The defining value of the speed of light. [ref: bipm_si_brochure_2019]
-/

@[expose] public section

open Dimension UnitDependent LTMCTUnitChoices CarriesDimension
open scoped NNReal

/-!

## A. The type

-/

/-- The speed of light in a vacuum, in a chosen but arbitrary system of units. -/
structure SpeedOfLight where
  /-- The underlying value of the speed of light. -/
  val : ℝ
  pos : 0 < val

namespace SpeedOfLight

/-!

## B. Instances

-/

instance instPositiveRealUnitCore : PositiveRealUnitCore SpeedOfLight where
  val := SpeedOfLight.val
  pos := SpeedOfLight.pos
  ofVal := fun r hr => ⟨r, hr⟩
  val_ofVal := by intros; rfl
  ofVal_val := by intro x; cases x; rfl

instance : Coe SpeedOfLight ℝ := ⟨SpeedOfLight.val⟩

@[simp]
lemma positiveRealUnitCore_val (c : SpeedOfLight) : PositiveRealUnitCore.val c = c.val := rfl

/-!

## C. Positivity

-/

@[simp]
lemma val_pos (c : SpeedOfLight) : 0 < (c : ℝ) := c.pos

@[simp]
lemma val_nonneg (c : SpeedOfLight) : 0 ≤ (c : ℝ) := le_of_lt c.pos

@[simp]
lemma val_ne_zero (c : SpeedOfLight) : (c : ℝ) ≠ 0 := ne_of_gt c.pos

/-!

## D. The dimension

-/

/-- The speed of light has the dimension `L T⁻¹`. -/
instance instHasDim : HasDim SpeedOfLight where
  d := L𝓭 * T𝓭⁻¹

end SpeedOfLight

/-!

## E. The value in our world

-/

/-- The speed of light in our world, `299792458 m s⁻¹`, exact. -/
noncomputable def speedOfLight : Dimensionful SpeedOfLight :=
  toDimensionful SI ⟨299792458, by norm_num⟩

@[simp]
lemma speedOfLight_in_SI : speedOfLight SI = ⟨299792458, by norm_num⟩ :=
  toDimensionful_apply_self SI _

namespace SpeedOfLight

/-!

## F. Specific to the speed of light

### F.1. The instance of one

We define the instance of one for `SpeedOfLight` to be the speed of light equal to `1`.
This is useful when we are working in units where the speed of light is equal to one.

-/

instance : One SpeedOfLight := ⟨1, by grind⟩

@[simp]
lemma val_one : (1 : SpeedOfLight).val = 1 := rfl

/-!

### F.2. As a dimensioned quantity

-/

/-- The speed of light as a quantity carrying the dimension of length over time,
in nonnegative real values. The underlying value is the same as that of the
`SpeedOfLight`. -/
def toWithDim (c : SpeedOfLight) : WithDim (L𝓭 * T𝓭⁻¹) ℝ≥0 := ⟨⟨c.val, le_of_lt c.pos⟩⟩

/-- The underlying value of the speed of light as a dimensioned quantity agrees with
the original value. -/
@[simp]
lemma toWithDim_val (c : SpeedOfLight) : (c.toWithDim.val : ℝ) = c.val := rfl

/-- The speed of light as a dimensioned quantity is positive. -/
@[simp]
lemma toWithDim_val_pos (c : SpeedOfLight) : 0 < c.toWithDim.val :=
  NNReal.coe_pos.mp c.val_pos

/-- Scaling a speed of light multiplies its value by the scale factor of the
  dimension of length over time. -/
@[simp]
lemma scaleUnit_val (c : SpeedOfLight) (u1 u2 : LTMCTUnitChoices) :
    (scaleUnit u1 u2 c).val = (u1.dimScale u2 (L𝓭 * T𝓭⁻¹) : ℝ) * c.val := rfl

/-- The map `toWithDim` commutes with changes of units. -/
@[simp]
lemma toWithDim_scaleUnit (c : SpeedOfLight) (u1 u2 : LTMCTUnitChoices) :
    (scaleUnit u1 u2 c).toWithDim = scaleUnit u1 u2 c.toWithDim := by
  refine WithDim.ext _ _ ?_
  simp only [toWithDim, WithDim.scaleUnit_val, scaleUnit_val]
  exact Subtype.ext rfl

end SpeedOfLight
