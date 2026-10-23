/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samyak Rai, Joseph Tooby-Smith
-/
module

public import Physlib.Units.PositiveRealUnit
public import Physlib.Units.WithDim.Basic
/-!

# The Speed of Light

## i. Overview

In this module we define a type for the speed of light in a vacuum,
along with some basic properties. An element of this type is a positive real number,
and should be thought of as the speed of light in some chosen but arbitrary system of units.

## ii. Key results

- `SpeedOfLight` : The type of speeds of light in a vacuum.
- `SpeedOfLight.instPositiveRealUnitCore` : The instance making `SpeedOfLight` a positive-real
  unit type, supplying the shared magnitude, ratio and rescaling API.
- `SpeedOfLight.toWithDim` : The speed of light as a quantity with the dimension of
  length over time.
- `SpeedOfLight.toWithDim_scaleUnit` : The map `toWithDim` commutes with changes of units.

## iii. Table of contents

- A. The Speed of Light type
- B. Instances on the type
- C. The instance of one
- D. Positivity properties
- E. As a dimensioned quantity

## iv. References

* None.
-/

@[expose] public section

open Dimension UnitDependent
open scoped NNReal

/-!

## A. The Speed of Light type

-/

/-- The speed of light in a vacuum. An element of this type should be thought of as
  the speed of light in some chosen but arbitrary system of units. -/
structure SpeedOfLight where
  /-- The underlying value of the speed of light. -/
  val : ℝ
  pos : 0 < val

namespace SpeedOfLight

/-!

## B. Instances on the type

The speed of light is a positive real magnitude, so it is an instance of
`PositiveRealUnitCore`. This supplies the ratio of two speeds of light as a non-negative
real, the rescaling of a speed of light by a positive factor, and the arithmetic laws
relating them, all shared with the fundamental unit types.

-/

instance instPositiveRealUnitCore : PositiveRealUnitCore SpeedOfLight where
  val := SpeedOfLight.val
  pos := SpeedOfLight.pos
  ofVal := fun r hr => ⟨r, hr⟩
  val_ofVal := by intros; rfl
  ofVal_val := by intro x; cases x; rfl

instance : Coe SpeedOfLight ℝ := ⟨SpeedOfLight.val⟩

/-!

## C. The instance of one

We define the instance of one for `SpeedOfLight` to be the speed of light equal to `1`.
This is useful when we are working in units where the speed of light is equal to one.

-/

instance : One SpeedOfLight := ⟨1, by grind⟩

@[simp]
lemma val_one : (1 : SpeedOfLight).val = 1 := rfl

/-- The magnitude supplied to `PositiveRealUnitCore` is the underlying value, so that the
  generic positive-real lemmas apply to `SpeedOfLight`. -/
@[simp]
lemma positiveRealUnitCore_val (c : SpeedOfLight) : PositiveRealUnitCore.val c = c.val := rfl

/-!

## D. Positivity properties

-/

@[simp]
lemma val_pos (c : SpeedOfLight) : 0 < (c : ℝ) := c.pos

@[simp]
lemma val_nonneg (c : SpeedOfLight) : 0 ≤ (c : ℝ) := le_of_lt c.pos

@[simp]
lemma val_ne_zero (c : SpeedOfLight) : (c : ℝ) ≠ 0 := ne_of_gt c.pos

/-!

## E. As a dimensioned quantity

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

/-- The speed of light scales under a change of units by the scale factor of the
  dimension of length over time. -/
noncomputable instance : UnitDependent SpeedOfLight where
  scaleUnit u1 u2 c :=
    ⟨(u1.dimScale u2 (L𝓭 * T𝓭⁻¹) : ℝ) * c.val,
      mul_pos (NNReal.coe_pos.mpr (LTMCTUnitChoices.dimScale_pos u1 u2 (L𝓭 * T𝓭⁻¹))) c.pos⟩
  scaleUnit_trans u1 u2 u3 c := PositiveRealUnitCore.ext (by
    show (u2.dimScale u3 (L𝓭 * T𝓭⁻¹) : ℝ) * ((u1.dimScale u2 (L𝓭 * T𝓭⁻¹) : ℝ) * c.val) = _
    rw [← mul_assoc, ← NNReal.coe_mul, mul_comm (u2.dimScale u3 (L𝓭 * T𝓭⁻¹)),
      LTMCTUnitChoices.dimScale_transitive]
    rfl)
  scaleUnit_trans' u1 u2 u3 c := PositiveRealUnitCore.ext (by
    show (u1.dimScale u2 (L𝓭 * T𝓭⁻¹) : ℝ) * ((u2.dimScale u3 (L𝓭 * T𝓭⁻¹) : ℝ) * c.val) = _
    rw [← mul_assoc, ← NNReal.coe_mul, LTMCTUnitChoices.dimScale_transitive]
    rfl)
  scaleUnit_id u c := PositiveRealUnitCore.ext (by
    show (u.dimScale u (L𝓭 * T𝓭⁻¹) : ℝ) * c.val = c.val
    rw [LTMCTUnitChoices.dimScale_self, NNReal.coe_one, one_mul])

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
