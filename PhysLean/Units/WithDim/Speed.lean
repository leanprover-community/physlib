/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Units.WithDim.Basic
/-!

# Speed

In this module we define the dimensionful type corresponding to an speed.
We define specific instances of speed, such as miles per hour, kilometers per hour, etc.

-/

@[expose] public section
open Dimension
open NNReal

/-- The type of speeds in the absence of a choice of unit. -/
abbrev DimSpeed : Type := Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ≥0)

namespace DimSpeed

open UnitChoices

/-!

## Basic speeds

-/
open Dimensionful
open UnitChoices CarriesDimension
/-- The dimensional speed corresponding to 1 meter per second. -/
noncomputable def oneMeterPerSecond : DimSpeed := toDimensionful SI ⟨1⟩

/-- The dimensional speed corresponding to 1 mile per hour. -/
noncomputable def oneMilePerHour : DimSpeed := toDimensionful ({SI with
  length := LengthUnit.miles, time := TimeUnit.hours} : UnitChoices) ⟨1⟩

/-- The dimensional speed corresponding to 1 kilometer per hour. -/
noncomputable def oneKilometerPerHour : DimSpeed := toDimensionful ({SI with
  length := LengthUnit.kilometers, time := TimeUnit.hours} : UnitChoices) ⟨1⟩

/-- The dimensional speed corresponding to 1 knot, aka, one nautical mile per hour. -/
noncomputable def oneKnot : DimSpeed := toDimensionful ({SI with
  length := LengthUnit.nauticalMiles, time := TimeUnit.hours} : UnitChoices) ⟨1⟩

/-- The dimensionful speed of light corresponding to 299792458 meters per second. -/
noncomputable def speedOfLight : Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ) :=
  toDimensionful SI ⟨299792458⟩

/-!

## Speed in SI units

-/

@[simp]
lemma oneMeterPerSecond_in_SI : oneMeterPerSecond SI = ⟨1⟩ := by
  simp [oneMeterPerSecond, toDimensionful_apply_apply]

@[simp]
lemma oneMilePerHour_in_SI : oneMilePerHour SI = ⟨0.44704⟩ := by
  simp [oneMilePerHour, dimScale, LengthUnit.miles, TimeUnit.hours, toDimensionful_apply_apply]
  ext
  simp only [NNReal.coe_ofScientific]
  norm_num

@[simp]
lemma oneKilometerPerHour_in_SI :
    oneKilometerPerHour SI = ⟨5/18⟩ := by
  simp [oneKilometerPerHour, dimScale,
    LengthUnit.kilometers, TimeUnit.hours, toDimensionful_apply_apply]
  ext
  simp only
  norm_num

@[simp]
lemma oneKnot_in_SI : oneKnot SI = ⟨463/900⟩ := by
  simp [oneKnot, dimScale, LengthUnit.nauticalMiles, TimeUnit.hours, toDimensionful_apply_apply]
  ext
  simp only
  norm_num

@[simp]
lemma speedOfLight_in_SI : speedOfLight SI = ⟨299792458⟩ := by
  simp [speedOfLight, toDimensionful_apply_apply]

/-!

## Relations between speeds

-/

lemma oneKnot_eq_mul_oneKilometerPerHour :
    oneKnot = (1.852 : ℝ≥0) • oneKilometerPerHour := by
  apply (toDimensionful SI).symm.injective
  simp [toDimensionful]
  ext
  norm_num

lemma oneKilometerPerHour_eq_mul_oneKnot:
    oneKilometerPerHour = (250/463 : ℝ≥0) • oneKnot := by
  apply (toDimensionful SI).symm.injective
  simp [toDimensionful]
  ext
  norm_num

lemma oneMeterPerSecond_eq_mul_oneMilePerHour :
    oneMeterPerSecond = (3125/1397 : ℝ≥0) • oneMilePerHour := by
  apply (toDimensionful SI).symm.injective
  simp [toDimensionful]
  ext
  norm_num

end DimSpeed
