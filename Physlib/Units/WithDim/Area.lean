/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Units.WithDim.Basic
/-!

# Area

In this module we define the dimensionful type corresponding to an area.
We define specific instances of areas, such as square meters, square feet, etc.

-/

@[expose] public section

open Dimension
open NNReal

/-- The type of areas in the absence of a choice of unit. -/
abbrev DimArea : Type := Dimensionful (WithDim (L𝓭 * L𝓭) ℝ≥0)

namespace DimArea

open LTMCTUnitChoices

/-!

## Basic areas

-/

open Dimensionful CarriesDimension

/-- The dimensional area corresponding to 1 square meter. -/
noncomputable def squareMeter : DimArea := toDimensionful SI ⟨1⟩

/-- The dimensional area corresponding to 1 square foot. -/
noncomputable def squareFoot : DimArea := toDimensionful ({SI with
  length := LengthUnit.feet} : LTMCTUnitChoices) ⟨1⟩

/-- The dimensional area corresponding to 1 square mile. -/
noncomputable def squareMile : DimArea := toDimensionful ({SI with
  length := LengthUnit.miles} : LTMCTUnitChoices) ⟨1⟩

/-- The dimensional area corresponding to 1 are (100 square meters). -/
noncomputable def are : DimArea := toDimensionful SI ⟨100⟩

/-- The dimensional area corresponding to 1 hectare (10,000 square meters). -/
noncomputable def hectare : DimArea := toDimensionful SI ⟨10000⟩

/-- The dimensional area corresponding to 1 acre (1/640 square miles). -/
noncomputable def acre : DimArea := toDimensionful ({SI with
  length := LengthUnit.miles} : LTMCTUnitChoices) ⟨(1/640)⟩

/-!

## Area in SI units

-/

@[simp]
lemma squareMeter_in_SI : squareMeter.1 SI = ⟨1⟩ := by
  simp [squareMeter]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma squareFoot_in_SI : squareFoot.1 SI = ⟨0.09290304⟩ := by
  simp [squareFoot, dimScale, LengthUnit.feet]
  ext
  simp [NNReal.coe_ofScientific]
  norm_num [toReal]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma squareMile_in_SI : squareMile.1 SI = ⟨2589988.110336⟩ := by
  simp [squareMile, dimScale, LengthUnit.miles]
  ext
  simp [NNReal.coe_ofScientific]
  norm_num [toReal]

@[simp]
lemma are_in_SI : are.1 SI = ⟨100⟩ := by
  simp [are]

@[simp]
lemma hectare_in_SI : hectare.1 SI = ⟨10000⟩ := by
  simp [hectare]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma acre_in_SI : acre.1 SI = ⟨4046.8564224⟩ := by
  simp [acre, dimScale, LengthUnit.miles]
  ext
  simp [NNReal.coe_ofScientific]
  norm_num [toReal]

/-!

## Relations between areas

-/

set_option backward.isDefEq.respectTransparency false in
/-- One acre is exactly `43560` square feet. -/
lemma acre_eq_mul_squareFeet : acre = (43560 : ℝ≥0) • squareFoot := by
  apply (toDimensionful SI).symm.injective
  ext
  norm_num [toDimensionful]

end DimArea
