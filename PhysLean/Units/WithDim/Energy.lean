/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Units.WithDim.Basic
/-!

# Energy

In this module we define the dimensionful type corresponding to an energy.
We define specific instances of energy.

-/

@[expose] public section
open Dimension
open NNReal

/-- Energy as a dimensional quantity with dimension `MLT⁻2`.. -/
abbrev DimEnergy : Type := Dimensionful (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

namespace DimEnergy
open UnitChoices Dimensionful CarriesDimension

/-- The dimensional energy corresponding to 1 joule, J. -/
noncomputable def joule : DimEnergy := toDimensionful SI ⟨1⟩

/-- The dimensional energy corresponding to 1 electron volt, 1.602176634×10−19 J. -/
noncomputable def electronVolt : DimEnergy := toDimensionful SI ⟨1.602176634e-19⟩

/-- The dimensional energy corresponding to 1 calorie, 4.184 J. -/
noncomputable def calorie : DimEnergy := toDimensionful SI ⟨4.184⟩

/-- The dimensional energy corresponding to 1 kilowatt-hours, (3,600,000 J). -/
noncomputable def kilowattHour : DimEnergy := toDimensionful SI ⟨3600000⟩

end DimEnergy
