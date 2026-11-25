/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Units.Basic
/-!

# Boltzmann constant

The Boltzmann constant, in the format of `Physlib/Units/Constants.lean`.

## i. Overview

The Boltzmann constant, named after Ludwig Boltzmann, has the dimension `M L² T⁻² Θ⁻¹` of an energy
over a temperature, and its value in SI units is exact. Section F adds the instance of one.

## ii. Key results

- `BoltzmannConstant` : The Boltzmann constant in a chosen but arbitrary system of units.
- `boltzmannConstant` : The Boltzmann constant in our world, `1.380649 × 10⁻²³ J K⁻¹`.

## iii. Table of contents

- A. The type
- B. Instances
- C. Positivity
- D. The dimension
- E. The value in our world
- F. Specific to the Boltzmann constant

## iv. References

* The defining value of the Boltzmann constant. [ref: bipm_si_brochure_2019]
-/

@[expose] public section

open Dimension LTMCTUnitChoices CarriesDimension

/-!

## A. The type

-/

/-- The Boltzmann constant, in a chosen but arbitrary system of units. -/
structure BoltzmannConstant where
  /-- The underlying value of the Boltzmann constant. -/
  val : ℝ
  pos : 0 < val

namespace BoltzmannConstant

/-!

## B. Instances

-/

instance instPositiveRealUnitCore : PositiveRealUnitCore BoltzmannConstant where
  val := BoltzmannConstant.val
  pos := BoltzmannConstant.pos
  ofVal := fun r hr => ⟨r, hr⟩
  val_ofVal := by intros; rfl
  ofVal_val := by intro x; cases x; rfl

instance : Coe BoltzmannConstant ℝ := ⟨BoltzmannConstant.val⟩

@[simp]
lemma positiveRealUnitCore_val (kB : BoltzmannConstant) :
    PositiveRealUnitCore.val kB = kB.val := rfl

/-!

## C. Positivity

-/

@[simp]
lemma val_pos (kB : BoltzmannConstant) : 0 < (kB : ℝ) := kB.pos

@[simp]
lemma val_nonneg (kB : BoltzmannConstant) : 0 ≤ (kB : ℝ) := le_of_lt kB.pos

@[simp]
lemma val_ne_zero (kB : BoltzmannConstant) : (kB : ℝ) ≠ 0 := ne_of_gt kB.pos

/-!

## D. The dimension

-/

/-- The Boltzmann constant has the dimension `M L² T⁻² Θ⁻¹`. -/
instance instHasDim : HasDim BoltzmannConstant where
  d := M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹

end BoltzmannConstant

/-!

## E. The value in our world

-/

/-- The Boltzmann constant in our world, `1.380649 × 10⁻²³ J K⁻¹`, exact. -/
noncomputable def boltzmannConstant : Dimensionful BoltzmannConstant :=
  toDimensionful SI ⟨1.380649e-23, by norm_num⟩

@[simp]
lemma boltzmannConstant_in_SI : boltzmannConstant SI = ⟨1.380649e-23, by norm_num⟩ :=
  toDimensionful_apply_self SI _

/-!

## F. Specific to the Boltzmann constant

The Boltzmann constant equal to `1`, for units in which it is one.

-/

namespace BoltzmannConstant

instance : One BoltzmannConstant := ⟨1, one_pos⟩

@[simp]
lemma val_one : (1 : BoltzmannConstant).val = 1 := rfl

end BoltzmannConstant
