/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Physlib.Units.Constants
public import Physlib.Units.WithDim.Basic
import Mathlib.Tactic.NormNum

/-!

# The Newtonian gravitational constant

Newton's gravitational constant `G`, in the format of `Physlib/Units/Constants.lean`, together with
geometric and natural unit systems in which `c = G = k_B = 1`.

## i. Overview

Newton's universal gravitational constant `G` has dimension `L³ M⁻¹ T⁻²` (`L𝓭 * L𝓭 * L𝓭 * M𝓭⁻¹ *
T𝓭⁻¹ * T𝓭⁻¹`) and CODATA 2022 recommended SI value `6.67430 × 10⁻¹¹ m³ kg⁻¹ s⁻²`. Because the
dimensions of `c` (`L T⁻¹`), `G` (`L³ M⁻¹ T⁻²`), and `k_B` (`M L² T⁻² Θ⁻¹`) are linearly
independent in the `(L, T, M, Θ)` base space, there exist systems of units in which `c`, `G`, and
`k_B` simultaneously take the numerical value `1`.

## ii. Key results

- `GravitationalConstant` : Newton's gravitational constant in a chosen but arbitrary system of
  units.
- `gravitationalConstantDimension`, `GravitationalConstant.instHasDim` : The dimension
  `L³ M⁻¹ T⁻²` of Newton's gravitational constant.
- `gravitationalConstant`, `gravitationalConstant_in_SI` : The gravitational constant in our world,
  `6.67430 × 10⁻¹¹ m³ kg⁻¹ s⁻²` (CODATA 2022).
- `GravitationalConstant.toWithDim`, `GravitationalConstant.toWithDim_scaleUnit` : The
  gravitational constant as a dimensioned quantity and unit-scaling equivariance.
- `exists_units_c_G_kB_eq_one` : Existence of a system of units `u : LTMCTUnitChoices` in which
  `(speedOfLight u).val = 1`, `(gravitationalConstant u).val = 1`, and
  `(boltzmannConstant u).val = 1`.

## iii. Table of contents

- A. The type
- B. Instances
- C. Positivity
- D. The dimension
- E. The value in our world
- F. Specific to the gravitational constant
  - F.1. The instance of one
  - F.2. As a dimensioned quantity
  - F.3. Natural and geometric unit systems

## iv. References

* None.

-/

@[expose] public section

namespace GeneralRelativity

open Dimension UnitDependent LTMCTUnitChoices CarriesDimension
open scoped NNReal

/-!

## A. The type

-/

/-- Newton's universal gravitational constant `G`, in a chosen but arbitrary system of units. -/
structure GravitationalConstant where
  /-- The underlying numerical value of the gravitational constant. -/
  val : ℝ
  /-- Positivity of the gravitational constant in any valid unit system. -/
  pos : 0 < val

namespace GravitationalConstant

/-!

## B. Instances

-/

instance instPositiveRealUnitCore : PositiveRealUnitCore GravitationalConstant where
  val := GravitationalConstant.val
  pos := GravitationalConstant.pos
  ofVal := fun r hr => ⟨r, hr⟩
  val_ofVal := by intros; rfl
  ofVal_val := by intro x; cases x; rfl

instance : Coe GravitationalConstant ℝ := ⟨GravitationalConstant.val⟩

@[simp]
lemma positiveRealUnitCore_val (G : GravitationalConstant) :
    PositiveRealUnitCore.val G = G.val := rfl

/-!

## C. Positivity

-/

@[simp]
lemma val_pos (G : GravitationalConstant) : 0 < (G : ℝ) := G.pos

@[simp]
lemma val_nonneg (G : GravitationalConstant) : 0 ≤ (G : ℝ) := le_of_lt G.pos

@[simp]
lemma val_ne_zero (G : GravitationalConstant) : (G : ℝ) ≠ 0 := ne_of_gt G.pos

/-!

## D. The dimension

-/

/-- The dimension `L³ M⁻¹ T⁻²` of Newton's gravitational constant `G`. -/
def gravitationalConstantDimension : Dimension LTMCTDimensionBase :=
  L𝓭 * L𝓭 * L𝓭 * M𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹

/-- Newton's gravitational constant has the dimension `L³ M⁻¹ T⁻²`. -/
instance instHasDim : HasDim GravitationalConstant where
  d := gravitationalConstantDimension

end GravitationalConstant

/-!

## E. The value in our world

-/

/-- Newton's gravitational constant in our world, `6.67430 × 10⁻¹¹ m³ kg⁻¹ s⁻²` (CODATA 2022). -/
noncomputable def gravitationalConstant : Dimensionful GravitationalConstant :=
  toDimensionful SI ⟨6.67430e-11, by norm_num⟩

@[simp]
lemma gravitationalConstant_in_SI :
    gravitationalConstant SI = ⟨6.67430e-11, by norm_num⟩ :=
  toDimensionful_apply_self SI _

namespace GravitationalConstant

/-!

## F. Specific to the gravitational constant

### F.1. The instance of one

We define the instance of one for `GravitationalConstant` to be the gravitational constant equal to
`1`, corresponding to geometric or Planck units.

-/

instance : One GravitationalConstant := ⟨1, Real.zero_lt_one⟩

@[simp]
lemma val_one : (1 : GravitationalConstant).val = 1 := rfl

/-!

### F.2. As a dimensioned quantity

-/

/-- Newton's gravitational constant as a quantity carrying the dimension `L³ M⁻¹ T⁻²` in
nonnegative real values. -/
def toWithDim (G : GravitationalConstant) :
    WithDim gravitationalConstantDimension ℝ≥0 :=
  ⟨⟨G.val, le_of_lt G.pos⟩⟩

/-- The underlying real value of `G.toWithDim` agrees with `G.val`. -/
@[simp]
lemma toWithDim_val (G : GravitationalConstant) : (G.toWithDim.val : ℝ) = G.val := rfl

/-- The gravitational constant as a dimensioned quantity is positive. -/
@[simp]
lemma toWithDim_val_pos (G : GravitationalConstant) : 0 < G.toWithDim.val :=
  NNReal.coe_pos.mp G.val_pos

/-- Scaling a gravitational constant between unit systems multiplies its value by the dimensional
scale factor of `L³ M⁻¹ T⁻²`. -/
@[simp]
lemma scaleUnit_val (G : GravitationalConstant) (u1 u2 : LTMCTUnitChoices) :
    (scaleUnit u1 u2 G).val =
      (u1.dimScale u2 gravitationalConstantDimension : ℝ) * G.val := rfl

/-- The map `toWithDim` commutes with changes of units. -/
@[simp]
lemma toWithDim_scaleUnit (G : GravitationalConstant) (u1 u2 : LTMCTUnitChoices) :
    (scaleUnit u1 u2 G).toWithDim = scaleUnit u1 u2 G.toWithDim := by
  refine WithDim.ext _ _ ?_
  simp only [toWithDim, WithDim.scaleUnit_val, scaleUnit_val]
  exact Subtype.ext rfl

end GravitationalConstant

/-!

### F.3. Natural and geometric unit systems

-/

/-- There exist units `u : LTMCTUnitChoices` in which the speed of light `c`, the Newtonian
gravitational constant `G`, and the Boltzmann constant `k_B` are simultaneously equal to `1`. -/
lemma exists_units_c_G_kB_eq_one : ∃ u : LTMCTUnitChoices,
    (speedOfLight u).val = 1 ∧ (gravitationalConstant u).val = 1 ∧
      (boltzmannConstant u).val = 1 := by
  refine ⟨{SI with
    length := PositiveRealUnitCore.scale 299792458 LengthUnit.meters
    mass := PositiveRealUnitCore.scale (299792458 ^ 3 / 6.67430e-11) MassUnit.kilograms
    temperature := PositiveRealUnitCore.scale
      ((299792458 ^ 3 / 6.67430e-11) * 299792458 ^ 2 / 1.380649e-23)
      TemperatureUnit.kelvin}, ?_, ?_, ?_⟩
  · change ((SI.dimScale _ (L𝓭 * T𝓭⁻¹) : ℝ≥0) : ℝ) * 299792458 = 1
    simp only [map_mul, map_inv, NNReal.coe_mul, NNReal.coe_inv, dimScale_L𝓭, dimScale_T𝓭]
    change (1 / (299792458 * 1) : ℝ) * (1 / 1)⁻¹ * 299792458 = 1
    norm_num
  · change ((SI.dimScale _ GravitationalConstant.gravitationalConstantDimension : ℝ≥0) : ℝ) *
      6.67430e-11 = 1
    unfold GravitationalConstant.gravitationalConstantDimension
    simp only [map_mul, map_inv, NNReal.coe_mul, NNReal.coe_inv, dimScale_L𝓭, dimScale_M𝓭,
      dimScale_T𝓭]
    change (1 / (299792458 * 1) : ℝ) * (1 / (299792458 * 1)) * (1 / (299792458 * 1)) *
      (1 / ((299792458 ^ 3 / 6.67430e-11) * 1))⁻¹ * (1 / 1)⁻¹ * (1 / 1)⁻¹ * 6.67430e-11 = 1
    norm_num
  · change ((SI.dimScale _ (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹) : ℝ≥0) : ℝ) * 1.380649e-23 = 1
    simp only [map_mul, map_inv, NNReal.coe_mul, NNReal.coe_inv, dimScale_L𝓭, dimScale_T𝓭,
      dimScale_M𝓭, dimScale_Θ𝓭]
    change (1 / ((299792458 ^ 3 / 6.67430e-11) * 1) : ℝ) *
      (1 / (299792458 * 1)) * (1 / (299792458 * 1)) * (1 / 1)⁻¹ * (1 / 1)⁻¹ *
      (1 / (((299792458 ^ 3 / 6.67430e-11) * 299792458 ^ 2 / 1.380649e-23) * 1))⁻¹ *
      1.380649e-23 = 1
    norm_num

end GeneralRelativity
