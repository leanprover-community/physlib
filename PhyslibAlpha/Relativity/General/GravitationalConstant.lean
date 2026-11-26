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
independent in the `(L, T, M, Θ)` base space, `exists_units_c_G_kB_eq_one` parallels
`Physlib.Units.Constants.exists_units_constants_eq_one` by constructing systems of units in which
`c`, `G`, and `k_B` simultaneously take the numerical value `1`.

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
- E. Specific to the gravitational constant
  - E.1. The instance of one
  - E.2. As a dimensioned quantity
- F. The value in our world
- G. Natural and geometric unit systems

## iv. References

* International Bureau of Weights and Measures (BIPM), *The International System of Units (SI
  Brochure)*, 9th ed. (2019), Sec. 2.2
  (https://www.bipm.org/documents/d/guest/si-brochure-9-en-pdf). [ref: bipm_si_brochure_2019]
* P. J. Mohr, D. B. Newell, B. N. Taylor, and E. Tiesinga, *CODATA Recommended Values of the
  Fundamental Physical Constants: 2022*, *Reviews of Modern Physics* 97(2), 025002 (2025)
  (https://physics.nist.gov/cuu/Constants/). [ref: CODATA2022]
* R. M. Wald, *General Relativity* (1984), App. F. [ref: wald_1984_general_relativity]
-/

@[expose] public section

open Dimension UnitDependent LTMCTUnitChoices CarriesDimension
open scoped NNReal

/-!

## A. The type

Following `Physlib/Units/Constants.lean`, `GravitationalConstant` packages a positive real value
representing Newton's constant in an arbitrary choice of units.

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

This section registers `PositiveRealUnitCore` and the real coercion so `GravitationalConstant`
transforms automatically under changes of `LTMCTUnitChoices`.

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

Basic positivity, nonnegativity, and nonvanishing lemmas for the numerical value of the
gravitational constant in any unit system.

-/

@[simp]
lemma val_pos (G : GravitationalConstant) : 0 < (G : ℝ) := G.pos

@[simp]
lemma val_nonneg (G : GravitationalConstant) : 0 ≤ (G : ℝ) := le_of_lt G.pos

@[simp]
lemma val_ne_zero (G : GravitationalConstant) : (G : ℝ) ≠ 0 := ne_of_gt G.pos

/-!

## D. The dimension

Newton's constant carries the mechanical dimension `L³ M⁻¹ T⁻²`, matching `G M / r²` having the
dimension of acceleration.

-/

/-- The dimension `L³ M⁻¹ T⁻²` of Newton's gravitational constant `G`. -/
def gravitationalConstantDimension : Dimension LTMCTDimensionBase :=
  L𝓭 * L𝓭 * L𝓭 * M𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹

/-- Equational expansion of `gravitationalConstantDimension` into base dimensions. -/
lemma gravitationalConstantDimension_eq :
    gravitationalConstantDimension = L𝓭 * L𝓭 * L𝓭 * M𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹ := rfl

/-- Newton's gravitational constant has the dimension `L³ M⁻¹ T⁻²`. -/
instance instHasDim : HasDim GravitationalConstant where
  d := gravitationalConstantDimension

/-!

## E. Specific to the gravitational constant

### E.1. The instance of one

We define the instance of one for `GravitationalConstant` to be the gravitational constant equal to
`1`, corresponding to geometric or Planck units.

-/

instance : One GravitationalConstant := ⟨1, Real.zero_lt_one⟩

@[simp]
lemma val_one : (1 : GravitationalConstant).val = 1 := rfl

/-!

### E.2. As a dimensioned quantity

Embedding `GravitationalConstant` into `WithDim` relates unit scaling directly to the dimensional
scale factor of `L³ M⁻¹ T⁻²`.

-/

/-- Newton's gravitational constant as a quantity carrying the dimension `L³ M⁻¹ T⁻²` in
nonnegative real values. -/
def toWithDim (G : GravitationalConstant) :
    WithDim gravitationalConstantDimension ℝ≥0 :=
  ⟨⟨G.val, le_of_lt G.pos⟩⟩

/-- The underlying real value of the dimensioned gravitational constant agrees with its numerical
value. -/
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

/-- Converting to a dimensioned quantity commutes with changes of units. -/
@[simp]
lemma toWithDim_scaleUnit (G : GravitationalConstant) (u1 u2 : LTMCTUnitChoices) :
    (scaleUnit u1 u2 G).toWithDim = scaleUnit u1 u2 G.toWithDim := by
  refine WithDim.ext _ _ ?_
  simp only [toWithDim, WithDim.scaleUnit_val, scaleUnit_val]
  exact Subtype.ext rfl

end GravitationalConstant

/-!

## F. The value in our world

The SI value is fixed from the CODATA 2022 recommended value `6.67430 × 10⁻¹¹ m³ kg⁻¹ s⁻²`.

-/

/-- Newton's gravitational constant in our world, `6.67430 × 10⁻¹¹ m³ kg⁻¹ s⁻²` (CODATA 2022). -/
noncomputable def gravitationalConstant : Dimensionful GravitationalConstant :=
  toDimensionful SI ⟨6.67430e-11, by norm_num⟩

/-- In SI units, `gravitationalConstant` takes the CODATA 2022 value
`6.67430 × 10⁻¹¹ m³ kg⁻¹ s⁻²`. -/
@[simp]
lemma gravitationalConstant_in_SI :
    gravitationalConstant SI = ⟨6.67430e-11, by norm_num⟩ :=
  toDimensionful_apply_self SI _

/-!

## G. Natural and geometric unit systems

Rescaling the SI length, mass, and temperature units simultaneously sets `c = 1`, `G = 1`, and
`k_B = 1` in `LTMCTUnitChoices`.

-/

private lemma speedOfLight_scaleUnit_SI (u : LTMCTUnitChoices) :
    (speedOfLight u).val = (SI.dimScale u (L𝓭 * T𝓭⁻¹) : ℝ) * 299792458 := rfl

private lemma gravitationalConstant_scaleUnit_SI (u : LTMCTUnitChoices) :
    (gravitationalConstant u).val =
      (SI.dimScale u GravitationalConstant.gravitationalConstantDimension : ℝ) *
        6.67430e-11 := rfl

private lemma boltzmannConstant_scaleUnit_SI (u : LTMCTUnitChoices) :
    (boltzmannConstant u).val =
      (SI.dimScale u (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹) : ℝ) * 1.380649e-23 := rfl

/-- There exist units `u : LTMCTUnitChoices` in which the speed of light `c`, the Newtonian
gravitational constant `G`, and the Boltzmann constant `k_B` are simultaneously equal to `1`. -/
lemma exists_units_c_G_kB_eq_one : ∃ u : LTMCTUnitChoices,
    (speedOfLight u).val = 1 ∧ (gravitationalConstant u).val = 1 ∧
      (boltzmannConstant u).val = 1 := by
  have hdiv : ∀ {U : Type} [PositiveRealUnitCore U] (x : U) (r : ℝ) (hr : 0 < r),
      ((x / PositiveRealUnitCore.scale r x hr : ℝ≥0) : ℝ) = 1 / r := by
    intro U _ x r hr
    rw [PositiveRealUnitCore.self_div_scale]
    rfl
  have hself : ∀ {U : Type} [PositiveRealUnitCore U] (x : U), ((x / x : ℝ≥0) : ℝ) = 1 := by
    intro U _ x
    simp
  refine ⟨{SI with
    length := PositiveRealUnitCore.scale 299792458 LengthUnit.meters
    mass := PositiveRealUnitCore.scale (299792458 ^ 3 / 6.67430e-11) MassUnit.kilograms
    temperature := PositiveRealUnitCore.scale
      ((299792458 ^ 3 / 6.67430e-11) * 299792458 ^ 2 / 1.380649e-23)
      TemperatureUnit.kelvin}, ?_, ?_, ?_⟩
  · rw [speedOfLight_scaleUnit_SI]
    simp only [map_mul, map_inv, NNReal.coe_mul, NNReal.coe_inv, dimScale_L𝓭, dimScale_T𝓭,
      SI_length, SI_time, hdiv, hself]
    norm_num
  · rw [gravitationalConstant_scaleUnit_SI,
      GravitationalConstant.gravitationalConstantDimension_eq]
    simp only [map_mul, map_inv, NNReal.coe_mul, NNReal.coe_inv, dimScale_L𝓭, dimScale_M𝓭,
      dimScale_T𝓭, SI_length, SI_mass, SI_time, hdiv, hself]
    norm_num
  · rw [boltzmannConstant_scaleUnit_SI]
    simp only [map_mul, map_inv, NNReal.coe_mul, NNReal.coe_inv, dimScale_L𝓭, dimScale_T𝓭,
      dimScale_M𝓭, dimScale_Θ𝓭, SI_length, SI_time, SI_mass, SI_temperature, hdiv, hself]
    norm_num
