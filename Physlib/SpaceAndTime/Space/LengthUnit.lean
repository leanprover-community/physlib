/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Units.PositiveRealUnit
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
/-!

# Units on Length

A unit of length corresponds to a choice of translationally-invariant
metric on the space manifold (to be defined). Such a choice is (non-canonically) equivalent to a
choice of positive real number. We define the type `LengthUnit` to be equivalent to the
positive reals.

On `LengthUnit` there is an instance of division giving a real number, corresponding to the
ratio of the two scales of length unit.

To define specific length units, we first state the existence of a
a given length unit, and then construct all other length units from it. We choose to state the
existence of the length unit of meters, and construct all other length units from that.

## References

* The BIPM SI Brochure, for the meter, the speed of light, and SI prefixes.
  [ref: bipm_si_brochure_2019]
* NIST Handbook 44, Appendix C, for the international foot-based units and the international
  nautical mile. [ref: nist_hb44_2023]
* IAU 2012 Resolution B2, for the astronomical unit. [ref: iau_2012_resolution_b2]
* The IAU Style Manual recommendations, for the Julian year convention used in the light-year.
  [ref: iau_style_manual_units]
* IAU 2015 Resolution B2, for the exact parsec convention. [ref: iau_2015_resolution_b2]

-/

@[expose] public section

/-- The choices of translationally-invariant metrics on the space-manifold.
  Such a choice corresponds to a choice of units for length. -/
structure LengthUnit where
  /-- The underlying scale of the unit. -/
  val : ℝ
  property : 0 < val

instance : PositiveRealUnitCore LengthUnit where
  val := LengthUnit.val
  pos := LengthUnit.property
  ofVal := fun r hr => ⟨r, hr⟩
  val_ofVal := by intros; rfl
  ofVal_val := by intro x; cases x; rfl
open NNReal

namespace LengthUnit

open PositiveRealUnitCore

/-!

## Specific choices of Length units

To define a specific length units.
We first define the notion of a meter to correspond to the length unit with underlying value
equal to `1`. This is really down to a choice in the isomorphism between the set of metrics
on the space manifold and the positive reals.
From this choice of meters, we can define other length units by scaling meters.

The references for the numerical definitions used below are:
* the BIPM SI Brochure for the meter, the speed of light, and SI prefixes:
  https://www.bipm.org/documents/d/guest/si-brochure-9-en-pdf [ref: bipm_si_brochure_2019]
* NIST Handbook 44, Appendix C, for the international foot-based units and
  the international nautical mile:
  https://doi.org/10.6028/NIST.HB.44-2023 [ref: nist_hb44_2023]
* IAU 2012 Resolution B2 for the astronomical unit:
  https://iauarchive.eso.org/static/resolutions/IAU2012_English.pdf [ref: iau_2012_resolution_b2]
* the IAU Style Manual recommendations for the Julian year convention used in
  the light-year:
  https://iauarchive.eso.org/publications/proceedings_rules/units/ [ref: iau_style_manual_units]
* IAU 2015 Resolution B2 for the exact parsec convention:
  https://iauarchive.eso.org/static/resolutions/IAU2015_English.pdf [ref: iau_2015_resolution_b2]

-/

/-- The definition of a length unit of meters. -/
def meters : LengthUnit := ⟨1, by norm_num⟩

/-- The length unit of femtometers (10⁻¹⁵ of a meter). -/
noncomputable def femtometers : LengthUnit := scale ((1/10) ^ (15)) meters

/-- The length unit of picometers (10⁻¹² of a meter). -/
noncomputable def picometers : LengthUnit := scale ((1/10) ^ (12)) meters

/-- The length unit of nanometers (10⁻⁹ of a meter). -/
noncomputable def nanometers : LengthUnit := scale ((1/10) ^ (9)) meters

/-- The length unit of micrometers (10⁻⁶ of a meter). -/
noncomputable def micrometers : LengthUnit := scale ((1/10) ^ (6)) meters

/-- The length unit of millimeters (10⁻³ of a meter). -/
noncomputable def millimeters : LengthUnit := scale ((1/10) ^ (3)) meters

/-- The length unit of centimeters (10⁻² of a meter). -/
noncomputable def centimeters : LengthUnit := scale ((1/10) ^ (2)) meters

/-- The length unit of inch (0.0254 meters). -/
noncomputable def inches : LengthUnit := scale (0.0254) meters

/-- The length unit of link (0.201168 meters). -/
noncomputable def links : LengthUnit := scale (0.201168) meters

/-- The length unit of feet (0.3048 meters) -/
noncomputable def feet : LengthUnit := scale (0.3048) meters

/-- The length unit of a yard (0.9144 meters) -/
noncomputable def yards : LengthUnit := scale (0.9144) meters

/-- The length unit of a rod (5.0292 meters) -/
noncomputable def rods : LengthUnit := scale (5.0292) meters

/-- The length unit of a chain (20.1168 meters) -/
noncomputable def chains : LengthUnit := scale (20.1168) meters

/-- The length unit of a furlong (201.168 meters) -/
noncomputable def furlongs : LengthUnit := scale (201.168) meters

/-- The length unit of kilometers (10³ meters). -/
noncomputable def kilometers : LengthUnit := scale ((10) ^ (3)) meters

/-- The length unit of a mile (1609.344 meters). -/
noncomputable def miles : LengthUnit := scale (1609.344) meters

/-- The length unit of a nautical mile (1852 meters). -/
noncomputable def nauticalMiles : LengthUnit := scale (1852) meters

/-- The length unit of an astronomical unit (149,597,870,700 meters). -/
noncomputable def astronomicalUnits : LengthUnit := scale (149597870700) meters

/-- The length unit of a light year (9,460,730,472,580,800 meters). -/
noncomputable def lightYears : LengthUnit := scale (9460730472580800) meters

/-- The length unit of a parsec (648,000/π astronomicalUnits). -/
noncomputable def parsecs : LengthUnit := scale (648000/Real.pi) astronomicalUnits
  (by norm_num; exact Real.pi_pos)

/-!

## Relations between length units

-/

/-- There are exactly 1760 yards in a mile. -/
lemma miles_div_yards : miles / yards = (⟨1760, by norm_num⟩ : ℝ≥0) :=
  NNReal.eq <| by
    simp [miles, yards]
    show (1609.344 : ℝ) / 0.9144 = ((⟨1760, by norm_num⟩ : ℝ≥0) : ℝ)
    push_cast
    norm_num

/-- There are exactly 220 yards in a furlong. -/
lemma furlongs_div_yards : furlongs / yards = (⟨220, by norm_num⟩ : ℝ≥0) := NNReal.eq <| by
  simp [furlongs, yards]
  show (201.168 : ℝ) / 0.9144 = ((⟨220, by norm_num⟩ : ℝ≥0) : ℝ)
  push_cast
  norm_num

end LengthUnit
