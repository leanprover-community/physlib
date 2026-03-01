/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Geometry.Manifold.Diffeomorph
import PhysLean.SpaceAndTime.Time.Basic
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

-/

/-- The choices of translationally-invariant metrics on the space-manifold.
  Such a choice corresponds to a choice of units for length. -/
structure LengthUnit where
  /-- The underlying scale of the unit. -/
  val : ℝ
  property : 0 < val

namespace LengthUnit

@[simp]
lemma val_ne_zero (x : LengthUnit) : x.val ≠ 0 := by
  exact Ne.symm (ne_of_lt x.property)

lemma val_pos (x : LengthUnit) : 0 < x.val := x.property

instance : Inhabited LengthUnit where
  default := ⟨1, by norm_num⟩

/-!

## Division of LengthUnit

-/

open NNReal

noncomputable instance : HDiv LengthUnit LengthUnit ℝ≥0 where
  hDiv x t := ⟨x.val / t.val, div_nonneg (le_of_lt x.val_pos) (le_of_lt t.val_pos)⟩

lemma div_eq_val (x y : LengthUnit) :
    (x / y) = (⟨x.val / y.val, div_nonneg (le_of_lt x.val_pos) (le_of_lt y.val_pos)⟩ : ℝ≥0) := rfl

@[simp]
lemma div_ne_zero (x y : LengthUnit) : ¬ x / y = (0 : ℝ≥0) := by
  rw [div_eq_val]
  refine coe_ne_zero.mp ?_
  simp

@[simp]
lemma div_pos (x y : LengthUnit) : (0 : ℝ≥0) < x/ y := by
  apply lt_of_le_of_ne
  · exact zero_le (x / y)
  · exact Ne.symm (div_ne_zero x y)

@[simp]
lemma div_self (x : LengthUnit) :
    x / x = (1 : ℝ≥0) := by
  simp [div_eq_val, x.val_ne_zero]

lemma div_symm (x y : LengthUnit) :
    x / y = (y / x)⁻¹ := NNReal.eq <| by
  rw [div_eq_val, inv_eq_one_div, div_eq_val]
  simp

@[simp]
lemma div_mul_div_coe (x y z : LengthUnit) :
    (x / y : ℝ) * (y /z : ℝ) = x /z := by
  simp [div_eq_val]
  field_simp

/-!

## The scaling of a length unit

-/

/-- The scaling of a length unit by a positive real. -/
def scale (r : ℝ) (x : LengthUnit) (hr : 0 < r := by norm_num) : LengthUnit :=
  ⟨r * x.val, mul_pos hr x.val_pos⟩

@[simp]
lemma scale_div_self (x : LengthUnit) (r : ℝ) (hr : 0 < r) :
    scale r x hr / x = (⟨r, le_of_lt hr⟩ : ℝ≥0) := by
  simp [scale, div_eq_val]

@[simp]
lemma self_div_scale (x : LengthUnit) (r : ℝ) (hr : 0 < r) :
    x / scale r x hr = (⟨1/r, _root_.div_nonneg (by simp) (le_of_lt hr)⟩ : ℝ≥0) := by
  simp [scale, div_eq_val]
  ext
  simp only [coe_mk]
  field_simp

@[simp]
lemma scale_one (x : LengthUnit) : scale 1 x = x := by
  simp [scale]

@[simp]
lemma scale_div_scale (x1 x2 : LengthUnit) {r1 r2 : ℝ} (hr1 : 0 < r1) (hr2 : 0 < r2) :
    scale r1 x1 hr1 / scale r2 x2 hr2 = (⟨r1, le_of_lt hr1⟩ / ⟨r2, le_of_lt hr2⟩) * (x1 / x2) := by
  refine NNReal.eq ?_
  simp [scale, div_eq_val]
  field_simp

@[simp]
lemma scale_scale (x : LengthUnit) (r1 r2 : ℝ) (hr1 : 0 < r1) (hr2 : 0 < r2) :
    scale r1 (scale r2 x hr2) hr1 = scale (r1 * r2) x (mul_pos hr1 hr2) := by
  simp [scale]
  ring
/-!

## Specific choices of Length units

To define a specific length units.
We first define the notion of a meter to correspond to the length unit with underlying value
equal to `1`. This is really down to a choice in the isomorphism between the set of metrics
on the space manifold and the positive reals.
From this choice of meters, we can define other length units by scaling meters.

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

TODO "ITXJV" "For each unit of charge give the reference the literature where it's definition
  is defined."

/-!

## Relations between length units

-/

/-- There are exactly 1760 yards in a mile. -/
lemma miles_div_yards : miles / yards = (⟨1760, by norm_num⟩ : ℝ≥0) :=
  NNReal.eq <| by simp [miles, yards]; norm_num

/-- There are exactly 220 yards in a furlong. -/
lemma furlongs_div_yards : furlongs / yards = (⟨220, by norm_num⟩ : ℝ≥0) := NNReal.eq <| by
  simp [furlongs, yards]; norm_num

end LengthUnit
