/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Geometry.Manifold.Diffeomorph
import PhysLean.SpaceAndTime.Time.Basic
/-!

# Units on Mass

A unit of mass corresponds to a choice of translationally-invariant
metric on the mass manifold (to be defined diffeomorphic to `ℝ≥0`).
Such a choice is (non-canonically) equivalent to a
choice of positive real number. We define the type `MassUnit` to be equivalent to the
positive reals.

On `MassUnit` there is an instance of division giving a real number, corresponding to the
ratio of the two scales of mass unit.

To define specific mass units, we first state the existence of a
a given mass unit, and then construct all other mass units from it. We choose to state the
existence of the mass unit of kilograms, and construct all other mass units from that.

-/

open NNReal

/-- The choices of translationally-invariant metrics on the mass-manifold.
  Such a choice corresponds to a choice of units for mass. -/
structure MassUnit where
  /-- The underlying scale of the unit. -/
  val : ℝ
  property : 0 < val

namespace MassUnit

@[simp]
lemma val_ne_zero (x : MassUnit) : x.val ≠ 0 := by
  exact Ne.symm (ne_of_lt x.property)

lemma val_pos (x : MassUnit) : 0 < x.val := x.property

instance : Inhabited MassUnit where
  default := ⟨1, by norm_num⟩

/-!

## Division of MassUnit

-/

noncomputable instance : HDiv MassUnit MassUnit ℝ≥0 where
  hDiv x t := ⟨x.val / t.val, div_nonneg (le_of_lt x.val_pos) (le_of_lt t.val_pos)⟩

lemma div_eq_val (x y : MassUnit) :
    x / y = (⟨x.val / y.val, div_nonneg (le_of_lt x.val_pos) (le_of_lt y.val_pos)⟩ : ℝ≥0) := rfl

@[simp]
lemma div_ne_zero (x y : MassUnit) : ¬ x / y = (0 : ℝ≥0) := by
  rw [div_eq_val]
  refine coe_ne_zero.mp ?_
  simp

@[simp]
lemma div_pos (x y : MassUnit) : (0 : ℝ≥0) < x/ y := by
  apply lt_of_le_of_ne
  · exact zero_le (x / y)
  · exact Ne.symm (div_ne_zero x y)

@[simp]
lemma div_self (x : MassUnit) :
    x / x = (1 : ℝ≥0) := by
  simp [div_eq_val, x.val_ne_zero]

lemma div_symm (x y : MassUnit) :
    x / y = (y / x)⁻¹ := NNReal.eq <| by
  rw [div_eq_val, inv_eq_one_div, div_eq_val]
  simp

@[simp]
lemma div_mul_div_coe (x y z : MassUnit) :
    (x / y : ℝ) * (y /z : ℝ) = x /z := by
  simp [div_eq_val]
  field_simp

/-!

## The scaling of a mass unit

-/

/-- The scaling of a mass unit by a positive real. -/
def scale (r : ℝ) (x : MassUnit) (hr : 0 < r := by norm_num) : MassUnit :=
  ⟨r * x.val, mul_pos hr x.val_pos⟩

@[simp]
lemma scale_div_self (x : MassUnit) (r : ℝ) (hr : 0 < r) :
    scale r x hr / x = (⟨r, le_of_lt hr⟩ : ℝ≥0) := by
  simp [scale, div_eq_val]

@[simp]
lemma self_div_scale (x : MassUnit) (r : ℝ) (hr : 0 < r) :
    x / scale r x hr = (⟨1/r, _root_.div_nonneg (by simp) (le_of_lt hr)⟩ : ℝ≥0) := by
  simp [scale, div_eq_val]
  ext
  simp only [coe_mk]
  field_simp

@[simp]
lemma scale_one (x : MassUnit) : scale 1 x = x := by
  simp [scale]

@[simp]
lemma scale_div_scale (x1 x2 : MassUnit) {r1 r2 : ℝ} (hr1 : 0 < r1) (hr2 : 0 < r2) :
    scale r1 x1 hr1 / scale r2 x2 hr2 = (⟨r1, le_of_lt hr1⟩ / ⟨r2, le_of_lt hr2⟩) * (x1 / x2) := by
  refine NNReal.eq ?_
  simp [scale, div_eq_val]
  field_simp

@[simp]
lemma scale_scale (x : MassUnit) (r1 r2 : ℝ) (hr1 : 0 < r1) (hr2 : 0 < r2) :
    scale r1 (scale r2 x hr2) hr1 = scale (r1 * r2) x (mul_pos hr1 hr2) := by
  simp [scale]
  ring

/-!

## Specific choices of mass units

To define a specific mass units.
We first define the notion of a kilogram to correspond to the mass unit with underlying value
equal to `1`. This is really down to a choice in the isomorphism between the set of metrics
on the mass manifold and the positive reals.
From this choice of kilograms, we can define other length units by scaling kilograms.

-/

/-- The definition of a mass unit of kilograms. -/
def kilograms : MassUnit := ⟨1, by norm_num⟩

/-- The mass unit of a microgram (10^(-9) of a kilogram). -/
noncomputable def micrograms : MassUnit := scale ((1/10) ^ 9) kilograms

/-- The mass unit of milligram (10^(-6) of a kilogram). -/
noncomputable def milligrams : MassUnit := scale ((1/10) ^ 6) kilograms

/-- The mass unit of grams (10^(-3) of a kilogram). -/
noncomputable def grams : MassUnit := scale ((1/10) ^ 3) kilograms

/-- The mass unit of (avoirdupois) ounces (0.028 349 523 125 of a kilogram). -/
noncomputable def ounces : MassUnit := scale (0.028349523125) kilograms

/-- The mass unit of (avoirdupois) pounds (0.453 592 37 of a kilogram). -/
noncomputable def pounds : MassUnit := scale (0.45359237) kilograms

/-- The mass unit of stones (14 pounds). -/
noncomputable def stones : MassUnit := scale (14) pounds

/-- The mass unit of a quarter (28 pounds). -/
noncomputable def quarters : MassUnit := scale (28) pounds

/-- The mass unit of hundredweights (112 pounds). -/
noncomputable def hundredweights : MassUnit := scale (112) pounds

/-- The mass unit of short tons (2000 pounds). -/
noncomputable def shortTons : MassUnit := scale (2000) pounds

/-- The mass unit of metric tons (1000 kilograms). -/
noncomputable def metricTons : MassUnit := scale (1000) kilograms

/-- The mass unit of long tons (2240 pounds). Also called shortweight tons. -/
noncomputable def longTons : MassUnit := scale (2240) pounds

/-- The mass unit of nominal solar masses (1.988416 × 10 ^ 30 kilograms).
  See: https://iopscience.iop.org/article/10.3847/0004-6256/152/2/41 -/
noncomputable def nominalSolarMasses : MassUnit := scale (1.988416e30) kilograms

/-!

## Relations between mass units

-/

lemma pounds_div_ounces : pounds / ounces = (16 : ℝ≥0) := NNReal.eq <| by
  simp [pounds, ounces]; norm_num

lemma shortTons_div_kilograms : shortTons / kilograms = (907.18474 : ℝ≥0) := NNReal.eq <| by
  simp [shortTons, pounds]; norm_num

lemma longTons_div_kilograms : longTons / kilograms = (1016.0469088 : ℝ≥0) := NNReal.eq <| by
  simp [longTons, pounds]; norm_num

end MassUnit
