/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Units.PositiveRealUnit
public import Mathlib.Analysis.RCLike.Basic
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

## References

* The numerical value used for the nominal solar mass. [ref: nominal_solar_mass_article]

-/

@[expose] public section

open NNReal

/-- The choices of translationally-invariant metrics on the mass-manifold.
  Such a choice corresponds to a choice of units for mass. -/
structure MassUnit where
  /-- The underlying scale of the unit. -/
  val : ℝ
  property : 0 < val

instance : PositiveRealUnitCore MassUnit where
  val := MassUnit.val
  pos := MassUnit.property
  ofVal := fun r hr => ⟨r, hr⟩
  val_ofVal := by intros; rfl
  ofVal_val := by intro x; cases x; rfl
open NNReal

namespace MassUnit

open PositiveRealUnitCore

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
  See: https://iopscience.iop.org/article/10.3847/0004-6256/152/2/41 [ref: nominal_solar_mass_article] -/
noncomputable def nominalSolarMasses : MassUnit := scale (1.988416e30) kilograms

/-!

## Relations between mass units

-/

lemma pounds_div_ounces : pounds / ounces = (16 : ℝ≥0) := NNReal.eq <| by
  simp [pounds, ounces]
  show (0.45359237 : ℝ) / 0.028349523125 = ((16 : ℝ≥0) : ℝ)
  push_cast
  norm_num

lemma shortTons_div_kilograms : shortTons / kilograms = (907.18474 : ℝ≥0) := NNReal.eq <| by
  simp [shortTons, pounds]; rw [toReal]; norm_num

lemma longTons_div_kilograms : longTons / kilograms = (1016.0469088 : ℝ≥0) := NNReal.eq <| by
  simp [longTons, pounds]; rw [toReal]; norm_num

end MassUnit
