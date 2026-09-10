/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Units.PositiveRealUnit
public import Mathlib.Analysis.RCLike.Basic
/-!

# Units on Temperature

A unit of temperature corresponds to a choice of translationally-invariant
metric on the temperature manifold (to be defined diffeomorphic to `ℝ≥0`).
Such a choice is (non-canonically) equivalent to a
choice of positive real number. We define the type `TemperatureUnit` to be equivalent to the
positive reals.

On `TemperatureUnit` there is an instance of division giving a real number, corresponding to the
ratio of the two scales of temperature unit.

To define specific temperature units, we first state the existence of a
a given temperature unit, and then construct all other temperature units from it.
We choose to state the
existence of the temperature unit of kelvin, and construct all other temperature units from that.

-/

@[expose] public section

open NNReal

/-- The choices of translationally-invariant metrics on the temperature-manifold.
  Such a choice corresponds to a choice of units for temperature. -/
structure TemperatureUnit where
  /-- The underlying scale of the unit. -/
  val : ℝ
  property : 0 < val

instance : PositiveRealUnitCore TemperatureUnit where
  val := TemperatureUnit.val
  pos := TemperatureUnit.property
  ofVal := fun r hr => ⟨r, hr⟩
  val_ofVal := by intros; rfl
  ofVal_val := by intro x; cases x; rfl
open NNReal

namespace TemperatureUnit

open PositiveRealUnitCore

/-!

## Specific choices of temperature units

To define a specific temperature units.
We first define the notion of a kelvin to correspond to the temperature unit with underlying value
equal to `1`. This is really down to a choice in the isomorphism between the set of metrics
on the temperature manifold and the positive reals.

Once we have defined kelvin, we can define other temperature units by scaling kelvin.

-/

/-- The definition of a temperature unit of kelvin. -/
def kelvin : TemperatureUnit := ⟨1, by norm_num⟩

/-- The temperature unit of degrees nanokelvin (10^(-9) kelvin). -/
noncomputable def nanokelvin : TemperatureUnit := scale (1e-9) kelvin

/-- The temperature unit of degrees microkelvin (10^(-6) kelvin). -/
noncomputable def microkelvin : TemperatureUnit := scale (1e-6) kelvin

/-- The temperature unit of degrees millikelvin (10^(-3) kelvin). -/
noncomputable def millikelvin : TemperatureUnit := scale (1e-3) kelvin

/-- The temperature unit of degrees fahrenheit ((5/9) of a kelvin).
  Note, this is fahrenheit starting at `0` absolute temperature. -/
noncomputable def absoluteFahrenheit : TemperatureUnit := scale (5 / 9) kelvin

end TemperatureUnit
