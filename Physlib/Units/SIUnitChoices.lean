/-
Copyright (c) 2026 Nicolas Rouquette. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rouquette
-/
module

public import Physlib.Units.UnitSystem
public import Physlib.Units.PositiveRealUnit
public import Physlib.Units.ISQDimensionBase
/-!

# A typed unit choice over the ISQ base quantities (the SI units)

`LTMCTUnitChoices` is the typed unit choice over PhysLib's default dimension basis
`LTMCTDimensionBase`. This module gives the *second* typed unit choice — over the
seven ISQ base quantities `ISQDimensionBase` — realised through the basis-generic
`UnitMagnitudeCatalog` / `UnitSystem` machinery of `Physlib.Units.UnitSystem`. It is the concrete
payoff of parametrising the unit side: the same generic layer produces a fully *typed*
unit choice over a different basis, and the scaling homomorphism comes for free from
`UnitScale.dimScale` — nothing is re-proved by hand.

The ISQ base quantities are length, mass, time, electric current, thermodynamic
temperature, amount of substance and luminous intensity. Four of the corresponding typed
unit types already exist (`LengthUnit`, `MassUnit`, `TimeUnit`, `TemperatureUnit`); the
remaining three — `CurrentUnit`, `AmountUnit`, `LuminousIntensityUnit` — are introduced
here. They follow the `LengthUnit` convention of a positive-real magnitude and support
rescaling and unit-ratio laws through `PositiveRealUnitCore`. Following PhysLib's
layout, these types may ultimately live under the relevant physics directories.

`SIUnitChoices := UnitSystem ISQDimensionBase` is then the typed SI unit choice, and
`SIUnitChoices.SI` is the coherent SI choice (metre, kilogram, second, ampere, kelvin,
mole, candela). Contrast `SIUnitChoices` (current-based, seven typed slots) with
`LTMCTUnitChoices` (charge-based, five typed slots): the machinery supports both, and the
`Dimension.ltmctToISQ` / `Dimension.isqToLTMCT` bridge relates their bases.

-/

@[expose] public section

open NNReal
open scoped BigOperators

/-!

## Typed unit types for the ISQ base quantities not already present

-/

/-- A unit of electric current — a choice of positive-real magnitude. The SI coherent
  choice is the ampere. -/
structure CurrentUnit where
  /-- The underlying scale of the unit. -/
  val : ℝ
  property : 0 < val

instance : PositiveRealUnitCore CurrentUnit where
  val := CurrentUnit.val
  pos := CurrentUnit.property
  ofVal := fun r hr => ⟨r, hr⟩
  val_ofVal := by intros; rfl
  ofVal_val := by intro x; cases x; rfl

namespace CurrentUnit

open PositiveRealUnitCore

/-- The SI coherent unit of electric current, the ampere. -/
def amperes : CurrentUnit := ⟨1, by norm_num⟩

/-- One milliampere, equal to `10⁻³` amperes. -/
noncomputable def milliamperes : CurrentUnit :=
  scale ((1 / 10) ^ 3) amperes

end CurrentUnit

/-- A unit of amount of substance — a choice of positive-real magnitude. The SI coherent
  choice is the mole. -/
structure AmountUnit where
  /-- The underlying scale of the unit. -/
  val : ℝ
  property : 0 < val

instance : PositiveRealUnitCore AmountUnit where
  val := AmountUnit.val
  pos := AmountUnit.property
  ofVal := fun r hr => ⟨r, hr⟩
  val_ofVal := by intros; rfl
  ofVal_val := by intro x; cases x; rfl

namespace AmountUnit

open PositiveRealUnitCore

/-- The SI coherent unit of amount of substance, the mole. -/
def moles : AmountUnit := ⟨1, by norm_num⟩

end AmountUnit

/-- A unit of luminous intensity — a choice of positive-real magnitude. The SI coherent
  choice is the candela. -/
structure LuminousIntensityUnit where
  /-- The underlying scale of the unit. -/
  val : ℝ
  property : 0 < val

instance : PositiveRealUnitCore LuminousIntensityUnit where
  val := LuminousIntensityUnit.val
  pos := LuminousIntensityUnit.property
  ofVal := fun r hr => ⟨r, hr⟩
  val_ofVal := by intros; rfl
  ofVal_val := by intro x; cases x; rfl

namespace LuminousIntensityUnit

open PositiveRealUnitCore

/-- The SI coherent unit of luminous intensity, the candela. -/
def candelas : LuminousIntensityUnit := ⟨1, by norm_num⟩

end LuminousIntensityUnit

/-!

## The ISQ `UnitMagnitudeCatalog` instance

Each ISQ base quantity is assigned its typed unit type; the magnitude layer is the
positive-real `val`, exactly as for the `LTMCTDimensionBase` instance.

-/

noncomputable instance : UnitMagnitudeCatalog ISQDimensionBase where
  Unit
    | .length => LengthUnit
    | .mass => MassUnit
    | .time => TimeUnit
    | .current => CurrentUnit
    | .temperature => TemperatureUnit
    | .amount => AmountUnit
    | .luminousIntensity => LuminousIntensityUnit
  mag {b} :=
    match b with
    | .length | .mass | .time | .current | .temperature | .amount | .luminousIntensity =>
        fun u => ⟨u.val, u.property.le⟩
  mag_pos {b} :=
    match b with
    | .length | .mass | .time | .current | .temperature | .amount | .luminousIntensity =>
        fun u => NNReal.coe_pos.mp u.property

/-!

## Folding over the ISQ base quantities

-/

open Finset in
/-- The product over the seven ISQ base quantities, in canonical enumeration order — the
  `ISQDimensionBase` companion to `prod_univ_LTMCTDimensionBase`, a reusable fact about the
  `Fintype` enumeration for folding `Finset.prod` over the ISQ basis. -/
lemma prod_univ_ISQDimensionBase {M : Type} [CommMonoid M] (f : ISQDimensionBase → M) :
    ∏ b, f b = f .length * f .mass * f .time * f .current * f .temperature
      * f .amount * f .luminousIntensity := by
  rw [show (univ : Finset ISQDimensionBase) =
        {.length, .mass, .time, .current, .temperature, .amount, .luminousIntensity} from by
      decide]
  rw [prod_insert (by decide), prod_insert (by decide), prod_insert (by decide),
    prod_insert (by decide), prod_insert (by decide), prod_insert (by decide), prod_singleton,
    ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc]

/-!

## `SIUnitChoices`

-/

/-- A **typed SI unit choice**: a typed unit at every ISQ base quantity. This is the
  seven-slot, current-based sibling of the five-slot, charge-based `LTMCTUnitChoices`,
  produced by the same basis-generic `UnitSystem` / `UnitMagnitudeCatalog` machinery. -/
abbrev SIUnitChoices := UnitSystem ISQDimensionBase

namespace SIUnitChoices

/-- The coherent SI unit choice: metre, kilogram, second, ampere, kelvin, mole, candela. -/
noncomputable def SI : SIUnitChoices := fun
  | .length => LengthUnit.meters
  | .mass => MassUnit.kilograms
  | .time => TimeUnit.seconds
  | .current => CurrentUnit.amperes
  | .temperature => TemperatureUnit.kelvin
  | .amount => AmountUnit.moles
  | .luminousIntensity => LuminousIntensityUnit.candelas

/-- The dimension-scaling homomorphism over the ISQ basis, obtained *for free* from the
  generic `UnitScale.dimScale` fold — no per-basis hand-rolling. -/
noncomputable def dimScale (u1 u2 : SIUnitChoices) : Dimension ISQDimensionBase →* ℝ≥0 :=
  UnitScale.dimScale u1.toScale u2.toScale

/-- Type-safety check: the current slot of a typed SI unit choice is a `CurrentUnit` —
  a `MassUnit` cannot be placed there. -/
example (u : SIUnitChoices) : CurrentUnit := u .current

/-- A quantity of ISQ dimension does not rescale between a unit choice and itself. -/
lemma dimScale_self (u : SIUnitChoices) (d : Dimension ISQDimensionBase) :
    dimScale u u d = 1 := UnitScale.dimScale_self _ d

end SIUnitChoices
