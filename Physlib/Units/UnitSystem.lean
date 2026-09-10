/-
Copyright (c) 2026 Nicolas Rouquette. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rouquette
-/
module

public import Physlib.Units.ParametricUnits
/-!

# Unit systems, parametrised in a dimension basis

A **unit system** is the everyday physics object: a rule fixing one concrete unit for
each base quantity. SI fixes the metre for length, the second for time, the kilogram for
mass, …; CGS fixes the centimetre, second and gram. Choosing a system gives every quantity
a numerical value; changing systems rescales those values.

This module makes that notion work for *any* dimension basis `B` (matching the
basis-generic `Dimension B`), while keeping units *typed*: the unit in the length slot has
type `LengthUnit`, the one in the time slot `TimeUnit`, so the checker rejects a mass unit
in a length slot.

* `UnitMagnitudeCatalog B` — the **menu** for basis `B`. For each base dimension `b : B` it
  gives a *type* `Unit b` of admissible units — so a dimension may offer many (length: metre,
  kilometre, micrometre, …) — and a *function* `mag` assigning each unit its one positive-real
  magnitude. The menu lists the options and picks none; many unit systems share one catalog.
* `UnitSystem B` — the **pick**: a function choosing *exactly one* unit per base dimension. A
  single unit system therefore fixes one length unit — metre *or* kilometre, never both — so
  metre and kilometre are two menu entries selected by two different `UnitSystem`s over the
  same catalog. SI and CGS are two such picks.
* `UnitSystem.toScale : UnitSystem B → UnitScale B` — forget the unit *types*, keep only
  the magnitudes, landing in the bare magnitude layer `UnitScale B` where the scaling
  homomorphism `UnitScale.dimScale` is proved once.

**Menu vs. pick.** The catalog is a menu, not a choice: it says which units exist and what
each weighs, but selects none — a `UnitSystem` makes the selection. And in PhysLib a base
unit *is* a positive real (`{ val : ℝ // 0 < val }`), i.e. its own magnitude, so the
magnitude comes fixed with the unit; there is no separate "assign a magnitude" step. Hence
metre, micrometre and kilometre are three *different* units on the one length menu, and
"SI in metres" versus "the same in micrometres" are two different `UnitSystem`s over the
**same** catalog — related by `UnitScale.dimScale`, which computes the 10⁶ factor between
them. (The multiplicity one might expect from "many magnitudes" lives here, among the unit
systems, not in many catalogs.)

The `LTMCTDimensionBase` catalog recovers PhysLib's five named unit types, and
`LTMCTUnitChoices ≃ UnitSystem LTMCTDimensionBase` exhibits the bespoke five-field record
as that instance. Scaling laws are **not** re-proved here — they live once on `UnitScale B`,
and the typed layer is a thin faithful wrapper projecting onto it via `toScale`.

This is the typed, basis-generic layer discussed as "Option D" in the review of the
dimension-parametrisation PR; it is the only design that keeps *both* basis-genericity and
typed-unit safety.

-/

@[expose] public section

open NNReal
open scoped BigOperators

/-- A **menu of typed units** for a basis `B`: for each base dimension `b : B`, a *type*
  `Unit b` of admissible units (a dimension may offer several — metre, kilometre, …) and a
  *function* `mag` giving each its single positive-real magnitude. It lists the options and
  picks none — a `UnitSystem` makes the pick. One catalog underlies many unit systems (SI,
  CGS, …); the magnitude is the data `toScale` reads to drive rescaling. -/
class UnitMagnitudeCatalog (B : Type) where
  /-- The typed unit type at each base dimension. -/
  Unit : B → Type
  /-- The positive-real magnitude of a typed unit. -/
  mag : {b : B} → Unit b → ℝ≥0
  /-- Every typed unit has a positive magnitude. -/
  mag_pos : ∀ {b : B} (u : Unit b), 0 < mag u

/-- A **unit system** over a basis `B` with a `UnitMagnitudeCatalog`: one typed unit chosen
  per base dimension — the pick off the catalog's menu, and the formal counterpart of SI,
  CGS, …. Over the default basis, `u .length : LengthUnit`, and a `MassUnit` cannot be
  placed in the length slot. -/
def UnitSystem (B : Type) [UnitMagnitudeCatalog B] := (b : B) → UnitMagnitudeCatalog.Unit b

namespace UnitSystem

variable {B : Type} [UnitMagnitudeCatalog B]

/-- Two unit systems agree once they pick the same unit at every base dimension: `UnitSystem`
  is extensional, as befits a choice-per-dimension. -/
@[ext]
theorem ext {u v : UnitSystem B} (h : ∀ b, u b = v b) : u = v := funext h

/-- Forget a unit system to its magnitude layer `UnitScale B`: keep each chosen unit's
  magnitude, drop its type — the layer where `UnitScale.dimScale` is already proved. -/
noncomputable def toScale (u : UnitSystem B) : UnitScale B where
  scale b := UnitMagnitudeCatalog.mag (u b)
  scale_pos b := UnitMagnitudeCatalog.mag_pos (u b)

@[simp]
lemma toScale_scale (u : UnitSystem B) (b : B) :
    (toScale u).scale b = UnitMagnitudeCatalog.mag (u b) := rfl

end UnitSystem

/-!

## The `LTMCTDimensionBase` catalog

The default basis's `UnitMagnitudeCatalog` recovers exactly PhysLib's five named typed unit
types, so `UnitSystem LTMCTDimensionBase` is the typed five-slot unit system and
`u .length : LengthUnit`, `LengthUnit.meters`, … all still work — and a `MassUnit` cannot
be placed in the length slot.

-/

noncomputable instance : UnitMagnitudeCatalog LTMCTDimensionBase where
  Unit
    | .length => LengthUnit
    | .time => TimeUnit
    | .mass => MassUnit
    | .charge => ChargeUnit
    | .temperature => TemperatureUnit
  mag {b} :=
    match b with
    | .length | .time | .mass | .charge | .temperature => fun u => ⟨u.val, u.property.le⟩
  mag_pos {b} :=
    match b with
    | .length | .time | .mass | .charge | .temperature => fun u => NNReal.coe_pos.mp u.property

/-- Type-safety check: a unit system over `LTMCTDimensionBase` projects onto the named typed
  unit types, so the length slot is a `LengthUnit` (and cannot hold a `MassUnit`). -/
example (u : UnitSystem LTMCTDimensionBase) : LengthUnit := u .length

example : UnitSystem LTMCTDimensionBase := fun
  | .length => LengthUnit.meters
  | .time => TimeUnit.seconds
  | .mass => MassUnit.kilograms
  | .charge => ChargeUnit.coulombs
  | .temperature => TemperatureUnit.kelvin

/-!

## `LTMCTUnitChoices` is `UnitSystem LTMCTDimensionBase`

The bespoke five-field record and the generic unit system over the default basis carry
the same data.

-/

namespace LTMCTUnitChoices

/-- The bespoke five-field `LTMCTUnitChoices` and the generic `UnitSystem LTMCTDimensionBase`
  are the same data. -/
def equivUnitSystem : LTMCTUnitChoices ≃ UnitSystem LTMCTDimensionBase where
  toFun u := fun
    | .length => u.length
    | .time => u.time
    | .mass => u.mass
    | .charge => u.charge
    | .temperature => u.temperature
  invFun f :=
    { length := f .length
      time := f .time
      mass := f .mass
      charge := f .charge
      temperature := f .temperature }
  left_inv u := by cases u; rfl
  right_inv f := by funext b; cases b <;> rfl

/-- The typed generic projection agrees with the bespoke `LTMCTUnitChoices.toScale`: reading
  `LTMCTUnitChoices` as a `UnitSystem` and forgetting to the magnitude layer is the same as
  the bespoke `toScale`. -/
lemma toScale_equivUnitSystem (u : LTMCTUnitChoices) :
    (equivUnitSystem u).toScale = u.toScale := by
  refine UnitScale.ext ?_
  funext b
  cases b <;> rfl

end LTMCTUnitChoices

/-!

## The bespoke scaling law is the generic fold

`LTMCTUnitChoices.dimScale` — the five explicit `rpow` factors written out by hand in
`Basic.lean` — is exactly the generic `UnitScale.dimScale` fold (a `Finset.prod` over the
basis) at the `LTMCTDimensionBase` instance, applied to `toScale`. This is what makes the
typed layer a *faithful* wrapper rather than a second, independent statement of the
scaling law: there is one source of truth, the generic fold on `UnitScale B`.

-/

open Finset in
/-- The product over the five default base quantities, in canonical enumeration order — a
  reusable fact about the `Fintype` enumeration of `LTMCTDimensionBase`, for folding
  `Finset.prod` over the default basis (e.g. in a hand-rolled scaling law). -/
lemma prod_univ_LTMCTDimensionBase {M : Type} [CommMonoid M]
    (f : LTMCTDimensionBase → M) :
    ∏ b, f b = f .length * f .time * f .mass * f .charge * f .temperature := by
  rw [show (univ : Finset LTMCTDimensionBase)
        = {.length, .time, .mass, .charge, .temperature} from by decide]
  rw [prod_insert (by decide), prod_insert (by decide), prod_insert (by decide),
    prod_insert (by decide), prod_singleton, ← mul_assoc, ← mul_assoc, ← mul_assoc]

namespace LTMCTUnitChoices

private lemma length_ratio (u1 u2 : LTMCTUnitChoices) :
    u1.length / u2.length = u1.toScale.scale .length / u2.toScale.scale .length := by
  apply NNReal.eq; rw [PositiveRealUnitCore.div_eq_val, NNReal.coe_div]; rfl

private lemma time_ratio (u1 u2 : LTMCTUnitChoices) :
    u1.time / u2.time = u1.toScale.scale .time / u2.toScale.scale .time := by
  apply NNReal.eq; rw [PositiveRealUnitCore.div_eq_val, NNReal.coe_div]; rfl

private lemma mass_ratio (u1 u2 : LTMCTUnitChoices) :
    u1.mass / u2.mass = u1.toScale.scale .mass / u2.toScale.scale .mass := by
  apply NNReal.eq; rw [PositiveRealUnitCore.div_eq_val, NNReal.coe_div]; rfl

private lemma charge_ratio (u1 u2 : LTMCTUnitChoices) :
    u1.charge / u2.charge = u1.toScale.scale .charge / u2.toScale.scale .charge := by
  apply NNReal.eq; rw [PositiveRealUnitCore.div_eq_val, NNReal.coe_div]; rfl

private lemma temperature_ratio (u1 u2 : LTMCTUnitChoices) :
    u1.temperature / u2.temperature =
      u1.toScale.scale .temperature / u2.toScale.scale .temperature := by
  apply NNReal.eq; rw [PositiveRealUnitCore.div_eq_val, NNReal.coe_div]; rfl

/-- The hand-rolled five-factor `LTMCTUnitChoices.dimScale` equals the basis-generic
  `UnitScale.dimScale` fold at `LTMCTDimensionBase`, applied to `toScale`. The scaling law
  therefore has a single source of truth on the magnitude layer `UnitScale B`. -/
lemma dimScale_eq_toScale_dimScale (u1 u2 : LTMCTUnitChoices) (d : Dimension LTMCTDimensionBase) :
    u1.dimScale u2 d = UnitScale.dimScale u1.toScale u2.toScale d := by
  rw [dimScale_apply, length_ratio, time_ratio, mass_ratio, charge_ratio, temperature_ratio,
    UnitScale.dimScale, MonoidHom.coe_mk, OneHom.coe_mk, prod_univ_LTMCTDimensionBase]
  simp only [Dimension.length, Dimension.time, Dimension.mass, Dimension.charge,
    Dimension.temperature, Dimension.exponent_length, Dimension.exponent_time,
    Dimension.exponent_mass, Dimension.exponent_charge, Dimension.exponent_temperature]

end LTMCTUnitChoices
