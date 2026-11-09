/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Units.Dimension
/-!

# PhysLib's default dimension basis

`LTMCTDimensionBase` is PhysLib's default basis of base dimensions — length, time,
mass, charge and temperature. `Dimension LTMCTDimensionBase` is the familiar
five-exponent dimension, and this module provides the concrete API on top of the
generic `Dimension B`:

* the `.length`, `.time`, `.mass`, `.charge`, `.temperature` exponent projections;
* the `ofLTMCTDimensionBase` constructor from five exponents; and
* the named generators `L𝓭`, `T𝓭`, `M𝓭`, `C𝓭`, `Θ𝓭`, shown to be the generic
  `single` base vectors.

This basis is *charge*-based with five generators, so it is deliberately **not** the
SI/ISQ base-quantity set (which takes electric current as base and adds amount of
substance and luminous intensity); see `ISQDimensionBase`.

-/

@[expose] public section

/-- PhysLib's default basis of base dimensions — `length`, `time`, `mass`,
  `charge`, `temperature`. Note this is *charge*-based, so it is not the SI/ISQ
  base-quantity set; see `Dimension`. -/
inductive LTMCTDimensionBase where
  /-- The length base dimension. -/
  | length
  /-- The time base dimension. -/
  | time
  /-- The mass base dimension. -/
  | mass
  /-- The charge base dimension. -/
  | charge
  /-- The temperature base dimension. -/
  | temperature
deriving DecidableEq

namespace LTMCTDimensionBase

instance : Fintype LTMCTDimensionBase where
  elems := {.length, .time, .mass, .charge, .temperature}
  complete := fun x => by cases x <;> decide

open Dimension in
/-- The fixed five-component exponent tuple for PhysLib's default dimension basis. -/
abbrev Exponents := Exponent × Exponent × Exponent × Exponent × Exponent

instance : DimensionBasis LTMCTDimensionBase where
  Exponents := Exponents
  addCommGroup := inferInstance
  exponentEquiv :=
    { toFun := fun ⟨l, t, m, c, temp⟩ => fun
        | .length => l | .time => t | .mass => m | .charge => c | .temperature => temp
      invFun f := ⟨f .length, f .time, f .mass, f .charge, f .temperature⟩
      left_inv e := by rcases e; rfl
      right_inv f := by funext b; cases b <;> rfl
      map_add' _ _ := by funext b; cases b <;> rfl }

end LTMCTDimensionBase

namespace Dimension

/-!

## The LTMCTDimensionBase projections

The five base-dimension exponents of a `Dimension LTMCTDimensionBase`, provided so that
the familiar `.length`, `.time`, `.mass`, `.charge`, `.temperature` API is available.

-/

/-- The length exponent of a `LTMCTDimensionBase` dimension. -/
def length (d : Dimension LTMCTDimensionBase) : Exponent := d.exponents.1
/-- The time exponent of a `LTMCTDimensionBase` dimension. -/
def time (d : Dimension LTMCTDimensionBase) : Exponent := d.exponents.2.1
/-- The mass exponent of a `LTMCTDimensionBase` dimension. -/
def mass (d : Dimension LTMCTDimensionBase) : Exponent := d.exponents.2.2.1
/-- The charge exponent of a `LTMCTDimensionBase` dimension. -/
def charge (d : Dimension LTMCTDimensionBase) : Exponent := d.exponents.2.2.2.1
/-- The temperature exponent of a `LTMCTDimensionBase` dimension. -/
def temperature (d : Dimension LTMCTDimensionBase) : Exponent := d.exponents.2.2.2.2

@[simp]
lemma exponent_length (d : Dimension LTMCTDimensionBase) : d.exponent .length = d.length := rfl

@[simp]
lemma exponent_time (d : Dimension LTMCTDimensionBase) : d.exponent .time = d.time := rfl

@[simp]
lemma exponent_mass (d : Dimension LTMCTDimensionBase) : d.exponent .mass = d.mass := rfl

@[simp]
lemma exponent_charge (d : Dimension LTMCTDimensionBase) : d.exponent .charge = d.charge := rfl

@[simp]
lemma exponent_temperature (d : Dimension LTMCTDimensionBase) :
    d.exponent .temperature = d.temperature := rfl

/-- Build a `LTMCTDimensionBase` dimension from its five exponents, in the order
  `⟨length, time, mass, charge, temperature⟩`. -/
def ofLTMCTDimensionBase (length time mass charge temperature : Exponent) :
    Dimension LTMCTDimensionBase :=
  ⟨(length, time, mass, charge, temperature)⟩

@[simp]
lemma ofLTMCTDimensionBase_length (l t m c θ : Exponent) :
    (ofLTMCTDimensionBase l t m c θ).length = l := rfl

@[simp]
lemma ofLTMCTDimensionBase_time (l t m c θ : Exponent) :
    (ofLTMCTDimensionBase l t m c θ).time = t := rfl

@[simp]
lemma ofLTMCTDimensionBase_mass (l t m c θ : Exponent) :
    (ofLTMCTDimensionBase l t m c θ).mass = m := rfl

@[simp]
lemma ofLTMCTDimensionBase_charge (l t m c θ : Exponent) :
    (ofLTMCTDimensionBase l t m c θ).charge = c := rfl

@[simp]
lemma ofLTMCTDimensionBase_temperature (l t m c θ : Exponent) :
    (ofLTMCTDimensionBase l t m c θ).temperature = θ := rfl

@[simp]
lemma time_mul (d1 d2 : Dimension LTMCTDimensionBase) :
    (d1 * d2).time = d1.time + d2.time := rfl

@[simp]
lemma length_mul (d1 d2 : Dimension LTMCTDimensionBase) :
    (d1 * d2).length = d1.length + d2.length := rfl

@[simp]
lemma mass_mul (d1 d2 : Dimension LTMCTDimensionBase) :
    (d1 * d2).mass = d1.mass + d2.mass := rfl

@[simp]
lemma charge_mul (d1 d2 : Dimension LTMCTDimensionBase) :
    (d1 * d2).charge = d1.charge + d2.charge := rfl

@[simp]
lemma temperature_mul (d1 d2 : Dimension LTMCTDimensionBase) :
    (d1 * d2).temperature = d1.temperature + d2.temperature := rfl

@[simp]
lemma one_length : (1 : Dimension LTMCTDimensionBase).length = 0 := rfl
@[simp]
lemma one_time : (1 : Dimension LTMCTDimensionBase).time = 0 := rfl

@[simp]
lemma one_mass : (1 : Dimension LTMCTDimensionBase).mass = 0 := rfl

@[simp]
lemma one_charge : (1 : Dimension LTMCTDimensionBase).charge = 0 := rfl

@[simp]
lemma one_temperature : (1 : Dimension LTMCTDimensionBase).temperature = 0 := rfl

@[simp]
lemma inv_length (d : Dimension LTMCTDimensionBase) : d⁻¹.length = -d.length := rfl

@[simp]
lemma inv_time (d : Dimension LTMCTDimensionBase) : d⁻¹.time = -d.time := rfl

@[simp]
lemma inv_mass (d : Dimension LTMCTDimensionBase) : d⁻¹.mass = -d.mass := rfl

@[simp]
lemma inv_charge (d : Dimension LTMCTDimensionBase) : d⁻¹.charge = -d.charge := rfl

@[simp]
lemma inv_temperature (d : Dimension LTMCTDimensionBase) : d⁻¹.temperature = -d.temperature := rfl

private lemma component_npow (component : Dimension LTMCTDimensionBase → Exponent)
    (b : LTMCTDimensionBase) (h : ∀ d, d.exponent b = component d)
    (d : Dimension LTMCTDimensionBase) (n : ℕ) :
    component (d ^ n) = n • component d := by
  calc
    component (d ^ n) = (d ^ n).exponent b := (h _).symm
    _ = n • d.exponent b := npow_exponent d n b
    _ = n • component d := congrArg (n • ·) (h _)

lemma component_epow (component : Dimension LTMCTDimensionBase → Exponent)
    (b : LTMCTDimensionBase) (h : ∀ d, d.exponent b = component d)
    (d : Dimension LTMCTDimensionBase) (c : Exponent) :
    component (d ^ c) = component d * c := by
  calc
    component (d ^ c) = (d ^ c).exponent b := (h _).symm
    _ = d.exponent b * c := epow_exponent d c b
    _ = component d * c := congrArg (· * c) (h _)

@[simp]
lemma div_length (d1 d2 : Dimension LTMCTDimensionBase) :
    (d1 / d2).length = d1.length - d2.length := rfl

@[simp]
lemma div_time (d1 d2 : Dimension LTMCTDimensionBase) : (d1 / d2).time = d1.time - d2.time := rfl

@[simp]
lemma div_mass (d1 d2 : Dimension LTMCTDimensionBase) : (d1 / d2).mass = d1.mass - d2.mass := rfl

@[simp]
lemma div_charge (d1 d2 : Dimension LTMCTDimensionBase) :
    (d1 / d2).charge = d1.charge - d2.charge := rfl

@[simp]
lemma div_temperature (d1 d2 : Dimension LTMCTDimensionBase) :
    (d1 / d2).temperature = d1.temperature - d2.temperature := rfl

@[simp]
lemma npow_length (d : Dimension LTMCTDimensionBase) (n : ℕ) : (d ^ n).length = n • d.length := by
  exact component_npow length .length exponent_length d n

@[simp]
lemma npow_time (d : Dimension LTMCTDimensionBase) (n : ℕ) : (d ^ n).time = n • d.time := by
  exact component_npow time .time exponent_time d n

@[simp]
lemma npow_mass (d : Dimension LTMCTDimensionBase) (n : ℕ) : (d ^ n).mass = n • d.mass := by
  exact component_npow mass .mass exponent_mass d n

@[simp]
lemma npow_charge (d : Dimension LTMCTDimensionBase) (n : ℕ) : (d ^ n).charge = n • d.charge := by
  exact component_npow charge .charge exponent_charge d n

@[simp]
lemma npow_temperature (d : Dimension LTMCTDimensionBase) (n : ℕ) :
    (d ^ n).temperature = n • d.temperature := by
  exact component_npow temperature .temperature exponent_temperature d n

/-- The length component of an `Exponent` power. Since `Pow (Dimension B) Exponent` is the
  default instance, an unascribed numeric exponent elaborates to this power rather than to
  the `ℕ` one, so `npow_length` does not apply to it and this lemma is what `simp` needs. -/
@[simp]
lemma epow_length (d : Dimension LTMCTDimensionBase) (c : Exponent) :
    (d ^ c).length = d.length * c := by
  exact component_epow length .length exponent_length d c

/-- The time component of an `Exponent` power. -/
@[simp]
lemma epow_time (d : Dimension LTMCTDimensionBase) (c : Exponent) :
    (d ^ c).time = d.time * c := by
  exact component_epow time .time exponent_time d c

/-- The mass component of an `Exponent` power. -/
@[simp]
lemma epow_mass (d : Dimension LTMCTDimensionBase) (c : Exponent) :
    (d ^ c).mass = d.mass * c := by
  exact component_epow mass .mass exponent_mass d c

/-- The charge component of an `Exponent` power. -/
@[simp]
lemma epow_charge (d : Dimension LTMCTDimensionBase) (c : Exponent) :
    (d ^ c).charge = d.charge * c := by
  exact component_epow charge .charge exponent_charge d c

/-- The temperature component of an `Exponent` power. -/
@[simp]
lemma epow_temperature (d : Dimension LTMCTDimensionBase) (c : Exponent) :
    (d ^ c).temperature = d.temperature * c := by
  exact component_epow temperature .temperature exponent_temperature d c

/-- The dimension corresponding to length. -/
def L𝓭 : Dimension LTMCTDimensionBase := ofLTMCTDimensionBase 1 0 0 0 0

@[simp]
lemma L𝓭_length : L𝓭.length = 1 := by rfl

@[simp]
lemma L𝓭_time : L𝓭.time = 0 := by rfl

@[simp]
lemma L𝓭_mass : L𝓭.mass = 0 := by rfl

@[simp]
lemma L𝓭_charge : L𝓭.charge = 0 := by rfl

@[simp]
lemma L𝓭_temperature : L𝓭.temperature = 0 := by rfl

/-- The dimension corresponding to time. -/
def T𝓭 : Dimension LTMCTDimensionBase := ofLTMCTDimensionBase 0 1 0 0 0

@[simp]
lemma T𝓭_length : T𝓭.length = 0 := by rfl

@[simp]
lemma T𝓭_time : T𝓭.time = 1 := by rfl

@[simp]
lemma T𝓭_mass : T𝓭.mass = 0 := by rfl

@[simp]
lemma T𝓭_charge : T𝓭.charge = 0 := by rfl

@[simp]
lemma T𝓭_temperature : T𝓭.temperature = 0 := by rfl

/-- The dimension corresponding to mass. -/
def M𝓭 : Dimension LTMCTDimensionBase := ofLTMCTDimensionBase 0 0 1 0 0

@[simp]
lemma M𝓭_length : M𝓭.length = 0 := by rfl

@[simp]
lemma M𝓭_time : M𝓭.time = 0 := by rfl

@[simp]
lemma M𝓭_mass : M𝓭.mass = 1 := by rfl

@[simp]
lemma M𝓭_charge : M𝓭.charge = 0 := by rfl

@[simp]
lemma M𝓭_temperature : M𝓭.temperature = 0 := by rfl

/-- The dimension corresponding to charge. -/
def C𝓭 : Dimension LTMCTDimensionBase := ofLTMCTDimensionBase 0 0 0 1 0

/-- The dimension corresponding to temperature. -/
def Θ𝓭 : Dimension LTMCTDimensionBase := ofLTMCTDimensionBase 0 0 0 0 1

@[simp]
lemma Θ𝓭_length : Θ𝓭.length = 0 := by rfl

@[simp]
lemma Θ𝓭_time : Θ𝓭.time = 0 := by rfl

@[simp]
lemma Θ𝓭_mass : Θ𝓭.mass = 0 := by rfl

@[simp]
lemma Θ𝓭_charge : Θ𝓭.charge = 0 := by rfl

@[simp]
lemma Θ𝓭_temperature : Θ𝓭.temperature = 1 := by rfl

/-!

## The named generators are the base vectors

Each named generator `L𝓭`, `T𝓭`, … is the generic `single` base vector at the
corresponding base dimension, exhibiting them as instances of the basis-generic API.

-/

lemma L𝓭_eq_single : L𝓭 = single .length := rfl

lemma T𝓭_eq_single : T𝓭 = single .time := rfl

lemma M𝓭_eq_single : M𝓭 = single .mass := rfl

lemma C𝓭_eq_single : C𝓭 = single .charge := rfl

lemma Θ𝓭_eq_single : Θ𝓭 = single .temperature := rfl

end Dimension
