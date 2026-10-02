/-
Copyright (c) 2026 Nicolas Rouquette. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rouquette
-/
module

public import Physlib.Units.Dimension
public import Mathlib.Data.Fintype.Card
/-!

# The ISQ base quantities

The International System of Quantities (ISQ), specified in ISO/IEC 80000-1 and
described in the International Vocabulary of Metrology (VIM, 3rd edition,
JCGM 200:2012), fixes seven mutually independent *base quantities*: length, mass,
time, electric current, thermodynamic temperature, amount of substance, and
luminous intensity.

`ISQDimensionBase` is that seven-element basis, realised as an instantiation
`Dimension ISQDimensionBase` of the parametric dimensional algebra. It differs from
PhysLib's default `LTMCTDimensionBase` in two ways:

* the electromagnetic base quantity is *electric current*, so electric charge is a
  *derived* dimension (`Q = I · T`, `ISQDimensionBase.charge`); and
* *amount of substance* and *luminous intensity* are additional independent base
  quantities.

## References

* ISO/IEC 80000-1:2009, Quantities and units — Part 1: General. [ref: iso_80000_1_2009]
* JCGM 200:2012, International vocabulary of metrology — Basic and general concepts and associated
  terms (VIM, 3rd edition). [ref: jcgm_200_2012]
-/

@[expose] public section

open Dimension

/-- The seven ISQ base quantities (ISO/IEC 80000-1; VIM 3rd edition). Unlike
  `LTMCTDimensionBase`, electric current is the electromagnetic base quantity (so
  charge is derived), and amount of substance and luminous intensity are further
  base quantities. -/
inductive ISQDimensionBase where
  /-- The length base quantity. -/
  | length
  /-- The mass base quantity. -/
  | mass
  /-- The time base quantity. -/
  | time
  /-- The electric-current base quantity. -/
  | current
  /-- The thermodynamic-temperature base quantity. -/
  | temperature
  /-- The amount-of-substance base quantity. -/
  | amount
  /-- The luminous-intensity base quantity. -/
  | luminousIntensity
deriving DecidableEq

instance : Fintype ISQDimensionBase where
  elems := {.length, .mass, .time, .current, .temperature, .amount, .luminousIntensity}
  complete := fun x => by cases x <;> decide

instance : DimensionBasis ISQDimensionBase := DimensionBasis.pi _

namespace ISQDimensionBase

/-- The ISQ has seven base quantities. -/
lemma card_eq_seven : Fintype.card ISQDimensionBase = 7 := by decide

/-- Electric charge is a *derived* dimension in the ISQ: `Q = I · T`. -/
def charge : Dimension ISQDimensionBase := single .current * single .time

/-- The derived charge dimension has electric-current exponent `1`. -/
lemma charge_exponent_current : charge.exponent .current = 1 := by
  simp [charge, single_exponent]

/-- The derived charge dimension has time exponent `1`. -/
lemma charge_exponent_time : charge.exponent .time = 1 := by
  simp [charge, single_exponent]

/-- The derived charge dimension has mass exponent `0`. -/
lemma charge_exponent_mass : charge.exponent .mass = 0 := by
  simp [charge, single_exponent]

/-- Amount of substance is an independent base dimension (absent from
  `LTMCTDimensionBase`). -/
lemma single_amount_ne_one : single (.amount : ISQDimensionBase) ≠ 1 := by
  intro h
  have := congrArg (fun d => Dimension.exponent d .amount) h
  simp [single_exponent] at this

/-- Luminous intensity is an independent base dimension (absent from
  `LTMCTDimensionBase`). -/
lemma single_luminousIntensity_ne_one :
    single (.luminousIntensity : ISQDimensionBase) ≠ 1 := by
  intro h
  have := congrArg (fun d => Dimension.exponent d .luminousIntensity) h
  simp [single_exponent] at this

end ISQDimensionBase
