/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.SpaceAndTime.Time.TimeUnit
import PhysLean.SpaceAndTime.Space.LengthUnit
import PhysLean.ClassicalMechanics.Mass.MassUnit
import PhysLean.Electromagnetism.Charge.ChargeUnit
import PhysLean.Thermodynamics.Temperature.TemperatureUnits
import PhysLean.Units.Dimension
/-!

# Dimensions and unit

A unit in physics arises from choice of something in physics which is non-canonical.
An example is the choice of translationally-invariant metric on the time manifold `TimeMan`.

A dimension is a property of a quantity related to how it changes with respect to a
change in the unit.

The fundamental choices one has in physics are related to:
- Time
- Length
- Mass
- Charge
- Temperature

(In fact temperature is not really a fundamental choice, however we leave this as a `TODO`.)

From these fundamental choices one can construct all other units and dimensions.

## Implementation details

Units within PhysLean are implemented with the following convention:
- The fundamental units, and the choices they correspond to, are defined within the
  appropriate physics directory, in particular:
  - `PhysLean/SpaceAndTime/Time/TimeUnit.lean`
  - `PhysLean/SpaceAndTime/Space/LengthUnit.lean`
  - `PhysLean/ClassicalMechanics/Mass/MassUnit.lean`
  - `PhysLean/Electromagnetism/Charge/ChargeUnit.lean`
  - `PhysLean/Thermodynamics/Temperature/TemperatureUnit.lean`
- In this `Units` directory, we define the necessary structures and properties
  to work derived units and dimensions.

## References

Zulip chats discussing units:
- https://leanprover.zulipchat.com/#narrow/channel/479953-PhysLean/topic/physical.20units
- https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/Dimensional.20Analysis.20Revisited/with/530238303

## Note

A lot of the results around units is still experimental and should be adapted based on needs.

## Other implementations of units

There are other implementations of units in Lean, in particular:
1. https://github.com/ATOMSLab/LeanDimensionalAnalysis/tree/main
2. https://github.com/teorth/analysis/blob/main/analysis/Analysis/Misc/SI.lean
3. https://github.com/ecyrbe/lean-units
Each of these have their own advantages and specific use-cases.
For example both (1) and (3) allow for or work in Floats, allowing computability and the use
of `#eval`. This is currently not possible with the more theoretical implementation here
in PhysLean which is based exclusively on Reals.

-/

/-!

## Units

-/
open NNReal

/-- The choice of units. -/
@[ext]
structure UnitChoices where
  /-- The length unit. -/
  length : LengthUnit
  /-- The time unit. -/
  time : TimeUnit
  /-- The mass unit. -/
  mass : MassUnit
  /-- The charge unit. -/
  charge : ChargeUnit
  /-- The temperature unit. -/
  temperature : TemperatureUnit

namespace UnitChoices

/-- Given two choices of units `u1` and `u2` and a dimension `d`, the
  element of `ℝ≥0` corresponding to the scaling (by definition) of a quantity of dimension `d`
  when changing from units `u1` to `u2`. -/
noncomputable def dimScale (u1 u2 : UnitChoices) :Dimension →* ℝ≥0 where
  toFun d :=
    (u1.length / u2.length) ^ (d.length : ℝ) *
    (u1.time / u2.time) ^ (d.time : ℝ) *
    (u1.mass / u2.mass) ^ (d.mass : ℝ) *
    (u1.charge / u2.charge) ^ (d.charge : ℝ) *
    (u1.temperature / u2.temperature) ^ (d.temperature : ℝ)
  map_one' := by
    simp
  map_mul' d1 d2 := by
    simp only [Dimension.length_mul, Rat.cast_add, Dimension.time_mul, Dimension.mass_mul,
      Dimension.charge_mul, Dimension.temperature_mul]
    repeat rw [rpow_add]
    ring
    all_goals
      simp

lemma dimScale_apply (u1 u2 : UnitChoices) (d : Dimension) :
    dimScale u1 u2 d =
      (u1.length / u2.length) ^ (d.length : ℝ) *
      (u1.time / u2.time) ^ (d.time : ℝ) *
      (u1.mass / u2.mass) ^ (d.mass : ℝ) *
      (u1.charge / u2.charge) ^ (d.charge : ℝ) *
      (u1.temperature / u2.temperature) ^ (d.temperature : ℝ) := rfl

@[simp]
lemma dimScale_self (u : UnitChoices) (d : Dimension) :
    dimScale u u d = 1 := by
  simp [dimScale]

@[simp]
lemma dimScale_one (u1 u2 : UnitChoices) :
    dimScale u1 u2 1 = 1 := by
  simp [dimScale]

lemma dimScale_transitive (u1 u2 u3 : UnitChoices) (d : Dimension) :
    dimScale u1 u2 d * dimScale u2 u3 d = dimScale u1 u3 d := by
  simp [dimScale]
  trans ((u1.length / u2.length) ^ (d.length : ℝ) * (u2.length / u3.length) ^ (d.length : ℝ)) *
    ((u1.time / u2.time) ^ (d.time : ℝ) * (u2.time / u3.time) ^ (d.time : ℝ)) *
    ((u1.mass / u2.mass) ^ (d.mass : ℝ) * (u2.mass / u3.mass) ^ (d.mass : ℝ)) *
    ((u1.charge / u2.charge) ^ (d.charge : ℝ) * (u2.charge / u3.charge) ^ (d.charge : ℝ)) *
    ((u1.temperature / u2.temperature) ^ (d.temperature : ℝ) *
      (u2.temperature / u3.temperature) ^ (d.temperature : ℝ))
  · ring
  repeat rw [← mul_rpow]
  apply NNReal.eq
  simp only [LengthUnit.div_eq_val, TimeUnit.div_eq_val, MassUnit.div_eq_val, ChargeUnit.div_eq_val,
    TemperatureUnit.div_eq_val, NNReal.coe_mul, coe_rpow, coe_mk]
  field_simp

@[simp]
lemma dimScale_mul_symm (u1 u2 : UnitChoices) (d : Dimension) :
    dimScale u1 u2 d * dimScale u2 u1 d = 1 := by
  rw [dimScale_transitive, dimScale_self]

@[simp]
lemma dimScale_coe_mul_symm (u1 u2 : UnitChoices) (d : Dimension) :
    (toReal (dimScale u1 u2 d)) * (toReal (dimScale u2 u1 d)) = 1 := by
  trans toReal (dimScale u1 u2 d * dimScale u2 u1 d)
  · rw [NNReal.coe_mul]
  simp

@[simp]
lemma dimScale_ne_zero (u1 u2 : UnitChoices) (d : Dimension) :
    dimScale u1 u2 d ≠ 0 := by
  simp [dimScale]

lemma dimScale_symm (u1 u2 : UnitChoices) (d : Dimension) :
    dimScale u1 u2 d = (dimScale u2 u1 d)⁻¹ := by
  simp only [dimScale_apply, mul_inv]
  congr
  · rw [LengthUnit.div_symm, inv_rpow]
  · rw [TimeUnit.div_symm, inv_rpow]
  · rw [MassUnit.div_symm, inv_rpow]
  · rw [ChargeUnit.div_symm, inv_rpow]
  · rw [TemperatureUnit.div_symm, inv_rpow]

lemma dimScale_of_inv_eq_swap (u1 u2 : UnitChoices) (d : Dimension) :
    dimScale u1 u2 d⁻¹ = dimScale u2 u1 d := by
  simp only [map_inv]
  conv_rhs => rw[dimScale_symm]

@[simp]
lemma smul_dimScale_injective {M : Type} [MulAction ℝ≥0 M] (u1 u2 : UnitChoices) (d : Dimension)
    (m1 m2 : M) :
    (u1.dimScale u2 d) • m1 = (u1.dimScale u2 d) • m2 ↔ m1 = m2:= by
  refine IsUnit.smul_left_cancel ?_
  refine isUnit_iff_exists_inv.mpr ?_
  use u1.dimScale u2 d⁻¹
  simp

@[simp]
lemma dimScale_pos (u1 u2 : UnitChoices) (d : Dimension) :
    0 < (dimScale u1 u2 d) := by
  apply lt_of_le_of_ne
  · simp
  · exact Ne.symm (dimScale_ne_zero u1 u2 d)

TODO "LCSAY" "Make SI : UnitChoices computable, probably by
  replacing the axioms defining the units. See here:
  https://leanprover.zulipchat.com/#narrow/channel/479953-PhysLean/topic/physical.20units/near/534914807"
/-- The choice of units corresponding to SI units, that is
- meters,
- seconds,
- kilograms,
- coulombs,
- kelvin.
-/
noncomputable def SI : UnitChoices where
  length := LengthUnit.meters
  time := TimeUnit.seconds
  mass := MassUnit.kilograms
  charge := ChargeUnit.coulombs
  temperature := TemperatureUnit.kelvin

@[simp]
lemma SI_length : SI.length = LengthUnit.meters := rfl

@[simp]
lemma SI_time : SI.time = TimeUnit.seconds := rfl

@[simp]
lemma SI_mass : SI.mass = MassUnit.kilograms := rfl

@[simp]
lemma SI_charge : SI.charge = ChargeUnit.coulombs := rfl

@[simp]
lemma SI_temperature : SI.temperature = TemperatureUnit.kelvin := rfl

/-- A `UnitChoices` which is related to `SI` by a prime scaling of each
  of the underlying units. This is useful in proving that a result is not
  dimensionally correct. -/
noncomputable def SIPrimed : UnitChoices where
  length := LengthUnit.scale 2 LengthUnit.meters
  time := TimeUnit.scale 3 TimeUnit.seconds
  mass := MassUnit.scale 5 MassUnit.kilograms
  charge := ChargeUnit.scale 7 ChargeUnit.coulombs
  temperature := TemperatureUnit.scale 11 TemperatureUnit.kelvin

@[simp]
lemma dimScale_SI_SIPrimed (d : Dimension) :
    dimScale SI SIPrimed d =
      (2⁻¹ : ℝ≥0) ^ (d.length : ℝ) *
      (3⁻¹ : ℝ≥0) ^ (d.time : ℝ) *
      (5⁻¹ : ℝ≥0) ^ (d.mass : ℝ) *
      (7⁻¹ : ℝ≥0) ^ (d.charge : ℝ) *
      (11⁻¹ : ℝ≥0) ^ (d.temperature : ℝ) := by
  simp [dimScale, SI, SIPrimed]
  rfl

@[simp]
lemma dimScale_SIPrimed_SI (d : Dimension) :
    dimScale SIPrimed SI d =
      (2 : ℝ≥0) ^ (d.length : ℝ) *
      (3 : ℝ≥0) ^ (d.time : ℝ) *
      (5 : ℝ≥0) ^ (d.mass : ℝ) *
      (7 : ℝ≥0) ^ (d.charge : ℝ) *
      (11 : ℝ≥0) ^ (d.temperature : ℝ) := by
  simp [dimScale, SI, SIPrimed]
  rfl

end UnitChoices

/-!

## Types carrying dimensions

Dimensions are assigned to types with the following type-classes

- `HasDim` for any type `M` with an associated dimension
- `CarriesDimension` for a type that also has an instance of `MulAction ℝ≥0 M`

-/

/-- This typeclass indicates that there is a dimension `dim M : Dimension`
  associated with the type `M`. -/
class HasDim (M : Type) where
  /-- The dimension associated with a type `M`. -/
  d : Dimension

alias dim := HasDim.d

/-- A type `M` carries a dimension `d` if every element of `M` is supposed to have
  this dimension. For example, the type `Time` will carry a dimension `T𝓭`. -/
class abbrev CarriesDimension (M : Type) := HasDim M, MulAction ℝ≥0 M

/-!

## Terms of the current dimension

Given a type `M` which carries a dimension `d`,
we are interested in elements of `M` which depend on a choice of units, i.e. functions
`UnitChoices → M`.

We define both a proposition
- `HasDimension f` which says that `f` scales correctly with units,
and a type
- `Dimensionful M` which is the subtype of functions which `HasDimension`.

-/

/-- A quantity of type `M` which depends on a choice of units `UnitChoices` is said to be
  of dimension `d` if it scales by `UnitChoices.dimScale u1 u2 d` under a change in units. -/
def HasDimension {M : Type} [CarriesDimension M] (f : UnitChoices → M) : Prop :=
  ∀ u1 u2 : UnitChoices, f u2 = UnitChoices.dimScale u1 u2 (dim M) • f u1

lemma hasDimension_iff {M : Type} [CarriesDimension M] (f : UnitChoices → M) :
    HasDimension f ↔ ∀ u1 u2 : UnitChoices, f u2 =
    UnitChoices.dimScale u1 u2 (dim M) • f u1 := by
  rfl

/-- The subtype of functions `UnitChoices → M`, for which `M` carries a dimension,
  which `HasDimension`. -/
def Dimensionful (M : Type) [CarriesDimension M] := Subtype (HasDimension (M := M))

instance {M : Type} [CarriesDimension M] : CoeFun (Dimensionful M) (fun _ => UnitChoices → M) where
  coe := Subtype.val

@[ext]
lemma Dimensionful.ext {M : Type} [CarriesDimension M] (f1 f2 : Dimensionful M)
    (h : f1.val = f2.val) : f1 = f2 := by
  cases f1
  cases f2
  simp_all

instance {M : Type} [CarriesDimension M] : MulAction ℝ≥0 (Dimensionful M) where
  smul a f := ⟨fun u => a • f.1 u, fun u1 u2 => by
    simp only
    rw [f.2 u1 u2]
    rw [smul_comm]⟩
  one_smul f := by
    ext u
    change (1 : ℝ≥0) • f.1 u = f.1 u
    simp
  mul_smul a b f := by
    ext u
    change (a * b) • f.1 u = a • (b • f.1 u)
    rw [smul_smul]

@[simp]
lemma Dimensionful.smul_apply {M : Type} [CarriesDimension M]
    (a : ℝ≥0) (f : Dimensionful M) (u : UnitChoices) :
    (a • f).1 u = a • f.1 u := rfl

/-- For `M` carrying a dimension `d`, the equivalence between `M` and `Dimension M`,
  given a choice of units. -/
noncomputable def CarriesDimension.toDimensionful {M : Type} [CarriesDimension M]
    (u : UnitChoices) :
    M ≃ Dimensionful M where
  toFun m := {
    val := fun u1 => (u.dimScale u1 (dim M)) • m
    property := fun u1 u2 => by
      simp [smul_smul]
      rw [mul_comm, UnitChoices.dimScale_transitive]}
  invFun f := f.1 u
  left_inv m := by
    simp
  right_inv f := by
    simp only
    ext u1
    simpa using (f.2 u u1).symm

lemma CarriesDimension.toDimensionful_apply_apply
    {M : Type} [CarriesDimension M] (u1 u2 : UnitChoices) (m : M) :
    (toDimensionful u1 m).1 u2 = (u1.dimScale u2 (dim M)) • m := by rfl
