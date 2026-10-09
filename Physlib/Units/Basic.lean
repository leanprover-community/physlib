/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.SpaceAndTime.Time.TimeUnit
public import Physlib.SpaceAndTime.Space.LengthUnit
public import Physlib.ClassicalMechanics.Mass.MassUnit
public import Physlib.Electromagnetism.Charge.ChargeUnit
public import Physlib.Thermodynamics.Temperature.TemperatureUnits
public import Physlib.Units.LTMCTDimensionBase
public import Physlib.Meta.TODO.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
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

Units within Physlib are implemented with the following convention:
- The fundamental units, and the choices they correspond to, are defined within the
  appropriate physics directory, in particular:
  - `Physlib/SpaceAndTime/Time/TimeUnit.lean`
  - `Physlib/SpaceAndTime/Space/LengthUnit.lean`
  - `Physlib/ClassicalMechanics/Mass/MassUnit.lean`
  - `Physlib/Electromagnetism/Charge/ChargeUnit.lean`
  - `Physlib/Thermodynamics/Temperature/TemperatureUnit.lean`
- In this `Units` directory, we define the necessary structures and properties
  to work derived units and dimensions.

## References

Zulip chats discussing units:

* https://leanprover.zulipchat.com/#narrow/channel/479953-Physlib/topic/physical.20units.
* https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/Dimensional.20Analysis.20Revisited/with/530238303.

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
in Physlib which is based exclusively on Reals.

-/

@[expose] public section

/-!

## Units

-/
open NNReal

/-- The choice of units. -/
@[ext]
structure LTMCTUnitChoices where
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

namespace LTMCTUnitChoices

/-- Given two choices of units `u1` and `u2` and a dimension `d`, the
  element of `ℝ≥0` corresponding to the scaling (by definition) of a quantity of dimension `d`
  when changing from units `u1` to `u2`. -/
noncomputable def dimScale (u1 u2 : LTMCTUnitChoices) :Dimension LTMCTDimensionBase →* ℝ≥0 where
  toFun d :=
    (u1.length / u2.length) ^ (d.length : ℝ) *
    (u1.time / u2.time) ^ (d.time : ℝ) *
    (u1.mass / u2.mass) ^ (d.mass : ℝ) *
    (u1.charge / u2.charge) ^ (d.charge : ℝ) *
    (u1.temperature / u2.temperature) ^ (d.temperature : ℝ)
  map_one' := by
    simp
  map_mul' d1 d2 := by
    simp only [Dimension.length_mul, Dimension.Exponent.coe_add, Rat.cast_add, Dimension.time_mul,
      Dimension.mass_mul, Dimension.charge_mul, Dimension.temperature_mul]
    repeat rw [NNReal.rpow_add (by simp)]
    ring

lemma dimScale_apply (u1 u2 : LTMCTUnitChoices) (d : Dimension LTMCTDimensionBase) :
    dimScale u1 u2 d =
      (u1.length / u2.length) ^ (d.length : ℝ) *
      (u1.time / u2.time) ^ (d.time : ℝ) *
      (u1.mass / u2.mass) ^ (d.mass : ℝ) *
      (u1.charge / u2.charge) ^ (d.charge : ℝ) *
      (u1.temperature / u2.temperature) ^ (d.temperature : ℝ) := rfl

@[simp]
lemma dimScale_self (u : LTMCTUnitChoices) (d : Dimension LTMCTDimensionBase) :
    dimScale u u d = 1 := by
  simp [dimScale]

@[simp]
lemma dimScale_one (u1 u2 : LTMCTUnitChoices) :
    dimScale u1 u2 1 = 1 := by
  simp [dimScale]

lemma dimScale_transitive (u1 u2 u3 : LTMCTUnitChoices) (d : Dimension LTMCTDimensionBase) :
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
  rw [PositiveRealUnitCore.div_mul_div, PositiveRealUnitCore.div_mul_div,
    PositiveRealUnitCore.div_mul_div, PositiveRealUnitCore.div_mul_div,
    PositiveRealUnitCore.div_mul_div]

@[simp]
lemma dimScale_mul_symm (u1 u2 : LTMCTUnitChoices) (d : Dimension LTMCTDimensionBase) :
    dimScale u1 u2 d * dimScale u2 u1 d = 1 := by
  rw [dimScale_transitive, dimScale_self]

@[simp]
lemma dimScale_coe_mul_symm (u1 u2 : LTMCTUnitChoices) (d : Dimension LTMCTDimensionBase) :
    (toReal (dimScale u1 u2 d)) * (toReal (dimScale u2 u1 d)) = 1 := by
  trans toReal (dimScale u1 u2 d * dimScale u2 u1 d)
  · rw [NNReal.coe_mul]
  simp

@[simp]
lemma dimScale_ne_zero (u1 u2 : LTMCTUnitChoices) (d : Dimension LTMCTDimensionBase) :
    dimScale u1 u2 d ≠ 0 := by
  simp [dimScale]

lemma dimScale_symm (u1 u2 : LTMCTUnitChoices) (d : Dimension LTMCTDimensionBase) :
    dimScale u1 u2 d = (dimScale u2 u1 d)⁻¹ := by
  simp only [dimScale_apply, mul_inv]
  congr
  · rw [PositiveRealUnitCore.div_symm, inv_rpow]
  · rw [PositiveRealUnitCore.div_symm, inv_rpow]
  · rw [PositiveRealUnitCore.div_symm, inv_rpow]
  · rw [PositiveRealUnitCore.div_symm, inv_rpow]
  · rw [PositiveRealUnitCore.div_symm, inv_rpow]

lemma dimScale_of_inv_eq_swap (u1 u2 : LTMCTUnitChoices) (d : Dimension LTMCTDimensionBase) :
    dimScale u1 u2 d⁻¹ = dimScale u2 u1 d := by
  simp only [map_inv]
  conv_rhs => rw[dimScale_symm]

@[simp]
lemma smul_dimScale_injective {M : Type} [MulAction ℝ≥0 M] (u1 u2 : LTMCTUnitChoices)
    (d : Dimension LTMCTDimensionBase) (m1 m2 : M) :
    (u1.dimScale u2 d) • m1 = (u1.dimScale u2 d) • m2 ↔ m1 = m2:= by
  refine IsUnit.smul_left_cancel ?_
  refine isUnit_iff_exists_inv.mpr ?_
  use u1.dimScale u2 d⁻¹
  simp

@[simp]
lemma dimScale_pos (u1 u2 : LTMCTUnitChoices) (d : Dimension LTMCTDimensionBase) :
    0 < (dimScale u1 u2 d) := by
  apply lt_of_le_of_ne
  · simp
  · exact Ne.symm (dimScale_ne_zero u1 u2 d)

/-- The scaling factor `dimScale u1 u2 d` regarded as a unit of `ℝ≥0`, that is as a strictly
  positive real. Dimensionful quantities are scaled by this rather than by `dimScale u1 u2 d`
  itself, so that a type whose elements are strictly positive, such as `SpeedOfLight`, can carry
  a dimension: no action of `ℝ≥0` on such a type can be compatible with the magnitude, since
  compatibility at `a = 0` would give `val (0 • m) = 0` while `val` is strictly positive. -/
noncomputable def dimScaleUnits (u1 u2 : LTMCTUnitChoices) (d : Dimension LTMCTDimensionBase) :
    ℝ≥0ˣ :=
  Units.mk0 (dimScale u1 u2 d) (dimScale_ne_zero u1 u2 d)

@[simp]
lemma dimScaleUnits_coe (u1 u2 : LTMCTUnitChoices) (d : Dimension LTMCTDimensionBase) :
    ((dimScaleUnits u1 u2 d : ℝ≥0)) = dimScale u1 u2 d := rfl

@[simp]
lemma dimScaleUnits_transitive (u1 u2 u3 : LTMCTUnitChoices)
    (d : Dimension LTMCTDimensionBase) :
    dimScaleUnits u1 u2 d * dimScaleUnits u2 u3 d = dimScaleUnits u1 u3 d := by
  apply Units.ext
  simpa using dimScale_transitive u1 u2 u3 d

/-- Scaling by `dimScaleUnits` agrees with scaling by `dimScale` whenever the type also carries
  an action of `ℝ≥0`, so that statements phrased either way normalise to the same form. -/
lemma dimScaleUnits_smul {M : Type} [MulAction ℝ≥0 M] (u1 u2 : LTMCTUnitChoices)
    (d : Dimension LTMCTDimensionBase) (m : M) :
    dimScaleUnits u1 u2 d • m = dimScale u1 u2 d • m := rfl

@[simp]
lemma dimScaleUnits_mul_dim (u1 u2 : LTMCTUnitChoices)
    (d1 d2 : Dimension LTMCTDimensionBase) :
    dimScaleUnits u1 u2 (d1 * d2) = dimScaleUnits u1 u2 d1 * dimScaleUnits u1 u2 d2 := by
  apply Units.ext
  simp

@[simp]
lemma dimScaleUnits_self (u : LTMCTUnitChoices) (d : Dimension LTMCTDimensionBase) :
    dimScaleUnits u u d = 1 := by
  apply Units.ext
  simp [dimScale_self]

TODO "Make SI : LTMCTUnitChoices computable, probably by
  replacing the axioms defining the units. See here:
  https://leanprover.zulipchat.com/#narrow/channel/479953-Physlib/topic/physical.20units/near/534914807"
/-- The choice of units corresponding to SI units, that is
- meters,
- seconds,
- kilograms,
- coulombs,
- kelvin.
-/
noncomputable def SI : LTMCTUnitChoices where
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

/-- A `LTMCTUnitChoices` which is related to `SI` by a prime scaling of each
  of the underlying units. This is useful in proving that a result is not
  dimensionally correct. -/
noncomputable def SIPrimed : LTMCTUnitChoices where
  length := PositiveRealUnitCore.scale 2 LengthUnit.meters
  time := PositiveRealUnitCore.scale 3 TimeUnit.seconds
  mass := PositiveRealUnitCore.scale 5 MassUnit.kilograms
  charge := PositiveRealUnitCore.scale 7 ChargeUnit.coulombs
  temperature := PositiveRealUnitCore.scale 11 TemperatureUnit.kelvin

@[simp]
lemma dimScale_SI_SIPrimed (d : Dimension LTMCTDimensionBase) :
    dimScale SI SIPrimed d =
      (2⁻¹ : ℝ≥0) ^ (d.length : ℝ) *
      (3⁻¹ : ℝ≥0) ^ (d.time : ℝ) *
      (5⁻¹ : ℝ≥0) ^ (d.mass : ℝ) *
      (7⁻¹ : ℝ≥0) ^ (d.charge : ℝ) *
      (11⁻¹ : ℝ≥0) ^ (d.temperature : ℝ) := by
  simp [dimScale, SI, SIPrimed]
  rfl

@[simp]
lemma dimScale_SIPrimed_SI (d : Dimension LTMCTDimensionBase) :
    dimScale SIPrimed SI d =
      (2 : ℝ≥0) ^ (d.length : ℝ) *
      (3 : ℝ≥0) ^ (d.time : ℝ) *
      (5 : ℝ≥0) ^ (d.mass : ℝ) *
      (7 : ℝ≥0) ^ (d.charge : ℝ) *
      (11 : ℝ≥0) ^ (d.temperature : ℝ) := by
  simp [dimScale, SI, SIPrimed]
  rfl

end LTMCTUnitChoices

/-!

## Types carrying dimensions

Dimensions are assigned to types with the following type-classes

- `HasDim` for any type `M` with an associated dimension
- `CarriesDimension` for a type that also has an instance of `MulAction ℝ≥0ˣ M`, that is an
  action of the strictly positive reals

The scaling factors relating two systems of units are never zero, so the positive reals suffice
here, and taking them rather than `ℝ≥0` lets a type whose elements are strictly positive, such as
`SpeedOfLight`, carry a dimension. On such a type no action of `ℝ≥0` can be compatible with the
magnitude, that is satisfy `val (a • x) = a * val x`: at `a = 0` compatibility would give
`val (0 • x) = 0`, while `val` is strictly positive. (A `MulAction ℝ≥0` does exist on any type,
the trivial one for instance, but it has nothing to do with the magnitude and so is of no use
here.)

A type which does carry an action of `ℝ≥0`, such as `ℝ` or any real vector space, obtains the
action of `ℝ≥0ˣ` by restriction, so it satisfies `CarriesDimension` as soon as it has a `HasDim`
instance. A declaration about such types should therefore assume `[HasDim M]` and
`[MulAction ℝ≥0 M]`, never `[CarriesDimension M]` and `[MulAction ℝ≥0 M]` together: with the
latter pair the two actions of `ℝ≥0ˣ` in scope, the one from `CarriesDimension` and the one
restricted from `ℝ≥0`, are unrelated, so the lemmas below relating `dimScaleUnits` to `dimScale`
do not apply and proofs about the scaling get stuck.

Where both actions genuinely coexist on one type, as they do on `Dimensionful M` below for every
`M` carrying an action of `ℝ≥0`, the declared action and the restricted one agree
definitionally, so nothing is ambiguous.

The same caution applies to the generic results about these actions, such as the instance on
`Dimensionful M` below and `WithDim.ofPositiveRealUnit_units_smul`: each is about one particular
`ℝ≥0ˣ` action, and a type carrying both a `PositiveRealUnitCore` instance and an action of `ℝ≥0`
would have two. No type does at present.

Several statements below therefore come in two forms, one for each action. The convention is that
the plain name carries the `ℝ≥0` statement, which needs `[MulAction ℝ≥0 M]` and is the form the
concrete unit calculations use, while the suffix `_units` marks the `ℝ≥0ˣ` statement, which holds
for every type carrying a dimension.

-/

/-- This typeclass indicates that there is a dimension `dim M : Dimension`
  associated with the type `M`. -/
class HasDim (M : Type) where
  /-- The dimension associated with a type `M`. -/
  d : Dimension LTMCTDimensionBase

alias dim := HasDim.d

/-- A type `M` carries a dimension `d` if every element of `M` is supposed to have
  this dimension. For example, the type `Time` will carry a dimension `T𝓭`. -/
class abbrev CarriesDimension (M : Type) := HasDim M, MulAction ℝ≥0ˣ M

/-!

## Terms of the current dimension

Given a type `M` which carries a dimension `d`,
we are interested in elements of `M` which depend on a choice of units, i.e. functions
`LTMCTUnitChoices → M`.

We define both a proposition
- `HasDimension f` which says that `f` scales correctly with units,
and a type
- `Dimensionful M` which is the subtype of functions which `HasDimension`.

-/

/-- A quantity of type `M` which depends on a choice of units `LTMCTUnitChoices` is said to be
  of dimension `d` if it scales by `LTMCTUnitChoices.dimScaleUnits u1 u2 d` under a change in
  units. -/
def HasDimension {M : Type} [CarriesDimension M] (f : LTMCTUnitChoices → M) : Prop :=
  ∀ u1 u2 : LTMCTUnitChoices, f u2 = LTMCTUnitChoices.dimScaleUnits u1 u2 (dim M) • f u1

lemma hasDimension_iff {M : Type} [CarriesDimension M] (f : LTMCTUnitChoices → M) :
    HasDimension f ↔ ∀ u1 u2 : LTMCTUnitChoices, f u2 =
    LTMCTUnitChoices.dimScaleUnits u1 u2 (dim M) • f u1 := by
  rfl

/-- The subtype of functions `LTMCTUnitChoices → M`, for which `M` carries a dimension,
  which `HasDimension`. -/
def Dimensionful (M : Type) [CarriesDimension M] := Subtype (HasDimension (M := M))

instance {M : Type} [CarriesDimension M] :
    CoeFun (Dimensionful M) (fun _ => LTMCTUnitChoices → M) where
  coe := Subtype.val

@[ext]
lemma Dimensionful.ext {M : Type} [CarriesDimension M] (f1 f2 : Dimensionful M)
    (h : f1.val = f2.val) : f1 = f2 := Subtype.ext h

instance {M : Type} [CarriesDimension M] : MulAction ℝ≥0ˣ (Dimensionful M) where
  smul a f := ⟨fun u => a • f.1 u, fun u1 u2 => by
    simp only
    rw [f.2 u1 u2, ← mul_smul, ← mul_smul, mul_comm]⟩
  one_smul f := by
    ext u
    change (1 : ℝ≥0ˣ) • f.1 u = f.1 u
    simp
  mul_smul a b f := by
    ext u
    change (a * b) • f.1 u = a • (b • f.1 u)
    rw [smul_smul]

/-- When `M` itself carries an action of `ℝ≥0`, a dimensionful quantity of `M` may be scaled by
  any non-negative real, not only by a strictly positive one. -/
instance {M : Type} [HasDim M] [MulAction ℝ≥0 M] :
    MulAction ℝ≥0 (Dimensionful M) where
  smul a f := ⟨fun u => a • f.1 u, fun u1 u2 => by
    simp only
    rw [f.2 u1 u2, LTMCTUnitChoices.dimScaleUnits_smul,
      LTMCTUnitChoices.dimScaleUnits_smul, ← mul_smul, ← mul_smul, mul_comm]⟩
  one_smul f := by
    ext u
    change (1 : ℝ≥0) • f.1 u = f.1 u
    simp
  mul_smul a b f := by
    ext u
    change (a * b) • f.1 u = a • (b • f.1 u)
    rw [smul_smul]

/-- The value of a non-negative real scaling of a dimensionful quantity. -/
@[simp]
lemma Dimensionful.smul_apply {M : Type} [HasDim M] [MulAction ℝ≥0 M]
    (a : ℝ≥0) (f : Dimensionful M) (u : LTMCTUnitChoices) :
    (a • f).1 u = a • f.1 u := rfl

@[simp]
lemma Dimensionful.smul_apply_units {M : Type} [CarriesDimension M]
    (a : ℝ≥0ˣ) (f : Dimensionful M) (u : LTMCTUnitChoices) :
    (a • f).1 u = a • f.1 u := rfl

/-- For `M` carrying a dimension `d`, the equivalence between `M` and `Dimension M`,
  given a choice of units. -/
noncomputable def CarriesDimension.toDimensionful {M : Type} [CarriesDimension M]
    (u : LTMCTUnitChoices) :
    M ≃ Dimensionful M where
  toFun m := {
    val := fun u1 => (u.dimScaleUnits u1 (dim M)) • m
    property := fun u1 u2 => by
      simp only [← mul_smul]
      rw [mul_comm, LTMCTUnitChoices.dimScaleUnits_transitive]}
  invFun f := f.1 u
  left_inv m := by
    simp
  right_inv f := by
    simp only
    ext u1
    simpa using (f.2 u u1).symm

/-- The value of `toDimensionful`, scaled by `dimScaleUnits`. This is the general form, holding
  for every type carrying a dimension. -/
lemma CarriesDimension.toDimensionful_apply_apply_units
    {M : Type} [CarriesDimension M] (u1 u2 : LTMCTUnitChoices) (m : M) :
    (toDimensionful u1 m).1 u2 = (u1.dimScaleUnits u2 (dim M)) • m := by rfl

/-- The value of `toDimensionful` for a type which also carries an action of `ℝ≥0`, phrased with
  `dimScale` in place of `dimScaleUnits`. This is the form the concrete unit calculations use. -/
@[simp]
lemma CarriesDimension.toDimensionful_apply_apply
    {M : Type} [HasDim M] [MulAction ℝ≥0 M] (u1 u2 : LTMCTUnitChoices) (m : M) :
    (toDimensionful u1 m).1 u2 = (u1.dimScale u2 (dim M)) • m := by rfl
