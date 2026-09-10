/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Units.PositiveRealUnit
public import Mathlib.Analysis.RCLike.Basic
/-!

# The units of charge

A unit of charge corresponding to a choice of translationally-invariant
metric on the charge manifold (to be defined diffeomorphic to `ℝ`).
Such a choice is (non-canonically) equivalent to a
choice of positive real number. We define the type `ChargeUnit` to be equivalent to the
positive reals.

We assume that the charge manifold is already defined with an orientation, with the
electron being in the negative direction.

On `ChargeUnit` there is an instance of division giving a real number, corresponding to the
ratio of the two scales of temperature unit.

To define specific charge units, we first state the existence of a
a given charge unit, and then construct all other charge units from it.
We choose to state the
existence of the charge unit of the coulomb, and construct all other charge units from that.

-/

@[expose] public section

open NNReal

/-- The choices of translationally-invariant metrics on the charge-manifold.
  Such a choice corresponds to a choice of units for charge.
  This assumes that an orientation has already being picked on the charge manifold. -/
structure ChargeUnit where
  /-- The underlying scale of the unit. -/
  val : ℝ
  property : 0 < val

instance : PositiveRealUnitCore ChargeUnit where
  val := ChargeUnit.val
  pos := ChargeUnit.property
  ofVal := fun r hr => ⟨r, hr⟩
  val_ofVal := by intros; rfl
  ofVal_val := by intro x; cases x; rfl
open NNReal

namespace ChargeUnit

open PositiveRealUnitCore

/-!

## Specific choices of charge units

We define specific choices of charge units.
We first define the notion of a columb to correspond to the charge unit with underlying value
equal to `1`. This is really down to a choice in the isomorphism between the set of metrics
on the charge manifold and the positive reals.

-/

/-- The definition of a charge unit of coulomb. -/
def coulombs : ChargeUnit := ⟨1, by norm_num⟩

/-- The charge unit of a elementryCharge (1.602176634×10−19 coulomb). -/
noncomputable def elementaryCharge : ChargeUnit := scale (1.602176634e-19) coulombs

end ChargeUnit
