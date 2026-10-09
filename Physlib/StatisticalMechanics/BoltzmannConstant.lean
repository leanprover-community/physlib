/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Units.PositiveRealUnit
/-!

# Boltzmann constant

The Boltzmann constant is a constant `kB` of dimension `m² kg s⁻² K⁻¹`, that is
`Energy/Temperature`. It is named after Ludwig Boltzmann.

In this module give the value of the Boltzmann constant.

We also define the type `BoltzmannConstant`, whose elements are the values the Boltzmann
constant takes in a chosen but arbitrary system of units.

-/

@[expose] public section

open NNReal

/-- The Boltzmann constant. An element of this type should be thought of as the Boltzmann
  constant in some chosen but arbitrary system of units. -/
structure BoltzmannConstant where
  /-- The underlying value of the Boltzmann constant. -/
  val : ℝ
  pos : 0 < val

namespace BoltzmannConstant

/-- The Boltzmann constant is a positive real magnitude, so it is an instance of
  `PositiveRealUnitCore`, which supplies the shared ratio and rescaling API. -/
instance instPositiveRealUnitCore : PositiveRealUnitCore BoltzmannConstant where
  val := BoltzmannConstant.val
  pos := BoltzmannConstant.pos
  ofVal := fun r hr => ⟨r, hr⟩
  val_ofVal := by intros; rfl
  ofVal_val := by intro x; cases x; rfl

instance : Coe BoltzmannConstant ℝ := ⟨BoltzmannConstant.val⟩

/-- The instance of one for `BoltzmannConstant` is the Boltzmann constant equal to `1`, which is
  the case in the units in which temperature is measured as an energy. -/
instance : One BoltzmannConstant := ⟨1, by grind⟩

@[simp]
lemma val_one : (1 : BoltzmannConstant).val = 1 := rfl

/-- The magnitude supplied to `PositiveRealUnitCore` is the underlying value, so that the
  generic positive-real lemmas apply to `BoltzmannConstant`. -/
@[simp]
lemma positiveRealUnitCore_val (kB : BoltzmannConstant) :
    PositiveRealUnitCore.val kB = kB.val := rfl

@[simp]
lemma val_pos (kB : BoltzmannConstant) : 0 < (kB : ℝ) := kB.pos

@[simp]
lemma val_nonneg (kB : BoltzmannConstant) : 0 ≤ (kB : ℝ) := le_of_lt kB.pos

@[simp]
lemma val_ne_zero (kB : BoltzmannConstant) : (kB : ℝ) ≠ 0 := ne_of_gt kB.pos

end BoltzmannConstant

namespace Constants

/-- The Boltzmann constant in units of `m ^ 2 kg s ^ (-2) K ^ (-1)`.
  As long as one does not use the underlying value of this quantity,
  then it can be used as Boltzmann's constant in an arbitrary set of units. -/
def kBAx : {p : ℝ | 0 < p} := ⟨1.380649e-23, by norm_num⟩

/-- The Boltzmann constant in a given but arbitrary set of units.
  Boltzman's constant has dimension equivalent to `Energy/Temperature`. -/
noncomputable def kB : ℝ := kBAx.1

/-- The Boltzmann constant is positive. -/
lemma kB_pos : 0 < kB := kBAx.2

/-- The Boltzmann constant is non-negative. -/
lemma kB_nonneg : 0 ≤ kB := le_of_lt kBAx.2

/-- The Boltzmann constant is not equal to zero. -/
lemma kB_ne_zero : kB ≠ 0 := by
  linarith [kB_pos]

end Constants
