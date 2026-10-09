/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.Units.PositiveRealUnit
/-!

# Newton's constant of gravitation

## i. Overview

In this module we define a type for Newton's constant of gravitation, along with some basic
properties. An element of this type is a positive real number, and should be thought of as
Newton's constant in some chosen but arbitrary system of units.

## ii. Key results

- `GravitationalConstant` : The type of Newton's constant of gravitation.
- `GravitationalConstant.instPositiveRealUnitCore` : The instance making `GravitationalConstant`
  a positive-real unit type, supplying the shared magnitude, ratio and rescaling API.

## iii. Table of contents

- A. The gravitational constant type
- B. Instances on the type
- C. The instance of one
- D. Positivity properties

## iv. References

* None.
-/

@[expose] public section

/-!

## A. The gravitational constant type

-/

/-- Newton's constant of gravitation. An element of this type should be thought of as
  Newton's constant in some chosen but arbitrary system of units. -/
structure GravitationalConstant where
  /-- The underlying value of Newton's constant. -/
  val : ℝ
  pos : 0 < val

namespace GravitationalConstant

/-!

## B. Instances on the type

Newton's constant is a positive real magnitude, so it is an instance of
`PositiveRealUnitCore`. This supplies the ratio of two values of the constant as a non-negative
real, the rescaling of a value by a positive factor, and the arithmetic laws relating them, all
shared with the fundamental unit types.

-/

instance instPositiveRealUnitCore : PositiveRealUnitCore GravitationalConstant where
  val := GravitationalConstant.val
  pos := GravitationalConstant.pos
  ofVal := fun r hr => ⟨r, hr⟩
  val_ofVal := by intros; rfl
  ofVal_val := by intro x; cases x; rfl

instance : Coe GravitationalConstant ℝ := ⟨GravitationalConstant.val⟩

/-!

## C. The instance of one

We define the instance of one for `GravitationalConstant` to be Newton's constant equal to `1`.
This is useful when we are working in geometrized units, in which `G` is equal to one.

-/

instance : One GravitationalConstant := ⟨1, by grind⟩

@[simp]
lemma val_one : (1 : GravitationalConstant).val = 1 := rfl

/-- The magnitude supplied to `PositiveRealUnitCore` is the underlying value, so that the
  generic positive-real lemmas apply to `GravitationalConstant`. -/
@[simp]
lemma positiveRealUnitCore_val (G : GravitationalConstant) :
    PositiveRealUnitCore.val G = G.val := rfl

/-!

## D. Positivity properties

-/

@[simp]
lemma val_pos (G : GravitationalConstant) : 0 < (G : ℝ) := G.pos

@[simp]
lemma val_nonneg (G : GravitationalConstant) : 0 ≤ (G : ℝ) := le_of_lt G.pos

@[simp]
lemma val_ne_zero (G : GravitationalConstant) : (G : ℝ) ≠ 0 := ne_of_gt G.pos

end GravitationalConstant
