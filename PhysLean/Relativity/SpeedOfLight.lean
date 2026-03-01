/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Algebra.Lie.Classical
import Mathlib.Analysis.Normed.Ring.Lemmas
/-!

# The Speed of Light

## i. Overview

In this module we define a type for the speed of light in a vacuum,
along with some basic properties. An element of this type is a positive real number,
and should be thought of as the speed of light in some chosen but arbitrary system of units.

## ii. Key results

- `SpeedOfLight` : The type of speeds of light in a vacuum.

## iii. Table of contents

- A. The Speed of Light type
- B. Instances on the type
- C. The instance of one
- D. Positivity properties

## iv. References

-/
open Matrix

/-!

## A. The Speed of Light type

-/

/-- The speed of light in a vacuum. An element of this type should be thought of as
  the speed of light in some chosen but arbitrary system of units. -/
structure SpeedOfLight where
  /-- The underlying value of the speed of light. -/
  val : ℝ
  pos : 0 < val

namespace SpeedOfLight

/-!

## B. Instances on the type

-/

instance : Coe SpeedOfLight ℝ := ⟨SpeedOfLight.val⟩

/-!

## C. The instance of one

We define the instance of one for `SpeedOfLight` to be the speed of light equal to `1`.
This is useful when we are working in units where the speed of light is equal to one.

-/

instance : One SpeedOfLight := ⟨1, by grind⟩

@[simp]
lemma val_one : (1 : SpeedOfLight).val = 1 := rfl

/-!

## D. Positivity properties

-/

@[simp]
lemma val_pos (c : SpeedOfLight) : 0 < (c : ℝ) := c.pos

@[simp]
lemma val_nonneg (c : SpeedOfLight) : 0 ≤ (c : ℝ) := le_of_lt c.pos

@[simp]
lemma val_ne_zero (c : SpeedOfLight) : (c : ℝ) ≠ 0 := ne_of_gt c.pos

end SpeedOfLight
