/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samyak Rai, Joseph Tooby-Smith
-/
module

public import Physlib.Units.PositiveRealUnit
/-!

# Planck's constant

In this module we define the reduced Planck's constant `ℏ` as a positive real number.
and also define the Planck's constant `h` also to be a positive real number with the
definition `h = 2 π ℏ`.

We also define the type `PlanckConstant`, whose elements are the values Planck's constant takes
in a chosen but arbitrary system of units.

Note that `ℏ` and `h` here are the older, rounded values, with `h` derived from `ℏ`. Since 2019
the SI instead fixes `h = 6.62607015 × 10⁻³⁴ J s` exactly and derives `ℏ` from it, which is what
`Physlib/Units/Constants.lean` records; the two accounts differ in the ninth significant
figure. The definitions here are kept as they are because several modules depend on them.

-/

@[expose] public section

open NNReal

/-- Planck's constant. An element of this type should be thought of as Planck's constant, or
  equally the reduced Planck's constant, in some chosen but arbitrary system of units. -/
structure PlanckConstant where
  /-- The underlying value of Planck's constant. -/
  val : ℝ
  pos : 0 < val

namespace PlanckConstant

/-- Planck's constant is a positive real magnitude, so it is an instance of
  `PositiveRealUnitCore`, which supplies the shared ratio and rescaling API. -/
instance instPositiveRealUnitCore : PositiveRealUnitCore PlanckConstant where
  val := PlanckConstant.val
  pos := PlanckConstant.pos
  ofVal := fun r hr => ⟨r, hr⟩
  val_ofVal := by intros; rfl
  ofVal_val := by intro x; cases x; rfl

instance : Coe PlanckConstant ℝ := ⟨PlanckConstant.val⟩

/-- The instance of one for `PlanckConstant` is the constant equal to `1`. Which constant is
  meant is whichever the element is taken to record: in natural units it is the reduced constant
  `ℏ` that is equal to one, and `h` is then `2 π`. -/
instance : One PlanckConstant := ⟨1, by grind⟩

@[simp]
lemma val_one : (1 : PlanckConstant).val = 1 := rfl

/-- The magnitude supplied to `PositiveRealUnitCore` is the underlying value, so that the
  generic positive-real lemmas apply to `PlanckConstant`. -/
@[simp]
lemma positiveRealUnitCore_val (ℏ : PlanckConstant) : PositiveRealUnitCore.val ℏ = ℏ.val := rfl

@[simp]
lemma val_pos (ℏ : PlanckConstant) : 0 < (ℏ : ℝ) := ℏ.pos

@[simp]
lemma val_nonneg (ℏ : PlanckConstant) : 0 ≤ (ℏ : ℝ) := le_of_lt ℏ.pos

@[simp]
lemma val_ne_zero (ℏ : PlanckConstant) : (ℏ : ℝ) ≠ 0 := ne_of_gt ℏ.pos

end PlanckConstant

namespace Constants

/-- The value of the reduced Planck's constant in units of J.s. -/
def ℏ : Subtype fun x : ℝ => 0 < x := ⟨1.054571817e-34, by norm_num⟩

/-- reduced Planck's constant is positive. -/
@[simp]
lemma ℏ_pos : 0 < (ℏ : ℝ) := ℏ.2

/-- reduced Planck's constant is non-negative. -/
@[simp]
lemma ℏ_nonneg : 0 ≤ (ℏ : ℝ) := le_of_lt ℏ.2

/-- reduced Planck's constant is not equal to zero. -/
@[simp]
lemma ℏ_ne_zero : (ℏ : ℝ) ≠ 0 := ne_of_gt ℏ.2

/-- reduced Planck's constant is not equal to zero, as a complex number. -/
lemma ℏ_ofReal_ne_zero : ((ℏ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ℏ_ne_zero

/-- The definition of Planck's constant in terms of Reduced Planck's constant,
 defined as `2 π ℏ` -/
noncomputable def h : Subtype fun x : ℝ => 0 < x := ⟨2 * Real.pi * (ℏ : ℝ),
mul_pos (mul_pos (by norm_num) Real.pi_pos) ℏ_pos⟩

/-- Planck's constant is positive. -/
@[simp]
lemma h_pos : 0 < (h : ℝ) := h.2

/-- Planck's constant is non-negative. -/
@[simp]
lemma h_nonneg : 0 ≤ (h : ℝ) := le_of_lt h.2

/-- Planck's constnat is not equal to zero. -/
@[simp]
lemma h_ne_zero : (h : ℝ) ≠ 0 := ne_of_gt h.2

/-- Planck's constant is `2 π` times the reduced Planck's constant. -/
lemma h_eq_two_pi_hbar : (h : ℝ) = 2 * Real.pi * (ℏ : ℝ) := rfl

end Constants
