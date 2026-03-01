/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Geometry.Manifold.Diffeomorph
import PhysLean.SpaceAndTime.Time.Basic
/-!

# Units on time

A unit of time corresponds to a choice of translationally-invariant
metric on the time manifold `TimeTransMan`. Such a choice is (non-canonically) equivalent to a
choice of positive real number. We define the type `TimeUnit` to be equivalent to the
positive reals.

On `TimeUnit` there is an instance of division giving a real number, corresponding to the
ratio of the two scales of time unit.

We define `HasTimeDimension` to be a property of a function from `TimeUnit` to a type `M`
which is a function that scales with the time unit with respect to the rational power `d`.

To define specific time units, we first state the existence of a
a given time unit, and then construct all other time units from it. We choose to state the
existence of the time unit of seconds, and construct all other time units from that.

-/

open NNReal

/-- The choices of translationally-invariant metrics on the manifold `TimeTransMan`.
  Such a choice corresponds to a choice of units for time. -/
structure TimeUnit : Type where
  /-- The underlying scale of the unit. -/
  val : ℝ
  property : 0 < val

namespace TimeUnit

@[simp]
lemma val_ne_zero (x : TimeUnit) : x.val ≠ 0 := by
  exact Ne.symm (ne_of_lt x.property)

lemma val_pos (x : TimeUnit) : 0 < x.val := x.property

instance : Inhabited TimeUnit where
  default := ⟨1, by norm_num⟩

/-!

## Division of TimeUnit

-/

noncomputable instance : HDiv TimeUnit TimeUnit ℝ≥0 where
  hDiv x t := ⟨x.val / t.val, div_nonneg (le_of_lt x.val_pos) (le_of_lt t.val_pos)⟩

lemma div_eq_val (x y : TimeUnit) :
    x / y = (⟨x.val / y.val, div_nonneg (le_of_lt x.val_pos) (le_of_lt y.val_pos)⟩ : ℝ≥0) := rfl

@[simp]
lemma div_ne_zero (x y : TimeUnit) : ¬ x / y = (0 : ℝ≥0) := by
  rw [div_eq_val]
  refine coe_ne_zero.mp ?_
  simp

@[simp]
lemma div_pos (x y : TimeUnit) : (0 : ℝ≥0) < x/ y := by
  apply lt_of_le_of_ne
  · exact zero_le (x / y)
  · exact Ne.symm (div_ne_zero x y)

@[simp]
lemma div_self (x : TimeUnit) :
    x / x = (1 : ℝ≥0) := by
  simp [div_eq_val, x.val_ne_zero]

lemma div_symm (x y : TimeUnit) :
    x / y = (y / x)⁻¹ := NNReal.eq <| by
  rw [div_eq_val, inv_eq_one_div, div_eq_val]
  simp

@[simp]
lemma div_mul_div_coe (x y z : TimeUnit) :
    (x / y : ℝ) * (y /z : ℝ) = x /z := by
  simp [div_eq_val]
  field_simp

/-!

## The scaling of a time unit

-/

/-- The scaling of a time unit by a positive real. -/
def scale (r : ℝ) (x : TimeUnit) (hr : 0 < r := by norm_num) : TimeUnit :=
  ⟨r * x.val, mul_pos hr x.val_pos⟩

@[simp]
lemma scale_div_self (x : TimeUnit) (r : ℝ) (hr : 0 < r) :
    scale r x hr / x = (⟨r, le_of_lt hr⟩ : ℝ≥0) := by
  simp [scale, div_eq_val]

@[simp]
lemma scale_one (x : TimeUnit) : scale 1 x = x := by
  simp [scale]

@[simp]
lemma scale_div_scale (x1 x2 : TimeUnit) {r1 r2 : ℝ} (hr1 : 0 < r1) (hr2 : 0 < r2) :
    scale r1 x1 hr1 / scale r2 x2 hr2 = (⟨r1, le_of_lt hr1⟩ / ⟨r2, le_of_lt hr2⟩) * (x1 / x2) := by
  refine NNReal.eq ?_
  simp [scale, div_eq_val]
  field_simp

@[simp]
lemma self_div_scale (x : TimeUnit) (r : ℝ) (hr : 0 < r) :
    x / scale r x hr = (⟨1/r, _root_.div_nonneg (by simp) (le_of_lt hr)⟩ : ℝ≥0) := by
  simp [scale, div_eq_val]
  ext
  simp only [coe_mk]
  field_simp

@[simp]
lemma scale_scale (x : TimeUnit) (r1 r2 : ℝ) (hr1 : 0 < r1) (hr2 : 0 < r2) :
    scale r1 (scale r2 x hr2) hr1 = scale (r1 * r2) x (mul_pos hr1 hr2) := by
  simp [scale]
  ring
/-!

## Specific choices of time units

To define a specific time units.
We first define the notion of a second to correspond to the length unit with underlying value
equal to `1`. This is really down to a choice in the isomorphism between the set of metrics
on the time manifold and the positive reals.
From this choice of second, we can define other length units by scaling second.

-/

/-- The definition of a time unit of seconds. -/
def seconds : TimeUnit := ⟨1, by norm_num⟩

/-- The time unit of femtoseconds (10⁻¹⁵ of a second). -/
noncomputable def femtoseconds : TimeUnit := scale ((1/10) ^ (15)) seconds

/-- The time unit of picoseconds (10⁻¹² of a second). -/
noncomputable def picoseconds : TimeUnit := scale ((1/10) ^ (12)) seconds

/-- The time unit of nanoseconds (10⁻⁹ of a second). -/
noncomputable def nanoseconds : TimeUnit := scale ((1/10) ^ (9)) seconds

/-- The time unit of microseconds (10⁻⁶ of a second). -/
noncomputable def microseconds : TimeUnit := scale ((1/10) ^ (6)) seconds

/-- The time unit of milliseconds (10⁻³ of a second). -/
noncomputable def milliseconds : TimeUnit := scale ((1/10) ^ (3)) seconds

/-- The time unit of centiseconds (10⁻² of a second). -/
noncomputable def centiseconds : TimeUnit := scale ((1/10) ^ (2)) seconds

/-- The time unit of deciseconds (10⁻¹ of a second). -/
noncomputable def deciseconds : TimeUnit := scale ((1/10) ^ (1)) seconds

/-- The time unit of minutes. -/
noncomputable def minutes : TimeUnit := scale 60 seconds

/-- The time unit of hours. -/
noncomputable def hours : TimeUnit := scale (60 * 60) seconds

/-- The time unit of 24 hour days. -/
noncomputable def days : TimeUnit := scale (24 * 60 * 60) seconds

/-- The time unit of 7 day weeks. -/
noncomputable def weeks : TimeUnit := scale (7 * 24 * 60 * 60) seconds

/-!

## Relations between time units

-/

lemma minutes_div_seconds : minutes / seconds = (60 : ℝ≥0) := NNReal.eq <| by simp [minutes]

lemma hours_div_seconds : hours / seconds = (3600 : ℝ≥0) := NNReal.eq <| by
  simp [hours]; norm_num

lemma days_div_seconds : days / seconds = (86400 : ℝ≥0) := NNReal.eq <| by
  simp [days]; norm_num

lemma weeks_div_seconds : weeks / seconds = (604800 : ℝ≥0) := NNReal.eq <| by
  simp [weeks]; norm_num

lemma days_div_minutes : days / minutes = (1440 : ℝ≥0) := NNReal.eq <| by
  simp [days, minutes]; norm_num

lemma weeks_div_minutes : weeks / minutes = (10080 : ℝ≥0) := NNReal.eq <| by
  simp [weeks, minutes]; norm_num

lemma days_div_hours : days / hours = (24 : ℝ≥0) := NNReal.eq <| by simp [hours, days]; norm_num

lemma weeks_div_hours : weeks / hours = (168 : ℝ≥0) := NNReal.eq <| by
  simp [weeks, hours]; norm_num

end TimeUnit
