/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Units.PositiveRealUnit
public import Mathlib.Analysis.RCLike.Basic
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

@[expose] public section

open NNReal

/-- The choices of translationally-invariant metrics on the manifold `TimeTransMan`.
  Such a choice corresponds to a choice of units for time. -/
structure TimeUnit : Type where
  /-- The underlying scale of the unit. -/
  val : ℝ
  property : 0 < val

instance : PositiveRealUnitCore TimeUnit where
  val := TimeUnit.val
  pos := TimeUnit.property
  ofVal := fun r hr => ⟨r, hr⟩
  val_ofVal := by intros; rfl
  ofVal_val := by intro x; cases x; rfl
open NNReal

namespace TimeUnit

open PositiveRealUnitCore

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

lemma minutes_div_seconds : minutes / seconds = (60 : ℝ≥0) := NNReal.eq <| by
  simp [minutes]; rw [toReal]

lemma hours_div_seconds : hours / seconds = (3600 : ℝ≥0) := NNReal.eq <| by
  simp [hours]; rw [toReal]; norm_num

lemma days_div_seconds : days / seconds = (86400 : ℝ≥0) := NNReal.eq <| by
  simp [days]; rw [toReal]; norm_num

lemma weeks_div_seconds : weeks / seconds = (604800 : ℝ≥0) := NNReal.eq <| by
  simp [weeks]; rw [toReal]; norm_num

lemma days_div_minutes : days / minutes = (1440 : ℝ≥0) := NNReal.eq <| by
  simp [days, minutes]
  show (24 * 60 * 60 : ℝ) / 60 = ((1440 : ℝ≥0) : ℝ)
  push_cast
  norm_num

lemma weeks_div_minutes : weeks / minutes = (10080 : ℝ≥0) := NNReal.eq <| by
  simp [weeks, minutes]
  show (7 * 24 * 60 * 60 : ℝ) / 60 = ((10080 : ℝ≥0) : ℝ)
  push_cast
  norm_num

lemma days_div_hours : days / hours = (24 : ℝ≥0) := NNReal.eq <| by
  simp [hours, days]
  show (24 * 60 * 60 : ℝ) / (60 * 60) = ((24 : ℝ≥0) : ℝ)
  push_cast
  norm_num

lemma weeks_div_hours : weeks / hours = (168 : ℝ≥0) := NNReal.eq <| by
  simp [weeks, hours]
  show (7 * 24 * 60 * 60 : ℝ) / (60 * 60) = ((168 : ℝ≥0) : ℝ)
  push_cast
  norm_num

end TimeUnit
