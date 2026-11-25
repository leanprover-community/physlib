/-
Copyright (c) 2026 Sabrina Pasterski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sabrina Pasterski
-/
module

public import Physlib.SpaceAndTime.Time.Basic
public import Physlib.SpaceAndTime.Time.TimeUnit

/-!
# Measuring elapsed time with a caesium clock

An ideal clock measures a duration by the change in phase of a reference oscillation.

## i. Overview

The SI second fixes the frequency of the radiation corresponding to the unperturbed ground-state
hyperfine transition of the caesium-133 atom. One second spans exactly 9 192 631 770 periods.
We model the accumulated phase in cycles, allowing fractional and signed differences.

For an ideal uniform clock the phase is an affine function of proper time along the clock.
The coordinate on `Time` has a fixed but arbitrary unit. Identifying an observed phase with
this ideal radiation is the physical input. Two distinct readings then determine the size of
the coordinate unit in SI seconds. The observation interval need not itself last one second,
and its endpoints need no absolute phase or time origin.

## ii. Key results

- `isCalibrated_iff_rate` relates a calibration observation to the rate in the chosen unit.
- `isCalibrated_iff_eq_unitOfReadings` recovers the unique time unit from two phase readings.
- `elapsed_seconds` recovers signed elapsed time in seconds from two phase readings.
- `one_second_iff` characterizes one-second intervals by the defining cycle count.

## iii. Table of contents

- A. Phase readings and calibration
- B. Recovering the unit and measuring durations

## iv. References

- BIPM, *The International System of Units (SI)*, 9th edition, section 2.3.1
  [ref: bipm_si_brochure_2019].

-/

@[expose] public noncomputable section

namespace Time.CaesiumClock

open TimeUnit

/-!
## A. Phase readings and calibration
-/

/-- The signed number of cycles between two readings, from unwrapped phase readings in cycles. -/
def elapsedCycles {E : Type*} (phase : E → ℝ) (start stop : E) : ℝ :=
  phase stop - phase start

/-- Cycle counts add when two measurement intervals are joined. -/
lemma elapsedCycles_add {E : Type*} (phase : E → ℝ) (a b c : E) :
    elapsedCycles phase a b + elapsedCycles phase b c = elapsedCycles phase a c := by
  unfold elapsedCycles
  ring

/-- The number of periods stipulated by the SI definition of one second. -/
def cyclesPerSecond : ℕ := 9192631770

/-- A uniform clock is calibrated in coordinate unit `u` when a single interval of one second
advances its phase by the defining count. The starting instant need not be specified. -/
def IsCalibrated (phase : Time →ᵃ[ℝ] ℝ) (u : TimeUnit) : Prop :=
  ∃ t : Time, elapsedCycles phase t ((seconds / u : ℝ) +ᵥ t) = cyclesPerSecond

private lemma elapsedCycles_eq_rate (phase : Time →ᵃ[ℝ] ℝ) (a b : Time) :
    elapsedCycles phase a b = (b -ᵥ a) * phase.linear 1 := by
  change phase b -ᵥ phase a = _
  rw [← phase.linear_apply_vsub]
  simpa using phase.linear.map_smul (b -ᵥ a) (1 : ℝ)

/-- One calibration interval determines the rate in cycles per coordinate unit. -/
lemma isCalibrated_iff_rate (phase : Time →ᵃ[ℝ] ℝ) (u : TimeUnit) :
    IsCalibrated phase u ↔ phase.linear 1 = (u / seconds : ℝ) * cyclesPerSecond := by
  have hcancel : (u / seconds : ℝ) * (seconds / u : ℝ) = 1 := by
    rw [PositiveRealUnitCore.div_mul_div_coe, PositiveRealUnitCore.div_self]
    rfl
  constructor
  · rintro ⟨t, ht⟩
    rw [elapsedCycles_eq_rate, vadd_vsub] at ht
    rw [← ht, ← mul_assoc, hcancel, one_mul]
  · intro h
    obtain ⟨t⟩ := (inferInstance : Nonempty Time)
    refine ⟨t, ?_⟩
    rw [elapsedCycles_eq_rate, vadd_vsub, h, ← mul_assoc, mul_comm (seconds / u : ℝ),
      hcancel, one_mul]

/-!
## B. Recovering the unit and measuring durations
-/

/-- The coordinate time unit inferred from two instants and the observed number of cycles
between them. Its size in seconds is the cycle count divided by the SI count and by the
coordinate duration. -/
def unitOfReadings (start stop : Time) (count : ℝ) (ht : 0 < stop -ᵥ start) (hc : 0 < count) :
    TimeUnit :=
  PositiveRealUnitCore.scale (count / ((stop -ᵥ start) * cyclesPerSecond)) seconds
    (div_pos hc (mul_pos ht (by norm_num [cyclesPerSecond])))

/-- For a uniform caesium clock, any two increasing phase readings in forward time determine
the unique calibrated unit, without a prior calibration or an independent rate measurement. -/
lemma isCalibrated_iff_eq_unitOfReadings (phase : Time →ᵃ[ℝ] ℝ) (u : TimeUnit)
    (start stop : Time) (ht : 0 < stop -ᵥ start) (hc : 0 < elapsedCycles phase start stop) :
    IsCalibrated phase u ↔
      u = unitOfReadings start stop (elapsedCycles phase start stop) ht hc := by
  have unit_ext (x y : TimeUnit) : x = y ↔ x.val = y.val :=
    ⟨congrArg TimeUnit.val, fun h ↦ PositiveRealUnitCore.ext (x := x) (y := y) h⟩
  rw [isCalibrated_iff_rate, unit_ext]
  change phase.linear 1 = u.val / 1 * cyclesPerSecond ↔
    u.val = elapsedCycles phase start stop / ((stop -ᵥ start) * cyclesPerSecond) * 1
  rw [div_one, mul_one, elapsedCycles_eq_rate,
    eq_div_iff (mul_ne_zero ht.ne' (by norm_num [cyclesPerSecond]))]
  calc
    _ ↔ u.val * cyclesPerSecond = phase.linear 1 := eq_comm
    _ ↔ (stop -ᵥ start) * (u.val * cyclesPerSecond) = (stop -ᵥ start) * phase.linear 1 :=
      (mul_right_inj' ht.ne').symm
    _ ↔ _ := by ring_nf

/-- Dividing the signed cycle count by the SI defining count gives the elapsed time in seconds,
even when the input instants use a different unit. -/
lemma elapsed_seconds {phase : Time →ᵃ[ℝ] ℝ} {u : TimeUnit} (h : IsCalibrated phase u)
    (start stop : Time) :
    elapsedCycles phase start stop / cyclesPerSecond = (stop -ᵥ start) * (u / seconds : ℝ) := by
  rw [elapsedCycles_eq_rate, (isCalibrated_iff_rate ..).1 h]
  field_simp [cyclesPerSecond]

/-- A pair of readings differs by the defining cycle count exactly when the second instant
is one SI second after the first, expressed in the coordinate unit. -/
lemma one_second_iff {phase : Time →ᵃ[ℝ] ℝ} {u : TimeUnit} (h : IsCalibrated phase u)
    (start stop : Time) :
    stop -ᵥ start = (seconds / u : ℝ) ↔ elapsedCycles phase start stop = cyclesPerSecond := by
  obtain ⟨t, ht⟩ := h
  rw [elapsedCycles_eq_rate, vadd_vsub] at ht
  have hr : phase.linear 1 ≠ 0 := by
    intro hzero
    simp [hzero, cyclesPerSecond] at ht
  rw [elapsedCycles_eq_rate, ← ht, mul_left_inj' hr]

end Time.CaesiumClock
