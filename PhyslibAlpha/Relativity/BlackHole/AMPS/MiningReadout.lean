/-
Copyright (c) 2026 AMPS formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AMPS formalization contributors
-/
module

public import PhyslibAlpha.Relativity.BlackHole.AMPS.Outcome

/-!
# A binary storage readout for a mined mode

Storage record and initial-state predictions.

## i. Overview

AMPS §3.1 includes the recovered mining equipment in the late radiation. In the ideal
measurement here a blank bit records whether an exterior oscillator has occupation `n`.
The apparatus couples to that number projector, leaves the early register untouched, and
returns a readable bit. These are physical assumptions on mode selectivity, access beneath
the angular-momentum barrier, and faithful storage and retrieval. The reversible coupling
models the transfer of one classical outcome. Absorption of the trapped energy, a trajectory
for the equipment, and its gravitational backreaction need separate dynamics.

The oscillator pair has unbounded occupation support. The measured storage statistics
bound the vacuum overlap of the initial pair, before its interaction with storage.

## ii. Key results

* `stored_conditional_pair_test`
* `stored_prediction_infalling_outcomes`

## iii. Table of contents

- A. Storage record and initial-state predictions

## iv. References

* [ref: Almheiri2013]

## A. Storage record and initial-state predictions
-/

@[expose] public section

noncomputable section

namespace AMPS.MiningReadout

open VacuumTest

/-- A storage bit and the exterior/partner pair, grouped by the two orthogonal bit states. -/
abbrev Device := PiLp 2 (fun _ : Bool => Pair)

/-- The two output bit sectors of a number-controlled flip. Within occupation `n` the
amplitudes come from the opposite storage bit, and on its complement from the same bit. -/
def controlledFlip (n : ℕ) (X : Device) : Device :=
  WithLp.toLp 2 (fun b => hit n (X (!b)) + (X b - hit n (X b)))

/-- The coupling permutes the two storage amplitudes exactly on the selected number event. -/
@[simp] lemma controlledFlip_apply (n : ℕ) (X : Device) (b : Bool) (k : ℕ × ℕ × Unit) :
    controlledFlip n X b k = if k.1 = n then X (!b) k else X b k := by
  change (if k.1 = n then X (!b) k else 0) + (X b k - (if k.1 = n then X b k else 0)) = _
  split <;> simp

/-- The same interaction run twice restores the full state, including storage coherences. -/
@[simp] lemma controlledFlip_twice (n : ℕ) (X : Device) :
    controlledFlip n (controlledFlip n X) = X := by
  ext b : 1
  apply lp.ext
  funext k
  by_cases h : k.1 = n <;> simp [h]

/-- The controlled occupation flip preserves the device norm. -/
lemma controlledFlip_norm (n : ℕ) (X : Device) : ‖controlledFlip n X‖ = ‖X‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hrow (b : Bool) : ‖controlledFlip n X b‖ ^ 2 =
      ‖hit n (X (!b))‖ ^ 2 + ‖X b - hit n (X b)‖ ^ 2 := by
    simpa only [controlledFlip, WithLp.ofLp_toLp, sq] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ (hit_inner_miss n (X (!b)) (X b))
  simp only [PiLp.norm_sq_eq_of_L2, Fintype.sum_bool, hrow, Bool.not_true, Bool.not_false]
  linarith only [hit_split_sq n (X false), hit_split_sq n (X true)]

/-- The ideal coupling is a unitary on the full pair-plus-storage Hilbert space. -/
def coupling (n : ℕ) : Device ≃ₗᵢ[ℂ] Device where
  toFun := controlledFlip n
  invFun := controlledFlip n
  left_inv := controlledFlip_twice n
  right_inv := controlledFlip_twice n
  norm_map' := controlledFlip_norm n
  map_add' x y := by
    ext b : 1
    apply lp.ext
    funext k
    by_cases h : k.1 = n <;> simp [h]
  map_smul' c x := by
    ext b : 1
    apply lp.ext
    funext k
    by_cases h : k.1 = n <;> simp [h]

/-- Prepare an initially blank storage bit next to the untouched pair. -/
def blank (x : Pair) : Device := WithLp.toLp 2 (fun b => if b then 0 else x)

@[simp] lemma norm_blank (x : Pair) : ‖blank x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [PiLp.norm_sq_eq_of_L2, blank]

/-- The pair in the stored-yes sector after coupling is the entire number-`n` projection. -/
@[simp] lemma coupling_blank_true (n : ℕ) (x : Pair) : coupling n (blank x) true = hit n x := by
  apply lp.ext
  funext k
  change controlledFlip n (blank x) true k = _
  by_cases h : k.1 = n <;> simp [h, blank, hit]

variable {R : Type*} [Fintype R]

/-- Output rows in the same early basis after recording the occupation event in storage. -/
def recorded (n : ℕ) (ψ : R → Pair) (r : R) : Device := coupling n (blank (ψ r))

/-- Born probability of early yes in the pair-plus-apparatus state. -/
def earlyProbability (yes : R → Bool) (X : R → Device) : ℝ :=
  ∑ r ∈ Finset.univ.filter (fun r => yes r = true), ‖X r‖ ^ 2

/-- Born probability that both the early test and the recovered storage bit give yes. -/
def storedJointProbability (yes : R → Bool) (X : R → Device) : ℝ :=
  ∑ r ∈ Finset.univ.filter (fun r => yes r = true), ‖X r true‖ ^ 2

/-- Probability of reading yes in storage, tracing over the full early register. -/
def storedProbability (X : R → Device) : ℝ := ∑ r, ‖X r true‖ ^ 2

@[simp] lemma earlyProbability_recorded (n : ℕ) (ψ : R → Pair) (yes : R → Bool) :
    earlyProbability yes (recorded n ψ) = markedProbability yes ψ := by
  simp [earlyProbability, markedProbability, recorded]

@[simp] lemma storedJointProbability_recorded (n : ℕ) (ψ : R → Pair) (yes : R → Bool) :
    storedJointProbability yes (recorded n ψ) = markedJointProbability yes ψ n := by
  simp [storedJointProbability, markedJointProbability, recorded, jointProbability]

@[simp] lemma storedProbability_recorded (n : ℕ) (ψ : R → Pair) :
    storedProbability (recorded n ψ) = outgoingProbability ψ n := by
  simp [storedProbability, outgoingProbability, recorded, jointProbability]

/-- For any normalized initial pair, the conditional occupation law read from the retrieved
bit bounds the rejection probability of the *initial* squeezed pair, before interaction. -/
lemma stored_conditional_pair_test (n : ℕ) (ψ : R → Pair) (yes : R → Bool)
    (hnorm : ∑ r, ‖ψ r‖ ^ 2 = 1) (ha : 0 < earlyProbability yes (recorded n ψ))
    {q : ℂ} (hq : q.normSq < 1) :
    let a := earlyProbability yes (recorded n ψ)
    let b := storedJointProbability yes (recorded n ψ)
    a * (b / a - thermalNumberWeight q n) ^ 2 ≤ 1 - pairProbability (vacuum q hq) ψ := by
  simpa using conditional_number_discrepancy hq yes ψ n hnorm (by simpa using ha)

/-- Use only the early and stored-bit probabilities after the readout to test the full-support
prediction-error criterion. A prediction above the thermal prior bounds the initial infalling
joint rejection, either individual counter as a disjunction, and the two-mode energy. -/
lemma stored_prediction_infalling_outcomes (n : ℕ) (ψ : R → Pair) (yes : R → Bool) (s g : ℝ)
    (hnorm : ∑ r, ‖ψ r‖ ^ 2 = 1) (hp : 0 < storedProbability (recorded n ψ))
    (ha : 0 < earlyProbability yes (recorded n ψ))
    (herr : let X := recorded n ψ
      storedProbability X - 2 * s * storedJointProbability yes X + s ^ 2 * earlyProbability yes X ≤
        g * storedProbability X)
    {q : ℂ} (hq : q.normSq < 1) (U : Pair ≃ₗᵢ[ℂ] InfallingPair)
    (hground : U (vacuum q hq) = infallingGround) :
    Outcome.InfallingOutcomeBounds
      (earlyProbability yes (recorded n ψ) * (max 0 (1 - g - thermalNumberWeight q n)) ^ 2)
      (fun r => U (ψ r)) := by
  rw [earlyProbability_recorded]
  apply Outcome.amps_full_support_outcomes ψ yes n s g hnorm (by simpa using hp) (by simpa using ha)
    _ hq U hground
  rw [Operational.errorWeight_eq]
  simpa using herr

end AMPS.MiningReadout
