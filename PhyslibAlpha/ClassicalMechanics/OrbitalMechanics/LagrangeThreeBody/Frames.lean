/-
Copyright (c) 2026 Qianli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qianli Ma
-/
module

public import PhyslibAlpha.ClassicalMechanics.OrbitalMechanics.LagrangeThreeBody.Existence

/-!
# Frame changes for the Lagrange orbit
Translations, boosts, time shifts, and reversal preserve the Newtonian force law.

## i. Overview

The acceleration depends on relative positions. A constant boost adds uniform drift
to the barycentre, and time reversal produces the clockwise orbit.

## ii. Key results

- `lagrange_solution_in_frame` gives the main result of this module.

## iii. Table of contents

- A. Galilean transformations and time changes

## iv. References

Chenciner and Féjoz, [ref: chenciner_fejoz_2008], §8, gives the equilateral
reduction of the Newtonian equations for arbitrary masses.
The Lean construction is adapted from [ref: ma_lagrange_three_body_lean].
-/

@[expose] public noncomputable section
open scoped BigOperators
namespace ClassicalMechanics.LagrangeThreeBody

/-!
## A. Galilean transformations and time changes
-/

lemma translated_pair_sub {ι : Type*} (q : ι → ℂ) (a : ℂ) (i j : ι) :
    (q j + a) - (q i + a) = q j - q i := by ring

lemma gravity_translation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : ℝ) (m : ι → ℝ) (q : ι → ℂ) (a : ℂ) (i : ι) :
    gravityAcceleration G m (fun j => q j + a) i = gravityAcceleration G m q i := by
  simp only [gravityAcceleration, translated_pair_sub]

lemma firstMoment_translation {ι : Type*} [Fintype ι]
    (m : ι → ℝ) (q : ι → ℂ) (a : ℂ) :
    firstMoment m (fun i => q i + a) = firstMoment m q + totalMass m • a := by
  simp only [firstMoment, totalMass, smul_add, Finset.sum_add_distrib,
    ← Finset.sum_smul]

/-- Position in a translated and uniformly moving inertial frame. -/
def framePosition (r : ℝ → Fin 3 → ℂ) (c u : ℂ) (t : ℝ) (i : Fin 3) : ℂ :=
  r t i + (c + (t : ℂ) * u)

/-- Velocity receives the same constant boost as the reference frame. -/
def frameVelocity (v : ℝ → Fin 3 → ℂ) (u : ℂ) (t : ℝ) (i : Fin 3) : ℂ := v t i + u

lemma frame_gravity (p : Parameters) (r : ℝ → Fin 3 → ℂ)
    (c u : ℂ) (t : ℝ) (i : Fin 3) :
    gravityAcceleration p.G p.mass (framePosition r c u t) i =
      gravityAcceleration p.G p.mass (r t) i := by
  exact gravity_translation p.G p.mass (r t) (c + (t : ℂ) * u) i

lemma frame_position_derivative (r v : ℝ → Fin 3 → ℂ) (c u : ℂ)
    (h : ∀ t i, HasDerivAt (fun s => r s i) (v t i) t) (t : ℝ) (i : Fin 3) :
    HasDerivAt (fun s => framePosition r c u s i) (frameVelocity v u t i) t := by
  have hu : HasDerivAt (fun s : ℝ => c + (s : ℂ) * u) u t := by
    simpa using (((hasDerivAt_id t).ofReal_comp.mul_const u).const_add c)
  exact (h t i).add hu

/-- Galilean invariance for any solution represented by our acceptance predicate. -/
lemma satisfiesNewton_frame (p : Parameters) (r v : ℝ → Fin 3 → ℂ)
    (h : SatisfiesNewton p r v) (c u : ℂ) :
    SatisfiesNewton p (framePosition r c u) (frameVelocity v u) := by
  refine ⟨frame_position_derivative r v c u h.1, ?_, ?_⟩
  · intro t i
    rw [frame_gravity]
    exact (h.2.1 t i).add_const u
  · intro t i j hij
    exact h.2.2 t (add_right_cancel hij)

/-- A concrete family with arbitrary barycentre location and constant drift. -/
lemma lagrange_solution_in_frame (p : Parameters) (c u : ℂ) :
    SatisfiesNewton p (framePosition (trajectory p) c u) (frameVelocity (velocity p) u) := by
  exact satisfiesNewton_frame p (trajectory p) (velocity p) (trajectory_satisfiesNewton p) c u

lemma frame_equidistant (p : Parameters) (c u : ℂ) (t : ℝ) :
    Equidistant (framePosition (trajectory p) c u t) p.side := by
  intro i j hij
  simpa only [framePosition, translated_pair_sub] using trajectory_equidistant p t i j hij

lemma frame_barycentre (p : Parameters) (c u : ℂ) (t : ℝ) :
    centerOfMass p.mass (framePosition (trajectory p) c u t) = c + (t : ℂ) * u := by
  unfold centerOfMass
  change (totalMass p.mass)⁻¹ •
    firstMoment p.mass (fun i => trajectory p t i + (c + (t : ℂ) * u)) = _
  rw [firstMoment_translation, trajectory_firstMoment, zero_add, smul_smul,
    inv_mul_cancel₀ (ne_of_gt (totalMass_pos p.mass p.mass_pos)), one_smul]

lemma frame_total_momentum (p : Parameters) (u : ℂ) (t : ℝ) :
    firstMoment p.mass (frameVelocity (velocity p) u t) = totalMass p.mass • u := by
  change firstMoment p.mass (fun i => velocity p t i + u) = _
  rw [firstMoment_translation, velocity_firstMoment, zero_add]

/-- The correct return statement for a moving barycentre: return plus drift. -/
lemma frame_period_return (p : Parameters) (c u : ℂ) (t : ℝ) (i : Fin 3) :
    framePosition (trajectory p) c u (t + orbitPeriod p) i =
      framePosition (trajectory p) c u t i + (orbitPeriod p : ℂ) * u := by
  unfold framePosition
  have hperiod : trajectory p (t + orbitPeriod p) i = trajectory p t i :=
    trajectory_periodic p i t
  rw [hperiod, Complex.ofReal_add]
  ring

lemma frame_velocity_periodic (p : Parameters) (u : ℂ) (i : Fin 3) :
    Function.Periodic (fun t => frameVelocity (velocity p) u t i) (orbitPeriod p) := by
  intro t
  unfold frameVelocity
  change velocity p (t + orbitPeriod p) i + u = velocity p t i + u
  exact congrArg (fun w => w + u) (velocity_periodic p i t)

/-- Selecting a different time origin does not change Newton's equations. -/
lemma satisfiesNewton_timeShift (p : Parameters) (r v : ℝ → Fin 3 → ℂ)
    (h : SatisfiesNewton p r v) (τ : ℝ) :
    SatisfiesNewton p (fun t => r (t + τ)) (fun t => v (t + τ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t i
    have ht : HasDerivAt (fun s : ℝ => s + τ) 1 t := (hasDerivAt_id t).add_const τ
    simpa only [Function.comp_def, one_smul] using (h.1 (t + τ) i).scomp t ht
  · intro t i
    have ht : HasDerivAt (fun s : ℝ => s + τ) 1 t := (hasDerivAt_id t).add_const τ
    simpa only [Function.comp_def, one_smul] using (h.2.1 (t + τ) i).scomp t ht
  · intro t
    exact h.2.2 (t + τ)

/-- A phase-shifted, translated, uniformly drifting triangular solution. -/
lemma lagrange_shifted_frame (p : Parameters) (τ : ℝ) (c u : ℂ) :
    SatisfiesNewton p
      (framePosition (fun t => trajectory p (t + τ)) c u)
      (frameVelocity (fun t => velocity p (t + τ)) u) := by
  exact satisfiesNewton_frame p _ _
    (satisfiesNewton_timeShift p _ _ (trajectory_satisfiesNewton p) τ) c u

/-- Time reversal changes the sign of velocity, not the sign of gravity. -/
lemma satisfiesNewton_timeReverse (p : Parameters) (r v : ℝ → Fin 3 → ℂ)
    (h : SatisfiesNewton p r v) :
    SatisfiesNewton p (fun t => r (-t)) (fun t i => -v (-t) i) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t i
    have ht : HasDerivAt (fun s : ℝ => -s) (-1) t := (hasDerivAt_id t).neg
    simpa only [Function.comp_def, neg_one_smul] using (h.1 (-t) i).scomp t ht
  · intro t i
    have ht : HasDerivAt (fun s : ℝ => -s) (-1) t := (hasDerivAt_id t).neg
    have hv := ((h.2.1 (-t) i).scomp t ht).neg
    change HasDerivAt (fun s => -v (-s) i)
      (-((-1 : ℝ) • gravityAcceleration p.G p.mass (r (-t)) i)) t at hv
    simpa only [neg_one_smul, neg_neg] using hv
  · intro t
    exact h.2.2 (-t)

/-- A clockwise solution, obtained without changing the attractive force law. -/
lemma lagrange_clockwise_solution (p : Parameters) :
    SatisfiesNewton p (fun t => trajectory p (-t)) (fun t i => -velocity p (-t) i) := by
  exact satisfiesNewton_timeReverse p _ _ (trajectory_satisfiesNewton p)

lemma clockwise_equidistant (p : Parameters) (t : ℝ) :
    Equidistant (trajectory p (-t)) p.side := trajectory_equidistant p (-t)

end ClassicalMechanics.LagrangeThreeBody
