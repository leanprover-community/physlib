/-
Copyright (c) 2026 Qianli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qianli Ma
-/
module

public import Physlib.ClassicalMechanics.PointParticle.NewtonianSystem.Basic
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Center of mass of a Newtonian system
Motion of the mass-weighted average of the particle positions in an inertial frame.

## i. Overview

The center of mass is the mass-weighted average of the particle positions. Its velocity is
the total momentum divided by the total mass. When there are no external forces,
`sum_mass_acceleration_eq_zero` from `NewtonianSystem.Basic` gives a zero derivative for
the total momentum. The center of mass then moves with constant velocity, so its position
at any time is determined by its position and the total momentum at a reference time.

## ii. Key results

- `hasDerivAt_centerOfMass` expresses the center-of-mass velocity in terms of total momentum.
- `centerOfMass_eq_of_noExternalForces` gives the center-of-mass position at any time from
  its position and the total momentum at a reference time.

## iii. Table of contents

- A. Motion of the center of mass

## iv. References

* [ref: goldstein_classicalmechanics], Chapter 1.
-/

@[expose] public noncomputable section

open scoped BigOperators Classical

namespace ClassicalMechanics.PointParticle.NewtonianSystem

open ReferenceFrame

variable {d : ℕ} (S : NewtonianSystem d)

/-!
## A. Motion of the center of mass
-/

/-- The center of mass in the system's frame coordinates. -/
def centerOfMass (t : ℝ) : S.Vector :=
  Finset.univ.centerMass (fun p : S.Particle => p.mass.val) (fun p => p.pos t)

/-- The center-of-mass velocity is the total momentum divided by the total mass. -/
lemma hasDerivAt_centerOfMass (t : ℝ) :
    HasDerivAt S.centerOfMass (S.mass⁻¹ • S.momentum t) t := by
  unfold centerOfMass Finset.centerMass momentum
  apply HasDerivAt.fun_const_smul
  apply HasDerivAt.fun_sum
  intro p _
  exact p.1.pos_twice_differentiable.1 t |>.hasDerivAt.const_smul p.mass.val

/-- In the absence of external forces, the center of mass moves with a constant velocity. -/
lemma hasDerivAt_centerOfMass_of_noExternalForces (hExt : S.externalForces = 0) (t₀ t : ℝ) :
    HasDerivAt S.centerOfMass (S.mass⁻¹ • S.momentum t₀) t := by
  have hP (u : ℝ) : HasDerivAt S.momentum 0 u := by
    rw [← S.sum_mass_acceleration_eq_zero hExt u]
    unfold momentum
    apply HasDerivAt.fun_sum
    intro p _
    exact p.1.pos_twice_differentiable.2 u |>.hasDerivAt.const_smul p.mass.val
  have h := is_const_of_deriv_eq_zero (fun u => (hP u).differentiableAt)
    (fun u => (hP u).deriv) t t₀
  simpa only [← h] using S.hasDerivAt_centerOfMass t

/-- The center of mass follows the straight line fixed by its initial position and momentum. -/
lemma centerOfMass_eq_of_noExternalForces (hExt : S.externalForces = 0) (t₀ t : ℝ) :
    S.centerOfMass t = S.centerOfMass t₀ + (t - t₀) • (S.mass⁻¹ • S.momentum t₀) := by
  let v := S.mass⁻¹ • S.momentum t₀
  have hd (u : ℝ) : HasDerivAt (fun s => S.centerOfMass s - (s - t₀) • v) 0 u := by
    have h := (S.hasDerivAt_centerOfMass_of_noExternalForces hExt t₀ u).sub
      (((hasDerivAt_id u).sub_const t₀).smul_const v)
    change HasDerivAt (fun s => S.centerOfMass s - (s - t₀) • v) (v - (1 : ℝ) • v) u at h
    simpa only [one_smul, sub_self] using h
  have hc := is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt)
    (fun u => (hd u).deriv) t t₀
  exact sub_eq_iff_eq_add.mp (by simpa only [sub_self, zero_smul, sub_zero] using hc)

end ClassicalMechanics.PointParticle.NewtonianSystem
