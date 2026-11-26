/-
Copyright (c) 2026 Qianli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qianli Ma
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Physlib.ClassicalMechanics.PointParticle.NewtonianSystem.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring

/-!
# Work and kinetic energy of a Newtonian system

The change in total kinetic energy equals the work done by the forces on the particles.

## i. Overview

The power delivered to a particle is the inner product of its velocity with the net force
acting on it. Newton's second law identifies this power with the rate of change of the
particle's kinetic energy. Summing over particles gives the total power. When the total power
is interval integrable, its integral gives the change in total kinetic energy.

## ii. Key results

- `totalPower` sums the powers delivered to the particles.
- `hasDerivAt_kineticEnergy` gives the instantaneous work–energy relation.
- `kineticEnergy_sub_eq_integral_totalPower` gives the work–energy relation over a time interval.

## iii. Table of contents

- A. Total power and work

## iv. References

* None.
-/

@[expose] public noncomputable section

open scoped BigOperators Classical InnerProductSpace

namespace ClassicalMechanics.PointParticle.NewtonianSystem

open ReferenceFrame MeasureTheory

variable {d : ℕ} (system : NewtonianSystem d)

/-!
## A. Total power and work
-/

/-- The total power delivered by the internal and external forces at time `t`. -/
def totalPower (t : ℝ) : ℝ :=
  ∑ p : system.Particle,
    ⟪p.velocity t, netForce p system.internalForces system.externalForces t⟫_ℝ

/-- The time derivative of total kinetic energy is the total power delivered to the system. -/
lemma hasDerivAt_kineticEnergy (t : ℝ) :
    HasDerivAt system.kineticEnergy (system.totalPower t) t := by
  unfold kineticEnergy totalPower
  apply HasDerivAt.fun_sum
  intro p _
  have hv : HasDerivAt p.velocity (p.acceleration t) t :=
    (p.1.pos_twice_differentiable.2 t).hasDerivAt
  have hf : netForce p system.internalForces system.externalForces t =
      p.mass.val • p.acceleration t :=
    congrFun (system.newton_second_law p) t
  rw [hf, real_inner_smul_right]
  change HasDerivAt (fun s => p.mass.val * ‖p.velocity s‖ ^ 2 / 2)
    (p.mass.val * ⟪p.velocity t, p.acceleration t⟫_ℝ) t
  convert (hv.norm_sq.const_mul p.mass.val).div_const (2 : ℝ) using 1
  ring

/-- The change in total kinetic energy equals the work over the oriented time interval
from `a` to `b`. -/
lemma kineticEnergy_sub_eq_integral_totalPower (a b : ℝ)
    (h : IntervalIntegrable system.totalPower volume a b) :
    system.kineticEnergy b - system.kineticEnergy a = ∫ t in a..b, system.totalPower t :=
  (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => system.hasDerivAt_kineticEnergy t) h).symm

end ClassicalMechanics.PointParticle.NewtonianSystem
