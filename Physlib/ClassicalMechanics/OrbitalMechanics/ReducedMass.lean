/-
Copyright (c) 2026 Qianli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qianli Ma
-/
module

public import Physlib.ClassicalMechanics.PointParticle.NewtonianSystem.CenterOfMass
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# Reduced mass of a Newtonian binary

The kinetic energy of two particles relative to their center of mass.

## i. Overview

Each particle's velocity relative to the center of mass is its velocity relative to the
other particle scaled by the other particle's mass fraction. The sum of their kinetic
energies in the center-of-mass frame is therefore half the reduced mass times the squared
relative speed.

## ii. Key results

- `sum_relativeKineticEnergy_eq_reducedMass` gives the kinetic energy relative to the center
  of mass for a Newtonian system of two particles.

## iii. Table of contents

- A. Kinetic energy of the relative motion

## iv. References

* None.
-/

@[expose] public noncomputable section

open scoped BigOperators Classical

namespace ClassicalMechanics.PointParticle.NewtonianSystem

/-!
## A. Kinetic energy of the relative motion
-/

/-- The kinetic energy of a Newtonian binary relative to its center of mass equals half the
reduced mass times the squared relative speed. -/
lemma sum_relativeKineticEnergy_eq_reducedMass {d : ℕ} (system : NewtonianSystem d)
    (e : Fin 2 ≃ system.Particle) (t : ℝ) :
    let v := deriv system.centerOfMass t
    let m₀ := (e 0).mass.val
    let m₁ := (e 1).mass.val
    (∑ p : system.Particle, p.mass.val * ‖p.velocity t - v‖ ^ 2 / 2) =
      (m₀ * m₁ / (m₀ + m₁)) * ‖(e 1).velocity t - (e 0).velocity t‖ ^ 2 / 2 := by
  let m₀ := (e 0).mass.val
  let m₁ := (e 1).mass.val
  let v₀ := (e 0).velocity t
  let v₁ := (e 1).velocity t
  let v := deriv system.centerOfMass t
  have hv : v = (m₀ + m₁)⁻¹ • (m₀ • v₀ + m₁ • v₁) := by
    dsimp only [v]
    rw [(system.hasDerivAt_centerOfMass t).deriv]
    unfold mass momentum
    rw [← e.sum_comp (fun p => p.mass.val), ← e.sum_comp (fun p => p.momentum t)]
    simp only [Fin.sum_univ_two]
    rfl
  have hm : m₀ + m₁ ≠ 0 := ne_of_gt (add_pos (e 0).mass.property (e 1).mass.property)
  have h₀ : v₀ - v = -(m₁ / (m₀ + m₁)) • (v₁ - v₀) := by
    rw [hv]
    match_scalars <;> field_simp [hm]
    ring
  have h₁ : v₁ - v = (m₀ / (m₀ + m₁)) • (v₁ - v₀) := by
    rw [hv]
    match_scalars <;> field_simp [hm]
    ring
  change (∑ p : system.Particle, p.mass.val * ‖p.velocity t - v‖ ^ 2 / 2) = _
  rw [← e.sum_comp (fun p => p.mass.val * ‖p.velocity t - v‖ ^ 2 / 2), Fin.sum_univ_two]
  change m₀ * ‖v₀ - v‖ ^ 2 / 2 + m₁ * ‖v₁ - v‖ ^ 2 / 2 =
    (m₀ * m₁ / (m₀ + m₁)) * ‖v₁ - v₀‖ ^ 2 / 2
  rw [h₀, h₁]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp [hm]
  ring

end ClassicalMechanics.PointParticle.NewtonianSystem
