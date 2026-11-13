/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chengyuan AI Lab
-/
module

public import PhyslibAlpha.ClassicalMechanics.OrbitalMechanics.Hohmann.Dynamics.Impulses
public import PhyslibAlpha.ClassicalMechanics.OrbitalMechanics.Hohmann.Dynamics.Invariants

/-!
# Joining the Hohmann coast to circular orbits

The incoming circle, transfer ellipse and outgoing circle share the burn positions.

## i. Overview

Each coast is defined on all real times. The flight uses them on successive intervals, with the
positions matched at the two impulses and velocities allowed to jump.

## ii. Key results

- `junction_velocity_jumps` gives the main result of this module.

## iii. Table of contents

- A. Coast arcs and their junctions

## iv. References

- [ref: hohmann_jpl_orbital_mechanics] describes the Hohmann ellipse and its apses.
-/

@[expose] public noncomputable section

namespace ClassicalMechanics.HohmannTransfer

/-!
## A. Coast arcs and their junctions
-/

/-- The inner circular coast before the departure impulse. -/
def incoming (p : Parameters) (t : ℝ) : ℂ := circularPosition p.mu p.r₁ 0 t
/-- The phase that places the outer circular orbit at the arrival apsis. -/
def outgoingPhase (p : Parameters) : ℝ := Real.pi-circularRate p.mu p.r₂*p.transferTime
/-- The outer circular coast after the arrival impulse. -/
def outgoing (p : Parameters) (t : ℝ) : ℂ :=
  circularPosition p.mu p.r₂ (outgoingPhase p) t
/-- The position throughout the two circular coasts and the transfer coast. -/
def flight (p : Parameters) (t : ℝ) : ℂ :=
  if t < 0 then incoming p t else if t ≤ p.transferTime then position p t else outgoing p t

lemma incoming_deriv (p : Parameters) (t : ℝ) :
    deriv (incoming p) t = circularVelocity p.mu p.r₁ 0 t :=
  (hasDerivAt_circularPosition _ _ _ _).deriv
lemma outgoing_deriv (p : Parameters) (t : ℝ) :
    deriv (outgoing p) t = circularVelocity p.mu p.r₂ (outgoingPhase p) t :=
  (hasDerivAt_circularPosition _ _ _ _).deriv
lemma incoming_newton (p : Parameters) (t : ℝ) :
    deriv (deriv (incoming p)) t = -(p.mu/‖incoming p t‖^3) • incoming p t :=
  circular_newton p.mu_pos p.r₁_pos 0 t
lemma outgoing_newton (p : Parameters) (t : ℝ) :
    deriv (deriv (outgoing p)) t = -(p.mu/‖outgoing p t‖^3) • outgoing p t :=
  circular_newton p.mu_pos p.r₂_pos (outgoingPhase p) t
lemma incoming_radius (p : Parameters) (t : ℝ) : ‖incoming p t‖ = p.r₁ :=
  norm_circularPosition p.r₁_pos 0 t
lemma outgoing_radius (p : Parameters) (t : ℝ) : ‖outgoing p t‖ = p.r₂ :=
  norm_circularPosition p.r₂_pos (outgoingPhase p) t
@[simp] lemma incoming_zero (p : Parameters) : incoming p 0 = pack p.r₁ 0 := by
  simp [incoming, circularPosition, pack]
lemma outgoing_angle (p : Parameters) :
    circularRate p.mu p.r₂*p.transferTime + outgoingPhase p = Real.pi := by
  unfold outgoingPhase
  ring
@[simp] lemma outgoing_arrival (p : Parameters) :
    outgoing p p.transferTime = pack (-p.r₂) 0 := by
  simp [outgoing, circularPosition, outgoing_angle, pack]
lemma incoming_velocity_zero (p : Parameters) :
    deriv (incoming p) 0 = pack 0 (circularSpeed p.mu p.r₁) := by
  rw [incoming_deriv]
  simp [circularVelocity, circularSpeed_eq_rate p.mu_pos p.r₁_pos, pack]
lemma outgoing_velocity_arrival (p : Parameters) :
    deriv (outgoing p) p.transferTime = pack 0 (-circularSpeed p.mu p.r₂) := by
  rw [outgoing_deriv]
  apply Complex.ext <;>
    simp [circularVelocity, outgoing_angle, pack, circularSpeed_eq_rate p.mu_pos p.r₂_pos]
lemma junction_positions (p : Parameters) :
    incoming p 0 = position p 0 ∧
      position p p.transferTime = outgoing p p.transferTime := by simp
lemma junction_velocity_jumps (p : Parameters) :
    deriv (position p) 0 - deriv (incoming p) 0 = entryImpulse p ∧
    deriv (outgoing p) p.transferTime - deriv (position p) p.transferTime = exitImpulse p := by
  rw [deriv_position, incoming_velocity_zero, outgoing_velocity_arrival]
  exact ⟨rfl,rfl⟩
lemma flight_before (p : Parameters) {t : ℝ} (ht : t < 0) :
    flight p t = incoming p t := by simp [flight, ht]
lemma flight_transfer (p : Parameters) {t : ℝ} (ht : t ∈ Set.Icc 0 p.transferTime) :
    flight p t = position p t := by simp [flight, not_lt.mpr ht.1, ht.2]
lemma flight_after (p : Parameters) {t : ℝ} (ht : p.transferTime < t) :
    flight p t = outgoing p t := by
  have h : ¬t<0 := not_lt.mpr (le_of_lt (lt_trans p.transferTime_pos ht))
  simp [flight, h, not_le.mpr ht]
lemma apsidal_parameters_unique (p : Parameters) {A E : ℝ}
    (_hA : 0 < A) (h₁ : A*(1-E)=p.r₁) (h₂ : A*(1+E)=p.r₂) :
    A = p.a ∧ E = p.e := by
  have ha : A = p.a := by unfold Parameters.a; nlinarith
  refine ⟨ha, ?_⟩
  unfold Parameters.e
  apply (eq_div_iff (ne_of_gt p.sum_pos)).2
  have hsum : p.r₁ + p.r₂ = 2 * A := by linarith [h₁, h₂]
  rw [hsum]
  linarith [h₁, h₂]

end ClassicalMechanics.HohmannTransfer
