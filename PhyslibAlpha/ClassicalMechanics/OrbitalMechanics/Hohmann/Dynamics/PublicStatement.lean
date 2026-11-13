/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chengyuan AI Lab
-/
module

public import PhyslibAlpha.ClassicalMechanics.OrbitalMechanics.Hohmann.Dynamics.Transfer

/-!
# Existence of an outward Hohmann transfer

Two positive ordered radii admit a tangential two-impulse transfer.

## i. Overview

The explicit ellipse joins two prograde circles at its apses. The statement exposes the time
derivatives, Newtonian equations, velocity jump norms, and transfer time in terms of the input
data.

## ii. Key results

- `exists_hohmann_transfer` gives the main result of this module.

## iii. Table of contents

- A. Existence and physical transfer identities

## iv. References

- [ref: hohmann_jpl_orbital_mechanics] describes the Hohmann ellipse and its apses.
-/

@[expose] public noncomputable section

namespace ClassicalMechanics.HohmannTransfer

/-!
## A. Existence and physical transfer identities
-/

/-- The explicit outward transfer satisfies the Newtonian equations and burn identities. -/
lemma hohmann_transfer (p : Parameters) :
    0 < p.transferTime ∧
    (∀ t, deriv (deriv (position p)) t =
      -(p.mu/‖position p t‖^3) • position p t) ∧
    (∀ t, p.r₁ ≤ ‖position p t‖ ∧ ‖position p t‖ ≤ p.r₂) ∧
    position p 0 = pack p.r₁ 0 ∧
    position p p.transferTime = pack (-p.r₂) 0 ∧
    deriv (position p) 0 = pack 0 (periSpeed p) ∧
    deriv (position p) p.transferTime = pack 0 (-apoSpeed p) ∧
    incoming p 0 = position p 0 ∧
    position p p.transferTime = outgoing p p.transferTime ∧
    (∀ t, deriv (deriv (incoming p)) t =
      -(p.mu/‖incoming p t‖^3) • incoming p t) ∧
    (∀ t, deriv (deriv (outgoing p)) t =
      -(p.mu/‖outgoing p t‖^3) • outgoing p t) ∧
    ‖deriv (position p) 0-deriv (incoming p) 0‖ = deltaV₁ p ∧
    ‖deriv (outgoing p) p.transferTime-deriv (position p) p.transferTime‖ = deltaV₂ p ∧
    0 < deltaV₁ p ∧ 0 < deltaV₂ p ∧
    deltaV₁ p = Real.sqrt (p.mu/p.r₁)*(Real.sqrt (2*p.r₂/(p.r₁+p.r₂))-1) ∧
    deltaV₂ p = Real.sqrt (p.mu/p.r₂)*(1-Real.sqrt (2*p.r₁/(p.r₁+p.r₂))) ∧
    p.transferTime = Real.pi*Real.sqrt (p.a^3/p.mu) ∧
    (∀ t, specificEnergy p.mu (position p t) (deriv (position p) t) = -p.mu/(2*p.a)) ∧
    (∀ t, cross (position p t) (deriv (position p) t) = p.a*p.b*p.n) := by
  refine ⟨p.transferTime_pos, second_deriv_position p, position_bounds p,
    position_departure p, position_arrival p, ?_, ?_,
    (junction_positions p).1, (junction_positions p).2,
    incoming_newton p, outgoing_newton p, ?_, ?_,
    deltaV₁_pos p, deltaV₂_pos p, deltaV₁_formula p, deltaV₂_formula p,
    p.transferTime_eq, coast_energy p, coast_angular_momentum p⟩
  · rw [deriv_position, velocity_departure]
  · rw [deriv_position, velocity_arrival]
  · rw [(junction_velocity_jumps p).1, entryImpulse_norm]
  · rw [(junction_velocity_jumps p).2, exitImpulse_norm]

/-- Existence without asking the reader to trust a project-defined orbit predicate.
All geometric and motion hypotheses are consequences, not input fields. -/
theorem exists_hohmann_transfer (mu r₁ r₂ : ℝ)
    (hmu : 0 < mu) (hr₁ : 0 < r₁) (horder : r₁ < r₂) :
    ∃ (q v c₁ c₂ : ℝ → ℂ) (τ d₁ d₂ : ℝ),
      0 < τ ∧ 0 < d₁ ∧ 0 < d₂ ∧
      (∀ t, HasDerivAt q (v t) t) ∧
      (∀ t, HasDerivAt v (-(mu/‖q t‖^3) • q t) t) ∧
      (∀ t, deriv (deriv q) t = -(mu/‖q t‖^3) • q t) ∧
      (∀ t, r₁ ≤ ‖q t‖ ∧ ‖q t‖ ≤ r₂) ∧
      q 0 = pack r₁ 0 ∧ q τ = pack (-r₂) 0 ∧
      (∀ t, ‖c₁ t‖ = r₁) ∧ (∀ t, ‖c₂ t‖ = r₂) ∧
      (∀ t, deriv (deriv c₁) t = -(mu/‖c₁ t‖^3) • c₁ t) ∧
      (∀ t, deriv (deriv c₂) t = -(mu/‖c₂ t‖^3) • c₂ t) ∧
      c₁ 0 = q 0 ∧ q τ = c₂ τ ∧
      v 0-deriv c₁ 0 = pack 0 d₁ ∧
      deriv c₂ τ-v τ = pack 0 (-d₂) ∧
      ‖v 0-deriv c₁ 0‖ = d₁ ∧ ‖deriv c₂ τ-v τ‖ = d₂ ∧
      d₁ = Real.sqrt (mu/r₁)*(Real.sqrt (2*r₂/(r₁+r₂))-1) ∧
      d₂ = Real.sqrt (mu/r₂)*(1-Real.sqrt (2*r₁/(r₁+r₂))) ∧
      τ = Real.pi*Real.sqrt (((r₁+r₂)/2)^3/mu) := by
  let p : Parameters := ⟨mu,r₁,r₂,hmu,hr₁,horder⟩
  refine ⟨position p,velocity p,incoming p,outgoing p,
    p.transferTime,deltaV₁ p,deltaV₂ p,p.transferTime_pos,
    deltaV₁_pos p,deltaV₂_pos p,hasDerivAt_position p,
    hasDerivAt_velocity_newton p,second_deriv_position p,position_bounds p,
    position_departure p,position_arrival p,incoming_radius p,outgoing_radius p,
    incoming_newton p,outgoing_newton p,
    (junction_positions p).1,(junction_positions p).2,?_,?_,?_,?_,
    deltaV₁_formula p,deltaV₂_formula p,p.transferTime_eq⟩
  · rw [incoming_velocity_zero]
    exact entryImpulse_eq p
  · rw [outgoing_velocity_arrival]
    exact exitImpulse_eq p
  · rw [incoming_velocity_zero]
    exact entryImpulse_norm p
  · rw [outgoing_velocity_arrival]
    exact exitImpulse_norm p

end ClassicalMechanics.HohmannTransfer
