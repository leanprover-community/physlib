/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qianli Ma
-/
module

public import PhyslibAlpha.ClassicalMechanics.OrbitalMechanics.Hohmann.Optimality.EndpointBounds

/-!
# Optimality over normalized endpoint velocities

The Hohmann endpoint velocities minimize the total impulse.

## i. Overview

Conservation of normalized energy and signed angular momentum supplies the endpoint constraints.
Taking nonnegative square roots gives lower bounds for the two impulses and the equality
conditions.

## ii. Key results

- `endpoint_equality_characterization` gives the main result of this module.

## iii. Table of contents

- A. The endpoint comparison and equality case

## iv. References

- [ref: hohmann_prussing_1992]. Prussing studies the two-impulse global comparison.
-/

@[expose] public noncomputable section

namespace ClassicalMechanics.HohmannOptimality

/-!
## A. The endpoint comparison and equality case
-/
open Shape

/-- Two endpoint velocities in their own oriented radial/tangential frames.
The two conservation equalities are endpoint constraints, NOT a theorem that
arbitrary supplied data form a Kepler arc. Newton arcs are connected separately. -/
structure EndpointData (s : Shape) where
  /-- The normalized radial velocity at the inner endpoint. -/
  radial₁ : ℝ
  /-- The normalized prograde tangential velocity at the inner endpoint. -/
  tangent₁ : ℝ
  /-- The normalized radial velocity at the outer endpoint. -/
  radial₂ : ℝ
  /-- The normalized prograde tangential velocity at the outer endpoint. -/
  tangent₂ : ℝ
  /-- The endpoints have the same signed angular momentum. -/
  angular : tangent₂ = s.alpha * tangent₁
  /-- The endpoints have the same specific mechanical energy. -/
  energy : radial₁^2+tangent₁^2-2 = radial₂^2+tangent₂^2-2*s.alpha

namespace EndpointData

/-- Twice the normalized specific energy of the endpoint data. -/
def w {s : Shape} (z : EndpointData s) : ℝ := z.radial₁^2+z.tangent₁^2-2
/-- The departure impulse magnitude for the normalized endpoint data. -/
def impulse₁ {s : Shape} (z : EndpointData s) : ℝ :=
  Real.sqrt (z.radial₁^2+(z.tangent₁-1)^2)
/-- The arrival impulse magnitude for the normalized endpoint data. -/
def impulse₂ {s : Shape} (z : EndpointData s) : ℝ :=
  Real.sqrt (z.radial₂^2+(z.tangent₂-s.circularOuter)^2)
/-- The sum of the impulse magnitudes for the specified transfer. -/
def cost {s : Shape} (z : EndpointData s) : ℝ := z.impulse₁ + z.impulse₂

lemma feasible {s : Shape} (z : EndpointData s) : s.Feasible z.w z.tangent₁ := by
  constructor
  · dsimp [w]; nlinarith [sq_nonneg z.radial₁]
  · have he := z.energy
    rw [z.angular] at he
    dsimp [w]
    nlinarith [sq_nonneg z.radial₂]
lemma impulse₁_nonneg {s : Shape} (z : EndpointData s) : 0 ≤ z.impulse₁ :=
  Real.sqrt_nonneg _
lemma impulse₂_nonneg {s : Shape} (z : EndpointData s) : 0 ≤ z.impulse₂ :=
  Real.sqrt_nonneg _
lemma impulse₁_sq {s : Shape} (z : EndpointData s) :
    z.impulse₁^2 = z.radial₁^2+(z.tangent₁-1)^2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
lemma impulse₂_sq {s : Shape} (z : EndpointData s) :
    z.impulse₂^2 = z.radial₂^2+(z.tangent₂-s.circularOuter)^2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
lemma impulse₁_sq_invariant {s : Shape} (z : EndpointData s) :
    z.impulse₁^2 = s.burnSquare₁ z.w z.tangent₁ := by
  rw [z.impulse₁_sq]
  dsimp [w, burnSquare₁]
  ring
lemma impulse₂_sq_invariant {s : Shape} (z : EndpointData s) :
    z.impulse₂^2 = s.burnSquare₂ z.w z.tangent₁ := by
  rw [z.impulse₂_sq, z.angular]
  have he := z.energy
  rw [z.angular] at he
  dsimp [w, burnSquare₂]
  nlinarith [s.c_sq]

end EndpointData

/-- A global inequality over ALL feasible endpoint velocities, not merely a
stationary-point or small-perturbation calculation. -/
lemma endpoint_impulses_lower_bound (s : Shape) (z : EndpointData s) :
    s.burnH₁ ≤ z.impulse₁ ∧ s.burnH₂ ≤ z.impulse₂ := by
  have h₁ := first_square_lower_bound s z.feasible
  have h₂ := second_square_lower_bound s z.feasible
  rw [← z.impulse₁_sq_invariant] at h₁
  rw [← z.impulse₂_sq_invariant] at h₂
  constructor
  · nlinarith [s.burnH₁_pos, z.impulse₁_nonneg]
  · nlinarith [s.burnH₂_pos, z.impulse₂_nonneg]

lemma endpoint_total_lower_bound (s : Shape) (z : EndpointData s) :
    s.costH ≤ z.cost := by
  have h := endpoint_impulses_lower_bound s z
  exact add_le_add h.1 h.2

/-- A feasible corner achieving the lower bound; physical attainment is H1. -/
def hohmannEndpoints (s : Shape) : EndpointData s where
  radial₁ := 0
  tangent₁ := s.hH
  radial₂ := 0
  tangent₂ := s.alpha*s.hH
  angular := rfl
  energy := by nlinarith [s.corner_relation]

lemma hohmannEndpoints_cost (s : Shape) : (hohmannEndpoints s).cost = s.costH := by
  have h₁ : (hohmannEndpoints s).impulse₁ = s.burnH₁ := by
    have hs := (hohmannEndpoints s).impulse₁_sq
    have hn := (hohmannEndpoints s).impulse₁_nonneg
    dsimp [hohmannEndpoints, burnH₁] at *
    nlinarith [s.one_lt_h]
  have h₂ : (hohmannEndpoints s).impulse₂ = s.burnH₂ := by
    have hs := (hohmannEndpoints s).impulse₂_sq
    have hn := (hohmannEndpoints s).impulse₂_nonneg
    dsimp [hohmannEndpoints, burnH₂] at *
    nlinarith [s.alpha_h_lt_c]
  exact congrArg₂ (· + ·) h₁ h₂

/-- Equality forces both endpoint radial velocities to vanish and fixes signed
angular momentum. No claim of uniqueness of flight time or orientation. -/
lemma endpoint_equality_characterization (s : Shape) (z : EndpointData s)
    (heq : z.cost = s.costH) :
    z.tangent₁ = s.hH ∧ z.tangent₂ = s.alpha*s.hH ∧
      z.radial₁ = 0 ∧ z.radial₂ = 0 := by
  have hb := endpoint_impulses_lower_bound s z
  have he₁ : z.impulse₁ = s.burnH₁ := by
    dsimp [EndpointData.cost, costH] at heq
    linarith
  have hs : s.burnSquare₁ z.w z.tangent₁ = s.burnH₁^2 := by
    rw [← z.impulse₁_sq_invariant, he₁]
  have pair := invariant_pair_of_first_square_eq s z.feasible hs
  have htan₂ : z.tangent₂ = s.alpha*s.hH := by rw [z.angular, pair.1]
  have hu : z.radial₁=0 := by
    have hw := pair.2
    dsimp [EndpointData.w, energyH] at hw
    rw [pair.1] at hw
    nlinarith [sq_nonneg z.radial₁]
  have hv : z.radial₂=0 := by
    have he := z.energy
    rw [hu, pair.1, htan₂] at he
    nlinarith [s.corner_relation, sq_nonneg z.radial₂]
  exact ⟨pair.1, htan₂, hu, hv⟩

end ClassicalMechanics.HohmannOptimality
