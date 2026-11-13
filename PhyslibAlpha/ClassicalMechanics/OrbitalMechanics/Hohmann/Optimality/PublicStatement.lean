/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chengyuan AI Lab
-/
module

public import PhyslibAlpha.ClassicalMechanics.OrbitalMechanics.Hohmann.Optimality.Fuel

/-!
# Global two-impulse Hohmann bounds

Every allowed Newtonian comparison arc satisfies the Hohmann lower bound.

## i. Overview

The global comparison is over two impulses between coplanar circular orbits with the same
orientation. The coast has free time and phase. A finite three-impulse cost comparison
distinguishes the larger class.

## ii. Key results

- `global_two_impulse_newton_lower_bound` gives the main result of this module.

## iii. Table of contents

- A. The lower bound and the finite cost comparison

## iv. References

- [ref: hohmann_prussing_1992]. Prussing studies the two-impulse global comparison.
-/

@[expose] public noncomputable section

namespace ClassicalMechanics.HohmannOptimality

/-!
## A. The lower bound and the finite cost comparison
-/

/-- Global means all feasible TWO-impulse, coplanar, co-oriented circle-to-circle
transfers, with free departure phase and flight time. A coast may have radial
velocity, negative momentum, or nonnegative energy. No third burn is allowed. -/
lemma global_two_impulse_endpoint_optimality (s : Shape) :
    (∀ z : EndpointData s, s.costH ≤ z.cost) ∧
    (hohmannEndpoints s).cost=s.costH ∧
    (∀ z : EndpointData s, z.cost=s.costH →
      z.tangent₁=s.hH ∧ z.tangent₂=s.alpha*s.hH ∧
      z.radial₁=0 ∧ z.radial₂=0) := by
  exact ⟨endpoint_total_lower_bound s, hohmannEndpoints_cost s,
    endpoint_equality_characterization s⟩

/-- The global inequality applies to genuinely differentiable Newtonian coast
arcs; conservation is proved in KeplerConservation rather than postulated. -/
theorem global_two_impulse_newton_lower_bound (p : Units) (a : KeplerArc p.mu)
    (h₀ : (a.state a.t₀).radius=p.r₁) (h₁ : (a.state a.t₁).radius=p.r₂) :
    p.bound ≤ (a.state a.t₀).impulse p.speed+(a.state a.t₁).impulse p.circular₂ :=
  KeplerArc.newton_arc_lower_bound p a h₀ h₁

/-- An unrestricted all-maneuver assertion is false: a finite 1→64→16
bielliptic construction has strictly smaller delta-v than Hohmann 1→16. -/
lemma finite_three_impulse_counterexample :
    (9/1000 : ℝ) < Bielliptic.hohmannCost 16 - Bielliptic.cost Bielliptic.«example» :=
  Bielliptic.finite_bielliptic_saves_deltaV

end ClassicalMechanics.HohmannOptimality
