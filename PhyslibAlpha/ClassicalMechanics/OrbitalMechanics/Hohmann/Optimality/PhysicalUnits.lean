/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chengyuan AI Lab
-/
module

public import PhyslibAlpha.ClassicalMechanics.OrbitalMechanics.Hohmann.Optimality.EndpointOptimality

/-!
# Restoring physical units to the Hohmann bounds

The normalized lower bound scales by the inner circular speed.

## i. Overview

The physical radial and tangential endpoint components are normalized by the inner circular
speed. The cost scales linearly and the feasibility equations are preserved.

## ii. Key results

- `PhysicalEndpoints.physical_lower_bound` gives the main result of this module.

## iii. Table of contents

- A. Physical endpoint data and normalization

## iv. References

- [ref: hohmann_prussing_1992]. Prussing studies the two-impulse global comparison.
-/

@[expose] public noncomputable section

namespace ClassicalMechanics.HohmannOptimality

/-!
## A. Physical endpoint data and normalization
-/

/-- The gravitational parameter and the ordered physical radii for the comparison. -/
structure Units where
  /-- The central gravitational parameter. -/
  mu : ℝ
  /-- The radius of the inner circular orbit. -/
  r₁ : ℝ
  /-- The radius of the outer circular orbit. -/
  r₂ : ℝ
  /-- The gravitational parameter is positive. -/
  mu_pos : 0 < mu
  /-- The inner radius is positive. -/
  r₁_pos : 0 < r₁
  /-- The outer radius exceeds the inner radius. -/
  outward : r₁ < r₂

namespace Units

lemma r₂_pos (p : Units) : 0 < p.r₂ := lt_trans p.r₁_pos p.outward
lemma r₁_ne (p : Units) : p.r₁ ≠ 0 := ne_of_gt p.r₁_pos
lemma r₂_ne (p : Units) : p.r₂ ≠ 0 := ne_of_gt p.r₂_pos

/-- The reciprocal radius ratio associated with the physical radii. -/
def shape (p : Units) : Shape where
  alpha := p.r₁/p.r₂
  alpha_pos := div_pos p.r₁_pos p.r₂_pos
  alpha_lt_one := (div_lt_one p.r₂_pos).2 p.outward

/-- The inner circular speed used as the unit of velocity. -/
def speed (p : Units) : ℝ := Real.sqrt (p.mu/p.r₁)
/-- The outer circular speed in physical units. -/
def circular₂ (p : Units) : ℝ := p.speed*p.shape.circularOuter
/-- The Hohmann cost bound in physical units. -/
def bound (p : Units) : ℝ := p.speed*p.shape.costH

lemma speed_pos (p : Units) : 0 < p.speed := Real.sqrt_pos.2 (div_pos p.mu_pos p.r₁_pos)
lemma speed_ne (p : Units) : p.speed ≠ 0 := ne_of_gt p.speed_pos
lemma speed_sq (p : Units) : p.speed^2 = p.mu/p.r₁ :=
  Real.sq_sqrt (le_of_lt (div_pos p.mu_pos p.r₁_pos))
lemma mu_over_r₂ (p : Units) : p.mu/p.r₂ = p.shape.alpha*p.speed^2 := by
  rw [p.speed_sq]
  dsimp [shape]
  field_simp [p.r₁_ne, p.r₂_ne]

lemma circular₂_eq_sqrt (p : Units) : p.circular₂ = Real.sqrt (p.mu/p.r₂) := by
  have hs : p.circular₂^2 = p.mu/p.r₂ := by
    dsimp [circular₂]
    rw [mul_pow, p.shape.c_sq, p.mu_over_r₂]
    ring
  have hn := mul_pos p.speed_pos p.shape.c_pos
  have hq := Real.sq_sqrt (le_of_lt (div_pos p.mu_pos p.r₂_pos))
  have hr := Real.sqrt_nonneg (p.mu/p.r₂)
  dsimp [circular₂] at *
  nlinarith

end Units

/-- Physical endpoint velocities sharing the same energy and angular momentum. -/
structure PhysicalEndpoints (p : Units) where
  /-- The radial velocity at the inner endpoint. -/
  radial₁ : ℝ
  /-- The prograde tangential velocity at the inner endpoint. -/
  tangent₁ : ℝ
  /-- The radial velocity at the outer endpoint. -/
  radial₂ : ℝ
  /-- The prograde tangential velocity at the outer endpoint. -/
  tangent₂ : ℝ
  /-- The endpoints have the same signed angular momentum. -/
  angular : p.r₁*tangent₁ = p.r₂*tangent₂
  /-- The endpoints have the same specific mechanical energy. -/
  energy : radial₁^2+tangent₁^2-2*p.mu/p.r₁ =
    radial₂^2+tangent₂^2-2*p.mu/p.r₂

namespace PhysicalEndpoints

/-- The sum of the impulse magnitudes for the specified transfer. -/
def cost {p : Units} (z : PhysicalEndpoints p) : ℝ :=
  Real.sqrt (z.radial₁^2+(z.tangent₁-p.speed)^2) +
  Real.sqrt (z.radial₂^2+(z.tangent₂-p.circular₂)^2)

/-- The endpoint data expressed in the inner radius and circular speed units. -/
def normalized {p : Units} (z : PhysicalEndpoints p) : EndpointData p.shape where
  radial₁ := z.radial₁/p.speed
  tangent₁ := z.tangent₁/p.speed
  radial₂ := z.radial₂/p.speed
  tangent₂ := z.tangent₂/p.speed
  angular := by
    change z.tangent₂/p.speed = (p.r₁/p.r₂)*(z.tangent₁/p.speed)
    field_simp [p.speed_ne, p.r₂_ne]
    nlinarith [z.angular]
  energy := by
    have he := z.energy
    have he' : z.radial₁^2+z.tangent₁^2-2*p.speed^2 =
        z.radial₂^2+z.tangent₂^2-2*p.shape.alpha*p.speed^2 := by
      calc
        _ = z.radial₁^2+z.tangent₁^2-2*p.mu/p.r₁ := by rw [p.speed_sq]; ring
        _ = z.radial₂^2+z.tangent₂^2-2*p.mu/p.r₂ := he
        _ = _ := by rw [show 2*p.mu/p.r₂=2*(p.mu/p.r₂) by ring, p.mu_over_r₂]; ring
    field_simp [p.speed_ne]
    nlinarith [he']

lemma norm_scale (a b v : ℝ) (hv : 0 < v) :
    v*Real.sqrt ((a/v)^2+(b/v)^2) = Real.sqrt (a^2+b^2) := by
  have h₁ := Real.sq_sqrt (add_nonneg (sq_nonneg (a/v)) (sq_nonneg (b/v)))
  have h₂ := Real.sq_sqrt (add_nonneg (sq_nonneg a) (sq_nonneg b))
  have hs : (v*Real.sqrt ((a/v)^2+(b/v)^2))^2 = a^2+b^2 := by
    rw [mul_pow, h₁]
    field_simp [ne_of_gt hv]

  have hn := mul_nonneg (le_of_lt hv) (Real.sqrt_nonneg ((a/v)^2+(b/v)^2))
  nlinarith [Real.sqrt_nonneg (a^2+b^2)]

lemma cost_eq_scaled {p : Units} (z : PhysicalEndpoints p) :
    z.cost = p.speed*z.normalized.cost := by
  dsimp [cost, normalized, EndpointData.cost, EndpointData.impulse₁, EndpointData.impulse₂]
  rw [mul_add]
  have h₁ : z.tangent₁/p.speed-1=(z.tangent₁-p.speed)/p.speed := by
    field_simp [p.speed_ne]
  have h₂ : z.tangent₂/p.speed-p.shape.circularOuter =
      (z.tangent₂-p.circular₂)/p.speed := by
    dsimp [Units.circular₂]
    field_simp [p.speed_ne]
  rw [h₁, h₂, norm_scale _ _ _ p.speed_pos, norm_scale _ _ _ p.speed_pos]

lemma physical_lower_bound {p : Units} (z : PhysicalEndpoints p) : p.bound ≤ z.cost := by
  rw [z.cost_eq_scaled]
  exact mul_le_mul_of_nonneg_left (endpoint_total_lower_bound p.shape z.normalized)
    (le_of_lt p.speed_pos)

end PhysicalEndpoints
end ClassicalMechanics.HohmannOptimality
