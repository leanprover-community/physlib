/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qianli Ma
-/
module

public import PhyslibAlpha.ClassicalMechanics.OrbitalMechanics.Hohmann.Optimality.PlanarState

/-!
# Kepler conservation and two-impulse bounds

Newtonian coast arcs supply the endpoint invariants needed for the cost bound.

## i. Overview

A comparison arc has differentiable position and velocity and avoids the centre throughout a
finite interval. The Newtonian equation gives constant energy and angular momentum without
restricting their signs.

## ii. Key results

- `KeplerArc.newton_arc_lower_bound` gives the main result of this module.

## iii. Table of contents

- A. Conservation along an arbitrary comparison arc

## iv. References

- [ref: hohmann_prussing_1992]. Prussing studies the two-impulse global comparison.
-/

@[expose] public noncomputable section

namespace ClassicalMechanics.HohmannOptimality

/-!
## A. Conservation along an arbitrary comparison arc
-/
open Set

/-- A noncollision Newtonian coast over a positive finite time interval. -/
structure KeplerArc (mu : ℝ) where
  /-- The time of the departure impulse. -/
  t₀ : ℝ
  /-- The time of the arrival impulse. -/
  t₁ : ℝ
  /-- The coast takes positive time. -/
  time_order : t₀ < t₁
  /-- The first Cartesian position coordinate as a function of time. -/
  x : ℝ → ℝ
  /-- The second Cartesian position coordinate as a function of time. -/
  y : ℝ → ℝ
  /-- The first Cartesian velocity coordinate as a function of time. -/
  vx : ℝ → ℝ
  /-- The second Cartesian velocity coordinate as a function of time. -/
  vy : ℝ → ℝ
  /-- The coast stays away from the attracting centre. -/
  radius_pos : ∀ t ∈ Icc t₀ t₁, 0 < Real.sqrt (x t^2+y t^2)
  /-- The first position derivative is the first velocity component. -/
  dx : ∀ t ∈ Icc t₀ t₁, HasDerivAt x (vx t) t
  /-- The second position derivative is the second velocity component. -/
  dy : ∀ t ∈ Icc t₀ t₁, HasDerivAt y (vy t) t
  /-- The first velocity derivative obeys Newtonian central acceleration. -/
  dvx : ∀ t ∈ Icc t₀ t₁,
    HasDerivAt vx (-mu*x t/(Real.sqrt (x t^2+y t^2))^3) t
  /-- The second velocity derivative obeys Newtonian central acceleration. -/
  dvy : ∀ t ∈ Icc t₀ t₁,
    HasDerivAt vy (-mu*y t/(Real.sqrt (x t^2+y t^2))^3) t

namespace KeplerArc

/-- The Cartesian state of the coast at the given time. -/
def state {mu : ℝ} (a : KeplerArc mu) (t : ℝ) : PlanarState :=
  ⟨a.x t,a.y t,a.vx t,a.vy t⟩
lemma left_mem {mu : ℝ} (a : KeplerArc mu) : a.t₀ ∈ Icc a.t₀ a.t₁ :=
  ⟨le_rfl, le_of_lt a.time_order⟩
lemma right_mem {mu : ℝ} (a : KeplerArc mu) : a.t₁ ∈ Icc a.t₀ a.t₁ :=
  ⟨le_of_lt a.time_order, le_rfl⟩

lemma radius_deriv {mu t : ℝ} (a : KeplerArc mu) (ht : t ∈ Icc a.t₀ a.t₁) :
    HasDerivAt (fun u => (a.state u).radius)
      ((a.x t*a.vx t+a.y t*a.vy t)/(a.state t).radius) t := by
  have hr := a.radius_pos t ht
  have harg : a.x t^2+a.y t^2 ≠ 0 := by
    intro hz
    rw [hz, Real.sqrt_zero] at hr
    exact (lt_irrefl 0) hr
  have hd := (((a.dx t ht).pow 2).add ((a.dy t ht).pow 2)).sqrt harg
  convert hd using 1
  · rfl
  · simp only [state, PlanarState.radius, Pi.add_apply, Pi.pow_apply, Nat.reduceSub,
      pow_one, Nat.cast_ofNat]
    field_simp [ne_of_gt hr]

lemma angular_deriv_zero {mu t : ℝ} (a : KeplerArc mu) (ht : t ∈ Icc a.t₀ a.t₁) :
    HasDerivAt (fun u => (a.state u).angular) 0 t := by
  have hd := ((a.dx t ht).mul (a.dvy t ht)).sub ((a.dy t ht).mul (a.dvx t ht))
  convert hd using 1
  · rfl
  · field_simp [ne_of_gt (a.radius_pos t ht)]
    ring

lemma energy_deriv_zero {mu t : ℝ} (a : KeplerArc mu) (ht : t ∈ Icc a.t₀ a.t₁) :
    HasDerivAt (fun u => (a.state u).energy mu) 0 t := by
  have hr : (a.state t).radius ≠ 0 := ne_of_gt (a.radius_pos t ht)
  have hk := ((a.dvx t ht).pow 2).add ((a.dvy t ht).pow 2)
  have hp := (hasDerivAt_const t (2*mu)).div (a.radius_deriv ht) hr
  convert hk.sub hp using 1
  · rfl
  · dsimp [state, PlanarState.radius] at hr ⊢
    field_simp [hr]
    ring

lemma equal_endpoints_of_zero_deriv {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hd : ∀ t ∈ Icc a b, HasDerivAt f 0 t) : f b=f a := by
  have hc : ContinuousOn f (Icc a b) := by
    intro t ht
    exact (hd t ht).continuousAt.continuousWithinAt
  have hh : ∀ t ∈ Ico a b, HasDerivWithinAt f 0 (Ici t) t := by
    intro t ht
    exact (hd t ⟨ht.1, le_of_lt ht.2⟩).hasDerivWithinAt
  exact constant_of_has_deriv_right_zero hc hh b ⟨hab,le_rfl⟩

lemma energy_conserved {mu : ℝ} (a : KeplerArc mu) :
    (a.state a.t₀).energy mu = (a.state a.t₁).energy mu := by
  exact (equal_endpoints_of_zero_deriv (le_of_lt a.time_order)
    (fun _ ht => a.energy_deriv_zero ht)).symm

lemma angular_conserved {mu : ℝ} (a : KeplerArc mu) :
    (a.state a.t₀).angular = (a.state a.t₁).angular := by
  exact (equal_endpoints_of_zero_deriv (le_of_lt a.time_order)
    (fun _ ht => a.angular_deriv_zero ht)).symm

/-- Obtain endpoint constraints from the actual ODE; no conservation law is an
input field of KeplerArc. Endpoint orientation and coast time are unrestricted. -/
def endpoints (p : Units) (a : KeplerArc p.mu)
    (h₀ : (a.state a.t₀).radius=p.r₁) (h₁ : (a.state a.t₁).radius=p.r₂) :
    PhysicalEndpoints p where
  radial₁ := (a.state a.t₀).radial
  tangent₁ := (a.state a.t₀).tangent
  radial₂ := (a.state a.t₁).radial
  tangent₂ := (a.state a.t₁).tangent
  angular := by
    rw [← h₀, ← h₁, PlanarState.radius_mul_tangent (a.state a.t₀) (a.radius_pos _ a.left_mem),
      PlanarState.radius_mul_tangent (a.state a.t₁) (a.radius_pos _ a.right_mem)]
    exact a.angular_conserved
  energy := by
    rw [PlanarState.polar_speed_sq (a.state a.t₀) (a.radius_pos _ a.left_mem),
      PlanarState.polar_speed_sq (a.state a.t₁) (a.radius_pos _ a.right_mem), ← h₀, ← h₁]
    exact a.energy_conserved

/-- Global two-impulse lower bound for every noncollision Newtonian coast arc.
No tangency, ellipse, energy sign or positive angular momentum is assumed. -/
lemma newton_arc_lower_bound (p : Units) (a : KeplerArc p.mu)
    (h₀ : (a.state a.t₀).radius=p.r₁) (h₁ : (a.state a.t₁).radius=p.r₂) :
    p.bound ≤ (a.state a.t₀).impulse p.speed + (a.state a.t₁).impulse p.circular₂ := by
  rw [PlanarState.impulse_polar (a.state a.t₀) _ (a.radius_pos _ a.left_mem),
    PlanarState.impulse_polar (a.state a.t₁) _ (a.radius_pos _ a.right_mem)]
  exact (endpoints p a h₀ h₁).physical_lower_bound

/-- Equality of the actual Cartesian cost forces the Hohmann endpoint velocities. -/
lemma newton_arc_equality_endpoints (p : Units) (a : KeplerArc p.mu)
    (h₀ : (a.state a.t₀).radius = p.r₁) (h₁ : (a.state a.t₁).radius = p.r₂)
    (he : (a.state a.t₀).impulse p.speed + (a.state a.t₁).impulse p.circular₂ = p.bound) :
    (a.state a.t₀).radial = 0 ∧ (a.state a.t₁).radial = 0 ∧
    (a.state a.t₀).tangent = p.speed * p.shape.hH ∧
    (a.state a.t₁).tangent = p.speed * (p.shape.alpha * p.shape.hH) := by
  let z := endpoints p a h₀ h₁
  rw [PlanarState.impulse_polar (a.state a.t₀) _ (a.radius_pos _ a.left_mem),
    PlanarState.impulse_polar (a.state a.t₁) _ (a.radius_pos _ a.right_mem)] at he
  change z.cost = p.speed * p.shape.costH at he
  rw [z.cost_eq_scaled] at he
  have hnorm := mul_left_cancel₀ p.speed_ne he
  obtain ⟨ht₁, ht₂, hu₁, hu₂⟩ := endpoint_equality_characterization p.shape z.normalized hnorm
  change (a.state a.t₀).tangent / p.speed = p.shape.hH at ht₁
  change (a.state a.t₁).tangent / p.speed = p.shape.alpha * p.shape.hH at ht₂
  change (a.state a.t₀).radial / p.speed = 0 at hu₁
  change (a.state a.t₁).radial / p.speed = 0 at hu₂
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [zero_mul] using (div_eq_iff p.speed_ne).1 hu₁
  · simpa only [zero_mul] using (div_eq_iff p.speed_ne).1 hu₂
  · exact ((div_eq_iff p.speed_ne).1 ht₁).trans (mul_comm _ _)
  · exact ((div_eq_iff p.speed_ne).1 ht₂).trans (mul_comm _ _)

end KeplerArc
end ClassicalMechanics.HohmannOptimality
