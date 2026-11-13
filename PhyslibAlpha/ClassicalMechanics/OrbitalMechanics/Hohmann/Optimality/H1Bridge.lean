/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chengyuan AI Lab
-/
module

public import PhyslibAlpha.ClassicalMechanics.OrbitalMechanics.Hohmann.Dynamics.PublicStatement
public import PhyslibAlpha.ClassicalMechanics.OrbitalMechanics.Hohmann.Optimality.PublicStatement

/-!
# Attainment of the Hohmann lower bound

The explicit Hohmann trajectory attains the lower bound within the comparison class.

## i. Overview

The apsidal speeds in the explicit transfer match the normalized optimal speeds. Taking real and
imaginary parts of the Newtonian coast gives a member of the very same comparison class used for
the lower bound.

## ii. Key results

- `h1_global_two_impulse_minimum` gives the main result of this module.

## iii. Table of contents

- A. Physical attainment and the minimum

## iv. References

- [ref: hohmann_prussing_1992]. Prussing studies the two-impulse global comparison.
-/

@[expose] public noncomputable section

namespace ClassicalMechanics.HohmannOptimality

/-!
## A. Physical attainment and the minimum
-/

/-- Data conversion only; no optimality assumption is added to H1. -/
def unitsOfH1 (p : HohmannTransfer.Parameters) : Units :=
  ⟨p.mu,p.r₁,p.r₂,p.mu_pos,p.r₁_pos,p.outward⟩

lemma h1_speed (p : HohmannTransfer.Parameters) :
    (unitsOfH1 p).speed=HohmannTransfer.circularSpeed p.mu p.r₁ := rfl
lemma h1_outer_speed (p : HohmannTransfer.Parameters) :
    (unitsOfH1 p).circular₂=HohmannTransfer.circularSpeed p.mu p.r₂ :=
  (unitsOfH1 p).circular₂_eq_sqrt

lemma h1_peri_speed (p : HohmannTransfer.Parameters) :
    (unitsOfH1 p).speed*(unitsOfH1 p).shape.hH=HohmannTransfer.periSpeed p := by
  let u := unitsOfH1 p
  have hs : (u.speed*u.shape.hH)^2=(HohmannTransfer.periSpeed p)^2 := by
    rw [mul_pow, u.speed_sq, u.shape.h_sq, HohmannTransfer.periSpeed_sq]
    dsimp [u, unitsOfH1, Units.shape]
    field_simp [p.r₁_ne, p.r₂_ne, ne_of_gt p.sum_pos]
    ring_nf
    field_simp [ne_of_gt p.sum_pos]
  have hp := mul_pos u.speed_pos u.shape.h_pos
  have hq := HohmannTransfer.periSpeed_pos p
  change u.speed*u.shape.hH=HohmannTransfer.periSpeed p
  nlinarith

lemma h1_apo_speed (p : HohmannTransfer.Parameters) :
    (unitsOfH1 p).speed*((unitsOfH1 p).shape.alpha*(unitsOfH1 p).shape.hH)=
      HohmannTransfer.apoSpeed p := by
  let u := unitsOfH1 p
  have hs : (u.speed*(u.shape.alpha*u.shape.hH))^2=(HohmannTransfer.apoSpeed p)^2 := by
    rw [mul_pow, mul_pow, u.speed_sq, u.shape.h_sq, HohmannTransfer.apoSpeed_sq]
    dsimp [u, unitsOfH1, Units.shape]
    field_simp [p.r₁_ne, p.r₂_ne, ne_of_gt p.sum_pos]
    ring_nf
    field_simp [ne_of_gt p.sum_pos]
  have hp := mul_pos u.speed_pos (mul_pos u.shape.alpha_pos u.shape.h_pos)
  have hq := HohmannTransfer.apoSpeed_pos p
  change u.speed*(u.shape.alpha*u.shape.hH)=HohmannTransfer.apoSpeed p
  nlinarith

lemma h1_bound_eq_totalDeltaV (p : HohmannTransfer.Parameters) :
    (unitsOfH1 p).bound=HohmannTransfer.totalDeltaV p := by
  calc
    (unitsOfH1 p).bound =
      ((unitsOfH1 p).speed*(unitsOfH1 p).shape.hH-(unitsOfH1 p).speed) +
      ((unitsOfH1 p).circular₂-(unitsOfH1 p).speed*
        ((unitsOfH1 p).shape.alpha*(unitsOfH1 p).shape.hH)) := by
      dsimp [Units.bound, Units.circular₂, Shape.costH, Shape.burnH₁, Shape.burnH₂]
      ring
    _ = HohmannTransfer.totalDeltaV p := by
      rw [h1_peri_speed, h1_apo_speed, h1_outer_speed, h1_speed]
      rfl

/-- Physical attainment from H1 plus a global lower bound against arbitrary
smooth two-impulse competitors. Free time, free phase, fixed central field. -/
theorem h1_global_two_impulse_minimum (p : HohmannTransfer.Parameters) :
    (∀ t, deriv (deriv (HohmannTransfer.position p)) t =
      -(p.mu/‖HohmannTransfer.position p t‖^3) • HohmannTransfer.position p t) ∧
    HohmannTransfer.position p 0=HohmannTransfer.pack p.r₁ 0 ∧
    HohmannTransfer.position p p.transferTime=HohmannTransfer.pack (-p.r₂) 0 ∧
    (unitsOfH1 p).bound=
      ‖HohmannTransfer.entryImpulse p‖+‖HohmannTransfer.exitImpulse p‖ ∧
    (∀ a : KeplerArc p.mu,
      (a.state a.t₀).radius=p.r₁ → (a.state a.t₁).radius=p.r₂ →
      HohmannTransfer.totalDeltaV p ≤
        (a.state a.t₀).impulse (HohmannTransfer.circularSpeed p.mu p.r₁)+
        (a.state a.t₁).impulse (HohmannTransfer.circularSpeed p.mu p.r₂)) := by
  refine ⟨HohmannTransfer.second_deriv_position p,
    HohmannTransfer.position_departure p,HohmannTransfer.position_arrival p,?_,?_⟩
  · rw [h1_bound_eq_totalDeltaV, HohmannTransfer.totalDeltaV_eq_sum_norms]
  · intro a h₀ h₁
    have h := KeplerArc.newton_arc_lower_bound (unitsOfH1 p) a h₀ h₁
    rw [h1_bound_eq_totalDeltaV, h1_speed, h1_outer_speed] at h
    exact h

/-- The explicit H1 coast is a member of the same class used for the lower bound. -/
def h1KeplerArc (p : HohmannTransfer.Parameters) : KeplerArc p.mu where
  t₀ := 0
  t₁ := p.transferTime
  time_order := p.transferTime_pos
  x := fun t => (HohmannTransfer.position p t).re
  y := fun t => (HohmannTransfer.position p t).im
  vx := fun t => (HohmannTransfer.velocity p t).re
  vy := fun t => (HohmannTransfer.velocity p t).im
  radius_pos := by
    intro t _
    simpa only [Complex.norm_def, Complex.normSq_apply, pow_two] using
      HohmannTransfer.norm_position_pos p t
  dx := by
    intro t _
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (HohmannTransfer.hasDerivAt_position p t)
  dy := by
    intro t _
    exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (HohmannTransfer.hasDerivAt_position p t)
  dvx := by
    intro t _
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
      (HohmannTransfer.hasDerivAt_velocity_newton p t)
    simpa only [Function.comp_def, Complex.reCLM_apply, HohmannTransfer.gravity,
      Complex.smul_re, smul_eq_mul, Complex.norm_def, Complex.normSq_apply, pow_two,
      ← neg_div, div_mul_eq_mul_div] using h
  dvy := by
    intro t _
    have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t
      (HohmannTransfer.hasDerivAt_velocity_newton p t)
    simpa only [Function.comp_def, Complex.imCLM_apply, HohmannTransfer.gravity,
      Complex.smul_im, smul_eq_mul, Complex.norm_def, Complex.normSq_apply, pow_two,
      ← neg_div, div_mul_eq_mul_div] using h

lemma h1_state_radius (p : HohmannTransfer.Parameters) (t : ℝ) :
    ((h1KeplerArc p).state t).radius = ‖HohmannTransfer.position p t‖ := by
  simp only [h1KeplerArc, KeplerArc.state, PlanarState.radius, Complex.norm_def,
    Complex.normSq_apply, pow_two]

/-- The comparison cost at departure is the first Hohmann burn magnitude. -/
private lemma h1_departure_cost (p : HohmannTransfer.Parameters) :
    ((h1KeplerArc p).state 0).impulse (HohmannTransfer.circularSpeed p.mu p.r₁) =
      HohmannTransfer.deltaV₁ p := by
  have hRadius : ((h1KeplerArc p).state 0).radius = p.r₁ := by
    rw [h1_state_radius, HohmannTransfer.position_departure]
    exact HohmannTransfer.norm_pack_eq p.r₁_pos.le (by ring)
  have hAbs := abs_of_pos (HohmannTransfer.deltaV₁_pos p)
  unfold PlanarState.impulse
  rw [hRadius]
  simpa [h1KeplerArc, KeplerArc.state, HohmannTransfer.deltaV₁,
    mul_div_cancel_right₀ _ p.r₁_ne, Real.sqrt_sq_eq_abs] using hAbs

/-- The comparison cost at arrival is the second Hohmann burn magnitude. -/
private lemma h1_arrival_cost (p : HohmannTransfer.Parameters) :
    ((h1KeplerArc p).state p.transferTime).impulse (HohmannTransfer.circularSpeed p.mu p.r₂) =
      HohmannTransfer.deltaV₂ p := by
  have hRadius : ((h1KeplerArc p).state p.transferTime).radius = p.r₂ := by
    rw [h1_state_radius, HohmannTransfer.position_arrival]
    exact HohmannTransfer.norm_pack_eq p.r₂_pos.le (by ring)
  unfold PlanarState.impulse
  rw [hRadius]
  simp [h1KeplerArc, KeplerArc.state, mul_neg, neg_div, mul_div_cancel_right₀ _ p.r₂_ne,
    Real.sqrt_sq_eq_abs]
  rw [show -HohmannTransfer.apoSpeed p + HohmannTransfer.circularSpeed p.mu p.r₂ =
    HohmannTransfer.deltaV₂ p by unfold HohmannTransfer.deltaV₂; ring]
  exact abs_of_pos (HohmannTransfer.deltaV₂_pos p)

/-- The lower bound is attained within the actual Newtonian comparison class. -/
lemma h1_attains_bound_in_kepler_class (p : HohmannTransfer.Parameters) :
    ∃ a : KeplerArc p.mu,
      (a.state a.t₀).radius = p.r₁ ∧ (a.state a.t₁).radius = p.r₂ ∧
      (a.state a.t₀).impulse (unitsOfH1 p).speed +
        (a.state a.t₁).impulse (unitsOfH1 p).circular₂ = (unitsOfH1 p).bound := by
  let a := h1KeplerArc p
  have h₀ : (a.state a.t₀).radius = p.r₁ := by
    change ((h1KeplerArc p).state 0).radius = p.r₁
    rw [h1_state_radius, HohmannTransfer.position_departure]
    exact HohmannTransfer.norm_pack_eq p.r₁_pos.le (by ring)
  have h₁ : (a.state a.t₁).radius = p.r₂ := by
    change ((h1KeplerArc p).state p.transferTime).radius = p.r₂
    rw [h1_state_radius, HohmannTransfer.position_arrival]
    exact HohmannTransfer.norm_pack_eq p.r₂_pos.le (by ring)
  refine ⟨a, h₀, h₁, ?_⟩
  rw [h1_bound_eq_totalDeltaV, HohmannTransfer.totalDeltaV, h1_speed, h1_outer_speed]
  change ((h1KeplerArc p).state 0).impulse _ +
    ((h1KeplerArc p).state p.transferTime).impulse _ = _
  rw [h1_departure_cost, h1_arrival_cost]

end ClassicalMechanics.HohmannOptimality
