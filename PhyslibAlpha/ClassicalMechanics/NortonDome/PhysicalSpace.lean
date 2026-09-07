/-
Copyright (c) 2026 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong
-/
module

public import PhyslibAlpha.ClassicalMechanics.NortonDome.Basic
public import Physlib.SpaceAndTime.Space.Module
/-!

# The Norton dome in physical space

## i. Overview

`NortonDome.Basic` writes the dynamics on the arc length `r`, with kinetic energy `½ m ṙ²` and
potential energy `-m g h(r)`. This module identifies that chart dynamics with a point mass
constrained to the surface of the dome, as `SimplePendulum.Geometric.PhysicalSpace` does for
the pendulum.

The motion is radial, so it suffices to work in the vertical plane through the apex, with the
apex at the origin and the vertical coordinate measured upwards. The profile is the arc-length
parametrised curve `s ↦ (x(s), -h(s))`, where `x'(s)² + h'(s)² = 1` and `h'(s) = √s / g` give
`x'(s) = √(1 - s/g²)` and `x(s) = (2g²/3) (1 - (1 - s/g²)^{3/2})`. The profile exists for
`0 ≤ s ≤ g²`; at `s = g²` it is vertical and Norton's model stops. While the arc length is in
that range the chart kinetic energy is `½ m ‖v‖²` by unit speed, and the chart potential energy
is the gravitational potential `m g y` at height `y`, so the chart Lagrangian is the
constrained Lagrangian.

## ii. Key results

- `NortonDome.horizontal` is the horizontal distance `x(s)` of the profile from the apex, with
  its derivative `hasDerivAt_horizontal`; `NortonDome.unit_speed` is the identity
  `x'(s)² + h'(s)² = 1`.
- `NortonDome.profile` is the profile curve `s ↦ (x(s), -h(s))` in the vertical plane, and
  `NortonDome.dome` its image on `0 ≤ s ≤ g²`.
- `NortonDome.spaceTrajectory` is the position of the particle in the plane along a chart
  trajectory; it lies on the dome, `spaceTrajectory_mem_dome`, while the arc length is in range.
- `NortonDome.deriv_spaceTrajectory` is the velocity of the particle in the plane, with the
  square of its speed `norm_sq_deriv_spaceTrajectory`.
- `NortonDome.kineticEnergy_eq_space`, `NortonDome.potentialEnergy_eq_height`,
  `NortonDome.lagrangian_eq_space` and `NortonDome.energy_eq_space` identify the chart
  energies and Lagrangian with those of the point mass in physical space.

## iii. Table of contents

- A. The profile of the dome in the plane
  - A.1. The horizontal coordinate and the unit-speed property
  - A.2. The profile curve and the dome
- B. The particle's position along a trajectory
- C. The particle's velocity and speed
- D. The energies and the Lagrangian in physical space

## iv. References

- Norton, J. D., *The dome: an unexpectedly simple failure of determinism*, Philosophy of
  Science 75 (2008), 786–798.
- `Physlib.ClassicalMechanics.Pendulum.SimplePendulum.Geometric.PhysicalSpace` (the same
  identification for the pendulum).

-/

@[expose] public section

namespace ClassicalMechanics.NortonDome
open Real InnerProductSpace Time

variable (S : NortonDome)

/-!

## A. The profile of the dome in the plane

-/

/-!

### A.1. The horizontal coordinate and the unit-speed property

The horizontal distance from the apex has derivative `√(1 - s/g²)`; with the slope `√s / g` of
the depth this gives unit speed.

-/

/-- The horizontal distance `x(s) = (2g²/3) (1 - (1 - s/g²)^{3/2})` of the profile of the dome
  from the apex at arc length `s`. -/
noncomputable def horizontal (s : ℝ) : ℝ := 2 * S.g ^ 2 / 3 * (1 - √(1 - s / S.g ^ 2) ^ 3)

/-- The horizontal distance of the profile from the apex, written out. -/
lemma horizontal_eq (s : ℝ) :
    S.horizontal s = 2 * S.g ^ 2 / 3 * (1 - √(1 - s / S.g ^ 2) ^ 3) := rfl

/-- The profile of the dome starts at the apex. -/
lemma horizontal_zero : S.horizontal 0 = 0 := by
  simp [horizontal_eq]

/-- The derivative of the horizontal distance with respect to the arc length is `√(1 - s/g²)`,
  at every `s`. -/
lemma hasDerivAt_horizontal (s : ℝ) : HasDerivAt S.horizontal (√(1 - s / S.g ^ 2)) s := by
  have h1 : HasDerivAt (fun y : ℝ => 1 - y / S.g ^ 2) (-(1 / S.g ^ 2)) s := by
    simpa using ((hasDerivAt_id s).div_const (S.g ^ 2)).const_sub (1 : ℝ)
  have h2 := (hasDerivAt_sqrt_pow_three (1 - s / S.g ^ 2)).comp s h1
  refine ((h2.const_sub (1 : ℝ)).const_mul (2 * S.g ^ 2 / 3)).congr_deriv ?_
  field_simp

/-- The horizontal distance of the profile from the apex is a differentiable function of the
  arc length. -/
@[fun_prop]
lemma horizontal_differentiable : Differentiable ℝ S.horizontal :=
  fun s => (S.hasDerivAt_horizontal s).differentiableAt

/-- Unit speed: for arc length `0 ≤ s ≤ g²` the derivatives of the horizontal distance and
  of the depth satisfy `x'(s)² + h'(s)² = 1`, so that `s` is indeed the arc length along the
  profile. -/
lemma unit_speed {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ S.g ^ 2) :
    √(1 - s / S.g ^ 2) ^ 2 + (√s / S.g) ^ 2 = 1 := by
  have hg := S.g_pos
  have hs : 0 ≤ 1 - s / S.g ^ 2 := sub_nonneg.mpr ((div_le_one (by positivity)).mpr h1)
  rw [Real.sq_sqrt hs, div_pow, Real.sq_sqrt h0]
  field_simp
  ring

/-!

### A.2. The profile curve and the dome

-/

/-- The profile of the dome in the vertical plane through the apex: the point at arc length
  `s` is at horizontal distance `x(s)` from the apex and at height `-h(s)`. -/
noncomputable def profile (s : ℝ) : Space 2 := ⟨![S.horizontal s, -S.height s]⟩

/-- The horizontal coordinate of the profile of the dome. -/
lemma profile_apply_zero (s : ℝ) : S.profile s 0 = S.horizontal s := by
  simp [profile]

/-- The vertical coordinate of the profile of the dome is minus its depth below the apex. -/
lemma profile_apply_one (s : ℝ) : S.profile s 1 = -S.height s := by
  simp [profile]

/-- The apex of the dome is the origin. -/
lemma profile_zero : S.profile 0 = 0 := by
  ext i
  fin_cases i <;> simp [profile, horizontal_zero, height_eq]

/-- The dome, in the vertical plane through its apex: the image of the profile on the range
  `0 ≤ s ≤ g²` of arc lengths on which the profile exists. -/
noncomputable def dome : Set (Space 2) := S.profile '' Set.Icc 0 (S.g ^ 2)

/-- The point of the profile at arc length `0 ≤ s ≤ g²` lies on the dome. -/
lemma profile_mem_dome {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ S.g ^ 2) : S.profile s ∈ S.dome :=
  ⟨s, ⟨h0, h1⟩, rfl⟩

/-!

## B. The particle's position along a trajectory

Along a chart trajectory `r` the particle is at the point of the profile at arc length
`r t 0`, on the dome while that is in range.

-/

/-- The position of the particle in the plane along the chart trajectory `r` of the arc
  length. -/
noncomputable def spaceTrajectory (r : Time → EuclideanSpace ℝ (Fin 1)) : Time → Space 2 :=
  fun t => S.profile (r t 0)

/-- The horizontal position of the particle along a chart trajectory. -/
lemma spaceTrajectory_apply_zero (r : Time → EuclideanSpace ℝ (Fin 1)) (t : Time) :
    S.spaceTrajectory r t 0 = S.horizontal (r t 0) :=
  S.profile_apply_zero _

/-- The height of the particle along a chart trajectory is minus the depth of the dome at its
  arc length. -/
lemma spaceTrajectory_apply_one (r : Time → EuclideanSpace ℝ (Fin 1)) (t : Time) :
    S.spaceTrajectory r t 1 = -S.height (r t 0) :=
  S.profile_apply_one _

/-- While its arc length is in the range `0 ≤ r ≤ g²` the particle is on the dome. -/
lemma spaceTrajectory_mem_dome (r : Time → EuclideanSpace ℝ (Fin 1)) {t : Time}
    (h0 : 0 ≤ r t 0) (h1 : r t 0 ≤ S.g ^ 2) : S.spaceTrajectory r t ∈ S.dome :=
  S.profile_mem_dome h0 h1

/-!

## C. The particle's velocity and speed

The velocity in the plane is the unit tangent `(x'(r), -h'(r))` times `ṙ`, so by unit speed the
square of the speed is `ṙ²` while the arc length is in range.

-/

/-- Along a differentiable chart trajectory the position of the particle is differentiable in
  time. -/
@[fun_prop]
lemma differentiable_spaceTrajectory (r : Time → EuclideanSpace ℝ (Fin 1))
    (hr : Differentiable ℝ r) : Differentiable ℝ (S.spaceTrajectory r) := by
  unfold spaceTrajectory profile
  apply Space.mk_differentiable.comp
  rw [differentiable_pi]
  intro i
  fin_cases i <;> (simp; fun_prop)

/-- The velocity of the particle in the plane along a differentiable chart trajectory `r` is
  `(√(1 - r/g²), -√r / g)` times the rate of change `ṙ` of the arc length: the unit tangent
  vector to the profile times `ṙ`. -/
lemma deriv_spaceTrajectory (r : Time → EuclideanSpace ℝ (Fin 1)) (hr : Differentiable ℝ r)
    (t : Time) :
    ∂ₜᵥ (S.spaceTrajectory r) t =
      !₂[√(1 - r t 0 / S.g ^ 2) * (∂ₜ r t) 0, -(√(r t 0) / S.g) * (∂ₜ r t) 0] := by
  refine PiLp.ext fun i ↦ ?_
  fin_cases i <;> apply (Time.derivVec_space (by fun_prop) t _).trans
  · simp only [S.spaceTrajectory_apply_zero, Fin.zero_eta, Matrix.cons_val_zero]
    exact Time.deriv_comp_coord 0 (hr t) (S.hasDerivAt_horizontal (r t 0))
  · simp only [Fin.mk_one, S.spaceTrajectory_apply_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [Time.deriv_comp_coord (f := fun x => -S.height x) 0 (hr t)
      ((S.hasDerivAt_height (r t 0)).neg)]

/-- While the arc length is in range, the square of the speed of the particle along a
  differentiable chart trajectory is `ṙ²`. -/
lemma norm_sq_deriv_spaceTrajectory (r : Time → EuclideanSpace ℝ (Fin 1))
    (hr : Differentiable ℝ r) {t : Time} (h0 : 0 ≤ r t 0) (h1 : r t 0 ≤ S.g ^ 2) :
    ‖∂ₜᵥ (S.spaceTrajectory r) t‖ ^ 2 = ((∂ₜ r t) 0) ^ 2 := by
  rw [S.deriv_spaceTrajectory r hr t, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  show (√(1 - r t 0 / S.g ^ 2) * (∂ₜ r t) 0) ^ 2 + (-(√(r t 0) / S.g) * (∂ₜ r t) 0) ^ 2 = _
  linear_combination ((∂ₜ r t) 0) ^ 2 * S.unit_speed h0 h1

/-!

## D. The energies and the Lagrangian in physical space

The chart kinetic energy is that of the particle in the plane while the arc length is in range,
and the chart potential energy is `m g y` at its height `y` at all times; the chart Lagrangian
is the constrained Lagrangian `T - V`.

-/

/-- The chart kinetic energy of the dome along a differentiable chart trajectory is the kinetic
  energy of the particle in physical space, while the arc length is in range. -/
lemma kineticEnergy_eq_space (r : Time → EuclideanSpace ℝ (Fin 1)) (hr : Differentiable ℝ r)
    {t : Time} (h0 : 0 ≤ r t 0) (h1 : r t 0 ≤ S.g ^ 2) :
    S.kineticEnergy r t = (1 / (2 : ℝ)) * S.m * ‖∂ₜᵥ (S.spaceTrajectory r) t‖ ^ 2 := by
  rw [S.norm_sq_deriv_spaceTrajectory r hr h0 h1, kineticEnergy_eq]
  simp only [PiLp.inner_apply, Fin.sum_univ_one, RCLike.inner_apply, conj_trivial]
  ring

/-- The chart potential energy of the dome is the gravitational potential `m g y` of the
  particle at its height `y` in physical space. -/
lemma potentialEnergy_eq_height (r : Time → EuclideanSpace ℝ (Fin 1)) (t : Time) :
    S.potentialEnergy (r t) = S.m * S.g * S.spaceTrajectory r t 1 := by
  rw [potentialEnergy, S.spaceTrajectory_apply_one r t]
  ring

/-- The chart Lagrangian of the dome along a differentiable chart trajectory is the constrained
  Lagrangian of the particle in physical space, while the arc length is in range. -/
lemma lagrangian_eq_space (r : Time → EuclideanSpace ℝ (Fin 1)) (hr : Differentiable ℝ r)
    {t : Time} (h0 : 0 ≤ r t 0) (h1 : r t 0 ≤ S.g ^ 2) :
    S.lagrangian t (r t) (∂ₜ r t) =
      (1 / (2 : ℝ)) * S.m * ‖∂ₜᵥ (S.spaceTrajectory r) t‖ ^ 2
        - S.m * S.g * S.spaceTrajectory r t 1 := by
  rw [S.lagrangian_eq_kineticEnergy_sub_potentialEnergy t r, S.kineticEnergy_eq_space r hr h0 h1,
    S.potentialEnergy_eq_height r t]

/-- The chart energy of the dome along a differentiable chart trajectory is the total energy of
  the particle in physical space, while the arc length is in range. -/
lemma energy_eq_space (r : Time → EuclideanSpace ℝ (Fin 1)) (hr : Differentiable ℝ r)
    {t : Time} (h0 : 0 ≤ r t 0) (h1 : r t 0 ≤ S.g ^ 2) :
    S.energy r t =
      (1 / (2 : ℝ)) * S.m * ‖∂ₜᵥ (S.spaceTrajectory r) t‖ ^ 2
        + S.m * S.g * S.spaceTrajectory r t 1 := by
  rw [← S.kineticEnergy_eq_space r hr h0 h1, ← S.potentialEnergy_eq_height r t]
  rfl

end ClassicalMechanics.NortonDome

end
