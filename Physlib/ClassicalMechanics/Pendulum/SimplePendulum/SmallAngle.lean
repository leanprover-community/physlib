/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.ClassicalMechanics.HarmonicOscillator.Solution
public import Physlib.ClassicalMechanics.Pendulum.SimplePendulum.Basic
/-!

# Small-angle motion of the simple gravity pendulum

## i. Overview

Near the bottom of its swing the torque of the simple gravity pendulum is
`-m g ℓ sin θ ≈ -m g ℓ θ`, so for small angles the equation of motion `I θ̈ = -m g ℓ sin θ`
linearizes to `I θ̈ = -m g ℓ θ`: the equation of a harmonic oscillator whose mass is the moment
of inertia `I = m ℓ²` of the pendulum and whose spring constant is the coefficient `m g ℓ` of
the linearized torque. The angular frequency `√(k/m)` of this oscillator is `√(g/ℓ)`, which is
exactly the constant `ω` of `SimplePendulum.Basic`, there described as the frequency of the
small oscillations.

This module packages the oscillator of the small oscillations as
`SimplePendulum.toHarmonicOscillator`, defines the linearized equation of motion
`θ̈ + ω² θ = 0` on the same Euclidean lift of the angle as the nonlinear equation, and proves
that for smooth lifts of the angle it is the equation of motion of the associated harmonic
oscillator, so that the solution theory of the harmonic oscillator applies verbatim to the
small oscillations of the pendulum.

The equivalence carries the whole solution theory of the oscillator over to the small
oscillations. Every choice of initial angle and initial angular velocity determines a smooth
small-angle motion, unique among the smooth solutions of the linearized equation of motion,
with the closed form `cos (ω t) x₀ + (sin (ω t)/ω) v₀`. Every small-angle motion is periodic
with the small-angle period `2π √(ℓ/g)`, in which neither the mass of the bob nor the amplitude
of the swing appears: within the linearization the pendulum is isochronous. The small-angle
motion released from rest at a given angle, the cosine `θ₀ cos (ω t)`, and its properties are
recorded in the companion module `SimplePendulum/ReleasedFromRest.lean`. The linearization is
not exact, and the final section measures what it discards: the torque differs from its
linearization `-m g ℓ θ` by exactly `m g ℓ (θ - sin θ)`, of norm at most `m g ℓ ‖θ‖³/6`, so every
small-angle motion solves the equation of motion of the pendulum itself up to a residual
cubically small in the angle.

## ii. Key results

- `SimplePendulum.toHarmonicOscillator` is the harmonic oscillator to which the pendulum
  linearizes, of mass `I = m ℓ²` and spring constant `m g ℓ`. The simp lemmas
  `toHarmonicOscillator_m` and `toHarmonicOscillator_k` record its data, and
  `toHarmonicOscillator_ω` identifies its angular frequency with the constant
  `SimplePendulum.ω` of the pendulum.
- `SimplePendulum.LinearizedEquationOfMotion` is the small-angle equation of motion
  `θ̈ + ω² θ = 0`. Its rotational Newton form is `linearizedEquationOfMotion_iff_newton`, and
  `linearizedEquationOfMotion_iff` identifies it, for smooth lifts of the angle, with the
  equation of motion of the associated harmonic oscillator. The linearization is literally
  differentiation: `fderiv_torque_zero_apply` identifies the derivative of the torque at the
  hanging equilibrium with the force of the oscillator, and
  `linearizedEquationOfMotion_iff_fderiv_torque` restates the linearized equation as the
  equation of motion with the torque replaced by that derivative.
- `SimplePendulum.smallAngleTrajectory` is the small-angle motion determined by a choice of
  initial conditions, the trajectory of the associated harmonic oscillator: it has the closed
  form `cos (ω t) x₀ + (sin (ω t)/ω) v₀` (`smallAngleTrajectory_eq`), it is smooth
  (`smallAngleTrajectory_contDiff`), it assumes its initial data at time `0`
  (`smallAngleTrajectory_at_zero`, `smallAngleTrajectory_velocity_at_zero`), and it satisfies
  the linearized equation of motion (`smallAngleTrajectory_linearizedEquationOfMotion`).
- `SimplePendulum.linearized_unique`: a smooth solution of the linearized equation of motion
  with the initial data of `IC` is `smallAngleTrajectory IC`. Together with the previous point,
  this is the existence and uniqueness of the small-angle motions.
- `SimplePendulum.smallAnglePeriod` is the period of the small oscillations, the period of the
  associated harmonic oscillator: `2π/ω` (`smallAnglePeriod_eq_two_pi_div_ω`), with closed
  form `2π √(ℓ/g)` (`smallAnglePeriod_eq`). Every small-angle trajectory is periodic with this
  period (`smallAngleTrajectory_periodic`), and along each the energy of the associated
  oscillator is the constant fixed by the initial data (`smallAngleTrajectory_energy`).
- `SimplePendulum.torque_sub_toHarmonicOscillator_force` computes the exact difference between
  the torque and the force of the associated oscillator: the term `m g ℓ (θ - sin θ)` the
  linearization discards. Its norm is at most `m g ℓ ‖θ‖³/6`
  (`norm_torque_sub_toHarmonicOscillator_force_le`), in coordinates `abs_torque_add_linear_le`,
  and `gradLagrangian_sub_toHarmonicOscillator` identifies the difference of the variational
  gradients of the two actions with the difference of torque and linearized force, with the
  norm bound `norm_gradLagrangian_sub_toHarmonicOscillator_le`.
- `SimplePendulum.norm_equationOfMotion_residual_le`: a small-angle motion nearly solves the
  equation of motion of the pendulum itself, leaving at every instant a residual of norm at
  most `m g ℓ ‖θ‖³/6` — the sense in which the small-angle theory approximates the pendulum;
  in variational form, `norm_gradLagrangian_le_of_linearizedEquationOfMotion` makes it a
  near-critical point of the pendulum's action.

## iii. Table of contents

- A. The harmonic oscillator of small oscillations
  - A.1. The associated harmonic oscillator
  - A.2. The frequency of the associated oscillator
- B. The linearized equation of motion
  - B.1. The linearized equation
  - B.2. Equivalence with the equation of motion of the oscillator
  - B.3. Linearization as differentiation of the torque
- C. Small-angle trajectories
  - C.1. The trajectory of given initial conditions
  - C.2. Existence and uniqueness
- D. The small-angle period
  - D.1. The period and its closed form
  - D.2. Periodicity and the energy of the small-angle motions
- E. The error of the linearization
  - E.1. The cubic bound on the torque
  - E.2. The variational gradients
  - E.3. The residual of the small-angle motions

## iv. References

References for the small-angle motion of the simple pendulum include:

* Huygens, Horologium Oscillatorium (1673). [ref: huygens_1673]
* Landau & Lifshitz, Mechanics, 3rd ed., §21. [ref: landau_mechanics]
* The module `Physlib.ClassicalMechanics.Pendulum.SimplePendulum.Basic`, whose equation of motion
  this module linearizes.
-/

@[expose] public section

namespace ClassicalMechanics

open Time
open scoped ContDiff

namespace SimplePendulum

variable (S : SimplePendulum)

/-!

## A. The harmonic oscillator of small oscillations

Replacing `sin θ` by `θ` in the equation of motion `I θ̈ = -m g ℓ sin θ` produces the equation
of a harmonic oscillator: the moment of inertia plays the role of the mass, and the coefficient
`m g ℓ` of the linearized torque plays the role of the spring constant. We record this
oscillator once and for all; its solution theory is the solution theory of the small
oscillations of the pendulum.

-/

/-!

### A.1. The associated harmonic oscillator

The data of the associated oscillator: the mass `I = m ℓ²` and the spring constant `m g ℓ`,
both positive because the data of the pendulum is.

-/

/-- The harmonic oscillator to which the pendulum linearizes: mass `I = m ℓ²`, spring
  constant `m g ℓ`. -/
noncomputable def toHarmonicOscillator : HarmonicOscillator where
  m := S.inertia
  k := S.m * S.g * S.ℓ
  m_pos := S.inertia_pos
  k_pos := by have := S.m_pos; have := S.g_pos; have := S.ℓ_pos; positivity

/-- The mass of the harmonic oscillator associated to the simple pendulum is the moment of
  inertia `I = m ℓ²` of the pendulum about its pivot. -/
@[simp]
lemma toHarmonicOscillator_m : S.toHarmonicOscillator.m = S.inertia := rfl

/-- The spring constant of the harmonic oscillator associated to the simple pendulum is
  `m g ℓ`, the coefficient of the linearized torque. -/
@[simp]
lemma toHarmonicOscillator_k : S.toHarmonicOscillator.k = S.m * S.g * S.ℓ := rfl

/-!

### A.2. The frequency of the associated oscillator

The angular frequency `√(k/m) = √(m g ℓ / m ℓ²)` of the associated oscillator collapses, the
mass cancelling, to `√(g/ℓ)`: the constant `ω` of the pendulum, as promised by its description
in `SimplePendulum.Basic` as the frequency of the small oscillations.

-/

/-- The angular frequency of the harmonic oscillator associated to the simple pendulum is the
  angular frequency `ω = √(g/ℓ)` of the small oscillations of the pendulum. -/
lemma toHarmonicOscillator_ω : S.toHarmonicOscillator.ω = S.ω := by
  unfold HarmonicOscillator.ω SimplePendulum.ω
  rw [toHarmonicOscillator_k, toHarmonicOscillator_m, inertia]
  congr 1
  field_simp

/-!

## B. The linearized equation of motion

The linearized equation of motion is the equation `θ̈ + ω² θ = 0` obtained from the scalar form
`θ̈ + ω² sin θ = 0` of the equation of motion by replacing `sin θ` with `θ`. It is stated, like
the nonlinear equation, on the Euclidean lift of the angle, and it is exactly the associated
harmonic oscillator's form of Newton's second law: multiplying by the moment of inertia converts
one pointwise equation into the other.

-/

/-!

### B.1. The linearized equation

The equation `θ̈ + ω² θ = 0`, together with its rotational Newton form `I θ̈ = -m g ℓ θ`, in
which the right-hand side is the force of the associated harmonic oscillator.

-/

/-- The linearized equation of motion `θ̈ + ω² θ = 0` of the simple pendulum, the small-angle
  form of the equation of motion, in which the torque is replaced by its linearization at the
  bottom of the swing. -/
def LinearizedEquationOfMotion (θ : Time → EuclideanSpace ℝ (Fin 1)) : Prop :=
  ∀ t, ∂ₜ (∂ₜ θ) t + (S.ω ^ 2) • θ t = 0

/-- The linearized equation of motion in the rotational form of Newton's second law: at every
  instant the rate of change `I θ̈` of the angular momentum equals the force `-m g ℓ θ` of the
  associated harmonic oscillator. No smoothness is required: the two pointwise equations differ
  by the nonzero factor `I`. -/
lemma linearizedEquationOfMotion_iff_newton (θ : Time → EuclideanSpace ℝ (Fin 1)) :
    S.LinearizedEquationOfMotion θ ↔
      ∀ t, S.inertia • ∂ₜ (∂ₜ θ) t = S.toHarmonicOscillator.force (θ t) := by
  simp only [LinearizedEquationOfMotion]
  refine forall_congr' fun t => ?_
  rw [S.toHarmonicOscillator.force_eq_linear, toHarmonicOscillator_k,
    neg_smul, eq_neg_iff_add_eq_zero, ← S.ω_sq_mul_inertia, mul_comm (S.ω ^ 2) S.inertia,
    ← smul_smul, ← smul_add, smul_eq_zero, or_iff_right S.inertia_ne_zero]

/-!

### B.2. Equivalence with the equation of motion of the oscillator

For a smooth lift of the angle, the linearized equation of motion is the equation of motion of
the associated harmonic oscillator, through the latter's own form of Newton's second law. The
solution theory of the harmonic oscillator thereby becomes available to the small oscillations
of the pendulum.

-/

/-- For a smooth lift of the angle, the linearized equation of motion of the simple pendulum is
  the equation of motion of the associated harmonic oscillator. The oscillator's equation of
  motion is the vanishing of the variational gradient of its action, which is totalized;
  smoothness is the regularity under which that variational description agrees with the pointwise
  one. The smoothness-free pointwise content is `linearizedEquationOfMotion_iff_newton`. -/
lemma linearizedEquationOfMotion_iff (θ : Time → EuclideanSpace ℝ (Fin 1))
    (hθ : ContDiff ℝ ∞ θ) :
    S.LinearizedEquationOfMotion θ ↔ S.toHarmonicOscillator.EquationOfMotion θ := by
  rw [S.toHarmonicOscillator.equationOfMotion_iff_newtons_2nd_law θ hθ]
  exact S.linearizedEquationOfMotion_iff_newton θ

/-!

### B.3. Linearization as differentiation of the torque

The linearized force is not an ansatz: it is the derivative of the pendulum's torque at the
hanging equilibrium. The torque vanishes at the equilibrium, so its best linear approximation
there is the derivative alone, and that derivative is exactly the force of the associated
harmonic oscillator. The linearized equation of motion is therefore the equation of motion
with the torque replaced by its derivative at the equilibrium — linearizing the pendulum is
differentiating its torque.

-/

/-- The derivative of the torque at the hanging equilibrium is the force of the associated
  harmonic oscillator: `(Dτ)(0) v = -m g ℓ v`. Linearizing the pendulum is differentiating
  its torque at the equilibrium. -/
lemma fderiv_torque_zero_apply (v : EuclideanSpace ℝ (Fin 1)) :
    fderiv ℝ S.torque 0 v = S.toHarmonicOscillator.force v := by
  have h1 := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).hasFDerivAt
    (x := (0 : EuclideanSpace ℝ (Fin 1)))
  have h2 := (Real.hasDerivAt_sin 0).comp_hasFDerivAt_of_eq
    (0 : EuclideanSpace ℝ (Fin 1)) h1 (by simp)
  have h3 := (h2.const_mul (-(S.m * S.g * S.ℓ))).smul_const
    (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))
  have hfun : S.torque = fun x : EuclideanSpace ℝ (Fin 1) =>
      (-(S.m * S.g * S.ℓ) * (Real.sin ∘ EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)) x) •
        EuclideanSpace.single (0 : Fin 1) (1 : ℝ) := by
    funext x
    rw [S.torque_eq x]
    simp [Function.comp_apply, neg_smul, neg_mul]
  rw [← hfun] at h3
  rw [h3.fderiv, S.toHarmonicOscillator.force_eq_linear, toHarmonicOscillator_k]
  ext i
  fin_cases i
  simp [smul_eq_mul, Real.cos_zero]

/-- The linearized equation of motion is the equation of motion with the torque replaced by
  its derivative at the hanging equilibrium. -/
lemma linearizedEquationOfMotion_iff_fderiv_torque (θ : Time → EuclideanSpace ℝ (Fin 1)) :
    S.LinearizedEquationOfMotion θ ↔
      ∀ t, S.inertia • ∂ₜ (∂ₜ θ) t = fderiv ℝ S.torque 0 (θ t) := by
  rw [S.linearizedEquationOfMotion_iff_newton θ]
  exact forall_congr' fun t => by rw [S.fderiv_torque_zero_apply (θ t)]

/-!

## C. Small-angle trajectories

For small angles the pendulum is approximated by its associated harmonic oscillator, and the
solution theory of the oscillator transfers verbatim: every choice of initial angle and
initial angular velocity determines a smooth motion, unique among the smooth solutions of the
linearized equation of motion. This section performs the transfer, and specializes it to the
classical motion released from rest at a given angle.

-/

/-!

### C.1. The trajectory of given initial conditions

The small-angle motion determined by an initial angle `IC.x₀` and an initial angular velocity
`IC.v₀` is the trajectory of the associated harmonic oscillator for the same initial
conditions. It is smooth in time, it assumes the prescribed initial data at time `0`, and
written out it is the familiar `cos (ω t) x₀ + (sin (ω t)/ω) v₀`, with the frequency of the
oscillator read as the `ω` of the pendulum.

-/

/-- The small-angle motion of the simple pendulum with initial angle `IC.x₀` and initial
  angular velocity `IC.v₀`: the trajectory of the associated harmonic oscillator with the same
  initial conditions. -/
noncomputable def smallAngleTrajectory (IC : HarmonicOscillator.InitialConditions) :
    Time → EuclideanSpace ℝ (Fin 1) :=
  IC.trajectory S.toHarmonicOscillator

/-- The small-angle trajectories of the simple pendulum are smooth in time. -/
@[fun_prop]
lemma smallAngleTrajectory_contDiff (IC : HarmonicOscillator.InitialConditions)
    {n : WithTop ℕ∞} : ContDiff ℝ n (S.smallAngleTrajectory IC) :=
  HarmonicOscillator.InitialConditions.trajectory_contDiff S.toHarmonicOscillator IC

/-- At time `0` the small-angle trajectory passes through its initial angle. -/
@[simp]
lemma smallAngleTrajectory_at_zero (IC : HarmonicOscillator.InitialConditions) :
    S.smallAngleTrajectory IC 0 = IC.x₀ := by
  simp [smallAngleTrajectory]

/-- At time `0` the small-angle trajectory moves with its initial angular velocity. -/
@[simp]
lemma smallAngleTrajectory_velocity_at_zero (IC : HarmonicOscillator.InitialConditions) :
    ∂ₜ (S.smallAngleTrajectory IC) 0 = IC.v₀ := by
  simp [smallAngleTrajectory]

/-- The closed form of the small-angle motion: `cos (ω t) x₀ + (sin (ω t)/ω) v₀`, the
  trajectory of the associated harmonic oscillator with its frequency read as the `ω` of the
  pendulum. -/
lemma smallAngleTrajectory_eq (IC : HarmonicOscillator.InitialConditions) :
    S.smallAngleTrajectory IC = fun t : Time =>
      Real.cos (S.ω * t.val) • IC.x₀ + (Real.sin (S.ω * t.val) / S.ω) • IC.v₀ := by
  unfold smallAngleTrajectory
  rw [HarmonicOscillator.InitialConditions.trajectory_eq, toHarmonicOscillator_ω]

/-!

### C.2. Existence and uniqueness

The small-angle trajectories solve the linearized equation of motion, and they are the only
smooth solutions: a smooth solution with the initial data of `IC` is the small-angle
trajectory of `IC`. Both statements are the corresponding statements for the associated
harmonic oscillator, read through the equivalence `linearizedEquationOfMotion_iff` of the two
equations of motion.

-/

/-- The small-angle trajectories satisfy the linearized equation of motion: for every choice
  of initial conditions the linearized equation has a smooth solution assuming them. -/
lemma smallAngleTrajectory_linearizedEquationOfMotion
    (IC : HarmonicOscillator.InitialConditions) :
    S.LinearizedEquationOfMotion (S.smallAngleTrajectory IC) :=
  (S.linearizedEquationOfMotion_iff _ (S.smallAngleTrajectory_contDiff IC)).mpr
    (HarmonicOscillator.InitialConditions.trajectory_equationOfMotion S.toHarmonicOscillator IC)

/-- Uniqueness of the small-angle motions: a smooth solution of the linearized equation of
  motion is determined by its initial angle and initial angular velocity, being the
  small-angle trajectory of those initial conditions. This is the uniqueness theorem for the
  associated harmonic oscillator, transferred through `linearizedEquationOfMotion_iff`. -/
lemma linearized_unique (IC : HarmonicOscillator.InitialConditions)
    (θ : Time → EuclideanSpace ℝ (Fin 1)) (hθ : ContDiff ℝ ∞ θ)
    (h : S.LinearizedEquationOfMotion θ) (h0 : θ 0 = IC.x₀) (hv : ∂ₜ θ 0 = IC.v₀) :
    θ = S.smallAngleTrajectory IC :=
  HarmonicOscillator.InitialConditions.trajectories_unique S.toHarmonicOscillator IC θ hθ
    ⟨(S.linearizedEquationOfMotion_iff θ hθ).mp h, h0, hv⟩

/-!

## D. The small-angle period

The associated harmonic oscillator completes one oscillation in the time `2π/ω`, and its
angular frequency is the `ω = √(g/ℓ)` of the pendulum: the small oscillations have period
`2π √(ℓ/g)`, independent of both the mass of the bob and the amplitude of the swing. Within
the linearization the pendulum is isochronous; the dependence of the true period on the
amplitude is invisible at this order.

-/

/-!

### D.1. The period and its closed form

The period of the small oscillations is the period of the associated harmonic oscillator. Its
closed form `2π √(ℓ/g)` involves only the length of the rod and the strength of gravity: the
mass of the bob cancelled from the frequency, and the amplitude never entered.

-/

/-- The period `2π √(ℓ/g)` of the small oscillations of the simple pendulum: the period of the
  associated harmonic oscillator. Within the linearization it does not depend on the
  amplitude — the small oscillations are isochronous, as derived by Huygens (1673). -/
noncomputable def smallAnglePeriod : ℝ := HarmonicOscillator.period S.toHarmonicOscillator

/-- The period of the small oscillations is `2π/ω`, one full circle of phase at the angular
  frequency `ω` of the small oscillations. -/
lemma smallAnglePeriod_eq_two_pi_div_ω : S.smallAnglePeriod = 2 * Real.pi / S.ω := by
  unfold smallAnglePeriod
  rw [HarmonicOscillator.period_eq, toHarmonicOscillator_ω]

/-- The closed form of the small-angle period: `2π √(ℓ/g)`. Neither the mass of the bob nor
  the amplitude of the swing appears. -/
lemma smallAnglePeriod_eq : S.smallAnglePeriod = 2 * Real.pi * √(S.ℓ / S.g) := by
  rw [smallAnglePeriod_eq_two_pi_div_ω]
  unfold SimplePendulum.ω
  rw [div_eq_mul_inv, ← Real.sqrt_inv, inv_div]

/-- The period of the small oscillations is positive. -/
lemma smallAnglePeriod_pos : 0 < S.smallAnglePeriod :=
  HarmonicOscillator.period_pos S.toHarmonicOscillator

/-!

### D.2. Periodicity and the energy of the small-angle motions

Advancing time by one period shifts the phase `ω t` by `2π` and so returns every small-angle
motion to its state: the small-angle trajectories are periodic with the small-angle period.
Along each of them the energy of the associated harmonic oscillator is constant, equal to the
value fixed by the initial data.

-/

/-- The small-angle trajectories of the simple pendulum are periodic with the small-angle
  period `2π √(ℓ/g)`. -/
lemma smallAngleTrajectory_periodic (IC : HarmonicOscillator.InitialConditions) :
    Function.Periodic (S.smallAngleTrajectory IC) (S.smallAnglePeriod : Time) :=
  HarmonicOscillator.trajectory_periodic S.toHarmonicOscillator IC

/-- Along a small-angle trajectory the energy of the associated harmonic oscillator is the
  constant `½ (I ‖v₀‖² + m g ℓ ‖IC.x₀‖²)` fixed by the initial data: the rotational kinetic term
  of the initial angular velocity plus the potential term of the initial angle. -/
lemma smallAngleTrajectory_energy (IC : HarmonicOscillator.InitialConditions) :
    S.toHarmonicOscillator.energy (S.smallAngleTrajectory IC) =
      fun _ => 1 / 2 * (S.inertia * ‖IC.v₀‖ ^ 2 + S.m * S.g * S.ℓ * ‖IC.x₀‖ ^ 2) :=
  HarmonicOscillator.trajectory_energy S.toHarmonicOscillator IC

/-!

## E. The error of the linearization

The linearization replaces the torque `-m g ℓ sin θ` by `-m g ℓ θ`. The replacement is not
exact, and this section measures what it discards: pointwise the two differ by
`m g ℓ (θ - sin θ)`, which the Taylor estimate for the sine bounds by `m g ℓ |θ|³/6`; the
difference of the variational gradients of the two actions is exactly this difference of the
torques, the inertial terms cancelling; and every small-angle motion solves the equation of
motion of the pendulum itself up to a residual of the same cubic size.

-/

/-!

### E.1. The cubic bound on the torque

The difference between the torque of the pendulum and the force of the associated oscillator
is exactly `m g ℓ (θ - sin θ)` times the unit vector of the angular direction, which the
Taylor estimate for the sine bounds in norm by `m g ℓ ‖θ‖³/6`: for small angles the discarded
term is cubically small. In the single coordinate of the angle the same bound reads
`m g ℓ |θ|³/6`.

-/

/-- The difference between the torque of the simple pendulum and the force of its associated
  harmonic oscillator is `m g ℓ (θ - sin θ)` times the unit vector of the angular direction:
  exactly the term the linearization discards. -/
lemma torque_sub_toHarmonicOscillator_force (x : EuclideanSpace ℝ (Fin 1)) :
    S.torque x - S.toHarmonicOscillator.force x =
      (S.m * S.g * S.ℓ * (x 0 - Real.sin (x 0))) • EuclideanSpace.single 0 1 := by
  rw [torque_eq, S.toHarmonicOscillator.force_eq_linear, toHarmonicOscillator_k]
  ext i
  fin_cases i
  simp only [Fin.isValue, neg_smul, sub_neg_eq_add, Fin.zero_eta, PiLp.add_apply,
    PiLp.neg_apply, PiLp.smul_apply, PiLp.single_eq_same, smul_eq_mul, mul_one]
  ring

/-- The normed form of the cubic bound: the torque of the simple pendulum differs from the
  force of its associated harmonic oscillator by at most `m g ℓ ‖θ‖³ / 6` in norm. -/
lemma norm_torque_sub_toHarmonicOscillator_force_le (x : EuclideanSpace ℝ (Fin 1)) :
    ‖S.torque x - S.toHarmonicOscillator.force x‖ ≤ S.m * S.g * S.ℓ * ‖x‖ ^ 3 / 6 := by
  have hc : (0 : ℝ) < S.m * S.g * S.ℓ := by
    have := S.m_pos; have := S.g_pos; have := S.ℓ_pos; positivity
  have hx : ‖x‖ = |x 0| := by
    rw [EuclideanSpace.norm_eq]
    simp [Real.sqrt_sq_eq_abs]
  rw [S.torque_sub_toHarmonicOscillator_force x, norm_smul, Real.norm_eq_abs, PiLp.norm_single,
    norm_one, mul_one, abs_mul, abs_of_pos hc, hx, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (Real.abs_sub_sin_le (x 0)) hc.le

/-- The torque of the simple pendulum differs from its linearization `-m g ℓ θ` by at most
  `m g ℓ |θ|³ / 6`: the error of the small-angle approximation is cubic in the angle. -/
lemma abs_torque_add_linear_le (x : EuclideanSpace ℝ (Fin 1)) :
    |S.torque x 0 + S.m * S.g * S.ℓ * x 0| ≤ S.m * S.g * S.ℓ * |x 0| ^ 3 / 6 := by
  have hc : (0 : ℝ) < S.m * S.g * S.ℓ := by
    have := S.m_pos; have := S.g_pos; have := S.ℓ_pos; positivity
  have key : S.torque x 0 + S.m * S.g * S.ℓ * x 0
      = S.m * S.g * S.ℓ * (x 0 - Real.sin (x 0)) := by
    calc S.torque x 0 + S.m * S.g * S.ℓ * x 0
        = (S.torque x - S.toHarmonicOscillator.force x) 0 := by
          rw [S.toHarmonicOscillator.force_eq_linear, toHarmonicOscillator_k]
          simp [PiLp.smul_apply, smul_eq_mul, sub_neg_eq_add]
      _ = S.m * S.g * S.ℓ * (x 0 - Real.sin (x 0)) := by
          rw [S.torque_sub_toHarmonicOscillator_force x]
          simp
  rw [key, abs_mul, abs_of_pos hc, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (Real.abs_sub_sin_le (x 0)) hc.le

/-!

### E.2. The variational gradients

The actions of the pendulum and of its associated oscillator have the same kinetic term, the
moment of inertia being the mass of the oscillator, so along a smooth lift of the angle the
difference of their variational gradients is the difference of torque and linearized force at
each instant: the linearization error of the dynamics is the linearization error of the
torque.

-/

/-- Along a smooth lift of the angle, the variational gradients of the actions of the simple
  pendulum and of its associated harmonic oscillator differ exactly by the difference between
  the torque and the linearized force: the inertial terms cancel. -/
lemma gradLagrangian_sub_toHarmonicOscillator (θ : Time → EuclideanSpace ℝ (Fin 1))
    (hθ : ContDiff ℝ ∞ θ) :
    S.gradLagrangian θ - S.toHarmonicOscillator.gradLagrangian θ =
      fun t => S.torque (θ t) - S.toHarmonicOscillator.force (θ t) := by
  rw [S.gradLagrangian_eq_torque θ hθ,
    S.toHarmonicOscillator.gradLagrangian_eq_force θ hθ]
  funext t
  simp only [Pi.sub_apply, toHarmonicOscillator_m]
  abel

/-- The normed form: along a smooth lift of the angle the variational gradients of the two
  actions differ at every instant by at most `m g ℓ ‖θ t‖³ / 6` — the two actions have the
  same critical-point equation to cubic accuracy in the angle. -/
lemma norm_gradLagrangian_sub_toHarmonicOscillator_le (θ : Time → EuclideanSpace ℝ (Fin 1))
    (hθ : ContDiff ℝ ∞ θ) (t : Time) :
    ‖S.gradLagrangian θ t - S.toHarmonicOscillator.gradLagrangian θ t‖ ≤
      S.m * S.g * S.ℓ * ‖θ t‖ ^ 3 / 6 := by
  have h := congrFun (S.gradLagrangian_sub_toHarmonicOscillator θ hθ) t
  rw [Pi.sub_apply] at h
  rw [h]
  exact S.norm_torque_sub_toHarmonicOscillator_force_le (θ t)

/-!

### E.3. The residual of the small-angle motions

Combining the linearized dynamics with the cubic bound: a small-angle motion does not solve
the equation of motion of the pendulum exactly, but the residual it leaves in it is cubically
small in the angle — the small-angle theory solves the pendulum's own equation up to an error
of at most `m g ℓ ‖θ‖³/6` at every instant.

-/

/-- A motion satisfying the linearized equation of motion nearly solves the equation of motion
  of the pendulum itself: at every instant the residual `I θ̈ - τ(θ)` has norm at most
  `m g ℓ ‖θ‖³ / 6`, cubically small for small angles. -/
lemma norm_equationOfMotion_residual_le (θ : Time → EuclideanSpace ℝ (Fin 1))
    (h : S.LinearizedEquationOfMotion θ) (t : Time) :
    ‖S.inertia • ∂ₜ (∂ₜ θ) t - S.torque (θ t)‖ ≤ S.m * S.g * S.ℓ * ‖θ t‖ ^ 3 / 6 := by
  rw [(S.linearizedEquationOfMotion_iff_newton θ).mp h t, ← neg_sub, norm_neg]
  exact S.norm_torque_sub_toHarmonicOscillator_force_le (θ t)


/-- The variational form of the residual: a smooth motion of the linearized dynamics is a
  near-critical point of the pendulum's own action — along it the variational gradient of the
  pendulum's action is cubically small in the angle. -/
lemma norm_gradLagrangian_le_of_linearizedEquationOfMotion
    (θ : Time → EuclideanSpace ℝ (Fin 1)) (hθ : ContDiff ℝ ∞ θ)
    (h : S.LinearizedEquationOfMotion θ) (t : Time) :
    ‖S.gradLagrangian θ t‖ ≤ S.m * S.g * S.ℓ * ‖θ t‖ ^ 3 / 6 := by
  have h0 : S.toHarmonicOscillator.gradLagrangian θ = 0 :=
    (S.toHarmonicOscillator.equationOfMotion_iff_gradLagrangian_zero θ).mp
      ((S.linearizedEquationOfMotion_iff θ hθ).mp h)
  have hb := S.norm_gradLagrangian_sub_toHarmonicOscillator_le θ hθ t
  simpa [h0] using hb

TODO "Derive the small-angle trajectories from the pendulum's own dynamics: for the solution of
  the nonlinear equation of motion with initial data scaled by `ε`, show that the motion rescaled
  by `ε⁻¹` converges to the small-angle trajectory of the unscaled data, uniformly on compact time
  intervals, as `ε → 0` — continuous dependence via a Grönwall bound, with the cubic residual of
  section E as input. This requires the global solution theory of the nonlinear equation."

end SimplePendulum

end ClassicalMechanics
