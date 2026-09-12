/-
Copyright (c) 2026 Florian Wiesner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuseppe Sorge, Florian Wiesner
-/
module

public import Physlib.ClassicalMechanics.DampedHarmonicOscillator.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.ODE.ExistUnique
/-!

# Solutions to the damped harmonic oscillator

## i. Overview

In this module we define the solution to the damped harmonic oscillator for given initial
conditions and prove that it satisfies the equation of motion. The solution selects the
appropriate closed form from the sign of the discriminant: trigonometric for the underdamped
case, polynomial for the critically damped case, and hyperbolic for the overdamped case.

## ii. Key results

- `InitialConditions` is a structure for the initial position and velocity.
- `trajectory` selects the appropriate regime-specific trajectory from the sign of the
  discriminant; `trajectory_eq_of_underdamped_relaxationTime` rewrites the underdamped
  solution with the relaxation time `τ`.
- `trajectory_equationOfMotion_of_underdamped`,
  `trajectory_equationOfMotion_of_criticallyDamped`, and
  `trajectory_equationOfMotion_of_overdamped` prove the selected trajectory satisfies the
  equation of motion in each damping regime.
- `trajectory_equationOfMotion` proves that the selected trajectory satisfies the equation
  of motion.
- `equationOfMotion_unique` proves that two smooth solutions with the same initial data agree, and
  `trajectories_unique` proves that the selected trajectory is the unique solution with the given
  initial conditions.

## iii. Table of contents

- A. The initial conditions
- B. Trajectories associated with the initial conditions
  - B.1. Regime-specific base trajectories
  - B.2. The selected trajectory
  - B.3. Shared calculus lemmas
  - B.4. Derivatives of the base trajectories
- C. Trajectories and equation of motion
  - C.1. The selected trajectory satisfies the equation of motion
  - C.2. Uniqueness of the solutions

## iv. References

References for the damped harmonic oscillator include:

* Landau & Lifshitz, Mechanics, page 76, section 25. [ref: landau_mechanics]
* Goldstein, Classical Mechanics, Chapter 6, Section 6.5 (Forced Vibrations and the Effect of
  Dissipative Forces). [ref: goldstein_classicalmechanics]
-/

@[expose] public section

namespace ClassicalMechanics
open Real
open Time
open ContDiff

namespace DampedHarmonicOscillator

variable (S : DampedHarmonicOscillator)

/-!

## A. The initial conditions

We define the type of initial conditions for the damped harmonic oscillator. The initial
conditions are the position and velocity at time `0`.

-/

/-- The initial conditions for the damped harmonic oscillator, specified by an initial
position and an initial velocity. -/
@[ext]
structure InitialConditions where
  /-- The initial position of the damped harmonic oscillator. -/
  x₀ : EuclideanSpace ℝ (Fin 1)
  /-- The initial velocity of the damped harmonic oscillator. -/
  v₀ : EuclideanSpace ℝ (Fin 1)

/-!

## B. Trajectories associated with the initial conditions

For each damping regime, we give an explicit formula for the trajectory with the specified
initial conditions.

### B.1. Regime-specific base trajectories

-/

/-- The oscillatory part of the underdamped trajectory before exponential decay. -/
noncomputable def underdampedBase
    (IC : InitialConditions) : Time → EuclideanSpace ℝ (Fin 1) := fun t =>
  cos (S.angularFrequency * t) • IC.x₀
    + (sin (S.angularFrequency * t)/S.angularFrequency) •
      (IC.v₀ + S.decayRate • IC.x₀)

/-- The polynomial part of the critically damped trajectory before exponential decay. -/
noncomputable def criticallyDampedBase
    (IC : InitialConditions) : Time → EuclideanSpace ℝ (Fin 1) := fun t =>
  IC.x₀ + (t : ℝ) • (IC.v₀ + S.decayRate • IC.x₀)

/-- The hyperbolic part of the overdamped trajectory before exponential decay. -/
noncomputable def overdampedBase
    (IC : InitialConditions) : Time → EuclideanSpace ℝ (Fin 1) := fun t =>
  cosh (S.angularFrequency * t) • IC.x₀
      + (sinh (S.angularFrequency * t) / S.angularFrequency) •
        (IC.v₀ + S.decayRate • IC.x₀)

/-!

### B.2. The selected trajectory

-/

/-- Given initial conditions, the solution selected from the damping regime of the
oscillator. -/
noncomputable def trajectory
    (IC : InitialConditions) : Time → EuclideanSpace ℝ (Fin 1) := by
  classical
  exact
    if S.IsUnderdamped then
      fun t : Time => exp (-S.decayRate * t) • S.underdampedBase IC t
    else if S.IsCriticallyDamped then
      fun t : Time => exp (-S.decayRate * t) • S.criticallyDampedBase IC t
    else
      fun t : Time => exp (-S.decayRate * t) • S.overdampedBase IC t

/-- In the underdamped regime, the selected trajectory uses the trigonometric base. -/
lemma trajectory_eq_of_underdamped (IC : InitialConditions) (hS : S.IsUnderdamped) :
    S.trajectory IC =
      fun t : Time => exp (-S.decayRate * t) • S.underdampedBase IC t := by
  classical
  simp [trajectory, hS]

/-- In the critically damped regime, the selected trajectory uses the polynomial base. -/
lemma trajectory_eq_of_criticallyDamped (IC : InitialConditions) (hS : S.IsCriticallyDamped) :
    S.trajectory IC =
      fun t : Time => exp (-S.decayRate * t) • S.criticallyDampedBase IC t := by
  classical
  have hnotUnder : ¬ S.IsUnderdamped := by
    rw [IsUnderdamped, IsCriticallyDamped] at *
    linarith
  simp [trajectory, hnotUnder, hS]

/-- In the overdamped regime, the selected trajectory uses the hyperbolic base. -/
lemma trajectory_eq_of_overdamped (IC : InitialConditions) (hS : S.IsOverdamped) :
    S.trajectory IC =
      fun t : Time => exp (-S.decayRate * t) • S.overdampedBase IC t := by
  classical
  rw [IsOverdamped] at hS
  have hnotUnder : ¬ S.IsUnderdamped := by
    rw [IsUnderdamped]
    linarith
  have hnotCritical : ¬ S.IsCriticallyDamped := by
    rw [IsCriticallyDamped]
    linarith
  simp [trajectory, hnotUnder, hnotCritical]

/-- In the underdamped regime, the selected trajectory is `exp (-t / τ)` times the
trigonometric base, `τ` being the relaxation time. -/
lemma trajectory_eq_of_underdamped_relaxationTime (IC : InitialConditions)
    (hS : S.IsUnderdamped) :
    S.trajectory IC =
      fun t : Time => exp (-(t : ℝ) / S.relaxationTime) • S.underdampedBase IC t := by
  rw [S.trajectory_eq_of_underdamped IC hS]
  funext t
  rw [S.exp_neg_decayRate_mul t]

/-- The selected trajectory is smooth. -/
lemma trajectory_contDiff (IC : InitialConditions) :
    ContDiff ℝ ∞ (S.trajectory IC) := by
  rcases S.isUnderdamped_or_isCriticallyDamped_or_isOverdamped with hS | hS | hS
  · rw [S.trajectory_eq_of_underdamped IC hS]
    unfold underdampedBase
    fun_prop
  · rw [S.trajectory_eq_of_criticallyDamped IC hS]
    unfold criticallyDampedBase
    fun_prop
  · rw [S.trajectory_eq_of_overdamped IC hS]
    unfold overdampedBase
    fun_prop

/-- The selected trajectory has initial position `IC.x₀`. -/
lemma trajectory_apply_zero (IC : InitialConditions) : S.trajectory IC 0 = IC.x₀ := by
  rcases S.isUnderdamped_or_isCriticallyDamped_or_isOverdamped with hS | hS | hS
  · rw [S.trajectory_eq_of_underdamped IC hS]
    simp [underdampedBase]
  · rw [S.trajectory_eq_of_criticallyDamped IC hS]
    simp [criticallyDampedBase]
  · rw [S.trajectory_eq_of_overdamped IC hS]
    simp [overdampedBase]

/-!

### B.3. Shared calculus lemmas

The three solution formulas all have the form `exp (-a * t) • y t`. The following private
lemmas compute the first and second derivatives of that expression and package the common
equation-of-motion argument.

-/

private lemma exp_decay_smul_velocity
    (a : ℝ) (y : Time → EuclideanSpace ℝ (Fin 1)) (hy : Differentiable ℝ y) :
    ∂ₜ (fun t : Time => exp (-a * t.val) • y t) =
      fun t : Time => exp (-a * t.val) • (∂ₜ y t - a • y t) := by
  funext t
  rw [Time.deriv]
  rw [fderiv_fun_smul (by fun_prop) (hy t)]
  rw [fderiv_exp (by fun_prop), fderiv_fun_mul (by fun_prop) (by fun_prop)]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply,
    fderiv_fun_neg, fderiv_fun_const, Pi.zero_apply, Time.fderiv_val,
    _root_.neg_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [← Time.deriv_eq]
  simp [smul_sub, smul_smul]
  module

private lemma exp_decay_smul_acceleration
    (a μ : ℝ) (y : Time → EuclideanSpace ℝ (Fin 1))
    (hy : Differentiable ℝ y) (hdy : Differentiable ℝ (∂ₜ y))
    (hy'' : ∂ₜ (∂ₜ y) = fun t => μ • y t) :
    ∂ₜ (∂ₜ (fun t : Time => exp (-a * t.val) • y t)) =
      fun t : Time => exp (-a * t.val) •
        (μ • y t - (2 * a) • ∂ₜ y t + a^2 • y t) := by
  rw [exp_decay_smul_velocity a y hy]
  funext t
  rw [Time.deriv]
  rw [fderiv_fun_smul (by fun_prop) (by fun_prop)]
  rw [fderiv_exp (by fun_prop), fderiv_fun_mul (by fun_prop) (by fun_prop)]
  rw [fderiv_fun_sub (hdy t) (by fun_prop)]
  rw [fderiv_fun_const_smul (hy t)]
  have hy''_t := congrFun hy'' t
  rw [Time.deriv] at hy''_t
  simp only [add_apply, _root_.sub_apply,
    ContinuousLinearMap.smulRight_apply, fderiv_fun_neg, fderiv_fun_const,
    Pi.zero_apply, Time.fderiv_val, _root_.neg_apply,
    FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [hy''_t, ← Time.deriv_eq]
  simp [smul_add, smul_sub, smul_smul]
  module

private lemma exp_decay_smul_equationOfMotion
    (a μ : ℝ) (y : Time → EuclideanSpace ℝ (Fin 1))
    (hy : Differentiable ℝ y) (hdy : Differentiable ℝ (∂ₜ y))
    (hy'' : ∂ₜ (∂ₜ y) = fun t => μ • y t)
    (hγ : S.γ = 2 * S.m * a) (hk : S.k = S.m * (a^2 - μ)) :
    S.EquationOfMotion (fun t : Time => exp (-a * t.val) • y t) := by
  intro t
  rw [exp_decay_smul_acceleration a μ y hy hdy hy'']
  rw [exp_decay_smul_velocity a y hy]
  rw [hγ, hk]
  simp [smul_add, smul_sub, smul_smul]
  module

/-!

### B.4. Derivatives of the base trajectories

The remaining private lemmas compute the velocity and acceleration of the trigonometric,
polynomial, and hyperbolic base trajectories before the exponential decay factor is applied.

-/

private lemma criticallyDampedBase_velocity (IC : InitialConditions) :
    ∂ₜ (S.criticallyDampedBase IC) =
      fun _ : Time => IC.v₀ + S.decayRate • IC.x₀ := by
  funext t
  change ∂ₜ (fun t : Time =>
    IC.x₀ + t.val • (IC.v₀ + S.decayRate • IC.x₀)) t = _
  rw [Time.deriv_eq, fderiv_fun_add (by fun_prop) (by fun_prop),
    fderiv_fun_const, fderiv_smul_const (by fun_prop)]
  simp

private lemma criticallyDampedBase_acceleration (IC : InitialConditions) :
    ∂ₜ (∂ₜ (S.criticallyDampedBase IC)) =
      fun _ => (0 : EuclideanSpace ℝ (Fin 1)) := by
  rw [criticallyDampedBase_velocity]
  funext t
  simp

private lemma underdampedBase_velocity (IC : InitialConditions) (hS : S.IsUnderdamped) :
    ∂ₜ (fun t : Time =>
      cos (S.angularFrequency * t.val) • IC.x₀ +
        (sin (S.angularFrequency * t.val) / S.angularFrequency) •
          (IC.v₀ + S.decayRate • IC.x₀)) =
    fun t : Time =>
      (-S.angularFrequency * sin (S.angularFrequency * t.val)) • IC.x₀ +
        cos (S.angularFrequency * t.val) •
          (IC.v₀ + S.decayRate • IC.x₀) := by
  have hΩ : S.angularFrequency ≠ 0 := S.angularFrequency_ne_zero_of_underdamped hS
  funext t
  have fderiv_comp_val_eq_deriv : ∀ g : ℝ → ℝ, DifferentiableAt ℝ g t.val →
      (fderiv ℝ (fun s : Time => g s.val) t) 1 = _root_.deriv g t.val := by
    intro g hg
    rw [fderiv_fun_comp t hg (by fun_prop), ContinuousLinearMap.comp_apply, Time.fderiv_val]
    simp
  rw [Time.deriv_eq, fderiv_fun_add (by fun_prop) (by fun_prop),
    fderiv_smul_const (by fun_prop), fderiv_smul_const (by fun_prop)]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply]
  rw [fderiv_comp_val_eq_deriv (fun s => cos (S.angularFrequency * s)) (by fun_prop),
    fderiv_comp_val_eq_deriv (fun s => sin (S.angularFrequency * s) / S.angularFrequency)
      (by fun_prop)]
  simp [mul_comm, hΩ]

private lemma underdampedBase_acceleration (IC : InitialConditions) (hS : S.IsUnderdamped) :
    ∂ₜ (∂ₜ (fun t : Time =>
      cos (S.angularFrequency * t.val) • IC.x₀ +
        (sin (S.angularFrequency * t.val) / S.angularFrequency) •
          (IC.v₀ + S.decayRate • IC.x₀))) =
    fun t : Time => -S.angularFrequency^2 •
      (cos (S.angularFrequency * t.val) • IC.x₀ +
        (sin (S.angularFrequency * t.val) / S.angularFrequency) •
          (IC.v₀ + S.decayRate • IC.x₀)) := by
  have hΩ : S.angularFrequency ≠ 0 := S.angularFrequency_ne_zero_of_underdamped hS
  rw [S.underdampedBase_velocity IC hS]
  funext t
  have fderiv_comp_val_eq_deriv : ∀ g : ℝ → ℝ, DifferentiableAt ℝ g t.val →
      (fderiv ℝ (fun s : Time => g s.val) t) 1 = _root_.deriv g t.val := by
    intro g hg
    rw [fderiv_fun_comp t hg (by fun_prop), ContinuousLinearMap.comp_apply, Time.fderiv_val]
    simp
  rw [Time.deriv_eq, fderiv_fun_add (by fun_prop) (by fun_prop),
    fderiv_smul_const (by fun_prop), fderiv_smul_const (by fun_prop)]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply]
  rw [fderiv_comp_val_eq_deriv (fun s => -S.angularFrequency * sin (S.angularFrequency * s))
      (by fun_prop),
    fderiv_comp_val_eq_deriv (fun s => cos (S.angularFrequency * s)) (by fun_prop)]
  simp [mul_comm, smul_smul, smul_add]
  field_simp [hΩ]

private lemma overdampedBase_velocity (IC : InitialConditions) (hS : S.IsOverdamped) :
    ∂ₜ (fun t : Time =>
      cosh (S.angularFrequency * t.val) • IC.x₀ +
        (sinh (S.angularFrequency * t.val) / S.angularFrequency) •
          (IC.v₀ + S.decayRate • IC.x₀)) =
    fun t : Time =>
      (S.angularFrequency * sinh (S.angularFrequency * t.val)) • IC.x₀ +
        cosh (S.angularFrequency * t.val) •
          (IC.v₀ + S.decayRate • IC.x₀) := by
  have hΩ : S.angularFrequency ≠ 0 := S.angularFrequency_ne_zero_of_overdamped hS
  funext t
  have fderiv_comp_val_eq_deriv : ∀ g : ℝ → ℝ, DifferentiableAt ℝ g t.val →
      (fderiv ℝ (fun s : Time => g s.val) t) 1 = _root_.deriv g t.val := by
    intro g hg
    rw [fderiv_fun_comp t hg (by fun_prop), ContinuousLinearMap.comp_apply, Time.fderiv_val]
    simp
  rw [Time.deriv_eq, fderiv_fun_add (by fun_prop) (by fun_prop),
    fderiv_smul_const (by fun_prop), fderiv_smul_const (by fun_prop)]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply]
  rw [fderiv_comp_val_eq_deriv (fun s => cosh (S.angularFrequency * s)) (by fun_prop),
    fderiv_comp_val_eq_deriv (fun s => sinh (S.angularFrequency * s) / S.angularFrequency)
      (by fun_prop)]
  simp [mul_comm, hΩ]

private lemma overdampedBase_acceleration (IC : InitialConditions) (hS : S.IsOverdamped) :
    ∂ₜ (∂ₜ (fun t : Time =>
      cosh (S.angularFrequency * t.val) • IC.x₀ +
        (sinh (S.angularFrequency * t.val) / S.angularFrequency) •
          (IC.v₀ + S.decayRate • IC.x₀))) =
    fun t : Time => S.angularFrequency^2 •
      (cosh (S.angularFrequency * t.val) • IC.x₀ +
        (sinh (S.angularFrequency * t.val) / S.angularFrequency) •
          (IC.v₀ + S.decayRate • IC.x₀)) := by
  have hΩ : S.angularFrequency ≠ 0 := S.angularFrequency_ne_zero_of_overdamped hS
  rw [S.overdampedBase_velocity IC hS]
  funext t
  have fderiv_comp_val_eq_deriv : ∀ g : ℝ → ℝ, DifferentiableAt ℝ g t.val →
      (fderiv ℝ (fun s : Time => g s.val) t) 1 = _root_.deriv g t.val := by
    intro g hg
    rw [fderiv_fun_comp t hg (by fun_prop), ContinuousLinearMap.comp_apply, Time.fderiv_val]
    simp
  rw [Time.deriv_eq, fderiv_fun_add (by fun_prop) (by fun_prop),
    fderiv_smul_const (by fun_prop), fderiv_smul_const (by fun_prop)]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply]
  rw [fderiv_comp_val_eq_deriv (fun s => S.angularFrequency * sinh (S.angularFrequency * s))
      (by fun_prop),
    fderiv_comp_val_eq_deriv (fun s => cosh (S.angularFrequency * s)) (by fun_prop)]
  simp [mul_comm, smul_smul, smul_add]
  field_simp [hΩ]

/-- The selected trajectory has initial velocity `IC.v₀`. -/
lemma trajectory_velocity_at_zero (IC : InitialConditions) :
    ∂ₜ (S.trajectory IC) 0 = IC.v₀ := by
  rcases S.isUnderdamped_or_isCriticallyDamped_or_isOverdamped with hS | hS | hS
  · rw [S.trajectory_eq_of_underdamped IC hS,
      exp_decay_smul_velocity S.decayRate (S.underdampedBase IC)
        (by unfold underdampedBase; fun_prop),
      show ∂ₜ (S.underdampedBase IC) = _ from S.underdampedBase_velocity IC hS]
    simp [underdampedBase]
  · rw [S.trajectory_eq_of_criticallyDamped IC hS,
      exp_decay_smul_velocity S.decayRate (S.criticallyDampedBase IC)
        (by unfold criticallyDampedBase; fun_prop),
      S.criticallyDampedBase_velocity IC]
    simp [criticallyDampedBase]
  · rw [S.trajectory_eq_of_overdamped IC hS,
      exp_decay_smul_velocity S.decayRate (S.overdampedBase IC)
        (by unfold overdampedBase; fun_prop),
      show ∂ₜ (S.overdampedBase IC) = _ from S.overdampedBase_velocity IC hS]
    simp [overdampedBase]

/-!
## C. Trajectories and equation of motion

The regime-specific trajectories satisfy the equation of motion for the damped harmonic
oscillator.

### C.1. The selected trajectory satisfies the equation of motion
-/

/-- In the critically damped regime, the selected trajectory satisfies the damped equation
of motion. -/
lemma trajectory_equationOfMotion_of_criticallyDamped (IC : InitialConditions)
    (hS : S.IsCriticallyDamped) :
    S.EquationOfMotion (S.trajectory IC) := by
  rw [S.trajectory_eq_of_criticallyDamped IC hS]
  have hγ : S.γ = 2 * S.m * S.decayRate := S.gamma_eq_two_mul_m_mul_decayRate
  have hk : S.k = S.m * (S.decayRate^2 - 0) := by
    simpa [sub_zero] using S.k_eq_m_mul_decayRate_sq_of_criticallyDamped hS
  refine S.exp_decay_smul_equationOfMotion S.decayRate 0 (S.criticallyDampedBase IC)
    (by
      unfold criticallyDampedBase
      fun_prop)
    (by
      rw [S.criticallyDampedBase_velocity IC]
      fun_prop) ?_ hγ hk
  simpa using S.criticallyDampedBase_acceleration IC

/-- In the underdamped regime, the selected trajectory satisfies the damped equation of
motion. -/
lemma trajectory_equationOfMotion_of_underdamped (IC : InitialConditions)
    (hS : S.IsUnderdamped) :
    S.EquationOfMotion (S.trajectory IC) := by
  rw [S.trajectory_eq_of_underdamped IC hS]
  have hγ : S.γ = 2 * S.m * S.decayRate := S.gamma_eq_two_mul_m_mul_decayRate
  have hk : S.k = S.m * (S.decayRate^2 - (-S.angularFrequency^2)) := by
    rw [S.k_eq_m_mul_ω_sq, S.angularFrequency_sq_of_underdamped hS]
    ring
  refine S.exp_decay_smul_equationOfMotion S.decayRate
    (-S.angularFrequency^2) (S.underdampedBase IC)
    (by
      unfold underdampedBase
      fun_prop) ?_
    (S.underdampedBase_acceleration IC hS) hγ hk
  rw [show ∂ₜ (S.underdampedBase IC) = _ from S.underdampedBase_velocity IC hS]
  fun_prop

/-- In the overdamped regime, the selected trajectory satisfies the damped equation of
motion. -/
lemma trajectory_equationOfMotion_of_overdamped (IC : InitialConditions)
    (hS : S.IsOverdamped) :
    S.EquationOfMotion (S.trajectory IC) := by
  rw [S.trajectory_eq_of_overdamped IC hS]
  have hγ : S.γ = 2 * S.m * S.decayRate := S.gamma_eq_two_mul_m_mul_decayRate
  have hk : S.k = S.m * (S.decayRate^2 - S.angularFrequency^2) := by
    rw [S.k_eq_m_mul_ω_sq, S.angularFrequency_sq_of_overdamped hS]
    ring
  refine S.exp_decay_smul_equationOfMotion S.decayRate (S.angularFrequency^2)
    (S.overdampedBase IC)
    (by
      unfold overdampedBase
      fun_prop) ?_
    (S.overdampedBase_acceleration IC hS) hγ hk
  rw [show ∂ₜ (S.overdampedBase IC) = _ from S.overdampedBase_velocity IC hS]
  fun_prop

/-- The selected trajectory satisfies the damped equation of motion. -/
lemma trajectory_equationOfMotion (IC : InitialConditions) :
    S.EquationOfMotion (S.trajectory IC) := by
  rcases S.isUnderdamped_or_isCriticallyDamped_or_isOverdamped with hS | hS | hS
  · exact S.trajectory_equationOfMotion_of_underdamped IC hS
  · exact S.trajectory_equationOfMotion_of_criticallyDamped IC hS
  · exact S.trajectory_equationOfMotion_of_overdamped IC hS

/-!

### C.2. Uniqueness of the solutions

Unlike the undamped oscillator, the mechanical energy is not conserved along a damped solution, so
uniqueness cannot be read off from a conserved positive-definite energy. Instead we reduce the
second-order equation of motion `m ẍ + γ ẋ + k x = 0` to the first-order linear system
`(x, ẋ)' = (ẋ, (1/m)(-k x - γ ẋ))` on the phase space and invoke the global
ODE-uniqueness theorem `ODE_solution_unique_univ` (the right-hand side is a continuous
linear map, hence Lipschitz).

-/

/-- The phase-space vector field of the damped oscillator, sending `(x, ẋ)` to
`(ẋ, -(k/m) x - (γ/m) ẋ)`, as a continuous linear map on `E × E`. -/
private noncomputable def phaseVectorField :
    EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) →L[ℝ]
      EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) :=
  (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))).prod
    ((-(S.m⁻¹ * S.k)) •
        ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)) +
      (-(S.m⁻¹ * S.γ)) •
        ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)))

private lemma phaseVectorField_apply (a b : EuclideanSpace ℝ (Fin 1)) :
    S.phaseVectorField (a, b) = (b, (-(S.m⁻¹ * S.k)) • a + (-(S.m⁻¹ * S.γ)) • b) := by
  simp [phaseVectorField]

/-- The phase curve `τ ↦ (z t, ẋ t)` (with `t = toRealCLE.symm τ`) of a smooth solution `z`
solves the first-order phase-space ODE with vector field `phaseVectorField`. -/
private lemma phaseCurve_hasDerivAt (z : Time → EuclideanSpace ℝ (Fin 1))
    (hz : ContDiff ℝ ∞ z) (hEOM : S.EquationOfMotion z) (τ : ℝ) :
    HasDerivAt (fun τ : ℝ => (z (Time.toRealCLE.symm τ), ∂ₜ z (Time.toRealCLE.symm τ)))
      (S.phaseVectorField (z (Time.toRealCLE.symm τ), ∂ₜ z (Time.toRealCLE.symm τ))) τ := by
  rw [S.phaseVectorField_apply,
    ← S.acceleration_eq_of_equationOfMotion z hEOM (Time.toRealCLE.symm τ)]
  exact (Time.hasDerivAt_comp_toRealCLE_symm z τ (hz.differentiable (by simp) _)).prodMk
    (Time.hasDerivAt_comp_toRealCLE_symm (∂ₜ z) τ (deriv_differentiable_of_contDiff z hz _))

/-- Any two smooth solutions of the damped equation of motion with the same initial position and
velocity are equal. -/
lemma equationOfMotion_unique (x y : Time → EuclideanSpace ℝ (Fin 1))
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hEOMx : S.EquationOfMotion x) (hEOMy : S.EquationOfMotion y)
    (h0 : x 0 = y 0) (hv0 : ∂ₜ x 0 = ∂ₜ y 0) :
    x = y := by
  have hIC : (fun τ : ℝ => (x (Time.toRealCLE.symm τ), ∂ₜ x (Time.toRealCLE.symm τ))) 0 =
      (fun τ : ℝ => (y (Time.toRealCLE.symm τ), ∂ₜ y (Time.toRealCLE.symm τ))) 0 := by
    have h00 : Time.toRealCLE.symm (0 : ℝ) = (0 : Time) := map_zero Time.toRealCLE.symm
    simp only [h00, h0, hv0]
  have hEq := ODE_solution_unique_univ
    (v := fun _ p => S.phaseVectorField p) (s := fun _ => Set.univ) (t₀ := (0 : ℝ))
    (f := fun τ : ℝ => (x (Time.toRealCLE.symm τ), ∂ₜ x (Time.toRealCLE.symm τ)))
    (g := fun τ : ℝ => (y (Time.toRealCLE.symm τ), ∂ₜ y (Time.toRealCLE.symm τ)))
    (fun _ => S.phaseVectorField.lipschitz.lipschitzOnWith)
    (fun τ => ⟨S.phaseCurve_hasDerivAt x hx hEOMx τ, Set.mem_univ _⟩)
    (fun τ => ⟨S.phaseCurve_hasDerivAt y hy hEOMy τ, Set.mem_univ _⟩)
    hIC
  funext t
  have h1 := congrFun hEq (Time.toRealCLE t)
  simp only [ContinuousLinearEquiv.symm_apply_apply] at h1
  exact (Prod.ext_iff.mp h1).1

/-- The selected trajectory is the unique smooth solution of the damped equation of motion with the
given initial conditions. -/
lemma trajectories_unique (IC : InitialConditions) (x : Time → EuclideanSpace ℝ (Fin 1))
    (hx : ContDiff ℝ ∞ x) (hEOM : S.EquationOfMotion x)
    (hx0 : x 0 = IC.x₀) (hv0 : ∂ₜ x 0 = IC.v₀) :
    x = S.trajectory IC := by
  refine S.equationOfMotion_unique x (S.trajectory IC) hx (S.trajectory_contDiff IC)
    hEOM (S.trajectory_equationOfMotion IC) ?_ ?_
  · rw [hx0, S.trajectory_apply_zero IC]
  · rw [hv0, S.trajectory_velocity_at_zero IC]

end DampedHarmonicOscillator

end ClassicalMechanics
