/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Lode Vermeulen
-/
import PhysLean.Meta.Informal.SemiFormal
import PhysLean.ClassicalMechanics.EulerLagrange
import PhysLean.ClassicalMechanics.HamiltonsEquations
import PhysLean.ClassicalMechanics.HarmonicOscillator.ConfigurationSpace
/-!

# The Classical Harmonic Oscillator

## i. Overview

The classical harmonic oscillator is a classical mechanical system corresponding to a
mass `m` under a force `- k x` where `k` is the spring constant and `x` is the position.

## ii. Key results

The key results in the study of the classical harmonic oscillator are the follows:

In the `Basic` module:
- `HarmonicOscillator` contains the input data to the problem.
- `EquationOfMotion` defines the equation of motion for the harmonic oscillator.
- `energy_conservation_of_equationOfMotion` proves that a trajectory satisfying the
  equation of motion conserves energy.
- `equationOfMotion_tfae` proves that the equation of motion of motion is equivalent to
  - Newton's second law,
  - Hamilton's equations,
  - the variational principal for the action,
  - the Hamilton variation principal.

In the `Solution` module:
- `InitialConditions` is a structure for the initial conditions for the harmonic oscillator.
- `trajectories` is the trajectories to the harmonic oscillator for given initial conditions.
- `trajectories_equationOfMotion` proves that the solution satisfies the equation of motion.

## iii. Table of contents

- A. The input data
- B. The angular frequency
- C. The energies
  - C.1. The definitions of the energies
  - C.2. Simple equalities for the energies
  - C.3. Differentiability of the energies
  - C.4. Time derivatives of the energies
- D. Lagrangian and the equation of motion
  - D.1. The Lagrangian
    - D.1.1. Equalities for the lagrangian
    - D.1.2. Smoothness of the lagrangian
    - D.1.3. Gradients of the lagrangian
  - D.2. The variational derivative of the action
    - D.2.1. Equality for the variational derivative
  - D.3. The equation of motion
    - D.3.1. Equation of motion if and only if variational-gradient of Lagrangian is zero
- E. Newton's second law
  - E.1. The force
    - E.1.1. The force is equal to `- k x`
  - E.2. Variational derivative of lagrangian and force
  - E.3. Equation of motion if and only if Newton's second law
- F. Energy conservation
  - F.1. Energy conservation in terms of time derivatives
  - F.2. Energy conservation in terms of constant energy
- G. Hamiltonian formulation
  - G.1. The canonical momentum
    - G.1.1. Equality for the canonical momentum
  - G.2. The Hamiltonian
    - G.2.1. Equality for the Hamiltonian
    - G.2.2. Smoothness of the Hamiltonian
    - G.2.3. Gradients of the Hamiltonian
  - G.3. Relation between Hamiltonian and energy
  - G.4. Hamilton equation operator
  - G.5. Equation of motion if and only if Hamilton's equations
- H. Equivalences between the different formulations of the equations of motion

## iv. References

References for the classical harmonic oscillator include:
- Landau & Lifshitz, Mechanics, page 58, section 21.

-/

namespace ClassicalMechanics
open Real
open Space
open InnerProductSpace

TODO "6VZHC" "Create a new folder for the damped harmonic oscillator, initially as a place-holder."

/-!

## A. The input data

We start by defining a structure containing the input data of the harmonic oscillator, and
proving basic properties thereof. The input data consists of the mass `m`
of the particle and the spring constant `k`.

-/

/-- The classical harmonic oscillator is specified by a mass `m`, and a spring constant `k`.
  Both the mass and the string constant are assumed to be positive. -/
structure HarmonicOscillator where
  /-- The mass of the harmonic Oscillator. -/
  m : ℝ
  /-- The spring constant of the harmonic oscillator. -/
  k : ℝ
  m_pos : 0 < m
  k_pos : 0 < k

namespace HarmonicOscillator

variable (S : HarmonicOscillator)

@[simp]
lemma k_ne_zero : S.k ≠ 0 := Ne.symm (ne_of_lt S.k_pos)

@[simp]
lemma m_ne_zero : S.m ≠ 0 := Ne.symm (ne_of_lt S.m_pos)

/-!

## B. The angular frequency

From the input data, it is possible to define the angular frequency `ω` of the harmonic oscillator,
as `√(k/m)`.

The angular frequency appears in the solutions to the equations of motion of the harmonic
oscillator.

Here we both define and proof properties related to the angular frequency.

-/

/-- The angular frequency of the classical harmonic oscillator, `ω`, is defined
  as `√(k/m)`. -/
noncomputable def ω : ℝ := √(S.k / S.m)

/-- The angular frequency of the classical harmonic oscillator is positive. -/
@[simp]
lemma ω_pos : 0 < S.ω := sqrt_pos.mpr (div_pos S.k_pos S.m_pos)

/-- The square of the angular frequency of the classical harmonic oscillator is equal to `k/m`. -/
lemma ω_sq : S.ω^2 = S.k / S.m := by
  rw [ω, sq_sqrt]
  exact div_nonneg (le_of_lt S.k_pos) (le_of_lt S.m_pos)

/-- The angular frequency of the classical harmonic oscillator is not equal to zero. -/
lemma ω_ne_zero : S.ω ≠ 0 := Ne.symm (ne_of_lt S.ω_pos)

/-- The inverse of the square of the angular frequency of the classical harmonic oscillator
  is `m/k`. -/
lemma inverse_ω_sq : (S.ω ^ 2)⁻¹ = S.m/S.k := by
  rw [ω_sq]
  field_simp

/-!

## C. The energies

The harmonic oscillator has a kinetic energy determined by it's velocity and
a potential energy determined by it's position.
These combine to give the total energy of the harmonic oscillator.

Here we state and prove a number of properties of these energies.

-/

open MeasureTheory ContDiff InnerProductSpace Time

/-!

### C.1. The definitions of the energies

We define the three energies, it is these energies which will control the dynamics
of the harmonic oscillator, through the lagrangian.

-/

/-- The kinetic energy of the harmonic oscillator is $\frac{1}{2} m ‖\dot x‖^2$. -/
noncomputable def kineticEnergy (xₜ : Time → ConfigurationSpace) : Time → ℝ := fun t =>
  (1 / (2 : ℝ)) * S.m * ⟪∂ₜ xₜ t, ∂ₜ xₜ t⟫_ℝ

/-- The potential energy of the harmonic oscillator is `1/2 k x ^ 2` -/
noncomputable def potentialEnergy (x : ConfigurationSpace) : ℝ :=
  (1 / (2 : ℝ)) • S.k • ⟪x, x⟫_ℝ

/-- The energy of the harmonic oscillator is the kinetic energy plus the potential energy. -/
noncomputable def energy (xₜ : Time → ConfigurationSpace) : Time → ℝ := fun t =>
  kineticEnergy S xₜ t + potentialEnergy S (xₜ t)

/-!

### C.2. Simple equalities for the energies

-/

lemma kineticEnergy_eq (xₜ : Time → ConfigurationSpace) :
    kineticEnergy S xₜ = fun t => (1 / (2 : ℝ)) * S.m * ⟪∂ₜ xₜ t, ∂ₜ xₜ t⟫_ℝ:= by rfl

lemma potentialEnergy_eq (x : ConfigurationSpace) :
    potentialEnergy S x = (1 / (2 : ℝ)) • S.k • ⟪x, x⟫_ℝ:= by rfl

lemma energy_eq (xₜ : Time → ConfigurationSpace) :
    energy S xₜ = fun t => kineticEnergy S xₜ t + potentialEnergy S (xₜ t) := by rfl
/-!

### C.3. Differentiability of the energies

On smooth trajectories the energies are differentiable.

-/
@[fun_prop]
lemma kineticEnergy_differentiable (xₜ : Time → ConfigurationSpace) (hx : ContDiff ℝ ∞ xₜ) :
    Differentiable ℝ (kineticEnergy S xₜ) := by
  rw [kineticEnergy_eq]
  change Differentiable ℝ ((fun x => (1 / (2 : ℝ)) * S.m * ⟪x, x⟫_ℝ) ∘ (fun t => ∂ₜ xₜ t))
  apply Differentiable.comp
  · fun_prop
  · exact deriv_differentiable_of_contDiff xₜ hx

@[fun_prop]
lemma potentialEnergy_differentiable (xₜ : Time → ConfigurationSpace) (hx : ContDiff ℝ ∞ xₜ) :
    Differentiable ℝ (fun t => potentialEnergy S (xₜ t)) := by
  simp only [potentialEnergy_eq, one_div, smul_eq_mul]
  change Differentiable ℝ ((fun x => 2⁻¹ * (S.k * ⟪x, x⟫_ℝ)) ∘ xₜ)
  apply Differentiable.comp
  · fun_prop
  · rw [contDiff_infty_iff_fderiv] at hx
    exact hx.1

@[fun_prop]
lemma energy_differentiable (xₜ : Time → ConfigurationSpace) (hx : ContDiff ℝ ∞ xₜ) :
    Differentiable ℝ (energy S xₜ) := by
  rw [energy_eq]
  fun_prop

/-!

### C.4. Time derivatives of the energies

For a general smooth trajectory (which may not satisfy the equations of motion) we can compute
the time derivatives of the energies.

-/

lemma kineticEnergy_deriv (xₜ : Time → ConfigurationSpace) (hx : ContDiff ℝ ∞ xₜ) :
    ∂ₜ (kineticEnergy S xₜ) = fun t => ⟪∂ₜ xₜ t, S.m • ∂ₜ (∂ₜ xₜ) t⟫_ℝ := by
  funext t
  unfold kineticEnergy
  conv_lhs => simp only [Time.deriv, one_div, ringHom_apply]
  change (fderiv ℝ ((fun x => 2⁻¹ * S.m * ⟪x, x⟫_ℝ) ∘ (fun t => ∂ₜ xₜ t)) t) 1 = _
  rw [fderiv_comp]
  rw [fderiv_const_mul (by fun_prop)]
  simp only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.coe_smul',
    ContinuousLinearMap.coe_comp', Pi.smul_apply, Function.comp_apply, smul_eq_mul]
  rw [fderiv_inner_apply]
  simp only [fderiv_id', ContinuousLinearMap.coe_id', id_eq]
  rw [real_inner_comm, ← inner_add_left, ← Time.deriv, real_inner_comm, ← inner_smul_right]
  congr 1
  simp only [smul_add]
  module
  repeat fun_prop

lemma potentialEnergy_deriv (xₜ : Time → ConfigurationSpace) (hx : ContDiff ℝ ∞ xₜ) :
    ∂ₜ (fun t => potentialEnergy S (xₜ t)) = fun t => ⟪∂ₜ xₜ t, S.k • xₜ t⟫_ℝ := by
  funext t
  unfold potentialEnergy
  conv_lhs => simp only [Time.deriv, one_div, smul_eq_mul]
  change (fderiv ℝ ((fun x => 2⁻¹ * (S.k * ⟪x, x⟫_ℝ)) ∘ (fun t => xₜ t)) t) 1 = _
  rw [fderiv_comp]
  rw [fderiv_const_mul (by fun_prop), fderiv_const_mul (by fun_prop)]
  simp only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.coe_smul',
    ContinuousLinearMap.coe_comp', Pi.smul_apply, Function.comp_apply, smul_eq_mul]
  rw [fderiv_inner_apply]
  simp only [fderiv_id', ContinuousLinearMap.coe_id', id_eq]
  trans S.k * ⟪xₜ t, ∂ₜ xₜ t⟫_ℝ
  · rw [real_inner_comm, ← inner_add_left, ← Time.deriv, real_inner_comm, ← inner_smul_right,
      ← inner_smul_right, ← inner_smul_right]
    congr 1
    module
  rw [real_inner_comm, ← inner_smul_right]
  repeat fun_prop
  apply Differentiable.differentiableAt
  rw [contDiff_infty_iff_fderiv] at hx
  exact hx.1

lemma energy_deriv (xₜ : Time → ConfigurationSpace) (hx : ContDiff ℝ ∞ xₜ) :
    ∂ₜ (energy S xₜ) = fun t => ⟪∂ₜ xₜ t, S.m • ∂ₜ (∂ₜ xₜ) t + S.k • xₜ t⟫_ℝ := by
  unfold energy
  funext t
  rw [Time.deriv_eq]
  rw [fderiv_fun_add (by fun_prop) (by apply S.potentialEnergy_differentiable xₜ hx)]
  simp only [ContinuousLinearMap.add_apply]
  rw [← Time.deriv_eq, ← Time.deriv_eq]
  rw [potentialEnergy_deriv, kineticEnergy_deriv]
  simp only
  rw [← inner_add_right]
  fun_prop
  fun_prop

/-!

## D. Lagrangian and the equation of motion

We state the lagrangian, and derive from that the equation of motion for the harmonic oscillator.

-/

/-!
### D.1. The Lagrangian

We define the lagrangian of the harmonic oscillator, as a function of phase-space. It is given by

$$L(t, x, v) := \frac{1}{2} m ‖v‖^2 - \frac{1}{2} k ‖x‖^2$$

In theory this definition is the kinetic energy minus the potential energy, however
to make the lagrangian a function on phase-space we reserve this result for a lemma.

-/

set_option linter.unusedVariables false in
/-- The lagrangian of the harmonic oscillator is the kinetic energy minus the potential energy. -/
@[nolint unusedArguments]
noncomputable def lagrangian (t : Time) (x : ConfigurationSpace)
    (v : ConfigurationSpace) : ℝ :=
  1 / (2 : ℝ) * S.m * ⟪v, v⟫_ℝ - S.potentialEnergy x

/-!

#### D.1.1. Equalities for the lagrangian

Equalities for the lagrangian. We prove some simple equalities for the lagrangian,
in particular that when applied to a trajectory it is the kinetic energy minus the potential energy.

-/

set_option linter.unusedVariables false in
@[nolint unusedArguments]
lemma lagrangian_eq : lagrangian S = fun t x v =>
    1 / (2 : ℝ) * S.m * ⟪v, v⟫_ℝ - 1 / (2 : ℝ) * S.k * ⟪x, x⟫_ℝ := by
  ext t x v
  simp [lagrangian, potentialEnergy]
  ring

lemma lagrangian_eq_kineticEnergy_sub_potentialEnergy (t : Time)
    (xₜ : Time → ConfigurationSpace) :
    lagrangian S t (xₜ t) (∂ₜ xₜ t) = kineticEnergy S xₜ t - potentialEnergy S (xₜ t) := by
  rw [lagrangian_eq, kineticEnergy, potentialEnergy]
  simp only [one_div, smul_eq_mul, sub_right_inj]
  ring

/-!

#### D.1.2. Smoothness of the lagrangian

The lagrangian is smooth in all its arguments.

-/

@[fun_prop]
lemma contDiff_lagrangian (n : WithTop ℕ∞) : ContDiff ℝ n ↿S.lagrangian := by
  rw [lagrangian_eq]
  apply ContDiff.sub
  · apply ContDiff.mul
    · apply ContDiff.mul
      · exact contDiff_const
      · exact contDiff_const
    · exact ContDiff.inner (𝕜 := ℝ) (contDiff_snd.comp contDiff_snd)
        (contDiff_snd.comp contDiff_snd)
  · apply ContDiff.mul
    · apply ContDiff.mul
      · exact contDiff_const
      · exact contDiff_const
    · exact ContDiff.inner (𝕜 := ℝ) (contDiff_fst.comp contDiff_snd)
        (contDiff_fst.comp contDiff_snd)

lemma toDual_symm_innerSL (x : ConfigurationSpace) :
    (InnerProductSpace.toDual ℝ ConfigurationSpace).symm (innerSL ℝ x) = x := by
  apply (innerSL_inj (𝕜:=ℝ) (E:=ConfigurationSpace)).1
  ext y
  simp [InnerProductSpace.toDual_symm_apply]

lemma gradient_inner_self (x : ConfigurationSpace) :
    gradient (fun y : ConfigurationSpace => ⟪y, y⟫_ℝ) x = (2 : ℝ) • x := by
  refine ext_inner_right (𝕜 := ℝ) fun y => ?_
  unfold gradient
  rw [InnerProductSpace.toDual_symm_apply]
  have hid : DifferentiableAt ℝ (fun y : ConfigurationSpace => y) x := differentiableAt_id
  rw [show (fun y : ConfigurationSpace => ⟪y, y⟫_ℝ) =
      fun y => ⟪(fun y => y) y, (fun y => y) y⟫_ℝ from rfl]
  rw [fderiv_inner_apply (𝕜 := ℝ) hid hid]
  simp only [fderiv_id', ContinuousLinearMap.coe_id', id_eq,
    ConfigurationSpace.inner_def, ConfigurationSpace.smul_val]
  ring

lemma gradient_const_mul_inner_self (c : ℝ) (x : ConfigurationSpace) :
    gradient (fun y : ConfigurationSpace => c * ⟪y, y⟫_ℝ) x = (2 * c) • x := by
  calc
    gradient (fun y : ConfigurationSpace => c * ⟪y, y⟫_ℝ) x
        = (InnerProductSpace.toDual ℝ ConfigurationSpace).symm
            (fderiv ℝ (fun y : ConfigurationSpace => c * ⟪y, y⟫_ℝ) x) := rfl
    _ = (InnerProductSpace.toDual ℝ ConfigurationSpace).symm
            (c • fderiv ℝ (fun y : ConfigurationSpace => ⟪y, y⟫_ℝ) x) := by
          rw [fderiv_const_mul (ConfigurationSpace.differentiableAt_inner_self x)]
    _ = c • gradient (fun y : ConfigurationSpace => ⟪y, y⟫_ℝ) x := by
          simp only [gradient, map_smul]
    _ = c • ((2 : ℝ) • x) := by
          rw [gradient_inner_self]
    _ = (2 * c) • x := by
          rw [smul_smul, mul_comm]

/-!

#### D.1.3. Gradients of the lagrangian

We now show results related to the gradients of the lagrangian with respect to the
position and velocity.

-/

private lemma gradient_add_const' {f : ConfigurationSpace → ℝ} {c : ℝ}
    (x : ConfigurationSpace) :
    gradient (fun y => f y + c) x = gradient f x := by
  unfold gradient
  rw [fderiv_add_const]

lemma gradient_lagrangian_position_eq (t : Time) (x : ConfigurationSpace)
    (v : ConfigurationSpace) :
    gradient (fun x => lagrangian S t x v) x = - S.k • x := by
  have h_eq : (fun y : ConfigurationSpace => lagrangian S t y v) =
      fun y => (-(1 / (2 : ℝ)) * S.k) * ⟪y, y⟫_ℝ + (1 / (2 : ℝ) * S.m * ⟪v, v⟫_ℝ) := by
    funext y; unfold lagrangian potentialEnergy; simp only [smul_eq_mul]; ring
  rw [h_eq, gradient_add_const', gradient_const_mul_inner_self]
  ext; simp only [ConfigurationSpace.smul_val]; ring

lemma gradient_lagrangian_velocity_eq (t : Time) (x : ConfigurationSpace)
    (v : ConfigurationSpace) :
    gradient (lagrangian S t x) v = S.m • v := by
  have h_eq : (fun y : ConfigurationSpace => lagrangian S t x y) =
      fun y => ((1 / (2 : ℝ)) * S.m) * ⟪y, y⟫_ℝ + (-(1 / (2 : ℝ)) * S.k * ⟪x, x⟫_ℝ) := by
    funext y; unfold lagrangian potentialEnergy; simp only [smul_eq_mul]; ring
  change gradient (fun y : ConfigurationSpace => lagrangian S t x y) v = S.m • v
  rw [h_eq, gradient_add_const', gradient_const_mul_inner_self]
  ext; simp only [ConfigurationSpace.smul_val]; ring

/-!

### D.2. The variational derivative of the action

We now write down the variational derivative for the harmonic oscillator, for
a trajectory $x(t)$ this is equal to

$$t\mapsto \left.\frac{\partial L(t, \dot x (t), q)}{\partial q}\right|_{q = x(t)} -
  \frac{d}{dt} \left.\frac{\partial L(t, v, x(t))}{\partial v}\right|_{v = \dot x (t)}$$

Setting this equal to zero corresponds to the Euler-Lagrange equations, and thereby the
equation of motion.

-/

/-- The Euler-Lagrange operator for the classical harmonic oscillator. -/
noncomputable def gradLagrangian (xₜ : Time → ConfigurationSpace) :
    Time → ConfigurationSpace :=
  (δ (q':=xₜ), ∫ t, lagrangian S t (q' t) (fderiv ℝ q' t 1))

/-!

#### D.2.1. Equality for the variational derivative

Basic equalities for the variational derivative of the action.

-/

lemma gradLagrangian_eq_eulerLagrangeOp (xₜ : Time → ConfigurationSpace)
    (hq : ContDiff ℝ ∞ xₜ) :
    gradLagrangian S xₜ = eulerLagrangeOp S.lagrangian xₜ := by
  rw [gradLagrangian,
    ClassicalMechanics.euler_lagrange_varGradient _ _ hq (S.contDiff_lagrangian _)]

/-!

### D.3. The equation of motion

The equation of motion for the harmonic oscillator is given by setting the
variational derivative of the action equal to zero.

-/

/-- The equation of motion for the Harmonic oscillator. -/
def EquationOfMotion (xₜ : Time → ConfigurationSpace) : Prop :=
  S.gradLagrangian xₜ = 0

/-!

#### D.3.1. Equation of motion if and only if variational-gradient of Lagrangian is zero

We write a simple iff statement for the definition of the equation of motions.

-/

lemma equationOfMotion_iff_gradLagrangian_zero (xₜ : Time → ConfigurationSpace) :
    S.EquationOfMotion xₜ ↔ S.gradLagrangian xₜ = 0 := by rfl

/-!

## E. Newton's second law

We define the force of the harmonic oscillator, and show that the equation of
motion is equivalent to Newton's second law.

-/

/-!

### E.1. The force

We define the force of the harmonic oscillator as the negative gradient of the potential energy,
and show that this is equal to `- k x`.

-/

/-- The force of the classical harmonic oscillator defined as `- dU(x)/dx` where `U(x)`
  is the potential energy. -/
noncomputable def force (S : HarmonicOscillator) (x : ConfigurationSpace) :
    ConfigurationSpace :=
  - gradient (potentialEnergy S) x

/-!

#### E.1.1. The force is equal to `- k x`

We now show that the force is equal to `- k x`.

-/

/-- The force on the classical harmonic oscillator is `- k x`. -/
lemma force_eq_linear (x : ConfigurationSpace) : force S x = - S.k • x := by
  unfold force potentialEnergy
  have hpot : (fun y : ConfigurationSpace => (1 / (2 : ℝ)) • S.k • ⟪y, y⟫_ℝ) =
      fun y => ((1 / (2 : ℝ)) * S.k) * ⟪y, y⟫_ℝ := by
    funext y
    simp [smul_eq_mul, mul_assoc]
  rw [hpot]
  have hgrad : gradient (fun y : ConfigurationSpace => ((1 / (2 : ℝ)) * S.k) * ⟪y, y⟫_ℝ) x
      = S.k • x := by
    simpa [smul_eq_mul, mul_assoc] using
      (gradient_const_mul_inner_self (c := (1 / (2 : ℝ)) * S.k) x)
  rw [hgrad]
  simp [neg_smul]

/-!

### E.2. Variational derivative of lagrangian and force

We relate the variational derivative of lagrangian to the force, and show the relation
to Newton's second law.

-/

/-- The Euler lagrange operator corresponds to Newton's second law. -/
lemma gradLagrangian_eq_force (xₜ : Time → ConfigurationSpace) (hx : ContDiff ℝ ∞ xₜ) :
    S.gradLagrangian xₜ = fun t => force S (xₜ t) - S.m • ∂ₜ (∂ₜ xₜ) t := by
  funext t
  rw [gradLagrangian_eq_eulerLagrangeOp S xₜ hx, eulerLagrangeOp]
  congr
  · simp [gradient_lagrangian_position_eq, force_eq_linear]
  · conv_lhs =>
      arg 1
      ext t'
      rw [gradient_lagrangian_velocity_eq]
    show ∂ₜ (fun t' => S.m • ∂ₜ xₜ t') t = S.m • ∂ₜ (∂ₜ xₜ) t
    have hd : DifferentiableAt ℝ (∂ₜ xₜ) t :=
      (deriv_differentiable_of_contDiff xₜ hx).differentiableAt
    calc
      ∂ₜ (fun t' => S.m • ∂ₜ xₜ t') t
          = fderiv ℝ (fun t' => S.m • ∂ₜ xₜ t') t 1 := rfl
      _ = S.m • (fderiv ℝ (∂ₜ xₜ) t 1) := by
          simpa using congrArg (fun L => L 1) (fderiv_const_smul (c := S.m) (f := ∂ₜ xₜ) hd)
      _ = S.m • ∂ₜ (∂ₜ xₜ) t := rfl

/-!

### E.3. Equation of motion if and only if Newton's second law

We show that the equation of motion is equivalent to Newton's second law.

-/

lemma equationOfMotion_iff_newtons_2nd_law (xₜ : Time → ConfigurationSpace)
    (hx : ContDiff ℝ ∞ xₜ) :
    S.EquationOfMotion xₜ ↔
    (∀ t, S.m • ∂ₜ (∂ₜ xₜ) t = force S (xₜ t)) := by
  rw [EquationOfMotion, gradLagrangian_eq_force S xₜ hx, funext_iff]
  simp only [Pi.zero_apply]
  conv_lhs =>
    enter [x]
    rw [sub_eq_zero, eq_comm]

/-!

## F. Energy conservation

In this section we show that any trajectory satisfying the equation of motion
conserves energy. This result simply follows from the definition of the energies,
and their derivatives, as well as the statement that the equations of motion are equivalent
to Newton's second law.

-/

/-!

### F.1. Energy conservation in terms of time derivatives

We prove that the time derivative of the energy is zero for any trajectory satisfying
the equation of motion.

-/

lemma energy_conservation_of_equationOfMotion (xₜ : Time → ConfigurationSpace)
    (hx : ContDiff ℝ ∞ xₜ)
    (h : S.EquationOfMotion xₜ) : ∂ₜ (S.energy xₜ) = 0 := by
  rw [energy_deriv _ _ hx]
  rw [equationOfMotion_iff_newtons_2nd_law _ _ hx] at h
  funext x
  simp only [Pi.zero_apply]
  rw [h]
  simp [force_eq_linear]

/-!

### F.2. Energy conservation in terms of constant energy

We prove that the energy is constant for any trajectory satisfying the equation of motion.

-/

lemma energy_conservation_of_equationOfMotion' (xₜ : Time → ConfigurationSpace)
    (hx : ContDiff ℝ ∞ xₜ)
    (h : S.EquationOfMotion xₜ) (t : Time) : S.energy xₜ t = S.energy xₜ 0 := by
  have h1 := S.energy_conservation_of_equationOfMotion xₜ hx h
  unfold Time.deriv at h1
  apply is_const_of_fderiv_eq_zero (𝕜 := ℝ)
  · exact energy_differentiable S xₜ hx
  intro t
  ext p
  simp only [ContinuousLinearMap.zero_apply]
  have hp : p = p.val • 1 := by ext; simp
  rw [hp]
  simp only [map_smul, smul_eq_mul, mul_eq_zero]
  right
  rw [funext_iff] at h1
  simpa using h1 t

/-!

## G. Hamiltonian formulation

We now turn to the Hamiltonian formulation of the harmonic oscillator.
We define the canonical momentum, the Hamiltonian, and show that the equations of
motion are equivalent to Hamilton's equations.

-/

/-!

### G.1. The canonical momentum

We define the canonical momentum as the gradient of the lagrangian with respect to
the velocity.

-/

/-- The equivalence between velocity and canonical momentum. -/
noncomputable def toCanonicalMomentum (t : Time) (x : ConfigurationSpace) :
    ConfigurationSpace ≃ₗ[ℝ] ConfigurationSpace where
  toFun v := gradient (S.lagrangian t x ·) v
  invFun p := (1 / S.m) • p
  left_inv v := by
    simp [gradient_lagrangian_velocity_eq]
  right_inv p := by
    simp [gradient_lagrangian_velocity_eq]
  map_add' v1 v2 := by
    simp [gradient_lagrangian_velocity_eq]
  map_smul' c v := by
    simp [gradient_lagrangian_velocity_eq]
    module

/-!

#### G.1.1. Equality for the canonical momentum

An simple equality for the canonical momentum.

-/

lemma toCanonicalMomentum_eq (t : Time) (x : ConfigurationSpace)
    (v : ConfigurationSpace) :
    toCanonicalMomentum S t x v = S.m • v := by
  simp [toCanonicalMomentum, gradient_lagrangian_velocity_eq]

/-!

### G.2. The Hamiltonian

The hamiltonian is defined as a function of time, canonical momentum and position, as
```
H = ⟪p, v⟫ - L(t, x, v)
```
where `v` is a function of `p` and `x` through the canonical momentum.

-/

/-- The hamiltonian as a function of time, momentum and position. -/
noncomputable def hamiltonian (t : Time) (p : ConfigurationSpace)
    (x : ConfigurationSpace) : ℝ :=
  ⟪p, (toCanonicalMomentum S t x).symm p⟫_ℝ - S.lagrangian t x ((toCanonicalMomentum S t x).symm p)

/-!

#### G.2.1. Equality for the Hamiltonian

We prove a simple equality for the Hamiltonian, to help in computations.

-/

lemma hamiltonian_eq :
    hamiltonian S = fun _ p x => (1 / (2 : ℝ)) * (1 / S.m) * ⟪p, p⟫_ℝ +
      (1 / (2 : ℝ)) * S.k * ⟪x, x⟫_ℝ := by
  funext t x p
  simp only [hamiltonian, toCanonicalMomentum, lagrangian_eq, one_div, LinearEquiv.coe_symm_mk',
    inner_smul_right, inner_smul_left, map_inv₀, ringHom_apply]
  have hm : S.m ≠ 0 := by exact m_ne_zero S
  field_simp
  ring

/-!

#### G.2.2. Smoothness of the Hamiltonian

We show that the Hamiltonian is smooth in all its arguments.

-/

@[fun_prop]
lemma hamiltonian_contDiff (n : WithTop ℕ∞) : ContDiff ℝ n ↿S.hamiltonian := by
  rw [hamiltonian_eq]
  apply ContDiff.add
  · apply ContDiff.mul
    · apply ContDiff.mul
      · exact contDiff_const
      · exact contDiff_const
    · exact ContDiff.inner (𝕜 := ℝ) (contDiff_fst.comp contDiff_snd)
        (contDiff_fst.comp contDiff_snd)
  · apply ContDiff.mul
    · apply ContDiff.mul
      · exact contDiff_const
      · exact contDiff_const
    · exact ContDiff.inner (𝕜 := ℝ) (contDiff_snd.comp contDiff_snd)
        (contDiff_snd.comp contDiff_snd)

/-!

#### G.2.3. Gradients of the Hamiltonian

We now write down the gradients of the Hamiltonian with respect to the momentum and position.

-/

lemma gradient_hamiltonian_position_eq (t : Time) (x : ConfigurationSpace)
    (p : ConfigurationSpace) :
    gradient (hamiltonian S t p) x = S.k • x := by
  have h_eq : (fun y : ConfigurationSpace => hamiltonian S t p y) =
      fun y => ((1 / (2 : ℝ)) * S.k) * ⟪y, y⟫_ℝ +
        ((1 / (2 : ℝ)) * (1 / S.m) * ⟪p, p⟫_ℝ) := by
    funext y; unfold hamiltonian; simp only [toCanonicalMomentum, lagrangian,
      potentialEnergy, LinearEquiv.coe_symm_mk', ConfigurationSpace.inner_def,
      ConfigurationSpace.smul_val, smul_eq_mul]
    have hm : S.m ≠ 0 := m_ne_zero S
    field_simp
    ring
  change gradient (fun y : ConfigurationSpace => hamiltonian S t p y) x = S.k • x
  rw [h_eq, gradient_add_const', gradient_const_mul_inner_self]
  ext; simp only [ConfigurationSpace.smul_val]; ring

lemma gradient_hamiltonian_momentum_eq (t : Time) (x : ConfigurationSpace)
    (p : ConfigurationSpace) :
    gradient (hamiltonian S t · x) p = (1 / S.m) • p := by
  have h_eq : (fun y : ConfigurationSpace => hamiltonian S t y x) =
      fun y => ((1 / (2 : ℝ)) * (1 / S.m)) * ⟪y, y⟫_ℝ +
        ((1 / (2 : ℝ)) * S.k * ⟪x, x⟫_ℝ) := by
    funext y; unfold hamiltonian; simp only [toCanonicalMomentum, lagrangian,
      potentialEnergy, LinearEquiv.coe_symm_mk', ConfigurationSpace.inner_def,
      ConfigurationSpace.smul_val, smul_eq_mul]
    have hm : S.m ≠ 0 := m_ne_zero S
    field_simp
    ring
  change gradient (fun y : ConfigurationSpace => hamiltonian S t y x) p = (1 / S.m) • p
  rw [h_eq, gradient_add_const', gradient_const_mul_inner_self]
  ext; simp only [ConfigurationSpace.smul_val]; ring

/-!

### G.3. Relation between Hamiltonian and energy

We show that the Hamiltonian, when evaluated on any trajectory, is equal to the energy.
This is independent of whether the trajectory satisfies the equations of motion or not.

-/

lemma hamiltonian_eq_energy (xₜ : Time → ConfigurationSpace) :
    (fun t => hamiltonian S t (toCanonicalMomentum S t (xₜ t) (∂ₜ xₜ t)) (xₜ t)) = energy S xₜ := by
  funext t
  have hsymm :
      (toCanonicalMomentum S t (xₜ t)).symm (S.m • ∂ₜ xₜ t) = ∂ₜ xₜ t := by
    rw [← toCanonicalMomentum_eq (S := S) (t := t) (x := xₜ t) (v := ∂ₜ xₜ t)]
    exact LinearEquiv.symm_apply_apply (toCanonicalMomentum S t (xₜ t)) (∂ₜ xₜ t)
  unfold hamiltonian lagrangian energy kineticEnergy potentialEnergy
  simp only [toCanonicalMomentum_eq,
    ConfigurationSpace.inner_def, ConfigurationSpace.smul_val, one_div, smul_eq_mul]
  rw [hsymm]
  ring_nf

/-!

### G.4. Hamilton equation operator

We define the operator on momentum-position phase-space whose vanishing is equivalent
to Hamilton's equations.

-/

/-- The operator on the momentum-position phase-space whose vanishing is equivalent to the
  hamilton's equations between the momentum and position. -/
noncomputable def hamiltonEqOp (p : Time → ConfigurationSpace)
    (q : Time → ConfigurationSpace) :=
  ClassicalMechanics.hamiltonEqOp (hamiltonian S) p q

/-!

### G.5. Equation of motion if and only if Hamilton's equations

We show that the equation of motion is equivalent to Hamilton's equations, that is
to the vanishing of the Hamilton equation operator.

-/

lemma equationOfMotion_iff_hamiltonEqOp_eq_zero (xₜ : Time → ConfigurationSpace)
    (hx : ContDiff ℝ ∞ xₜ) : S.EquationOfMotion xₜ ↔
    hamiltonEqOp S (fun t => S.toCanonicalMomentum t (xₜ t) (∂ₜ xₜ t)) xₜ = 0 := by
  rw [hamiltonEqOp, hamiltonEqOp_eq_zero_iff_hamiltons_equations]
  simp [toCanonicalMomentum_eq, gradient_hamiltonian_momentum_eq, gradient_hamiltonian_position_eq]
  rw [equationOfMotion_iff_newtons_2nd_law _ _ hx]
  have hderiv_smul : ∀ t, ∂ₜ (fun t' => S.m • ∂ₜ xₜ t') t = S.m • ∂ₜ (∂ₜ xₜ) t := by
    intro t
    have hd : DifferentiableAt ℝ (∂ₜ xₜ) t :=
      (deriv_differentiable_of_contDiff xₜ hx).differentiableAt
    calc
      ∂ₜ (fun t' => S.m • ∂ₜ xₜ t') t
          = fderiv ℝ (fun t' => S.m • ∂ₜ xₜ t') t 1 := rfl
      _ = S.m • (fderiv ℝ (∂ₜ xₜ) t 1) := by
          simpa using congrArg (fun L => L 1) (fderiv_const_smul (c := S.m) (f := ∂ₜ xₜ) hd)
      _ = S.m • ∂ₜ (∂ₜ xₜ) t := rfl
  simp [hderiv_smul, force_eq_linear]

/-!

## H. Equivalences between the different formulations of the equations of motion

We show that the following are equivalent statements for a smooth trajectory `xₜ`:
- The equation of motion holds. (aka the Euler-Lagrange equations hold.)
- Newton's second law holds.
- Hamilton's equations hold.
- The variational principle for the action holds.
- The Hamilton variational principle holds.

-/

lemma equationOfMotion_tfae (xₜ : Time → ConfigurationSpace) (hx : ContDiff ℝ ∞ xₜ) :
    List.TFAE [S.EquationOfMotion xₜ,
      (∀ t, S.m • ∂ₜ (∂ₜ xₜ) t = force S (xₜ t)),
      hamiltonEqOp S (fun t => S.toCanonicalMomentum t (xₜ t) (∂ₜ xₜ t)) xₜ = 0,
      (δ (q':=xₜ), ∫ t, lagrangian S t (q' t) (fderiv ℝ q' t 1)) = 0,
      (δ (pq':= fun t => (S.toCanonicalMomentum t (xₜ t) (∂ₜ xₜ t), xₜ t)),
        ∫ t, ⟪(pq' t).1, ∂ₜ (Prod.snd ∘ pq') t⟫_ℝ - S.hamiltonian t (pq' t).1 (pq' t).2) = 0] := by
  rw [← equationOfMotion_iff_hamiltonEqOp_eq_zero, ← equationOfMotion_iff_newtons_2nd_law]
  rw [hamiltons_equations_varGradient, euler_lagrange_varGradient]
  simp only [List.tfae_cons_self]
  rw [← gradLagrangian_eq_eulerLagrangeOp, ← equationOfMotion_iff_gradLagrangian_zero]
  simp only [List.tfae_cons_self]
  erw [← equationOfMotion_iff_hamiltonEqOp_eq_zero]
  simp only [List.tfae_cons_self, List.tfae_singleton]
  repeat fun_prop
  simp [toCanonicalMomentum_eq]
  repeat fun_prop

end HarmonicOscillator

end ClassicalMechanics
