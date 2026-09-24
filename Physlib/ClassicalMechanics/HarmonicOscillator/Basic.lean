/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Lode Vermeulen
-/
module

public import Physlib.ClassicalMechanics.EulerLagrange
public import Physlib.ClassicalMechanics.HamiltonsEquations
public import Physlib.Mathematics.Calculus.Gradient
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
/-!

# The Classical Harmonic Oscillator

## i. Overview

The classical harmonic oscillator is a classical mechanical system corresponding to a
mass `m` under a force `- k x` where `k` is the spring constant and `x` is the position.

In this file, a coordinate system is assumed where position and velocity both have type
`EuclideanSpace ℝ (Fin 1)`. This is a simpler model often used for pedagogical purpose,
but only works because both the configuration space (position) and its tangent space (velocity)
are isomorphic to Euclidean Space. A proper formalisation should include the geometric properties
of the state space via manifolds and tangent bundles.

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

* Landau & Lifshitz, Mechanics, page 58, section 21. [ref: landau_mechanics]

A reference for the geometric model of position/velocity discussed in a TODO below:

* https://web.williams.edu/Mathematics/it3/texts/var_noether.pdf.
  [ref: terek_variational_manifolds]
-/

@[expose] public section

namespace ClassicalMechanics
open Real
open Space
open InnerProductSpace

TODO "Create a new file for the geometric model which properly models the position as a
    configuration space and velocity as its tangent space, then show explicitly how this
    coordinate model is a simplification of the geometric model.
    A nice reference for such an analysis is:
    https://web.williams.edu/Mathematics/it3/texts/var_noether.pdf [ref: terek_variational_manifolds]"

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
lemma k_ne_zero : S.k ≠ 0 := S.k_pos.ne'

@[simp]
lemma m_ne_zero : S.m ≠ 0 := S.m_pos.ne'

/-!

## B. The angular frequency

From the input data, it is possible to define the angular frequency `ω` of the harmonic oscillator,
as `√(k/m)`.

The angular frequency appears in the solutions to the equations of motion of the harmonic
oscillator.

Here we both define and prove properties related to the angular frequency.

-/

/-- The angular frequency of the classical harmonic oscillator, `ω`, is defined
  as `√(k/m)`. -/
noncomputable def ω : ℝ := √(S.k / S.m)

/-- The angular frequency of the classical harmonic oscillator is positive. -/
@[simp]
lemma ω_pos : 0 < S.ω := sqrt_pos.mpr (div_pos S.k_pos S.m_pos)

/-- The square of the angular frequency of the classical harmonic oscillator is equal to `k/m`. -/
lemma ω_sq : S.ω^2 = S.k / S.m := sq_sqrt (div_pos S.k_pos S.m_pos).le

/-- The angular frequency of the classical harmonic oscillator is not equal to zero. -/
lemma ω_ne_zero : S.ω ≠ 0 := S.ω_pos.ne'

/-- The inverse of the square of the angular frequency of the classical harmonic oscillator
  is `m/k`. -/
lemma inverse_ω_sq : (S.ω ^ 2)⁻¹ = S.m/S.k := by rw [ω_sq, inv_div]

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
noncomputable def kineticEnergy (xₜ : Time → EuclideanSpace ℝ (Fin 1)) : Time → ℝ := fun t =>
  (1 / (2 : ℝ)) * S.m * ⟪∂ₜ xₜ t, ∂ₜ xₜ t⟫_ℝ

/-- The potential energy of the harmonic oscillator is `1/2 k x ^ 2` -/
noncomputable def potentialEnergy (x : EuclideanSpace ℝ (Fin 1)) : ℝ :=
  (1 / (2 : ℝ)) • S.k • ⟪x, x⟫_ℝ

/-- The energy of the harmonic oscillator is the kinetic energy plus the potential energy. -/
noncomputable def energy (xₜ : Time → EuclideanSpace ℝ (Fin 1)) : Time → ℝ := fun t =>
  kineticEnergy S xₜ t + potentialEnergy S (xₜ t)

/-!

### C.2. Simple equalities for the energies

-/

lemma kineticEnergy_eq (xₜ : Time → EuclideanSpace ℝ (Fin 1)) :
    kineticEnergy S xₜ = fun t => (1 / (2 : ℝ)) * S.m * ⟪∂ₜ xₜ t, ∂ₜ xₜ t⟫_ℝ:= by rfl

lemma potentialEnergy_eq (x : EuclideanSpace ℝ (Fin 1)) :
    potentialEnergy S x = (1 / (2 : ℝ)) • S.k • ⟪x, x⟫_ℝ:= by rfl

lemma energy_eq (xₜ : Time → EuclideanSpace ℝ (Fin 1)) :
    energy S xₜ = fun t => kineticEnergy S xₜ t + potentialEnergy S (xₜ t) := by rfl
/-!

### C.3. Differentiability of the energies

On smooth trajectories the energies are differentiable.

-/
@[fun_prop]
lemma kineticEnergy_differentiable (xₜ : Time → EuclideanSpace ℝ (Fin 1)) (hx : ContDiff ℝ ∞ xₜ) :
    Differentiable ℝ (kineticEnergy S xₜ) := by
  rw [kineticEnergy_eq]
  fun_prop

@[fun_prop]
lemma potentialEnergy_differentiable (xₜ : Time → EuclideanSpace ℝ (Fin 1)) (hx : ContDiff ℝ ∞ xₜ) :
    Differentiable ℝ (fun t => potentialEnergy S (xₜ t)) := by
  have hd : Differentiable ℝ xₜ := hx.differentiable (by simp)
  simp only [potentialEnergy_eq]
  fun_prop

@[fun_prop]
lemma energy_differentiable (xₜ : Time → EuclideanSpace ℝ (Fin 1)) (hx : ContDiff ℝ ∞ xₜ) :
    Differentiable ℝ (energy S xₜ) := by
  rw [energy_eq]
  fun_prop

/-!

### C.4. Time derivatives of the energies

For a general smooth trajectory (which may not satisfy the equations of motion) we can compute
the time derivatives of the energies.

-/

lemma kineticEnergy_deriv (xₜ : Time → EuclideanSpace ℝ (Fin 1)) (hx : ContDiff ℝ ∞ xₜ) :
    ∂ₜ (kineticEnergy S xₜ) = fun t => ⟪∂ₜ xₜ t, S.m • ∂ₜ (∂ₜ xₜ) t⟫_ℝ := by
  funext t
  unfold kineticEnergy
  have hd : DifferentiableAt ℝ (∂ₜ xₜ) t :=
    (deriv_differentiable_of_contDiff xₜ hx).differentiableAt
  rw [Time.deriv_eq, fderiv_const_mul (by fun_prop), _root_.smul_apply,
    fderiv_inner_apply (𝕜 := ℝ) hd hd, ← Time.deriv_eq]
  simp [inner_smul_right, real_inner_comm]
  ring

lemma potentialEnergy_deriv (xₜ : Time → EuclideanSpace ℝ (Fin 1)) (hx : ContDiff ℝ ∞ xₜ) :
    ∂ₜ (fun t => potentialEnergy S (xₜ t)) = fun t => ⟪∂ₜ xₜ t, S.k • xₜ t⟫_ℝ := by
  funext t
  have hd : DifferentiableAt ℝ xₜ t := (hx.differentiable (by simp)).differentiableAt
  simp only [potentialEnergy_eq, smul_eq_mul, ← mul_assoc]
  rw [Time.deriv_eq, fderiv_const_mul (by fun_prop), _root_.smul_apply,
    fderiv_inner_apply (𝕜 := ℝ) hd hd, ← Time.deriv_eq]
  simp [inner_smul_right, real_inner_comm]
  ring

lemma energy_deriv (xₜ : Time → EuclideanSpace ℝ (Fin 1)) (hx : ContDiff ℝ ∞ xₜ) :
    ∂ₜ (energy S xₜ) = fun t => ⟪∂ₜ xₜ t, S.m • ∂ₜ (∂ₜ xₜ) t + S.k • xₜ t⟫_ℝ := by
  unfold energy
  funext t
  rw [Time.deriv_eq, fderiv_fun_add (by fun_prop) (S.potentialEnergy_differentiable xₜ hx t)]
  simp only [_root_.add_apply, ← Time.deriv_eq, kineticEnergy_deriv _ _ hx,
    potentialEnergy_deriv _ _ hx, ← inner_add_right]

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
noncomputable def lagrangian (t : Time) (x : EuclideanSpace ℝ (Fin 1))
    (v : EuclideanSpace ℝ (Fin 1)) : ℝ :=
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
  simp [lagrangian, potentialEnergy, mul_assoc]

lemma lagrangian_eq_kineticEnergy_sub_potentialEnergy (t : Time)
    (xₜ : Time → EuclideanSpace ℝ (Fin 1)) :
    lagrangian S t (xₜ t) (∂ₜ xₜ t) = kineticEnergy S xₜ t - potentialEnergy S (xₜ t) := by
  rfl

/-!

#### D.1.2. Smoothness of the lagrangian

The lagrangian is smooth in all its arguments.

-/

@[fun_prop]
lemma contDiff_lagrangian (n : WithTop ℕ∞) : ContDiff ℝ n ↿S.lagrangian := by
  rw [lagrangian_eq]
  fun_prop

/-!

#### D.1.3. Gradients of the lagrangian

We now show results related to the gradients of the lagrangian with respect to the
position and velocity.

-/

lemma gradient_lagrangian_position_eq (t : Time) (x : EuclideanSpace ℝ (Fin 1))
    (v : EuclideanSpace ℝ (Fin 1)) :
    gradient (fun x => lagrangian S t x v) x = - S.k • x := by
  have h_eq : (fun y : EuclideanSpace ℝ (Fin 1) => lagrangian S t y v) =
      fun y => (-(1 / (2 : ℝ)) * S.k) * ⟪y, y⟫_ℝ + (1 / (2 : ℝ) * S.m * ⟪v, v⟫_ℝ) := by
    funext y; simp only [lagrangian_eq]; ring
  rw [h_eq, gradient_add_const, gradient_const_mul_inner_self]
  module

lemma gradient_lagrangian_velocity_eq (t : Time) (x : EuclideanSpace ℝ (Fin 1))
    (v : EuclideanSpace ℝ (Fin 1)) :
    gradient (lagrangian S t x) v = S.m • v := by
  have h_eq : (fun y : EuclideanSpace ℝ (Fin 1) => lagrangian S t x y) =
      fun y => ((1 / (2 : ℝ)) * S.m) * ⟪y, y⟫_ℝ + (-(1 / (2 : ℝ)) * S.k * ⟪x, x⟫_ℝ) := by
    funext y; simp only [lagrangian_eq]; ring
  change gradient (fun y : EuclideanSpace ℝ (Fin 1) => lagrangian S t x y) v = S.m • v
  rw [h_eq, gradient_add_const, gradient_const_mul_inner_self]
  module

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
noncomputable def gradLagrangian (xₜ : Time → EuclideanSpace ℝ (Fin 1)) :
    Time → EuclideanSpace ℝ (Fin 1) :=
  (δ (q':=xₜ), ∫ t, lagrangian S t (q' t) (fderiv ℝ q' t 1))

/-!

#### D.2.1. Equality for the variational derivative

Basic equalities for the variational derivative of the action.

-/

lemma gradLagrangian_eq_eulerLagrangeOp (xₜ : Time → EuclideanSpace ℝ (Fin 1))
    (hq : ContDiff ℝ ∞ xₜ) :
    gradLagrangian S xₜ = eulerLagrangeOp S.lagrangian xₜ := by
  rw [gradLagrangian, euler_lagrange_varGradient _ _ hq (S.contDiff_lagrangian _)]

/-!

### D.3. The equation of motion

The equation of motion for the harmonic oscillator is given by setting the
variational derivative of the action equal to zero.

-/

/-- The equation of motion for the Harmonic oscillator. -/
def EquationOfMotion (xₜ : Time → EuclideanSpace ℝ (Fin 1)) : Prop :=
  S.gradLagrangian xₜ = 0

/-!

#### D.3.1. Equation of motion if and only if variational-gradient of Lagrangian is zero

We write a simple iff statement for the definition of the equation of motions.

-/

lemma equationOfMotion_iff_gradLagrangian_zero (xₜ : Time → EuclideanSpace ℝ (Fin 1)) :
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
noncomputable def force (S : HarmonicOscillator) (x : EuclideanSpace ℝ (Fin 1)) :
    EuclideanSpace ℝ (Fin 1) :=
  - gradient (potentialEnergy S) x

/-!

#### E.1.1. The force is equal to `- k x`

We now show that the force is equal to `- k x`.

-/

/-- The force on the classical harmonic oscillator is `- k x`. -/
lemma force_eq_linear (x : EuclideanSpace ℝ (Fin 1)) : force S x = - S.k • x := by
  have hpot : potentialEnergy S = fun y : EuclideanSpace ℝ (Fin 1) =>
      ((1 / (2 : ℝ)) * S.k) * ⟪y, y⟫_ℝ := by
    funext y
    simp [potentialEnergy, mul_assoc]
  unfold force
  rw [hpot, gradient_const_mul_inner_self]
  module

/-!

### E.2. Variational derivative of lagrangian and force

We relate the variational derivative of lagrangian to the force, and show the relation
to Newton's second law.

-/

/-- The Euler lagrange operator corresponds to Newton's second law. -/
lemma gradLagrangian_eq_force (xₜ : Time → EuclideanSpace ℝ (Fin 1)) (hx : ContDiff ℝ ∞ xₜ) :
    S.gradLagrangian xₜ = fun t => force S (xₜ t) - S.m • ∂ₜ (∂ₜ xₜ) t := by
  funext t
  rw [gradLagrangian_eq_eulerLagrangeOp S xₜ hx, eulerLagrangeOp]
  simp [gradient_lagrangian_position_eq, gradient_lagrangian_velocity_eq, force_eq_linear,
    Time.deriv_smul _ S.m (deriv_differentiable_of_contDiff xₜ hx)]

/-!

### E.3. Equation of motion if and only if Newton's second law

We show that the equation of motion is equivalent to Newton's second law.

-/

lemma equationOfMotion_iff_newtons_2nd_law (xₜ : Time → EuclideanSpace ℝ (Fin 1))
    (hx : ContDiff ℝ ∞ xₜ) :
    S.EquationOfMotion xₜ ↔
    (∀ t, S.m • ∂ₜ (∂ₜ xₜ) t = force S (xₜ t)) := by
  rw [EquationOfMotion, gradLagrangian_eq_force S xₜ hx, funext_iff]
  simp only [Pi.zero_apply, sub_eq_zero]
  exact forall_congr' fun t => eq_comm

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

lemma energy_conservation_of_equationOfMotion (xₜ : Time → EuclideanSpace ℝ (Fin 1))
    (hx : ContDiff ℝ ∞ xₜ)
    (h : S.EquationOfMotion xₜ) : ∂ₜ (S.energy xₜ) = 0 := by
  rw [equationOfMotion_iff_newtons_2nd_law _ _ hx] at h
  funext t
  rw [energy_deriv _ _ hx]
  simp [h, force_eq_linear]

/-!

### F.2. Energy conservation in terms of constant energy

We prove that the energy is constant for any trajectory satisfying the equation of motion.

-/

lemma energy_conservation_of_equationOfMotion' (xₜ : Time → EuclideanSpace ℝ (Fin 1))
    (hx : ContDiff ℝ ∞ xₜ)
    (h : S.EquationOfMotion xₜ) (t : Time) : S.energy xₜ t = S.energy xₜ 0 := by
  apply is_const_of_fderiv_eq_zero (𝕜 := ℝ) (energy_differentiable S xₜ hx)
  intro t
  ext p
  rw [p.eq_one_smul, map_smul, ← Time.deriv_eq,
    S.energy_conservation_of_equationOfMotion xₜ hx h]
  simp

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
noncomputable def toCanonicalMomentum (t : Time) (x : EuclideanSpace ℝ (Fin 1)) :
    EuclideanSpace ℝ (Fin 1) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 1) where
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

lemma toCanonicalMomentum_eq (t : Time) (x : EuclideanSpace ℝ (Fin 1))
    (v : EuclideanSpace ℝ (Fin 1)) :
    toCanonicalMomentum S t x v = S.m • v :=
  gradient_lagrangian_velocity_eq S t x v

/-!

### G.2. The Hamiltonian

The hamiltonian is defined as a function of time, canonical momentum and position, as
```
H = ⟪p, v⟫ - L(t, x, v)
```
where `v` is a function of `p` and `x` through the canonical momentum.

-/

/-- The hamiltonian as a function of time, momentum and position. -/
noncomputable def hamiltonian (t : Time) (p : EuclideanSpace ℝ (Fin 1))
    (x : EuclideanSpace ℝ (Fin 1)) : ℝ :=
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
  field_simp
  ring

/-!

#### G.2.2. Smoothness of the Hamiltonian

We show that the Hamiltonian is smooth in all its arguments.

-/

@[fun_prop]
lemma hamiltonian_contDiff (n : WithTop ℕ∞) : ContDiff ℝ n ↿S.hamiltonian := by
  rw [hamiltonian_eq]
  fun_prop

/-!

#### G.2.3. Gradients of the Hamiltonian

We now write down the gradients of the Hamiltonian with respect to the momentum and position.

-/

lemma gradient_hamiltonian_position_eq (t : Time) (x : EuclideanSpace ℝ (Fin 1))
    (p : EuclideanSpace ℝ (Fin 1)) :
    gradient (hamiltonian S t p) x = S.k • x := by
  have h_eq : (fun y : EuclideanSpace ℝ (Fin 1) => hamiltonian S t p y) =
      fun y => ((1 / (2 : ℝ)) * S.k) * ⟪y, y⟫_ℝ +
        ((1 / (2 : ℝ)) * (1 / S.m) * ⟪p, p⟫_ℝ) := by
    funext y
    simp only [hamiltonian_eq]
    ring
  change gradient (fun y : EuclideanSpace ℝ (Fin 1) => hamiltonian S t p y) x = S.k • x
  rw [h_eq, gradient_add_const, gradient_const_mul_inner_self]
  module

lemma gradient_hamiltonian_momentum_eq (t : Time) (x : EuclideanSpace ℝ (Fin 1))
    (p : EuclideanSpace ℝ (Fin 1)) :
    gradient (hamiltonian S t · x) p = (1 / S.m) • p := by
  have h_eq : (fun y : EuclideanSpace ℝ (Fin 1) => hamiltonian S t y x) =
      fun y => ((1 / (2 : ℝ)) * (1 / S.m)) * ⟪y, y⟫_ℝ +
        ((1 / (2 : ℝ)) * S.k * ⟪x, x⟫_ℝ) := by
    funext y
    simp only [hamiltonian_eq]
  change gradient (fun y : EuclideanSpace ℝ (Fin 1) => hamiltonian S t y x) p = (1 / S.m) • p
  rw [h_eq, gradient_add_const, gradient_const_mul_inner_self]
  module

/-!

### G.3. Relation between Hamiltonian and energy

We show that the Hamiltonian, when evaluated on any trajectory, is equal to the energy.
This is independent of whether the trajectory satisfies the equations of motion or not.

-/

lemma hamiltonian_eq_energy (xₜ : Time → EuclideanSpace ℝ (Fin 1)) :
    (fun t => hamiltonian S t (toCanonicalMomentum S t (xₜ t) (∂ₜ xₜ t)) (xₜ t)) = energy S xₜ := by
  funext t
  rw [hamiltonian_eq]
  unfold energy kineticEnergy potentialEnergy
  simp only [toCanonicalMomentum_eq, inner_smul_left, inner_smul_right, smul_eq_mul, ringHom_apply]
  field_simp

/-!

### G.4. Hamilton equation operator

We define the operator on momentum-position phase-space whose vanishing is equivalent
to Hamilton's equations.

-/

/-- The operator on the momentum-position phase-space whose vanishing is equivalent to the
  hamilton's equations between the momentum and position. -/
noncomputable def hamiltonEqOp (p : Time → EuclideanSpace ℝ (Fin 1))
    (q : Time → EuclideanSpace ℝ (Fin 1)) :=
  ClassicalMechanics.hamiltonEqOp (hamiltonian S) p q

/-!

### G.5. Equation of motion if and only if Hamilton's equations

We show that the equation of motion is equivalent to Hamilton's equations, that is
to the vanishing of the Hamilton equation operator.

-/

lemma equationOfMotion_iff_hamiltonEqOp_eq_zero (xₜ : Time → EuclideanSpace ℝ (Fin 1))
    (hx : ContDiff ℝ ∞ xₜ) : S.EquationOfMotion xₜ ↔
    hamiltonEqOp S (fun t => S.toCanonicalMomentum t (xₜ t) (∂ₜ xₜ t)) xₜ = 0 := by
  rw [hamiltonEqOp, hamiltonEqOp_eq_zero_iff_hamiltons_equations]
  simp [toCanonicalMomentum_eq, gradient_hamiltonian_momentum_eq, gradient_hamiltonian_position_eq]
  rw [equationOfMotion_iff_newtons_2nd_law _ _ hx]
  simp [Time.deriv_smul _ S.m (deriv_differentiable_of_contDiff xₜ hx), force_eq_linear]

/-!

## H. Equivalences between the different formulations of the equations of motion

We show that the following are equivalent statements for a smooth trajectory `xₜ`:
- The equation of motion holds. (aka the Euler-Lagrange equations hold.)
- Newton's second law holds.
- Hamilton's equations hold.
- The variational principle for the action holds.
- The Hamilton variational principle holds.

-/

lemma equationOfMotion_tfae (xₜ : Time → EuclideanSpace ℝ (Fin 1)) (hx : ContDiff ℝ ∞ xₜ) :
    List.TFAE [S.EquationOfMotion xₜ,
      (∀ t, S.m • ∂ₜ (∂ₜ xₜ) t = force S (xₜ t)),
      hamiltonEqOp S (fun t => S.toCanonicalMomentum t (xₜ t) (∂ₜ xₜ t)) xₜ = 0,
      (δ (q':=xₜ), ∫ t, lagrangian S t (q' t) (fderiv ℝ q' t 1)) = 0,
      (δ (pq':= fun t => (S.toCanonicalMomentum t (xₜ t) (∂ₜ xₜ t), xₜ t)),
        ∫ t, ⟪(pq' t).1, ∂ₜ (Prod.snd ∘ pq') t⟫_ℝ - S.hamiltonian t (pq' t).1 (pq' t).2) = 0] := by
  rw [← equationOfMotion_iff_hamiltonEqOp_eq_zero, ← equationOfMotion_iff_newtons_2nd_law]
  rw [hamiltons_equations_varGradient, euler_lagrange_varGradient]
  simp only [List.tfae_cons_of_mem, List.mem_cons_self]
  rw [← gradLagrangian_eq_eulerLagrangeOp, ← equationOfMotion_iff_gradLagrangian_zero]
  simp only [List.tfae_cons_of_mem, List.mem_cons_self]
  erw [← equationOfMotion_iff_hamiltonEqOp_eq_zero]
  simp only [List.tfae_cons_of_mem, List.mem_cons_self, List.tfae_singleton]
  repeat fun_prop
  simp [toCanonicalMomentum_eq]
  repeat fun_prop

end HarmonicOscillator

end ClassicalMechanics
