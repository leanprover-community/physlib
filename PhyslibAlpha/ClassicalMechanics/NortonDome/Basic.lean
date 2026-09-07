/-
Copyright (c) 2026 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong
-/
module

public import Physlib.ClassicalMechanics.EulerLagrange
public import Physlib.Mathematics.Calculus.Gradient
public import PhyslibAlpha.ClassicalMechanics.NortonDome.Sqrt
/-!

# The Norton dome

## i. Overview

The Norton dome is a point mass `m` sliding without friction, under gravity `g`, on a
rotationally symmetric dome whose surface lies a depth `h(r) = (2/(3g)) r^{3/2}` below its
apex at arc length `r`. Its force is continuous, yet a mass at rest on the apex may stay there
forever or start sliding down at any later instant: the equation of motion has more than one
solution with given initial data. It is the standard example of the failure of determinism in
Newtonian mechanics and, mathematically, of the failure of uniqueness for an ODE whose
right-hand side is continuous but not Lipschitz.

Newton's laws, as stated, do not determine the motion. A Newtonian system that is to be
deterministic must add something the laws do not state, a regularity condition on the force or
a restriction on the admissible motions; which addition belongs to Newtonian mechanics is
debated, and the folder does not decide it. It proves what each candidate condition buys and
that the dome fails each. Reading order:

- `NortonDome.Basic` (this file): the dome, its energies, force, equation of motion `r̈ = √r`,
  and the failure of the Lipschitz condition at the apex.
- `NortonDome.Solution`: rest at the apex and departure at any instant `T` are all solutions
  from the same initial data, `exists_isSolution_ne`.
- `NortonDome.PhysicalSpace`: the arc-length chart as a point mass constrained to the surface.
- `NortonDome.NewtonianSystem`: the minimal `NewtonianSystem`; determinism, the first law and
  the regularity conditions as predicates; a locally Lipschitz force gives determinism.
- `NortonDome.Determinism`: the dome is not deterministic, violates the first law, and fails
  each regularity condition.
- `NortonDome.PeanoExistence`, `NortonDome.PosPartPow`, `NortonDome.Sqrt`: supporting
  analysis. Peano's theorem is pending in Mathlib and marked `@[sorryful]`; all else is proved.

The configuration is the arc length `r`, carried as for the pendulum on the Euclidean lift
`Time → EuclideanSpace ℝ (Fin 1)`. The physical dome is `r ≥ 0`; the chart is all of `ℝ`, and
for `r < 0` the truncated square root makes the force vanish. With `T = ½ m ṙ²` and
`V = -m g h(r) = -(2m/3) r^{3/2}` the equation of motion is `m r̈ = -dV/dr = m √r`, so
`r̈ = √r`: `m` and `g` cancel. Norton's profile presumes units in which the constant fixing the
size of the dome is `1`.

The force `√r` is continuous but not Lipschitz at the apex, and the potential is `C¹` but not
`C²` there; see `NortonDome.Determinism`. So the Picard–Lindelöf hypothesis, which the pendulum
satisfies, fails for the dome. For the same reason the Euler–Lagrange theorem
`euler_lagrange_varGradient`, which needs a smooth Lagrangian, does not apply, and the equation
of motion is identified only with the vanishing of the pointwise Euler–Lagrange operator.

## ii. Key results

- `NortonDome` holds the input data, the mass `m` and the gravitational acceleration `g`.
- `NortonDome.height` is the depth `(2/(3g)) r^{3/2}` of the dome below its apex, with its
  derivative `hasDerivAt_height` and `C¹` regularity `height_contDiff_one`.
- `NortonDome.kineticEnergy`, `NortonDome.potentialEnergy` and `NortonDome.energy` are the
  energies, with the gradient `gradient_potentialEnergy` of the potential and the time
  derivatives `kineticEnergy_deriv`, `potentialEnergy_deriv` and `energy_deriv` along twice
  differentiable curves.
- `NortonDome.lagrangian` is the Lagrangian `T - V`, with its partial gradients
  `gradient_lagrangian_position_eq` and `gradient_lagrangian_velocity_eq`.
- `NortonDome.force` is the generalized force `m √r` conjugate to the arc length. It is
  continuous, `force_continuous`, but not Lipschitz on any closed ball about the apex,
  `not_lipschitzOnWith_force`.
- `NortonDome.EquationOfMotion` is the equation of motion `m r̈ = F(r)`, with its scalar form
  `equationOfMotion_iff_scalar`; `NortonDome.IsSolution` is a twice differentiable solution.
- `NortonDome.equationOfMotion_iff_eulerLagrangeOp_zero` identifies the equation of motion,
  for curves with differentiable velocity, with the vanishing of the Euler–Lagrange operator.
- `NortonDome.IsSolution.energy_eq` is the conservation of energy along a solution.

## iii. Table of contents

- A. The input data
- B. The profile of the dome
  - B.1. The height below the apex
  - B.2. The derivative of the profile
- C. The energies
  - C.1. The definitions of the energies
  - C.2. Differentiability and the gradient of the potential
  - C.3. Time derivatives of the energies
- D. The Lagrangian
- E. The force and the equation of motion
  - E.1. The force
  - E.2. Regularity of the force
  - E.3. The equation of motion
  - E.4. Solutions
- F. The Euler–Lagrange operator
- G. Energy conservation

## iv. References

- Norton, J. D., *The dome: an unexpectedly simple failure of determinism*, Philosophy of
  Science 75 (2008), 786–798.
- Malament, D. B., *Norton's slippery slope*, Philosophy of Science 75 (2008), 799–816.

-/

@[expose] public section

namespace ClassicalMechanics
open Real InnerProductSpace

/-!

## A. The input data

The dome is specified by the mass of the particle and the gravitational acceleration; its shape
is fixed by Norton's formula.

-/

/-- The Norton dome is specified by the mass `m` of the particle sliding on it and the
  gravitational acceleration `g`, both positive. The configuration of the particle is the arc
  length from the apex. -/
structure NortonDome where
  /-- The mass of the particle. -/
  m : ℝ
  /-- The gravitational acceleration. -/
  g : ℝ
  m_pos : 0 < m
  g_pos : 0 < g

namespace NortonDome

variable (S : NortonDome)

/-- The mass of the particle is not equal to zero. -/
@[simp]
lemma m_ne_zero : S.m ≠ 0 := S.m_pos.ne'

/-- The gravitational acceleration is not equal to zero. -/
@[simp]
lemma g_ne_zero : S.g ≠ 0 := S.g_pos.ne'

/-!

## B. The profile of the dome

Norton's profile is the depth `h(r) = (2/(3g)) r^{3/2}` of the surface below the apex at arc
length `r`, written here as `(2/(3g)) √r ^ 3` so that it is defined, and vanishes, for `r ≤ 0`.

-/

/-!

### B.1. The height below the apex

-/

/-- The depth of the surface of the dome below its apex at arc length `r` from the apex,
  `(2/(3g)) r^{3/2}`. It vanishes at the apex and for negative arguments. -/
noncomputable def height (r : ℝ) : ℝ := 2 / (3 * S.g) * √r ^ 3

/-- The depth of the dome below its apex, written out. -/
lemma height_eq (r : ℝ) : S.height r = 2 / (3 * S.g) * √r ^ 3 := rfl

/-- The depth of the dome below its apex is non-negative. -/
lemma height_nonneg (r : ℝ) : 0 ≤ S.height r := by
  rw [height_eq]
  have hg := S.g_pos
  positivity

/-- The depth of the dome below its apex vanishes exactly at and before the apex. -/
lemma height_eq_zero_iff (r : ℝ) : S.height r = 0 ↔ r ≤ 0 := by
  rw [height_eq, mul_eq_zero, pow_eq_zero_iff three_ne_zero, Real.sqrt_eq_zero']
  simp

/-!

### B.2. The derivative of the profile

The slope `√r / g` of the profile is continuous and vanishes at the apex, so the profile is
`C¹`. The slope itself is not differentiable at the apex, so the profile is not `C²`.

-/

/-- The derivative of the depth of the dome with respect to the arc length is `√r / g`, at
  every `r`, including the apex. -/
lemma hasDerivAt_height (r : ℝ) : HasDerivAt S.height (√r / S.g) r := by
  have h := (hasDerivAt_sqrt_pow_three r).const_mul (2 / (3 * S.g))
  refine h.congr_deriv ?_
  field_simp

/-- The depth of the dome is a differentiable function of the arc length. -/
@[fun_prop]
lemma height_differentiable : Differentiable ℝ S.height :=
  fun r => (S.hasDerivAt_height r).differentiableAt

/-- The derivative of the depth of the dome with respect to the arc length is `√r / g`. -/
lemma deriv_height : deriv S.height = fun r => √r / S.g :=
  funext fun r => (S.hasDerivAt_height r).deriv

/-- The depth of the dome is a `C¹` function of the arc length. -/
lemma height_contDiff_one : ContDiff ℝ 1 S.height := by
  rw [contDiff_one_iff_deriv, deriv_height]
  exact ⟨S.height_differentiable, by fun_prop⟩

open Time

/-!

## C. The energies

The kinetic energy is `½ m ṙ²`, `r` being the arc length so that the speed is `|ṙ|`, and the
potential energy is `-m g h(r)`, normalized to vanish at the apex.

-/

/-!

### C.1. The definitions of the energies

-/

/-- The kinetic energy of the particle on the dome along a curve `r` of the arc length is
  `½ m ‖ṙ‖²`. -/
noncomputable def kineticEnergy (r : Time → EuclideanSpace ℝ (Fin 1)) : Time → ℝ := fun t =>
  (1 / (2 : ℝ)) * S.m * ⟪∂ₜ r t, ∂ₜ r t⟫_ℝ

/-- The potential energy of the particle on the dome at arc length `x` from the apex is
  `-m g h(x 0)`, the gravitational potential at depth `h` below the apex, which vanishes at the
  apex. -/
noncomputable def potentialEnergy (x : EuclideanSpace ℝ (Fin 1)) : ℝ :=
  -(S.m * S.g * S.height (x 0))

/-- The energy of the particle on the dome is the kinetic energy plus the potential energy. -/
noncomputable def energy (r : Time → EuclideanSpace ℝ (Fin 1)) : Time → ℝ := fun t =>
  S.kineticEnergy r t + S.potentialEnergy (r t)

/-- The kinetic energy of the particle on the dome, written out. -/
lemma kineticEnergy_eq (r : Time → EuclideanSpace ℝ (Fin 1)) :
    S.kineticEnergy r = fun t => (1 / (2 : ℝ)) * S.m * ⟪∂ₜ r t, ∂ₜ r t⟫_ℝ := rfl

/-- The potential energy of the particle on the dome is `-(2m/3) r^{3/2}`: the gravitational
  acceleration cancels against the shape of the dome. -/
lemma potentialEnergy_eq (x : EuclideanSpace ℝ (Fin 1)) :
    S.potentialEnergy x = -(2 * S.m / 3) * √(x 0) ^ 3 := by
  rw [potentialEnergy, height_eq]
  field_simp

/-- The energy of the particle on the dome, written out. -/
lemma energy_eq (r : Time → EuclideanSpace ℝ (Fin 1)) :
    S.energy r = fun t => S.kineticEnergy r t + S.potentialEnergy (r t) := rfl

/-- The potential energy of the particle on the dome is non-positive, the apex being the
  highest point of the dome. -/
lemma potentialEnergy_nonpos (x : EuclideanSpace ℝ (Fin 1)) : S.potentialEnergy x ≤ 0 := by
  rw [potentialEnergy, neg_nonpos]
  exact mul_nonneg (mul_pos S.m_pos S.g_pos).le (S.height_nonneg _)

/-- The potential energy of the particle on the dome vanishes exactly at the apex, that is for
  arc length `≤ 0`. -/
lemma potentialEnergy_eq_zero_iff (x : EuclideanSpace ℝ (Fin 1)) :
    S.potentialEnergy x = 0 ↔ x 0 ≤ 0 := by
  rw [potentialEnergy, neg_eq_zero, mul_eq_zero, or_iff_right (mul_pos S.m_pos S.g_pos).ne',
    height_eq_zero_iff]

/-!

### C.2. Differentiability and the gradient of the potential

The potential energy is differentiable, with gradient `-m √r` times the unit vector of the
arc-length coordinate. It is `C¹` but not `C²`, since `√r` is not differentiable at `0`.

-/

/-- The cube of the square root of the arc-length coordinate is differentiable on the Euclidean
  lift, at every point. -/
lemma differentiableAt_sqrt_coord_pow_three (x : EuclideanSpace ℝ (Fin 1)) :
    DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin 1) => √(y 0) ^ 3) x := by
  have h : HasFDerivAt ((fun y : ℝ => √y ^ 3) ∘ ⇑(EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1))) _ x :=
    (hasDerivAt_sqrt_pow_three (x 0)).comp_hasFDerivAt x
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).hasFDerivAt
  exact h.differentiableAt

/-- The potential energy of the particle on the dome is a differentiable function of the arc
  length. -/
@[fun_prop]
lemma differentiable_potentialEnergy : Differentiable ℝ S.potentialEnergy := by
  intro x
  have h : S.potentialEnergy = fun y => -(2 * S.m / 3) * √(y 0) ^ 3 :=
    funext S.potentialEnergy_eq
  rw [h]
  exact (differentiableAt_sqrt_coord_pow_three x).const_mul _

/-- The gradient of the potential energy of the particle on the dome is `-m √r` times the unit
  vector of the arc-length coordinate. -/
lemma gradient_potentialEnergy (x : EuclideanSpace ℝ (Fin 1)) :
    gradient S.potentialEnergy x = -(S.m * √(x 0)) • EuclideanSpace.single 0 1 := by
  have h : S.potentialEnergy = fun y => -(2 * S.m / 3) * √(y 0) ^ 3 :=
    funext S.potentialEnergy_eq
  rw [h, gradient_const_mul _ (differentiableAt_sqrt_coord_pow_three x),
    gradient_comp_coord 0 x (hasDerivAt_sqrt_pow_three (x 0)), smul_smul]
  congr 1
  ring

/-- Along a curve of the arc length with differentiable velocity the kinetic energy is
  differentiable in time. -/
@[fun_prop]
lemma kineticEnergy_differentiable (r : Time → EuclideanSpace ℝ (Fin 1))
    (hr' : Differentiable ℝ (∂ₜ r)) : Differentiable ℝ (S.kineticEnergy r) := by
  rw [kineticEnergy_eq]
  fun_prop

/-- Along a differentiable curve of the arc length the potential energy is a differentiable
  function of the time. -/
@[fun_prop]
lemma potentialEnergy_differentiable (r : Time → EuclideanSpace ℝ (Fin 1))
    (hr : Differentiable ℝ r) : Differentiable ℝ (fun t => S.potentialEnergy (r t)) :=
  S.differentiable_potentialEnergy.comp hr

/-- Along a twice differentiable curve of the arc length the energy is differentiable in
  time. -/
@[fun_prop]
lemma energy_differentiable (r : Time → EuclideanSpace ℝ (Fin 1)) (hr : Differentiable ℝ r)
    (hr' : Differentiable ℝ (∂ₜ r)) : Differentiable ℝ (S.energy r) := by
  rw [energy_eq]
  fun_prop

/-!

### C.3. Time derivatives of the energies

Along a twice differentiable curve, solution or not, the time derivatives of the energies are
inner products against the velocity; the equation of motion makes the two contributions cancel.

-/

/-- The rate of change of the kinetic energy is the velocity paired with `m r̈`. -/
lemma kineticEnergy_deriv (r : Time → EuclideanSpace ℝ (Fin 1))
    (hr' : Differentiable ℝ (∂ₜ r)) :
    ∂ₜ (S.kineticEnergy r) = fun t => ⟪∂ₜ r t, S.m • ∂ₜ (∂ₜ r) t⟫_ℝ := by
  funext t
  unfold kineticEnergy
  have hd : DifferentiableAt ℝ (∂ₜ r) t := hr' t
  rw [Time.deriv_eq, fderiv_const_mul (by fun_prop), _root_.smul_apply,
    fderiv_inner_apply (𝕜 := ℝ) hd hd, ← Time.deriv_eq]
  simp [inner_smul_right, real_inner_comm]
  ring

/-- The rate of change of the potential energy is the velocity paired with the gradient of the
  potential. -/
lemma potentialEnergy_deriv (r : Time → EuclideanSpace ℝ (Fin 1)) (hr : Differentiable ℝ r) :
    ∂ₜ (fun t => S.potentialEnergy (r t)) =
      fun t => ⟪∂ₜ r t, gradient S.potentialEnergy (r t)⟫_ℝ := by
  funext t
  have hf : HasFDerivAt (fun t => S.potentialEnergy (r t)) _ t :=
    (S.differentiable_potentialEnergy (r t)).hasFDerivAt.comp t (hr t).hasFDerivAt
  rw [Time.deriv_eq, hf.fderiv]
  simp [Time.deriv_eq]

/-- The rate of change of the energy is the velocity paired with the sum of `m r̈` and the
  gradient of the potential; the equation of motion is exactly the vanishing of that sum. -/
lemma energy_deriv (r : Time → EuclideanSpace ℝ (Fin 1)) (hr : Differentiable ℝ r)
    (hr' : Differentiable ℝ (∂ₜ r)) :
    ∂ₜ (S.energy r) =
      fun t => ⟪∂ₜ r t, S.m • ∂ₜ (∂ₜ r) t + gradient S.potentialEnergy (r t)⟫_ℝ := by
  unfold energy
  funext t
  rw [Time.deriv_eq, fderiv_fun_add (S.kineticEnergy_differentiable r hr' t)
    (S.potentialEnergy_differentiable r hr t)]
  simp only [_root_.add_apply, ← Time.deriv_eq, S.kineticEnergy_deriv r hr',
    S.potentialEnergy_deriv r hr, ← inner_add_right]

/-!

## D. The Lagrangian

The Lagrangian `L = ½ m ṙ² + m g h(r)` is a function on phase space. Unlike those of the
harmonic oscillator and the pendulum it is only `C¹`; its partial gradients still exist, and
are the force of section E and the momentum `m ṙ`.

-/

set_option linter.unusedVariables false in
/-- The Lagrangian of the particle on the dome, `L(t, r, ṙ) = ½ m ‖ṙ‖² - V(r)`, the kinetic
  energy minus the potential energy as a function on phase space. It does not depend on the
  time. -/
@[nolint unusedArguments]
noncomputable def lagrangian (t : Time) (x v : EuclideanSpace ℝ (Fin 1)) : ℝ :=
  (1 / (2 : ℝ)) * S.m * ⟪v, v⟫_ℝ - S.potentialEnergy x

/-- Along a curve of the arc length the Lagrangian of the particle on the dome is the kinetic
  energy minus the potential energy. -/
lemma lagrangian_eq_kineticEnergy_sub_potentialEnergy (t : Time)
    (r : Time → EuclideanSpace ℝ (Fin 1)) :
    S.lagrangian t (r t) (∂ₜ r t) = S.kineticEnergy r t - S.potentialEnergy (r t) := rfl

/-- The gradient of the Lagrangian of the particle on the dome in the arc length is minus the
  gradient of the potential energy, `m √r` times the unit vector of the arc-length
  coordinate. -/
lemma gradient_lagrangian_position_eq (t : Time) (x v : EuclideanSpace ℝ (Fin 1)) :
    gradient (fun x => S.lagrangian t x v) x = (S.m * √(x 0)) • EuclideanSpace.single 0 1 := by
  have h : (fun y : EuclideanSpace ℝ (Fin 1) => S.lagrangian t y v) =
      fun y => (-1 : ℝ) * S.potentialEnergy y + (1 / (2 : ℝ)) * S.m * ⟪v, v⟫_ℝ := by
    funext y
    rw [lagrangian]
    ring
  rw [h, gradient_add_const, gradient_const_mul _ (S.differentiable_potentialEnergy x),
    gradient_potentialEnergy]
  module

/-- The gradient of the Lagrangian of the particle on the dome in the velocity is the momentum
  `m ṙ`. -/
lemma gradient_lagrangian_velocity_eq (t : Time) (x v : EuclideanSpace ℝ (Fin 1)) :
    gradient (S.lagrangian t x) v = S.m • v := by
  have h : S.lagrangian t x = fun y : EuclideanSpace ℝ (Fin 1) =>
      ((1 / (2 : ℝ)) * S.m) * ⟪y, y⟫_ℝ + -S.potentialEnergy x := by
    funext y
    rw [lagrangian]
    ring
  rw [h, gradient_add_const, gradient_const_mul_inner_self]
  module

/-!

## E. The force and the equation of motion

Gravity exerts the generalized force `m √r` conjugate to the arc length, balanced against
`m r̈`. As for the pendulum this pointwise relation is the definition of the equation of
motion; the variational derivative of the action is not available, the Lagrangian not being
smooth.

-/

/-!

### E.1. The force

-/

/-- The generalized force on the particle on the dome conjugate to the arc length, minus the
  gradient of the potential energy, `F = -∂V/∂r`. -/
noncomputable def force (x : EuclideanSpace ℝ (Fin 1)) : EuclideanSpace ℝ (Fin 1) :=
  -gradient S.potentialEnergy x

/-- The force on the particle on the dome is `m √r` times the unit vector of the arc-length
  coordinate: it points away from the apex, and vanishes there. -/
lemma force_eq (x : EuclideanSpace ℝ (Fin 1)) :
    S.force x = (S.m * √(x 0)) • EuclideanSpace.single 0 1 := by
  rw [force, gradient_potentialEnergy, neg_smul, neg_neg]

/-- The single component of the force on the particle on the dome is `m √r`. -/
lemma force_apply (x : EuclideanSpace ℝ (Fin 1)) : S.force x 0 = S.m * √(x 0) := by
  rw [force_eq]
  simp

/-- The force on the particle on the dome vanishes at the apex. -/
lemma force_zero : S.force 0 = 0 := by
  rw [force_eq]
  simp

/-!

### E.2. Regularity of the force

The force is continuous. It is not Lipschitz on any closed ball about the apex, since the square
root is not Lipschitz on any `[0, ε]`: the Picard–Lindelöf hypothesis fails, which is the
source of the non-uniqueness.

-/

/-- The force on the particle on the dome is a continuous function of the arc length. -/
@[fun_prop]
lemma force_continuous : Continuous S.force := by
  have h : S.force = fun x => (S.m * √(x 0)) • EuclideanSpace.single 0 1 := funext S.force_eq
  rw [h]
  fun_prop

/-- The distance between two multiples of the unit vector of the arc-length coordinate is the
  distance between the coefficients. -/
lemma dist_smul_single (a b : ℝ) :
    dist (a • EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) (b • EuclideanSpace.single 0 1) =
      |a - b| := by
  rw [dist_eq_norm, ← sub_smul, norm_smul, PiLp.norm_single, norm_one, mul_one,
    Real.norm_eq_abs]

/-- The force on the particle on the dome is not Lipschitz on any closed ball about the apex,
  for any Lipschitz constant. -/
lemma not_lipschitzOnWith_force (K : NNReal) {ε : ℝ} (hε : 0 < ε) :
    ¬ LipschitzOnWith K S.force (Metric.closedBall 0 ε) := by
  intro h
  refine not_lipschitzOnWith_sqrt ⟨(K : ℝ) / S.m, div_nonneg K.2 S.m_pos.le⟩ hε ?_
  refine LipschitzOnWith.of_dist_le_mul fun y hy z hz => ?_
  have hmem : ∀ w ∈ Set.Icc (0 : ℝ) ε,
      w • EuclideanSpace.single (0 : Fin 1) (1 : ℝ) ∈ Metric.closedBall 0 ε := by
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, PiLp.norm_single, norm_one,
      mul_one, Real.norm_eq_abs, abs_of_nonneg hw.1]
    exact hw.2
  have := h.dist_le_mul _ (hmem y hy) _ (hmem z hz)
  rw [force_eq, force_eq, dist_smul_single, dist_smul_single] at this
  simp only [PiLp.smul_apply, PiLp.single_apply, if_true, smul_eq_mul, mul_one,
    ← mul_sub, abs_mul, abs_of_pos S.m_pos] at this
  show dist √y √z ≤ (K : ℝ) / S.m * dist y z
  rw [Real.dist_eq, Real.dist_eq, div_mul_eq_mul_div, le_div_iff₀ S.m_pos, mul_comm]
  exact this

/-!

### E.3. The equation of motion

-/

/-- The equation of motion of the particle on the dome: at every instant `m r̈` equals the
  generalized force `F(r) = m √r`. This pointwise relation is the definition; for curves with
  differentiable velocity it is the vanishing of the Euler–Lagrange operator of the Lagrangian,
  `equationOfMotion_iff_eulerLagrangeOp_zero`. -/
def EquationOfMotion (r : Time → EuclideanSpace ℝ (Fin 1)) : Prop :=
  ∀ t, S.m • ∂ₜ (∂ₜ r) t = S.force (r t)

/-- The equation of motion with all terms on one side: at every instant `m r̈` plus the
  gradient of the potential energy vanishes. This is the combination `energy_deriv` pairs with
  the velocity. -/
lemma equationOfMotion_iff_newtons_2nd_law (r : Time → EuclideanSpace ℝ (Fin 1)) :
    S.EquationOfMotion r ↔
      ∀ t, S.m • ∂ₜ (∂ₜ r) t + gradient S.potentialEnergy (r t) = 0 := by
  simp only [EquationOfMotion, force, eq_neg_iff_add_eq_zero]

/-- The equation of motion of the particle on the dome in scalar form, `r̈ = √r`. Both the mass
  and the gravitational acceleration have cancelled. -/
lemma equationOfMotion_iff_scalar (r : Time → EuclideanSpace ℝ (Fin 1)) :
    S.EquationOfMotion r ↔ ∀ t, ∂ₜ (∂ₜ r) t 0 = √(r t 0) := by
  simp only [EquationOfMotion]
  refine forall_congr' fun t => ?_
  rw [force_eq]
  constructor
  · intro h
    have := congrArg (fun y : EuclideanSpace ℝ (Fin 1) => y 0) h
    simpa [S.m_ne_zero] using this
  · intro h
    ext i
    fin_cases i
    simp [h]

/-!

### E.4. Solutions

A solution is a twice differentiable curve, position and velocity both differentiable, satisfying
the equation of motion: the regularity of `ClassicalMechanics.ReferenceFrame.Particle` and the
least under which the acceleration exists. Regularity is part of the definition because the bare
pointwise equation, whose derivatives are zero wherever they do not exist, admits rough accidental
solutions. Smoothness is not demanded: the motions leaving the apex are `C³` but not `C⁴`.

-/

/-- A solution of the dome is a twice differentiable curve of the arc length, its position and
  velocity both differentiable, satisfying the equation of motion. -/
def IsSolution (r : Time → EuclideanSpace ℝ (Fin 1)) : Prop :=
  Differentiable ℝ r ∧ Differentiable ℝ (∂ₜ r) ∧ S.EquationOfMotion r

/-- The position along a solution of the dome is differentiable. -/
lemma IsSolution.differentiable {S : NortonDome} {r : Time → EuclideanSpace ℝ (Fin 1)}
    (h : S.IsSolution r) : Differentiable ℝ r := h.1

/-- The velocity along a solution of the dome is differentiable. -/
lemma IsSolution.deriv_differentiable {S : NortonDome} {r : Time → EuclideanSpace ℝ (Fin 1)}
    (h : S.IsSolution r) : Differentiable ℝ (∂ₜ r) := h.2.1

/-- A solution of the dome satisfies the equation of motion. -/
lemma IsSolution.equationOfMotion {S : NortonDome} {r : Time → EuclideanSpace ℝ (Fin 1)}
    (h : S.IsSolution r) : S.EquationOfMotion r := h.2.2

/-!

## F. The Euler–Lagrange operator

With the gradients of section D, the pointwise Euler–Lagrange operator along any curve with
differentiable velocity is the force minus `m r̈`, so its vanishing is the equation of motion.
The identification of this operator with the variational derivative of the action,
`euler_lagrange_varGradient`, needs a smooth Lagrangian and so does not apply to the dome.

-/

/-- Along a curve of the arc length with differentiable velocity the Euler–Lagrange operator of
  the Lagrangian of the dome is the force minus `m r̈`. -/
lemma eulerLagrangeOp_lagrangian (r : Time → EuclideanSpace ℝ (Fin 1))
    (hr' : Differentiable ℝ (∂ₜ r)) :
    eulerLagrangeOp S.lagrangian r = fun t => S.force (r t) - S.m • ∂ₜ (∂ₜ r) t := by
  funext t
  rw [eulerLagrangeOp]
  simp [S.gradient_lagrangian_position_eq, S.gradient_lagrangian_velocity_eq, S.force_eq,
    Time.deriv_smul _ S.m hr']

/-- For a curve of the arc length with differentiable velocity the equation of motion of the
  dome holds if and only if the Euler–Lagrange operator of its Lagrangian vanishes along it. -/
lemma equationOfMotion_iff_eulerLagrangeOp_zero (r : Time → EuclideanSpace ℝ (Fin 1))
    (hr' : Differentiable ℝ (∂ₜ r)) :
    S.EquationOfMotion r ↔ eulerLagrangeOp S.lagrangian r = 0 := by
  rw [S.eulerLagrangeOp_lagrangian r hr', funext_iff]
  simp only [EquationOfMotion, Pi.zero_apply, sub_eq_zero]
  exact forall_congr' fun t => eq_comm

/-!

## G. Energy conservation

Along any twice differentiable curve satisfying the equation of motion the energy is constant.
This follows from `energy_deriv`. Conservation of energy does not restore uniqueness: the motion
at rest at the apex and every motion leaving it all have zero energy, which is proved in
`NortonDome.Solution` as `energy_rest` and `energy_solution`.

-/

/-- Along a twice differentiable curve of the arc length satisfying the equation of motion the
  time derivative of the energy of the dome vanishes. -/
lemma energy_conservation_of_equationOfMotion (r : Time → EuclideanSpace ℝ (Fin 1))
    (hr : Differentiable ℝ r) (hr' : Differentiable ℝ (∂ₜ r)) (h : S.EquationOfMotion r) :
    ∂ₜ (S.energy r) = 0 := by
  rw [S.equationOfMotion_iff_newtons_2nd_law r] at h
  funext t
  rw [S.energy_deriv r hr hr']
  simp [h t]

/-- Along a twice differentiable curve of the arc length satisfying the equation of motion the
  energy of the dome at any time is equal to its initial value. -/
lemma energy_conservation_of_equationOfMotion' (r : Time → EuclideanSpace ℝ (Fin 1))
    (hr : Differentiable ℝ r) (hr' : Differentiable ℝ (∂ₜ r)) (h : S.EquationOfMotion r)
    (t : Time) : S.energy r t = S.energy r 0 := by
  apply is_const_of_fderiv_eq_zero (𝕜 := ℝ) (S.energy_differentiable r hr hr')
  intro t
  ext p
  rw [p.eq_one_smul, map_smul, ← Time.deriv_eq,
    S.energy_conservation_of_equationOfMotion r hr hr' h]
  simp

/-- The energy of the dome along a solution at any time is equal to its initial value. -/
lemma IsSolution.energy_eq {S : NortonDome} {r : Time → EuclideanSpace ℝ (Fin 1)}
    (h : S.IsSolution r) (t : Time) : S.energy r t = S.energy r 0 :=
  S.energy_conservation_of_equationOfMotion' r h.differentiable h.deriv_differentiable
    h.equationOfMotion t

end NortonDome

end ClassicalMechanics

end
