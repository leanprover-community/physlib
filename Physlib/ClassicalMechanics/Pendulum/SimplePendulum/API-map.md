# Simple pendulum

A simple pendulum is a bob on a rigid massless rod of length ℓ, pinned at a pivot and swinging
in a vertical plane under gravity g. Its configuration is the angle of the rod from the
downward vertical, taken modulo a full turn, so the configuration space is a circle, and the
bob sits at (ℓ sin θ, −ℓ cos θ) in the plane. The motion obeys θ̈ + (g/ℓ) sin θ = 0.

For small amplitudes the pendulum is a harmonic oscillator of period 2π√(ℓ/g). For librations —
amplitudes below the inverted position — the period grows with the amplitude, and is given by a
complete elliptic integral, 4√(ℓ/g) K(sin²(θ₀/2)).

This API records the configuration space with its manifold structure and its embedding into
physical space, the lifted Lagrangian and equation of motion, and the equivalence of that
equation with the vanishing of the variational gradient of the action. Energy is conserved, the
Hamiltonian formulation is available, and the Newtonian, scalar, Hamiltonian and variational
formulations are shown to agree. Also here: the equilibria, with the separatrix energy and the
energy bounds on either side of it; the invariance of the lifted dynamics under shifting the
angle by whole turns; the uniqueness of the solution with given initial angle and angular
velocity, with its time-reversal symmetry; and, for any initial data, a curve with that data
solving the equation of motion near the initial instant.

The small-angle limit is treated in full — the linearized dynamics as a harmonic oscillator,
the period 2π√(ℓ/g), and a cubic bound on the linearization error — as is the
amplitude-dependent period formula, with its small-angle limit and its monotonicity and bounds
in the amplitude. Identifying that formula with the return time of the nonlinear motion remains
open.

## Built on

- Space — `Physlib/SpaceAndTime/Space`
- Configuration space for pendulum — `Physlib/ClassicalMechanics/Pendulum`

## Requirements

The key data structure is defined: the configuration space of the simple pendulum, the angle of
the rod from the downward vertical modulo a full turn. [1]

That configuration space is a manifold. [2]

The angular lift from the real line to the configuration space is available, periodic with
period 2π. [3]

The configuration space maps into space, giving the position of the bob there, subject to the
rod-length constraint. [4]

A trajectory will be defined on the configuration space. [planned]

The Lagrangian of the simple pendulum and its equation of motion are defined. [5]

The equation of motion holds exactly when the variational gradient of the action vanishes, and
energy is conserved along solutions. [6]

The Hamiltonian formulation is available, and the Newtonian, scalar, Hamiltonian and
variational formulations agree. [7]

The equilibria are solutions, and come with the separatrix energy and the energy bounds below
and above it. [8]

Shifting the angle by a whole number of turns leaves the lifted dynamics unchanged. [9]

The solution with a given initial angle and angular velocity is unique, and the solutions are
symmetric under time reversal. [10]

For any initial angle and angular velocity there is a curve with that initial data which
satisfies the equation of motion within ε of the initial instant. [11]

In the small-angle limit the pendulum is a harmonic oscillator of mass m ℓ² and spring constant
m g ℓ: the linearized equation of motion is the oscillator's, its motions exist and are unique,
and the period is 2π√(ℓ/g). [12]

The full and the linearized dynamics are related by the cubic bound m g ℓ |θ|³/6 on the error
in the torque, and the difference of the variational gradients of the two actions is the
difference of torque and linearized force. [13]

The period of a libration of amplitude θ₀ is 4√(ℓ/g) K(sin²(θ₀/2)), which equals 2π√(ℓ/g) at
zero amplitude; its small-angle limit, its monotonicity and its bounds in the amplitude are
recorded. [14]

That formula will be shown to be the period of the solution released from rest at amplitude θ₀,
for amplitudes strictly between zero and the inverted position. [planned]

## Further reading

- Landau & Lifshitz, Mechanics, 3rd Edition, Chapter 1 (The Equations of motion), Section 5 (The Lagrangian for a system of particles).
- Landau & Lifshitz, Mechanics, 3rd Edition, Chapter 3 (Integration of the equations of motion), Section 11 (Motion in one dimension), Problem 1 (the period of the pendulum as a complete elliptic integral).
- Landau & Lifshitz, Mechanics, 3rd Edition, Chapter 5 (Small oscillations), Section 21 (Free oscillations in one dimension).
- Landau & Lifshitz, Mechanics, 3rd Edition, Chapter 7 (The canonical equations), Section 40 (Hamilton's equations).

## Lean declarations

1. Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Geometric/Basic.lean — `SimplePendulum.ConfigurationSpace`,
   `SimplePendulum.ConfigurationSpace.circleHomeomorph`
2. Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Geometric/Basic.lean — `SimplePendulum.ConfigurationSpace.instChartedSpace`,
   `SimplePendulum.ConfigurationSpace.instIsManifold`
3. Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Geometric/Basic.lean — `SimplePendulum.ConfigurationSpace.ofAngle`,
   `SimplePendulum.ConfigurationSpace.ofAngle_periodic`,
   `SimplePendulum.ConfigurationSpace.ofAngle_eq_iff`
4. Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Geometric/Basic.lean — `SimplePendulum.ConfigurationSpace.toSpace`,
   `SimplePendulum.ConfigurationSpace.toSpace_ofAngle`,
   `SimplePendulum.ConfigurationSpace.toSpace_norm`
5. Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Basic.lean — `SimplePendulum.lagrangian`,
   `SimplePendulum.torque`, `SimplePendulum.EquationOfMotion`,
   `SimplePendulum.equationOfMotion_iff_scalar`
6. Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Basic.lean — `SimplePendulum.equationOfMotion_iff_gradLagrangian_zero`,
   `SimplePendulum.energy_conservation_of_equationOfMotion`
7. Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Hamiltonian.lean — `SimplePendulum.hamiltonian`,
   `SimplePendulum.hamiltonEqOp`, `SimplePendulum.equationOfMotion_tfae`
8. Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Equilibria.lean — `SimplePendulum.equationOfMotion_const_zero`,
   `SimplePendulum.equationOfMotion_const_pi`, `SimplePendulum.isSolution_const_zero`,
   `SimplePendulum.isSolution_const_pi`, `SimplePendulum.separatrixEnergy`,
   `SimplePendulum.neg_one_lt_cos_of_energy_lt`, `SimplePendulum.deriv_ne_zero_of_energy_gt`
9. Physlib/ClassicalMechanics/Pendulum/SimplePendulum/LiftInvariance.lean — `SimplePendulum.equationOfMotion_add_int_mul_two_pi`,
   `SimplePendulum.energy_add_int_mul_two_pi`, `SimplePendulum.isSolution_add_int_mul_two_pi`
10. Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Solution.lean — `SimplePendulum.phaseVectorField`,
   `SimplePendulum.equationOfMotion_unique`, `SimplePendulum.IsSolution.eq_of_initial`,
   `SimplePendulum.isSolution_comp_neg`, `SimplePendulum.releasedFromRest_even`
11. Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Solution.lean — `SimplePendulum.exists_local_solution`
12. Physlib/ClassicalMechanics/Pendulum/SimplePendulum/SmallAngle.lean — `SimplePendulum.toHarmonicOscillator`,
   `SimplePendulum.linearizedEquationOfMotion_iff`,
   `SimplePendulum.smallAngleTrajectory_linearizedEquationOfMotion`,
   `SimplePendulum.linearized_unique`, `SimplePendulum.smallAnglePeriod_eq`
13. Physlib/ClassicalMechanics/Pendulum/SimplePendulum/SmallAngle.lean — `SimplePendulum.abs_torque_add_linear_le`,
   `SimplePendulum.gradLagrangian_sub_toHarmonicOscillator`
14. Physlib/ClassicalMechanics/Pendulum/SimplePendulum/PeriodFormula.lean — `SimplePendulum.periodFormula`,
   `SimplePendulum.periodFormula_neg`, `SimplePendulum.periodFormula_zero`,
   `SimplePendulum.continuousOn_periodFormula`,
   `SimplePendulum.continuousAt_periodFormula_zero`,
   `SimplePendulum.periodFormula_tendsto_smallAnglePeriod`, `SimplePendulum.periodFormula_mono`,
   `SimplePendulum.periodFormula_strictMono`, `SimplePendulum.monotoneOn_periodFormula`,
   `SimplePendulum.strictMonoOn_periodFormula`,
   `SimplePendulum.smallAnglePeriod_le_periodFormula`, `SimplePendulum.periodFormula_pos`,
   `SimplePendulum.periodFormula_le`, `SimplePendulum.periodFormula_le'`
