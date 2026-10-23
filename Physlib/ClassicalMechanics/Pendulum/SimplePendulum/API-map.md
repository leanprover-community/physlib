# Simple pendulum

## Abstract (Alpha)

A simple pendulum is a bob on a rigid massless rod of length ℓ, pinned at a pivot and swinging in a
vertical plane under gravity g. Its configuration is the angle of the rod from the downward
vertical, taken modulo a full turn, so the configuration space is a circle and the bob sits at (ℓ
sin θ, −ℓ cos θ) in the plane. The motion obeys θ̈ + (g/ℓ) sin θ = 0, which admits Newtonian,
Lagrangian and Hamiltonian formulations, conserves energy, and has a unique solution for given
initial angle and angular velocity. For small amplitudes the pendulum is a harmonic oscillator of
period 2π√(ℓ/g); for librations — amplitudes below the inverted position — the period grows with the
amplitude and is given by the complete elliptic integral 4√(ℓ/g) K(sin²(θ₀/2)).

## Content (Alpha)

### Configuration space

The configuration space of the simple pendulum, one of the pendulum configuration spaces {1}, is the
angle of the rod from the downward vertical modulo a full turn, homeomorphic to the circle. [1] That
configuration space is a manifold. [2] The angular lift from the real line to the configuration
space is periodic with period 2π, and two angles give the same configuration exactly when they
differ by a whole number of turns. [3] The configuration space maps into physical space {2}, sending
an angle θ to the position (ℓ sin θ, −ℓ cos θ) of the bob, which lies at distance ℓ from the pivot.
[4] A trajectory is a curve in the configuration space. [TODO]

### Dynamics

The Lagrangian of the simple pendulum is the kinetic energy ½ m ℓ² θ̇² minus the gravitational
potential energy {3}. Its equation of motion m ℓ² θ̈ = −m g ℓ sin θ equates the rate of change of
angular momentum with the gravitational torque, and is equivalent to the scalar form θ̈ + (g/ℓ) sin
θ = 0. [5] The equation of motion holds exactly when the variational gradient of the action
vanishes, and energy is conserved along solutions. [6] The Hamiltonian formulation {4} is
equivalent: the Newtonian, scalar, Hamiltonian and variational formulations agree. [7]

The hanging and the inverted positions are equilibria and solve the equation of motion. The
separatrix energy 2 m g ℓ divides the motions: below it the pendulum never reaches the inverted
position, and above it the angular velocity never vanishes. [8] Shifting the angle by a whole number
of turns leaves the lifted dynamics unchanged. [9] The solution with a given initial angle and
angular velocity is unique, the solutions are symmetric under time reversal, and a pendulum released
from rest swings symmetrically in time. [10] For any initial angle and angular velocity there is a
curve with that initial data which satisfies the equation of motion within ε of the initial instant.
[11]

### Small oscillations and the period

In the small-angle limit {5} the pendulum is a harmonic oscillator of mass m ℓ² and spring constant
m g ℓ: the linearized equation of motion is the oscillator's, its motions exist and are unique, and
the period is 2π√(ℓ/g). [12] The full and the linearized dynamics are related by the cubic bound
m g ℓ |θ|³/6 on the error in the torque, and the difference of the variational gradients of the two
actions is the difference of the torque and the linearized force. [13]

The period of a libration of amplitude θ₀ is 4√(ℓ/g) K(sin²(θ₀/2)) {6}. This formula equals
2π√(ℓ/g) at zero amplitude, tends to the small-angle period as the amplitude goes to zero, increases
with the amplitude on [0, π), and is bounded below by the small-angle period and above by the
small-angle period divided by cos(θ₀/2). [14] It is the period of the solution released from rest
at amplitude θ₀, for amplitudes strictly between zero and the inverted position. [TODO]

## Lean References

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

## References

1. Configuration space for pendulum API map — Physlib/ClassicalMechanics/Pendulum/API-map.md
2. Space API map — Physlib/SpaceAndTime/Space/API-map.md
3. Landau & Lifshitz, *Mechanics*, 3rd Edition, Chapter 1 (The Equations of motion), Section 5 (The
   Lagrangian for a system of particles).
4. Landau & Lifshitz, *Mechanics*, 3rd Edition, Chapter 7 (The canonical equations), Section 40
   (Hamilton's equations).
5. Landau & Lifshitz, *Mechanics*, 3rd Edition, Chapter 5 (Small oscillations), Section 21 (Free
   oscillations in one dimension).
6. Landau & Lifshitz, *Mechanics*, 3rd Edition, Chapter 3 (Integration of the equations of motion),
   Section 11 (Motion in one dimension), Problem 1.
