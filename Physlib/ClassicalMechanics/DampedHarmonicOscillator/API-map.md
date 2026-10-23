# Damped harmonic oscillator

## Abstract (Alpha)

A damped harmonic oscillator is a mass under a restoring force proportional to its displacement and
a damping force proportional to its velocity, so that m ẍ + γ ẋ + k x = 0. Its data is that of the
undamped oscillator — a positive mass and spring constant — together with a nonnegative damping
coefficient, and position and velocity live in one-dimensional Euclidean space, with a trajectory a
map from time into it. The sign of the discriminant γ² − 4 m k splits the motion into underdamped,
critically damped and overdamped regimes, each solved in closed form, and the Caldirola–Kanai
Lagrangian gives the dissipative dynamics a variational description.

## Content (Alpha)

A damped harmonic oscillator {1}{2} is specified by its mass, its spring constant and its damping
coefficient. [1] Its equation of motion, for a trajectory from time {3} into one-dimensional
Euclidean space, is m ẍ + γ ẋ + k x = 0. [2] The force on the mass is −k x − γ ẋ, and the equation
of motion is Newton's second law for that force. [3] With no damping the system is the undamped
harmonic oscillator, and the two equations of motion agree. [6]

The kinetic energy is ½ m ‖ẋ‖², that of the underlying undamped oscillator. [10] The potential
energy is ½ k ‖x‖². [11] Along a solution the mechanical energy dissipates at the rate −γ ‖ẋ‖², and
strictly decreases whenever the velocity is nonzero and the damping is positive. [4]

The discriminant γ² − 4 m k classifies the motion: it is underdamped when the discriminant is
negative, critically damped when it vanishes, and overdamped when it is positive, and each regime
has a decay rate γ/(2m) and an angular frequency. [5] The initial conditions of the oscillator are
an initial position and an initial velocity. [7] The trajectory with those initial conditions has a
closed form appropriate to the damping regime — trigonometric, polynomial or hyperbolic, each
multiplied by an exponential decay. [8] That trajectory satisfies the equation of motion. [9] It is
the unique solution of the equation of motion with the given initial conditions. [14]

The Caldirola–Kanai Lagrangian is the undamped Lagrangian multiplied by the growing exponential
exp(γ t / m). [12] Its variational gradient reduces to the Euler–Lagrange equations, and vanishes
exactly on solutions of the equation of motion. [13] This Lagrangian goes back to Caldirola {4} and
Kanai {5}.

## Lean References

1. Physlib/ClassicalMechanics/DampedHarmonicOscillator/Basic.lean — `DampedHarmonicOscillator`
2. Physlib/ClassicalMechanics/DampedHarmonicOscillator/Basic.lean — `EquationOfMotion`
3. Physlib/ClassicalMechanics/DampedHarmonicOscillator/Basic.lean — `force`,
   `equationOfMotion_iff_newtons_2nd_law`
4. Physlib/ClassicalMechanics/DampedHarmonicOscillator/Basic.lean — `energy_dissipation_rate`,
   `energy_not_conserved`
5. Physlib/ClassicalMechanics/DampedHarmonicOscillator/Basic.lean — `discriminant`, `decayRate`,
   `IsUnderdamped`, `IsCriticallyDamped`, `IsOverdamped`, `angularFrequency`
6. Physlib/ClassicalMechanics/DampedHarmonicOscillator/Basic.lean — `toUndamped`,
   `toUndamped_equationOfMotion`
7. Physlib/ClassicalMechanics/DampedHarmonicOscillator/Solution.lean — `InitialConditions`
8. Physlib/ClassicalMechanics/DampedHarmonicOscillator/Solution.lean — `trajectory`
9. Physlib/ClassicalMechanics/DampedHarmonicOscillator/Solution.lean — `trajectory_equationOfMotion`
10. Physlib/ClassicalMechanics/HarmonicOscillator/Basic.lean — `kineticEnergy`
11. Physlib/ClassicalMechanics/HarmonicOscillator/Basic.lean — `potentialEnergy`
12. Physlib/ClassicalMechanics/DampedHarmonicOscillator/Basic.lean — `lagrangian`
13. Physlib/ClassicalMechanics/DampedHarmonicOscillator/Basic.lean — `gradLagrangian`,
   `gradLagrangian_eq_force`, `equationOfMotion_iff_gradLagrangian_zero`
14. Physlib/ClassicalMechanics/DampedHarmonicOscillator/Solution.lean — `equationOfMotion_unique`,
   `trajectories_unique`

## References

1. Landau & Lifshitz, *Mechanics*, page 76, Section 25.
2. Goldstein, *Classical Mechanics*, Chapter 2.
3. Time API map — Physlib/SpaceAndTime/Time/API-map.md
4. Caldirola, *Nuovo Cimento* 18 (1941) 393.
5. Kanai, *Progress of Theoretical Physics* 3 (1948) 440.
