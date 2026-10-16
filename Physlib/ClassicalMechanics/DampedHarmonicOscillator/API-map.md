# Damped harmonic oscillator

A damped harmonic oscillator is a mass under a restoring force proportional to its displacement
and a damping force proportional to its velocity, so that m ẍ + γ ẋ + k x = 0. Its data is that
of the undamped oscillator — a positive mass and spring constant, with the natural frequency
and energy that come with them — together with a nonnegative damping coefficient. Position and
velocity live in the one-dimensional Euclidean space, and a trajectory is a map from time into
it.

The basic module gives the equation of motion, the force and its equivalence with Newton's
second law, and the rate at which mechanical energy is dissipated along a solution. The sign of
the discriminant γ² − 4 m k selects one of three regimes — underdamped, critically damped,
overdamped — each with its own decay rate and angular frequency; with no damping at all the
system is the undamped oscillator again. The Caldirola–Kanai Lagrangian, the undamped
Lagrangian scaled by a growing exponential, has a variational gradient that vanishes exactly on
solutions of the equation of motion.

The solution module fixes the initial conditions and gives the closed-form trajectory for each
regime — trigonometric, polynomial or hyperbolic, each multiplied by an exponential decay — and
proves that it solves the equation of motion.

## Built on

- Harmonic oscillator — `Physlib/ClassicalMechanics/HarmonicOscillator`
- Time — `Physlib/SpaceAndTime/Time`

## Requirements

The key data structure is defined: the mass, the spring constant and the damping coefficient of
a damped harmonic oscillator. [1]

The equation of motion m ẍ + γ ẋ + k x = 0 is defined. [2]

The force is defined, and the equation of motion is equivalent to Newton's second law. [3]

Along a solution the mechanical energy dissipates at the rate −γ ‖ẋ‖², and strictly decreases
whenever the velocity is nonzero and the damping is positive. [4]

The underdamped, critically damped and overdamped regimes are classified by the discriminant
γ² − 4 m k, and the decay rate and the angular frequency of each regime are defined. [5]

With no damping the system reduces to the undamped harmonic oscillator, the two equations of
motion agreeing. [6]

The initial conditions of a damped harmonic oscillator are defined. [7]

The trajectory is defined, in the closed form appropriate to the damping regime. [8]

That trajectory satisfies the equation of motion. [9]

The kinetic energy is defined. [10]

The potential energy is defined. [11]

The Lagrangian is defined. [12]

The variational gradient of the Lagrangian simplifies to the Euler–Lagrange equations. [13]

The trajectory is the unique solution of the equation of motion with the given initial
conditions. [14]

## Further reading

- Landau & Lifshitz, Mechanics, page 76, section 25.
- Goldstein, Classical Mechanics, Chapter 2.
- Caldirola, Nuovo Cimento 18 (1941) 393.
- Kanai, Progress of Theoretical Physics 3 (1948) 440.

## Lean declarations

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
