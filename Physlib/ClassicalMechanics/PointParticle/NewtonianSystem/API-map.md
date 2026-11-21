# Newtonian systems of point particles

## Abstract (Alpha)

Two motions describe an isolated binary star. The center of mass moves uniformly, as it does
for any isolated Newtonian system. The displacement from one star to the other obeys the
inverse-square equation of motion wherever the stars are apart. Its gravitational parameter
depends on the sum of the two masses.

## Content (Alpha)

### Particles and forces in an inertial frame

A Newtonian system consists of a finite multiset of particles in an inertial frame, together
with their internal and external forces. The net force on each particle equals its mass times
its acceleration. Each internal force has an equal and opposite partner with the same
multiplicity, so the internal forces sum to zero. [1]

For a binary, label the two particle occurrences 0 and 1. Write their masses as m₀ and m₁,
their positions as x₀(t) and x₁(t), and their total mass as M = m₀ + m₁. In frame coordinates
their center of mass is R(t) = (m₀ x₀(t) + m₁ x₁(t)) / M. [2]

### Motion of the center of mass

For a system of positive total mass M and total momentum P(t), the velocity of its center of mass is
R′(t) = P(t) / M. [3] When the collection of external forces is empty, the center-of-mass
position and total momentum at any reference time t₀ determine the center of mass at every
time t by R(t) = R(t₀) + (t − t₀) P(t₀) / M. This applies to the binary for any internal
forces satisfying Newton's laws {1}. [4]

### Relative motion under mutual gravity

Let G be the gravitational constant and s the displacement from a target to a source of mass m.
When s is nonzero, the source contributes G m s / ‖s‖³ to the target's acceleration. Summing
over all other particles gives the target's gravitational acceleration. [5] Multiplying each
contribution by the target mass gives
the corresponding internal force. Exchanging source and target reverses that force, so the
collection over all ordered pairs of distinct particles satisfies Newton's third law. [6]

With these internal forces and an empty collection of external forces, the acceleration
equation for a particle is equivalent to Newton's second law. Given trajectories satisfying
the gravitational acceleration equation for every particle at every time, one can therefore
form a Newtonian system with those trajectories and forces. [7]

In the binary, take r(t) = x₁(t) − x₀(t), the displacement from star 0 to star 1. Suppose
the only forces are the stars' mutual gravitational forces. At each time t with x₁(t) ≠ x₀(t),
the relative acceleration is r″(t) = −G M r(t) / ‖r(t)‖³. Both masses enter the gravitational
parameter G M because both stars accelerate {1}. [8]

## Lean References

1. Physlib/ClassicalMechanics/PointParticle/NewtonianSystem/Basic.lean —
   `NewtonianSystem`, `internalForce_sum_zero`
2. PhyslibAlpha/ClassicalMechanics/OrbitalMechanics/BinaryStar.lean —
   `centerOfMass_eq_of_two_particles`
3. Physlib/ClassicalMechanics/PointParticle/NewtonianSystem/CenterOfMass.lean —
   `centerOfMass`, `hasDerivAt_centerOfMass`
4. Physlib/ClassicalMechanics/PointParticle/NewtonianSystem/CenterOfMass.lean —
   `centerOfMass_eq_of_noExternalForces`
5. PhyslibAlpha/ClassicalMechanics/OrbitalMechanics/NewtonianGravity.lean —
   `pairGravityAcceleration`, `gravityAcceleration`
6. PhyslibAlpha/ClassicalMechanics/OrbitalMechanics/NewtonianGravity.lean —
   `pairGravity`, `pairGravity_reverse`, `gravityForces`, `gravityForces_reverse`
7. PhyslibAlpha/ClassicalMechanics/OrbitalMechanics/NewtonianGravity.lean —
   `acceleration_eq_gravity_iff`, `ofGravity`
8. PhyslibAlpha/ClassicalMechanics/OrbitalMechanics/BinaryStar.lean —
   `hasDerivAt_deriv_relativePosition_of_gravity`

## References

1. H. Goldstein, C. P. Poole and J. L. Safko, *Classical Mechanics*, 3rd ed.,
   Addison-Wesley, 2002, §§1.2, 3.1 and 3.7.
