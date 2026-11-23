# Newtonian systems of point particles

## Abstract (Alpha)

A Newtonian system describes finitely many point particles in an inertial frame. Each particle
accelerates under the forces acting on it. Internal forces come in equal and opposite pairs,
so they cancel when summed over the system. The total momentum determines the velocity of
the center of mass, which is constant in the absence of external forces.

## Content (Alpha)

### Particles and forces in an inertial frame

A particle has a constant positive mass and a position that depends on time. In an inertial
frame the position is twice differentiable. Its first derivative is the velocity and its
second derivative is the acceleration. [1]

A Newtonian system collects the particles and the forces acting on them in one inertial
frame. Each force has a time-dependent vector value and a target particle. An internal force
also has a source particle distinct from its target. The net force on a particle is the sum
of all internal and external forces on that target, counting each occurrence. [2][3]

Newton's second law identifies this net force with the particle's mass times its acceleration.
Newton's third law pairs each internal force with its reverse, which swaps the source and
target and negates the force. The two occur with the same multiplicity, so the sum of all
internal forces vanishes at each time {1}. [2][4]

### Total quantities and the center of mass

Summing the particle masses gives the total mass M. Summing their momenta gives the total
momentum P(t), and summing their individual kinetic energies gives the total kinetic energy.
The net external force sums just the forces applied from outside the system. [5]

For positive M, the center of mass R(t) is the mass-weighted average of the particle positions
and its velocity is R′(t) = P(t) / M. [6] If the collection of external forces is empty, the
center of mass moves at constant velocity. Its position at any time t is
R(t) = R(t₀) + (t − t₀) P(t₀) / M for any reference time t₀ {1}. [7]

### A system with pairwise gravity

Let G be the gravitational constant and s the displacement from a target to a source of mass m.
At nonzero separation the source contributes G m s / ‖s‖³ to the target's acceleration. Summing
over all other particles gives its gravitational acceleration. Multiplying by the target mass
gives the net gravitational force. [8] Exchanging source and target reverses the force, so
the collection of these forces satisfies Newton's third law. [9] Given trajectories satisfying the
gravitational acceleration equation for every particle at every time, they form a Newtonian
system with these internal forces and no external forces. [10]

### An isolated binary star

Label the stars 0 and 1, with masses m₀ and m₁ and positions x₀(t) and x₁(t). Their center
of mass is R(t) = (m₀ x₀(t) + m₁ x₁(t)) / M, where M = m₀ + m₁. [11] Its uniform motion
follows from the general isolated-system result. [7] If the stars interact by mutual gravity
alone, their relative displacement r(t) = x₁(t) − x₀(t) satisfies the inverse-square equation
r″(t) = −G M r(t) / ‖r(t)‖³ at each time when their positions are distinct {1}. [12]

## Lean References

1. Physlib/ClassicalMechanics/PointParticle/Basic.lean — `Particle`, `velocity`, `acceleration`
2. Physlib/ClassicalMechanics/PointParticle/NewtonianSystem/Basic.lean —
   `NewtonianSystem`, `reverse_count_eq`, `internalForce_sum_zero`
3. Physlib/ClassicalMechanics/Force.lean — `Force`, `InternalForce`, `netForce`
4. Physlib/ClassicalMechanics/Force.lean — `InternalForce.reverse`
5. Physlib/ClassicalMechanics/PointParticle/NewtonianSystem/Basic.lean —
   `mass`, `momentum`, `kineticEnergy`, `netExternalForce`
6. Physlib/ClassicalMechanics/PointParticle/NewtonianSystem/CenterOfMass.lean —
   `centerOfMass`, `hasDerivAt_centerOfMass`
7. Physlib/ClassicalMechanics/PointParticle/NewtonianSystem/CenterOfMass.lean —
   `centerOfMass_eq_of_noExternalForces`
8. PhyslibAlpha/ClassicalMechanics/OrbitalMechanics/NewtonianGravity.lean —
   `pairGravityAcceleration`, `gravityAcceleration`, `netForce_gravity`
9. PhyslibAlpha/ClassicalMechanics/OrbitalMechanics/NewtonianGravity.lean —
   `pairGravity`, `pairGravity_reverse`, `gravityForces_reverse`
10. PhyslibAlpha/ClassicalMechanics/OrbitalMechanics/NewtonianGravity.lean — `ofGravity`
11. PhyslibAlpha/ClassicalMechanics/OrbitalMechanics/BinaryStar.lean —
    `centerOfMass_eq_of_two_particles`
12. PhyslibAlpha/ClassicalMechanics/OrbitalMechanics/BinaryStar.lean —
    `hasDerivAt_deriv_relativePosition_of_gravity`

## References

1. H. Goldstein, C. P. Poole and J. L. Safko, *Classical Mechanics*, 3rd ed.,
   Addison-Wesley, 2002, §§1.2, 3.1 and 3.7.
