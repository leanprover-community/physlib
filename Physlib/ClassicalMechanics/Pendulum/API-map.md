# Configuration space for pendulum

A pendulum is a mass swinging under gravity on a string or a rod. Its configuration is fixed by
the angles it makes and, when the support can move, by the position of the support, so its
configuration space is naturally a product of circles and lines. This API covers the pendulum
problems of Landau and Lifshitz, Mechanics, 3rd ed., Chapter 1, Section 5.

The sliding pendulum has a configuration space in the generalized coordinates of the support
position and the string angle. The simple pendulum's configuration space — an angle taken
modulo a full turn — carries the manifold structure and the map into space, and has an API map
of its own under the simple pendulum directory, where its Lagrangian and equation of motion on
the Euclidean lift are also recorded. What is recorded here is the trajectory built on the
configuration space, and the identification of the lifted Lagrangian with that of the bob in
physical space. The coplanar double pendulum's configuration space is declared but not yet
defined, and the remaining pivot-motion problems carry documentation only.

## Built on

- Classical mechanics Lagrangian — `Physlib/ClassicalMechanics/Lagrangian`
- Space — `Physlib/SpaceAndTime/Space`

## Requirements

The key data structure is defined: the configuration space of the pendulum, taken here in the
generalized coordinates of the support position and the string angle of the sliding
pendulum. [1]

The configuration space of the simple pendulum is a manifold. [2]

The configuration space of the simple pendulum maps into space, giving the position of the bob
there. [3]

A trajectory of the pendulum is a curve in the configuration space. [4]

The Lagrangian is defined on that configuration space, and agrees with the Lagrangian of the
bob moving in physical space. [5][6]

## Further reading

- Landau & Lifshitz, Mechanics, 3rd Edition, Chapter 1 (The Equations of motion), Section 5 (The Lagrangian for a system of particles).

## Lean declarations

1. Physlib/ClassicalMechanics/Pendulum/SlidingPendulum.lean — `ConfigurationSpace`
2. Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Geometric/Basic.lean — `SimplePendulum.ConfigurationSpace.instIsManifold`
3. Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Geometric/Basic.lean — `SimplePendulum.ConfigurationSpace.toSpace`
4. Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Geometric/Trajectory.lean — `SimplePendulum.Trajectory`,
   `SimplePendulum.Trajectory.ofLift`
5. Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Basic.lean — `SimplePendulum.lagrangian`
6. Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Geometric/PhysicalSpace.lean — `SimplePendulum.lagrangian_eq_space`
