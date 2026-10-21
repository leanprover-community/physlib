# Configuration space for pendulum

## Abstract (Alpha)

A pendulum is a mass swinging under gravity on a string or a rod. Its configuration is fixed by the
angles it makes and, when the support can move, by the position of the support, so its configuration
space is naturally a product of circles and lines in the sense of the general configuration space of
a mechanical system. This map covers two pendulum problems: the sliding pendulum, whose
configuration is the support position together with the string angle, and the simple pendulum,
whose configuration is a single angle taken modulo a full turn and whose dynamics are recorded in
full separately.

## Content (Alpha)

The configuration space {1} of the sliding pendulum {2} is given by two generalized coordinates: the
horizontal position of the support and the angle the string makes with the vertical. [1]

The configuration space of the simple pendulum {3} is a manifold. [2] It maps into physical space
{4}, giving the position of the bob there. [3] A trajectory of the simple pendulum is a curve in its
configuration space, and every lift of the angle to the real line describes one. [4] The Lagrangian
of the simple pendulum is a function of the lifted angle and angular velocity, and along a
differentiable lift it agrees with the constrained Lagrangian of the bob moving in physical space.
[5][6]

## Lean References

1. Physlib/ClassicalMechanics/Pendulum/SlidingPendulum.lean — `ConfigurationSpace`
2. Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Geometric/Basic.lean — `SimplePendulum.ConfigurationSpace.instIsManifold`
3. Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Geometric/Basic.lean — `SimplePendulum.ConfigurationSpace.toSpace`
4. Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Geometric/Trajectory.lean — `SimplePendulum.Trajectory`,
   `SimplePendulum.Trajectory.ofLift`
5. Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Basic.lean — `SimplePendulum.lagrangian`
6. Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Geometric/PhysicalSpace.lean — `SimplePendulum.lagrangian_eq_space`

## References

1. Configuration Space API map — Physlib/ClassicalMechanics/Lagrangian/API-map.md
2. Landau & Lifshitz, *Mechanics*, 3rd Edition, Chapter 1 (The Equations of motion), Section 5 (The
   Lagrangian for a system of particles).
3. Simple pendulum API map — Physlib/ClassicalMechanics/Pendulum/SimplePendulum/API-map.md
4. Space API map — Physlib/SpaceAndTime/Space/API-map.md
