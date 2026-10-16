# Configuration Space

The configuration space of a mechanical system is the manifold of the configurations it can
instantaneously be in, coordinatised by generalized coordinates. It is the base on which the
Lagrangian formulation of mechanics is built: a Lagrangian is a function on the tangent bundle
of positions and velocities, and the Euler–Lagrange equations pick out the physical motions as
curves in the configuration space.

The library does not yet have a general, system-agnostic configuration space, nor a Lagrangian
built over one; that is what the requirements below ask for. Configuration spaces for
particular systems do exist, and are tracked in their own API maps — the geometric harmonic
oscillator and the pendulum.

## Built on

- Space — `Physlib/SpaceAndTime/Space`

## Requirements

A configuration manifold abstracting over the choice of mechanical system will be available
across the Lagrangian API. [planned]

Generalized coordinates and the velocity phase space will be treated in general, over that
shared configuration space, so that a Lagrangian can be defined on them for the
Euler–Lagrange API. [planned]

## Further reading

- Ivo Terek, Introductory Variational Calculus on Manifolds, Section 1
- Landau and Lifshitz, Mechanics, 3rd ed., Chapter 1 (generalised coordinates, the principle of least action, the Lagrangian)

## Lean declarations

*None yet.*
