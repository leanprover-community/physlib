# Configuration Space

## Abstract (Alpha)

The configuration space of a mechanical system is the manifold of its configurations, and its
charts are generalised coordinates. It is the base on which the Lagrangian formulation of
mechanics is built, Lagrangians being functions on its tangent bundle of positions and velocities.
Particular systems, such as the harmonic oscillator and the pendulum, have configuration spaces of
their own, which are to be configuration spaces in this general, system-agnostic sense.

## Content (Alpha)

A configuration space is a smooth manifold without boundary, abstracting over the choice of
mechanical system {1}{2}, and is shared across the Lagrangian formulation {3}. [1] In global
generalised coordinates {4}, a curve is smooth if and only if its coordinate curve is, and its
velocity is the time derivative of the coordinate curve. [2] The configuration spaces of the
geometric harmonic oscillator {5} and the simple pendulum {6} are configuration spaces in this
sense. [TODO]

## Lean References

1. Physlib/ClassicalMechanics/ConfigurationSpace/Basic.lean — `ConfigurationSpace`
2. Physlib/SpaceAndTime/Time/ManifoldCurves.lean — `Time.contMDiff_iff_contDiff_vadd`,
   `Time.tangentMap_eq_deriv_vadd`

## References

1. Ivo Terek, *Introductory Variational Calculus on Manifolds*.
2. V. I. Arnold, *Mathematical Methods of Classical Mechanics*.
3. Lagrangian mechanics API map — Physlib/ClassicalMechanics/Lagrangian/API-map.md
4. L. D. Landau and E. M. Lifshitz, *Mechanics*.
5. Configuration space of the harmonic oscillator API map —
   Physlib/ClassicalMechanics/HarmonicOscillator/Geometric/API-map.md
6. Configuration space for pendulum API map — Physlib/ClassicalMechanics/Pendulum/API-map.md
