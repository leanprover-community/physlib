# Configuration space of the harmonic oscillator

The one-dimensional harmonic oscillator is a mass on a spring: one particle on a line, pulled
back by a force proportional to its displacement. Its configuration is a single real
coordinate, so its configuration space is a one-dimensional smooth manifold, a trajectory is a
curve from time into that manifold, and the kinetic energy comes from the mass metric, the
mass-scaled Euclidean inner product on tangent vectors.

This API builds that picture geometrically rather than in coordinates. The configuration space
wraps a single global coordinate and carries the topology it induces, a coordinate
homeomorphism and analytic diffeomorphism onto the Euclidean model, charted-space and manifold
structures, the tangent-coordinate infrastructure, and a map to physical space. Smoothness of a
trajectory reduces to smoothness of its coordinate curve, the velocity is a tangent vector
recovered as the derivative of that curve, and the geometric kinetic energy comes out as the
familiar mass-scaled expression.

## Built on

- Harmonic oscillator — `Physlib/ClassicalMechanics/HarmonicOscillator`
- Space — `Physlib/SpaceAndTime/Space`
- Time — `Physlib/SpaceAndTime/Time`

## Requirements

The key data structure is defined: the configuration space of the classical harmonic
oscillator, carrying a single global coordinate valued in the one-dimensional Euclidean space,
with extensionality in that coordinate and function-like access to it. [1]

The configuration space carries the topology induced by its global coordinate, together with
the equivalence and homeomorphism to the Euclidean model that transport Hausdorffness and
second countability across. [2]

The configuration space is a smooth manifold, charted by a single global chart, and that chart
is an analytic diffeomorphism onto the Euclidean model. [3]

Each tangent space is a finite-dimensional normed real vector space, with the chart-induced
continuous linear equivalence to the Euclidean coordinate model. [4]

The configuration space maps to the actual position of the particle in physical space, by
reading off the underlying coordinate. [5]

A trajectory of the oscillator is a time-parametrised curve into the configuration space, with
its coordinate curve and its curve of positions in physical space. [6]

A trajectory is smooth exactly when its coordinate curve is, and likewise differentiable; the
geometric velocity is a tangent vector, and it is the time derivative of the coordinate
curve. [7]

The configuration space carries the oscillator's mass Riemannian metric, the mass-scaled
Euclidean inner product in global tangent coordinates, which is positive definite and
computable in coordinates. [8]

The geometric kinetic energy is defined from that metric, and recovers the standard mass-scaled
coordinate expression. [9]

## Further reading

- Ivo Terek, Introductory Variational Calculus on Manifolds, Section 1 (pages 1-2), Basic definitions and examples.

## Lean declarations

1. Physlib/ClassicalMechanics/HarmonicOscillator/Geometric/Basic.lean — `ConfigurationSpace`,
   `val`, `ext`, `coe_apply`
2. Physlib/ClassicalMechanics/HarmonicOscillator/Geometric/Basic.lean — `valEquiv`,
   `valHomeomorphism`
3. Physlib/ClassicalMechanics/HarmonicOscillator/Geometric/Basic.lean — `valDiffeomorph`,
   `ChartedSpace instance`, `IsManifold instance`
4. Physlib/ClassicalMechanics/HarmonicOscillator/Geometric/Basic.lean — `tangentCoord`,
   `instNormedAddCommGroupTangent`, `instNormedSpaceTangent`, `instFiniteDimensionalTangent`
5. Physlib/ClassicalMechanics/HarmonicOscillator/Geometric/Basic.lean — `toSpace`,
   `toSpace_apply`
6. Physlib/ClassicalMechanics/HarmonicOscillator/Geometric/Trajectory.lean — `Trajectory`,
   `coord`, `toSpace`, `coord_apply`
7. Physlib/ClassicalMechanics/HarmonicOscillator/Geometric/Trajectory.lean — `contMDiff_iff_contDiff_coord`,
   `mdifferentiableAt_iff_differentiableAt_coord`, `velocity`, `velocity_eq_deriv_coord`
8. Physlib/ClassicalMechanics/HarmonicOscillator/Geometric/KineticEnergy.lean — `massMetricVal`,
   `massMetricVal_apply`, `massMetricVal_pos`, `massRiemannianMetric`,
   `massRiemannianMetric_pos`, `massRiemannianMetric_inner_apply`
9. Physlib/ClassicalMechanics/HarmonicOscillator/Geometric/KineticEnergy.lean — `geometricKineticEnergy`,
   `geometricKineticEnergy_eq`, `geometricKineticEnergy_massMetric_eq`
