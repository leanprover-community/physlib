# Configuration space of the harmonic oscillator

## Abstract (Alpha)

The one-dimensional harmonic oscillator is a mass on a spring: one particle on a line, pulled back
by a force proportional to its displacement. Its configuration is a single real coordinate, so its
configuration space is a one-dimensional smooth manifold, a trajectory is a curve from time into
that manifold, and the kinetic energy comes from the mass metric, the mass-scaled Euclidean inner
product on tangent vectors. Treated geometrically rather than in coordinates, the configuration
space carries a global chart onto the Euclidean model and a map into physical space; smoothness of a
trajectory reduces to smoothness of its coordinate curve, the velocity is the derivative of that
curve, and the geometric kinetic energy is the familiar mass-scaled expression.

## Content (Alpha)

### The configuration space

The configuration space of the classical harmonic oscillator, in the geometric setting of Terek {1},
carries a single global coordinate valued in one-dimensional Euclidean space; two configurations are
equal when their coordinates are, and a configuration can be applied like a function to read off its
coordinate. [1] The configuration space carries the topology induced by its global coordinate, and
is equivalent and homeomorphic to the Euclidean model, which transports Hausdorffness and second
countability across. [2]

The configuration space is a smooth manifold, charted by a single global chart, and that chart is an
analytic diffeomorphism onto the Euclidean model. [3] Each tangent space is a finite-dimensional
normed real vector space, with a chart-induced continuous linear equivalence to the Euclidean
coordinate model. [4] The configuration space maps to the actual position of the particle in
physical space {2}, by reading off the underlying coordinate. [5]

### Trajectories and kinetic energy

A trajectory of the oscillator is a curve from time {3} into the configuration space, with its
coordinate curve and its curve of positions in physical space. [6] A trajectory is smooth exactly
when its coordinate curve is, and likewise differentiable; the geometric velocity is a tangent
vector, and it is the time derivative of the coordinate curve. [7]

The configuration space carries the oscillator's mass Riemannian metric, the mass-scaled Euclidean
inner product in global tangent coordinates, which is positive definite and computable in
coordinates. [8] The geometric kinetic energy of a tangent vector v is ½ g(v, v) for that metric g,
and recovers the standard mass-scaled coordinate expression ½ m ‖v‖². [9]

## Lean References

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

## References

1. Ivo Terek, *Introductory Variational Calculus on Manifolds*, Section 1 (pages 1-2), Basic
   definitions and examples.
2. Space API map — Physlib/SpaceAndTime/Space/API-map.md
3. Time API map — Physlib/SpaceAndTime/Time/API-map.md
