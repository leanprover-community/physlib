# Fluid

## Abstract (Alpha)

A fluid is described by the spatial distribution of its velocity, density and pressure, as fields
over space and time, and the continuity equation, the equations of motion and the thermodynamic
balance laws are statements about those fields. The independent data is spread over a tower of
structures: a fluid flow carries density and velocity, a Cauchy flow adds the stress tensor and the
specific body force, and a thermodynamic Cauchy flow adds entropy and enthalpy, while pressure
enters through the stress laws.

## Content (Alpha)

A fluid {1} is the spatial distribution of its velocity, density and pressure, as fields over space
{2} and time {3}; a fluid flow carries the density and the velocity, while the pressure enters
separately through the stress laws. [1][TODO] The flow out of a volume is the flux of fluid
through the boundary of a spatial region. [TODO]

The mass flux density is the momentum density ρ u, the product of the density and the velocity,
whose divergence enters the continuity equation; the convective momentum flux is ρ u ⊗ u. [2] The
equation of continuity, ∂ₜρ + ∇ · (ρ u) = 0, expresses the local conservation of mass, in a
pointwise classical form, through its residual, and in a smooth form that implies the classical one.
[3]

An ideal, inviscid fluid has Cauchy stress −p I, whose divergence is −∇p. [5] Euler's equation is
the equation of motion of an ideal fluid: continuity, Cauchy momentum balance and inviscid stress,
with the conservative and convective forms equivalent for differentiable fields. [4] Bernoulli's
equation states that the Bernoulli function ½ |u|² + h + Φ, with h the specific enthalpy and Φ the
potential of the body force, is spatially constant, locally that its spatial gradient vanishes. [6]

The entropy flux density is ρ s u, with s the specific entropy. [TODO] The energy flux of a fluid
is ρ u (½ |u|² + h). [TODO]

## Lean References

1. Physlib/FluidDynamics/FluidFlow/Basic.lean — `FluidFlow`, `rho`, `velocity`
2. Physlib/FluidDynamics/FluidFlow/Momentum.lean — `momentumDensity`, `momentumFlux`
3. Physlib/FluidDynamics/FluidFlow/Continuity.lean — `ClassicalContinuityEquation`,
   `continuityResidual`, `SmoothContinuityEquation`,
   `classicalContinuityEquation_of_smoothContinuityEquation`
4. Physlib/FluidDynamics/Euler/Basic.lean — `Euler`, `ConvectiveEuler`,
   `euler_iff_convectiveEuler`
5. Physlib/FluidDynamics/CauchyFlow/Inviscid.lean — `IsInviscid`,
   `matrixDiv_stress_eq_neg_grad_pressure_of_is_inviscid`
6. Physlib/FluidDynamics/ThermodynamicCauchyFlow/Bernoulli.lean — `bernoulliFunction`,
   `LocalBernoulliLaw`, `BernoulliLaw`

## References

1. Landau, L. D. and Lifshitz, E. M., *Fluid Mechanics* (Course of Theoretical Physics, vol. 6),
   2nd ed., Chapter 1 (continuity, Euler equation, Bernoulli equation, energy and momentum flux).
2. Space API map — Physlib/SpaceAndTime/Space/API-map.md
3. Time API map — Physlib/SpaceAndTime/Time/API-map.md
