# Fluid

A fluid is described by the spatial distribution of its velocity, density and pressure. That
description is the core data structure of fluid dynamics, and the continuity equation, the
equations of motion and the thermodynamic balance laws are built on it.

The independent data is spread over a tower of structures: a fluid flow carries density and
velocity, a Cauchy flow adds the stress tensor and the specific body force, and a thermodynamic
Cauchy flow adds entropy and enthalpy. Pressure is a field of none of them — it enters
separately through the stress laws — so the requirement below asking for one structure carrying
velocity, density and pressure is still only partly met.

The mass flux density and the equation of continuity are fully formalized, the latter in
conservative, residual and smooth forms with the implications between them, as are the Euler
equation, the ideal fluid and the Bernoulli equation. The entropy flux density, the energy
flux, and the flow out of a volume are open. Entropy itself is a field of the thermodynamic
Cauchy flow, but the flux density built from it is not yet defined.

## Built on

- Space — `Physlib/SpaceAndTime/Space`
- Time — `Physlib/SpaceAndTime/Time`

## Requirements

The key data structure for a fluid, the spatial distribution of its velocity, density and
pressure, will be defined. What exists carries the density and the velocity; pressure is not a
field of the structure, and enters separately through the stress laws. [1][planned]

The flow out of a volume, the flux of fluid through the boundary of a spatial region, will be
defined. [planned]

The mass flux density, the vector whose divergence enters the continuity equation, is defined —
as the momentum density, which is the density times the velocity. [2]

The equation of continuity expresses the local conservation of mass. [3]

Euler's equation is the equation of motion of an ideal, inviscid fluid. [4]

An ideal fluid is defined. [5]

The entropy flux density will be defined. [planned]

Bernoulli's equation is proved. [6]

The energy flux of a fluid will be defined. [planned]

## Further reading

- Landau, L. D. and Lifshitz, E. M., Fluid Mechanics (Course of Theoretical Physics, vol. 6), 2nd ed., Chapter 1 (continuity, Euler equation, Bernoulli equation, energy and momentum flux)

## Lean declarations

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
