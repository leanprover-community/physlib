# FLRW cosmology

## Abstract (Alpha)

A Friedmann–Lemaître–Robertson–Walker spacetime models a universe that is homogeneous and
isotropic. Its geometry is fixed by a scale factor, a function of cosmic time on the time
manifold, together with the curvature of the spatial slices, which is spherical, flat or saddle.
The expansion rate is the Hubble parameter, its change is measured by the deceleration parameter,
and the dynamics is governed by the Friedmann equations, which tie the scale factor to the
energy density and pressure of the cosmic fluid, to the spatial curvature and to the cosmological
constant. Around these sit the continuity equation, barotropic equations of state with their
density scaling laws, the cosmological constant as a fluid, exact solutions, the density
parameters and their closure relation, the reduced Hubble function of the standard cosmological
model, the age of the universe, the energy conditions of the cosmic fluid with the acceleration
criterion, eternal expansion together with the Big-Bang bound on the interval of cosmic time, and
the cosmological distances, the redshift and the horizons.

## Content (Alpha)

### The FLRW model

On the largest scales the observed universe looks the same at every point and in every direction: it
is homogeneous and isotropic. This is the cosmological principle. A
Friedmann–Lemaître–Robertson–Walker (FLRW) universe is a model of spacetime that assumes it exactly,
so that at each instant of cosmic time space is homogeneous and isotropic. Its metric is
ds² = −c² dt² + a(t)² (dr² + S(r)² dΩ²), so space at time t is a fixed three-dimensional geometry
stretched by the scale factor a(t), and S(r) sets the size of the sphere at radial distance r. (For
the Robertson–Walker metric see Weinberg {2} and Baumann {3}.) The metric is a Lorentzian metric on
spacetime. [TODO]

Homogeneity and isotropy leave three possible spatial geometries: spherical, flat and saddle, with
S(r) equal to k sin(r/k), r and k sinh(r/k) respectively, where k is the curvature radius. [1] The
flat geometry is the large-radius limit of the curved ones: as the curvature radius tends to
infinity, the S(r) of the spherical and saddle geometries tends to that of the flat one. [2]

An FLRW model is therefore a scale factor, positive and twice differentiable on an open interval of
cosmic time {1}, together with a spatial geometry. [3] The spatial geometry supplies the curvature
parameter of the Friedmann equations, positive for the spherical geometry, zero for the flat one and
negative for the saddle one. [3]

The Hubble parameter H = ∂ₜ a / a is a function of the scale factor and cosmic time, and is nonzero
wherever the scale factor and its derivative both are. [4] The deceleration parameter is
q = −(∂ₜ ∂ₜ a) a / (∂ₜ a)². The derivative ∂ₜ H obeys the quotient-rule formula, q equals
−(1 + (∂ₜ H) / H²) and ∂ₜ H equals −H² (1 + q), and ∂ₜ H < 0 holds exactly when q > −1, both
pointwise and in existential form. [5]

An FLRW model that decelerates on its interval and is expanding at t₀ lies below its tangent line at
t₀, so it cannot be defined earlier than t₀ − 1 / H(t₀) and its interval is bounded below. [6]

### The cosmic fluid

A cosmic fluid is an energy density and a pressure, each a function of cosmic time; the empty fluid
has zero density and pressure. [7] A barotropic fluid has pressure P = w ρ c² for a constant
equation-of-state parameter w. [8] The cosmological constant is itself a fluid, with density
ρ_Λ = Λ c² / (8πG) and pressure p_Λ = −ρ_Λ c², and folding it into the cosmic fluid gives the fluid
with density ρ + ρ_Λ and pressure p + p_Λ. [9] Its pressure is the w = −1 barotropic pressure of
its density. [10]

The null, weak, strong and dominant energy conditions of the cosmic fluid are defined, with the
implications between them: the dominant condition implies the weak one, and the weak and strong
conditions each imply the null one. [11]

### The Friedmann equations

The first-order Friedmann equation (∂ₜ a / a)² = (8πG/3) ρ − k c² / a² + Λ c² / 3 relates a scale
factor and an energy density, with the curvature parameter explicit; the second-order Friedmann
equation ∂ₜ ∂ₜ a / a = −(4πG/3) (ρ + 3 p / c²) + Λ c² / 3 involves a pressure as well and has no
curvature term. The cosmological constant, Newton's constant and the speed of light appear
explicitly in both. [12] A model filled with a fluid solves the Friedmann equations when both hold
on the interval of the model, the curvature parameter being read off the spatial geometry. [13]
The Friedmann equations are derived from the Einstein field equations
G_μν + Λ g_μν = (8πG / c⁴) T_μν for the FLRW metric, with T_μν the stress–energy tensor of a perfect
fluid of density ρ and pressure p: the time–time component gives the first-order equation, and the
spatial components combined with it give the second-order equation. [TODO]

The continuity equation ∂ₜ ρ + 3 H (ρ + P/c²) = 0 of the cosmic fluid holds at an instant whenever
the first-order Friedmann equation holds throughout a neighbourhood of that instant together with
the second-order equation; conversely, the second-order equation follows from the first-order
equation and the continuity equation wherever the scale factor is changing. [14] Every solution of
the Friedmann equations therefore satisfies the continuity equation. [15] (See Dodelson and Schmidt
{4} for the smooth, expanding universe.) Under a barotropic equation of state, the continuity
equation implies the density scaling law ρ t = ρ t₀ (a t / a t₀)^(−3(1+w)), and conversely; dust,
radiation and vacuum energy are special cases. [16]

Each Friedmann equation with a cosmological constant is equivalent to the same equation without one
for the fluid with the cosmological constant folded in. [17] Hence a solution of the Friedmann
equations with Λ is a solution without Λ for the combined fluid. [18]

On the interval of a solution the universe accelerates, 0 < ∂ₜ ∂ₜ a, exactly when
ρ + 3 p / c² < 0, without and with Λ. [19] For a spatial geometry of non-positive curvature,
0 ≤ Λ and positive density, the expansion never stops; with 0 ≤ ρ, 0 ≤ p and Λ = 0 the solution
decelerates, so it has a Big Bang in the finite past. [20]

### Solutions of the Friedmann equations

The de Sitter model, filled with the empty fluid, solves the Friedmann equations at all times. [21]
Unlike a decelerating solution it is defined at all times, so it has no Big Bang. [22] The Milne
model, filled with the empty fluid, solves the Friedmann equations after its Big Bang. [23] The flat
power-law models, filled with their fluid, solve the Friedmann equations on t > 0 for the matching
equation of state. [24] The radiation-dominated and Einstein–de Sitter models are the cases n = 1/2
and n = 2/3, and after their Big Bang they too solve the Friedmann equations. [25][26]

### Density parameters, the standard model and the age

The critical density of an FLRW model is ρ_cr = 3 H² / (8πG), and the density parameters are
Ω = ρ / ρ_cr for a cosmic fluid in the model, Ω_K = −k c² / (H² a²), k being the curvature parameter
of its spatial geometry, and Ω_Λ = Λ c² / (3 H²), the density parameter of the cosmological constant
as a fluid; folding the cosmological constant into the fluid adds Ω_Λ to its density parameter. [27]
For a solution of the Friedmann equations, the first-order equation is the closure relation
Ω + Ω_Λ + Ω_K = 1 at the times of its interval at which H ≠ 0. [28] In terms of the density
parameters of barotropic components the deceleration parameter is q = ½ Σ_i Ω_i (1 + 3 w_i), with
its ΛCDM special case. [29]

The standard cosmological model has reduced Hubble function
E(x)² = Ω_Λ + Ω_m x⁻³ + Ω_r x⁻⁴ + Ω_K x⁻², with H = H₀ E(a / a₀) for a solution of the Friedmann
equations whose cosmic fluid is made of matter and radiation obeying their scaling laws between two
times of its interval, and with radiation–matter and matter–Λ equality scale factors. [30] The age
of the universe is t₀ = H₀⁻¹ ∫₀¹ dx / (x E(x)). [31]

### Distances, redshift and horizons

The distances are defined for an FLRW model, at the times of its interval. The comoving distance
of a source emitting at t and observed at t₀ is χ = c ∫ dτ / a from t to t₀, so that
∂ₜ χ = −c / a. The redshift is 1 + z = a(t₀) / a(t), with ∂ₜ z = −(1 + z) H, and ∂ₜ a = a H;
combining the two, ∂ₜ χ = (c / (a(t₀) H)) ∂ₜ z, the change of variables dχ = c dz / H for
a(t₀) = 1. The proper distance D = a χ obeys the Hubble–Lemaître law ∂ₜ D = H D, and the recession
velocity ∂ₜ D equals c exactly at the Hubble radius R_H = c / H. [32] The transverse comoving
distance r(χ) is the profile of the spatial geometry of the model. With K its curvature parameter
and curvature radius 1 / √|K|, it is (1 / √K) sin(√K χ), χ or (1 / √(−K)) sinh(√(−K) χ) for
positive, zero or negative K. The particle and event horizons at t integrate c / a over the times
of the interval before and after t, and the particle horizon of the Einstein–de Sitter model is
3 c t₀^(2/3) t^(1/3). [33]

The energy of a photon scales as E ∝ 1 / a along its null geodesic, and the comoving distance is
the integral χ = c ∫ dz / H(z) in the redshift for a(t₀) = 1. [TODO]

## Lean References

1. Physlib/Cosmology/FLRW/Basic.lean — `SpatialGeometry`, `SpatialGeometry.S`
2. Physlib/Cosmology/FLRW/Basic.lean — `limit_S_sphere`, `limit_S_saddle`, `tendsto_sin_rx_over_x`,
   `tendsto_sinh_rx_over_x`, `mul_sin_as_div`, `mul_sinh_as_div`
3. Physlib/Cosmology/FLRW/Basic.lean — `FLRW`, `FLRW.a_ne_zero`, `FLRW.differentiableAt_a`,
   `FLRW.differentiableAt_deriv_a`, `SpatialGeometry.curvature`, `SpatialGeometry.curvature_flat`,
   `SpatialGeometry.curvature_spherical_pos`, `SpatialGeometry.curvature_saddle_neg`
4. Physlib/Cosmology/FLRW/Basic.lean — `hubbleConstant`, `hubbleConstant_ne_zero`
5. Physlib/Cosmology/FLRW/Basic.lean — `decelerationParameter`, `deriv_hubbleConstant`,
   `decelerationParameter_eq_one_plus_hubbleConstant`, `deriv_hubbleConstant_eq_neg_sq_mul`,
   `deriv_hubbleConstant_neg_iff`, `exists_deriv_hubbleConstant_neg_iff`
6. Physlib/Cosmology/FLRW/Basic.lean — `FLRW.mk_mem_I_of_mem_Icc`,
   `FLRW.continuousOn_deriv_scaleFactor_mk`, `FLRW.scaleFactor_le_tangent`,
   `FLRW.lt_of_mem_I_of_decelerating`, `FLRW.bddBelow_I_of_decelerating`
7. Physlib/Cosmology/FLRW/Basic.lean — `CosmicFluid`, `CosmicFluid.empty`
8. Physlib/Cosmology/FLRW/MatterContent.lean — `barotropicPressure`
9. Physlib/Cosmology/FLRW/Basic.lean — `FLRW.FriedmannEquation.cosmologicalConstantDensity`,
   `FLRW.FriedmannEquation.cosmologicalConstantPressure`, `CosmicFluid.addCosmologicalConstant`
10. Physlib/Cosmology/FLRW/MatterContent.lean — `cosmologicalConstantPressure_eq_barotropic`
11. Physlib/Cosmology/FLRW/EnergyConditions.lean — `CosmicFluid.NullEnergyCondition`,
   `CosmicFluid.WeakEnergyCondition`, `CosmicFluid.StrongEnergyCondition`,
   `CosmicFluid.DominantEnergyCondition`, `CosmicFluid.DominantEnergyCondition.weakEnergyCondition`,
   `CosmicFluid.WeakEnergyCondition.nullEnergyCondition`,
   `CosmicFluid.StrongEnergyCondition.nullEnergyCondition`
12. Physlib/Cosmology/FLRW/Basic.lean — `FirstOrderFriedmann`, `SecondOrderFriedmann`
13. Physlib/Cosmology/FLRW/Basic.lean — `FLRW.FriedmannSolution`
14. Physlib/Cosmology/FLRW/MatterContent.lean — `ContinuityEquation`, `deriv_firstOrderFriedmann`,
   `continuityEquation_of_friedmann`, `secondOrderFriedmann_of_continuityEquation`
15. Physlib/Cosmology/FLRW/MatterContent.lean — `FLRW.FriedmannSolution.continuityEquation`
16. Physlib/Cosmology/FLRW/MatterContent.lean — `deriv_of_continuityEquation_barotropic`,
   `density_scaling`, `continuityEquation_of_scaling`, `density_scaling_dust`,
   `density_scaling_radiation`, `density_scaling_vacuum`
17. Physlib/Cosmology/FLRW/MatterContent.lean — `firstOrderFriedmann_iff_lambdaFluid`,
   `secondOrderFriedmann_iff_lambdaFluid`
18. Physlib/Cosmology/FLRW/FriedmannSolution.lean —
   `FLRW.friedmannSolution_iff_addCosmologicalConstant`
19. Physlib/Cosmology/FLRW/FriedmannSolution.lean —
   `FLRW.FriedmannSolution.deriv_deriv_scaleFactor_pos_iff`,
   `FLRW.FriedmannSolution.deriv_deriv_scaleFactor_pos_iff_lambda`
20. Physlib/Cosmology/FLRW/FriedmannSolution.lean —
   `FLRW.FriedmannSolution.deriv_scaleFactor_ne_zero`,
   `FLRW.FriedmannSolution.deriv_scaleFactor_pos`,
   `FLRW.FriedmannSolution.deriv_deriv_scaleFactor_nonpos`, `FLRW.FriedmannSolution.lt_of_mem_I`,
   `FLRW.FriedmannSolution.bddBelow_I`
21. Physlib/Cosmology/FLRW/DeSitter.lean — `FLRW.deSitter`, `FLRW.friedmannSolution_deSitter`
22. Physlib/Cosmology/FLRW/DeSitter.lean — `FLRW.not_bddBelow_deSitter_I`
23. Physlib/Cosmology/FLRW/Solutions.lean — `FLRW.milne`, `FLRW.friedmannSolution_milne`
24. Physlib/Cosmology/FLRW/SpecificCases/PowerLaw.lean — `FLRW.powerLaw`, `CosmicFluid.powerLaw`,
   `FLRW.friedmannSolution_powerLaw`
25. Physlib/Cosmology/FLRW/SpecificCases/RadiationDominated.lean — `FLRW.radiationDominated`,
   `FLRW.friedmannSolution_radiationDominated`
26. Physlib/Cosmology/FLRW/SpecificCases/EinsteinDeSitter.lean — `FLRW.einsteinDeSitter`,
   `FLRW.friedmannSolution_einsteinDeSitter`
27. Physlib/Cosmology/FLRW/DensityParameters.lean — `FLRW.criticalDensity`, `FLRW.densityParameter`,
   `FLRW.curvatureDensityParameter`, `FLRW.lambdaDensityParameter`,
   `FLRW.lambdaDensityParameter_eq_densityParameter`,
   `FLRW.densityParameter_addCosmologicalConstant`
28. Physlib/Cosmology/FLRW/DensityParameters.lean —
   `FLRW.FriedmannSolution.densityParameter_add_lambda_add_curvature`,
   `FLRW.FriedmannSolution.densityParameter_add_curvature`
29. Physlib/Cosmology/FLRW/FriedmannSolution.lean —
   `FLRW.FriedmannSolution.decelerationParameter_eq_sum`,
   `FLRW.FriedmannSolution.decelerationParameter_lambdaCDM`
30. Physlib/Cosmology/FLRW/ReducedHubble.lean — `reducedHubble`,
   `FLRW.FriedmannSolution.sq_hubbleConstant_eq_mul_densityParameters`,
   `FLRW.FriedmannSolution.sq_hubbleConstant_eq_reducedHubble`,
   `FLRW.FriedmannSolution.hubbleConstant_eq_reducedHubble`, `equalityScaleFactorRadiationMatter`,
   `equalityScaleFactorMatterLambda`
31. Physlib/Cosmology/FLRW/Age.lean — `age`, `age_eq`
32. Physlib/Cosmology/FLRW/Distances.lean — `FLRW.comovingDistance`, `FLRW.deriv_comovingDistance`,
   `FLRW.redshift`, `FLRW.one_add_redshift`, `FLRW.deriv_redshift`,
   `FLRW.deriv_scaleFactor_eq_mul_hubbleConstant`,
   `FLRW.deriv_comovingDistance_eq_mul_deriv_redshift`, `FLRW.properDistance`,
   `FLRW.deriv_properDistance`, `FLRW.hubbleRadius`, `FLRW.deriv_properDistance_eq_iff`
33. Physlib/Cosmology/FLRW/Distances.lean — `FLRW.transverseComovingDistance`,
   `FLRW.transverseComovingDistance_of_curvature_pos`,
   `FLRW.transverseComovingDistance_of_curvature_eq_zero`,
   `FLRW.transverseComovingDistance_of_curvature_neg`, `FLRW.particleHorizon`, `FLRW.eventHorizon`,
   `FLRW.particleHorizon_einsteinDeSitter`

## References

1. Time API map — Physlib/SpaceAndTime/Time/API-map.md
2. S. Weinberg, *Cosmology*, Oxford University Press (2008), Chapter 1.
3. D. Baumann, *Cosmology*, Cambridge University Press (2022), Chapter 2.
4. S. Dodelson and F. Schmidt, *Modern Cosmology*, 2nd ed., Chapter 2.
