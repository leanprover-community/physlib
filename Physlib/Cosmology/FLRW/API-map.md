# FLRW cosmology

A Friedmann–Lemaître–Robertson–Walker spacetime models a universe that is homogeneous and
isotropic. Its geometry is fixed by a scale factor, a function of cosmic time, together with
the curvature of the spatial slices, which is spherical, flat or saddle. The expansion rate is
the Hubble parameter H = (∂ₜ a) / a, and the change in that rate is measured by the
deceleration parameter q = −(∂ₜ ∂ₜ a) a / (∂ₜ a)². The dynamics is governed by the Friedmann
equations, which tie the scale factor to the energy density and pressure of the cosmic fluid,
to the spatial curvature, and to the cosmological constant.

The API is built around two structures and one proposition: an FLRW model, which is a scale
factor positive and twice differentiable on an open interval of cosmic time together with a
spatial geometry; a cosmic fluid, which is an energy density and a pressure; and the statement
that a model filled with a fluid satisfies both Friedmann equations on its interval, the
curvature parameter being read off the spatial geometry. Around those sit the spatial geometry
itself with its metric profile, the flat limits of the curved cases, the Hubble and
deceleration parameters, and the relation between them.

The matter content is developed through the continuity equation and its relation to the two
Friedmann equations, the barotropic equation of state with the density scaling laws it implies,
and the cosmological constant treated as a fluid in its own right. The exact solutions — de
Sitter, radiation-dominated, Einstein–de Sitter, Milne and Einstein static — are given, with de
Sitter and Milne also presented as FLRW models that solve the Friedmann equations when filled
with the empty fluid, at all times and after a Big Bang respectively. Beyond that are the
critical density and the density parameters with their closure relation, the reduced Hubble
function of the standard cosmological model with its equality scale factors, and the age of the
universe.

Conformal time and the conformal Hubble factor, cosmological distances and redshift, and the
energy conditions and the Big-Bang singularity are not formalized; their modules carry only
TODO items.

## Built on

- Time — `Physlib/SpaceAndTime/Time`

## Requirements

The spatial geometry of the constant-time slices is defined, as a choice between spherical,
flat and saddle, together with the metric profile giving the transverse radius k sin(r/k), r,
or k sinh(r/k) in the three cases. [1]

The flat geometry is the large-radius limit of the curved ones: the profile of the spherical
and of the saddle geometry tends to the flat profile as the curvature radius tends to
infinity. [2]

The key data structure is defined: an FLRW model, a scale factor positive and twice
differentiable on an open interval of cosmic time, together with a spatial geometry. The
spatial geometry supplies the curvature parameter of the Friedmann equations — positive for the
spherical geometry, zero for the flat one, negative for the saddle one. [3]

The cosmic fluid is defined by its energy density and pressure as functions of cosmic time,
along with the empty fluid; and a model filled with such a fluid solves the Friedmann equations
when both hold on the interval of the model. The continuity equation follows from that as a
lemma, as does the closure relation of the density parameters. The de Sitter model at all
times, and the Milne model after its Big Bang, filled with the empty fluid, are
examples. [4][5][6][7]

The first-order Friedmann equation (∂ₜ a / a)² = (8πG/3) ρ − k c² / a² + Λ c² / 3 and the
second-order Friedmann equation ∂ₜ ∂ₜ a / a = −(4πG/3) (ρ + 3 p / c²) + Λ c² / 3 are stated as
propositions: the first on a scale factor and an energy density with the curvature parameter
explicit, the second additionally on a pressure and with no curvature term. The cosmological
constant, Newton's constant and the speed of light are explicit in both. [8]

The Hubble parameter H = ∂ₜ a / a is defined as a function of the scale factor and cosmic time,
and is nonzero wherever the scale factor and its derivative both are. [9]

The deceleration parameter q = −(∂ₜ ∂ₜ a) a / (∂ₜ a)² is defined, with the quotient-rule
formula for ∂ₜ H, the identities q = −(1 + (∂ₜ H) / H²) and ∂ₜ H = −H² (1 + q), and the
pointwise and existential equivalences between ∂ₜ H < 0 and q > −1. [10]

The continuity equation ∂ₜ ρ + 3 H (ρ + P/c²) = 0 of the cosmic fluid is stated at an instant,
and related to the two Friedmann equations: it follows from the first-order equation holding
throughout a neighbourhood of that instant together with the second-order equation, and
conversely the second-order equation follows from the first-order equation and the continuity
equation wherever the scale factor is changing. [11]

The barotropic equation of state P = w ρ c² is defined, with the density scaling law
ρ t = ρ t₀ (a t / a t₀)^(−3(1+w)) that the barotropic continuity equation implies, its
converse, and its dust, radiation and vacuum-energy special cases. [12]

The cosmological constant is available as a fluid: its density ρ_Λ = Λ c² / (8πG) and pressure
p_Λ = −ρ_Λ c² are defined, each Friedmann equation with a cosmological constant is equivalent
to the same equation without one for the combined fluid, and that pressure is the w = −1
barotropic pressure of that density. [13]

The critical density ρ_cr = 3 H² / (8πG) and the density parameters Ω = ρ / ρ_cr,
Ω_K = −k c² / (H² a²) and Ω_Λ = Λ c² / (3 H²) are defined, and the first-order Friedmann
equation is read as the closure relation Ω + Ω_Λ + Ω_K = 1. [14]

The reduced Hubble function E(x)² = Ω_Λ + Ω_m x⁻³ + Ω_r x⁻⁴ + Ω_K x⁻² of the standard
cosmological model is defined, with H = H₀ E(a / a₀) for matter and radiation obeying their
scaling laws, the age t₀ = H₀⁻¹ ∫₀¹ dx / (x E(x)), and the radiation–matter and matter–Λ
equality scale factors. [15][16]

## Further reading

- D. Baumann, Cosmology, Cambridge University Press (2022), Chapter 2 (FLRW geometry, Hubble parameter, Friedmann equations, matter content)
- S. Dodelson and F. Schmidt, Modern Cosmology, 2nd ed., Chapter 2 (the smooth, expanding universe)
- S. Weinberg, Cosmology, Oxford University Press (2008), Chapter 1 (the Robertson-Walker metric, the deceleration parameter, the Friedmann equations)

## Lean declarations

1. Physlib/Cosmology/FLRW/Basic.lean — `SpatialGeometry`, `SpatialGeometry.S`
2. Physlib/Cosmology/FLRW/Basic.lean — `limit_S_sphere`, `limit_S_saddle`,
   `tendsto_sin_rx_over_x`, `tendsto_sinh_rx_over_x`, `mul_sin_as_div`, `mul_sinh_as_div`
3. Physlib/Cosmology/FLRW/Basic.lean — `FLRW`, `FLRW.a_ne_zero`, `FLRW.differentiableAt_a`,
   `FLRW.differentiableAt_deriv_a`, `SpatialGeometry.curvature`,
   `SpatialGeometry.curvature_flat`, `SpatialGeometry.curvature_spherical_pos`,
   `SpatialGeometry.curvature_saddle_neg`
4. Physlib/Cosmology/FLRW/Basic.lean — `CosmicFluid`, `CosmicFluid.empty`,
   `FLRW.FriedmannSolution`
5. Physlib/Cosmology/FLRW/MatterContent.lean — `FLRW.FriedmannSolution.continuityEquation`
6. Physlib/Cosmology/FLRW/DensityParameters.lean — `FLRW.FriedmannSolution.densityParameter_add_lambda_add_curvature`
7. Physlib/Cosmology/FLRW/Solutions.lean — `FLRW.deSitter`, `FLRW.friedmannSolution_deSitter`,
   `FLRW.milne`, `FLRW.friedmannSolution_milne`
8. Physlib/Cosmology/FLRW/Basic.lean — `FirstOrderFriedmann`, `SecondOrderFriedmann`
9. Physlib/Cosmology/FLRW/Basic.lean — `hubbleConstant`, `hubbleConstant_ne_zero`
10. Physlib/Cosmology/FLRW/Basic.lean — `decelerationParameter`, `deriv_hubbleConstant`,
   `decelerationParameter_eq_one_plus_hubbleConstant`, `deriv_hubbleConstant_eq_neg_sq_mul`,
   `deriv_hubbleConstant_neg_iff`, `exists_deriv_hubbleConstant_neg_iff`
11. Physlib/Cosmology/FLRW/MatterContent.lean — `ContinuityEquation`,
   `deriv_firstOrderFriedmann`, `continuityEquation_of_friedmann`,
   `secondOrderFriedmann_of_continuityEquation`
12. Physlib/Cosmology/FLRW/MatterContent.lean — `barotropicPressure`,
   `deriv_of_continuityEquation_barotropic`, `density_scaling`, `continuityEquation_of_scaling`,
   `density_scaling_dust`, `density_scaling_radiation`, `density_scaling_vacuum`
13. Physlib/Cosmology/FLRW/MatterContent.lean — `cosmologicalConstantDensity`,
   `cosmologicalConstantPressure`, `firstOrderFriedmann_iff_lambdaFluid`,
   `secondOrderFriedmann_iff_lambdaFluid`, `cosmologicalConstantPressure_eq_barotropic`
14. Physlib/Cosmology/FLRW/DensityParameters.lean — `criticalDensity`, `densityParameter`,
   `curvatureDensityParameter`, `lambdaDensityParameter`,
   `densityParameter_add_lambda_add_curvature`, `densityParameter_add_curvature`
15. Physlib/Cosmology/FLRW/ReducedHubble.lean — `reducedHubble`,
   `sq_hubbleConstant_eq_reducedHubble`, `hubbleConstant_eq_reducedHubble`,
   `equalityScaleFactorRadiationMatter`, `equalityScaleFactorMatterLambda`
16. Physlib/Cosmology/FLRW/Age.lean — `age`, `age_eq`
