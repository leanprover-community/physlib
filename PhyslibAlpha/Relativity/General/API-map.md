# General Relativity and Modified Gravity

## Abstract (Alpha)

General Relativity models gravitation as the pseudo-Riemannian geometry of a four-dimensional
spacetime manifold carrying a Lorentzian metric of signature (-, +, +, +) governed by the Einstein
field equations. This API formalizes coordinate differential geometry from a spacetime metric and
its analytical inverse through the Levi-Civita Christoffel symbols, Riemann curvature, Ricci
tensor, Ricci scalar, and Einstein tensor, together with covariant conservation, geodesic
dynamics, the ADM 3+1 initial-value formulation, linearized gravitational waves, Newton's
gravitational constant in arbitrary and natural unit systems, exact black-hole and cosmological
solutions (Minkowski, Schwarzschild, interior Schwarzschild, Schwarzschild-de Sitter,
Reissner-Nordström, Kerr, and Friedmann-Lemaître-Robertson-Walker), and sixteen modified or
alternative theories and frameworks of gravitation.

## Content (Alpha)

### Metric geometry, curvature, coordinate differentiation, and Einstein field equations

A rank-2 covariant tensor is represented as an n × n matrix of components [1], paired with a
nondegenerate metric carrying its explicit two-sided inverse [2], with the four-dimensional
Minkowski metric η = diag(-1, 1, 1, 1) as the flat reference background [3]. Conformal
rescalings g ↦ Ω g preserve metric invertibility [4] and leave null tangent cones invariant [5].
Algebraic (0, 4) Riemann curvature tensors satisfy pair antisymmetry, pair-exchange symmetry, and
the first Bianchi identity [6][82], and contract with the inverse metric to the symmetric Ricci tensor
[7] and scalar curvature defined as its metric trace [8][9]. Using coordinate-axis partial
derivatives bridged to `SpaceTime.deriv` [10][85], coordinate curvature operators compute the
Levi-Civita Christoffel symbols from a coordinate metric field [11], construct the Riemann
curvature tensor [12][13], Ricci tensor, Ricci scalar, and Einstein tensor, and establish that any
covariant coordinate components lower to algebraic curvature contractions through the bridge
in [79], and that any
locally constant metric has identically vanishing connection and curvature [13]. From any metric
and curvature tensor, the Einstein tensor G_{ij} = R_{ij} - ½ R g_{ij} is symmetric, has metric
trace (1 - n / 2) R in n dimensions, and in n = 4 spacetime dimensions makes the vacuum Einstein
equation equivalent to Ricci flatness and G + Λ g = 0 equivalent to Ric = Λ g [14], while
contracted second-Bianchi curvature derivatives establish covariant divergence-freeness of the
Einstein tensor and stress-energy conservation [15]. In four dimensions, the trace-free Maxwell
stress-energy tensor [16] bridges index-level electrovacuum sources to Physlib's coordinate-free
electromagnetic field strength [17]{2}{3}.
Coordinate-free covariant differentiation on general smooth manifolds is a planned extension. [TODO]

### Geodesics, ADM 3+1 decomposition, linearized gravity, and physical constants

Test-particle trajectories satisfy the second-order geodesic differential equation driven by a
`GeodesicSystem`, whose first-order phase-space vector field is smooth and admits unique local
solutions by the Picard-Lindelöf theorem, reducing to straight lines when the connection vanishes
[18]. In the Arnowitt-Deser-Misner 3+1 initial-value formulation, spatial slices carry a
Riemannian 3-metric and symmetric extrinsic curvature tensor K_{ij} subject to the Hamiltonian and
momentum constraint equations (using the 3D Levi-Civita covariant derivative `∇K`), which simplify
on time-symmetric (K_{ij} = 0) and maximal (tr K = 0) slices [19][83], distinguish flat Minkowski
vacuum data [20] from non-vacuum initial data with anisotropic extrinsic curvature [21]. Around the
Minkowski background g = η + h, first-order perturbation theory packages symmetric metric
perturbations `MetricPerturbation` [22], defines the Minkowski trace `perturbationTrace` and
trace-reversed perturbation h̄_{ij} = h_{ij} - ½ η_{ij} h [23], and defines the Minkowski
d'Alembertian wave operator □_η [24]. Linearized curvature constructs the linearized Christoffel
symbols [25], Riemann tensor [26], Ricci tensor and scalar curvature [27], and Einstein tensor [28],
establishing diffeomorphism gauge invariance [29], proving that in Lorenz gauge the linearized
Einstein tensor reduces to -½ □_η h̄_{ij} [30], verifying that transverse-traceless gravitational
waves solve the linearized vacuum equations [31], bridging the spatial Laplacian `laplacian3` on
constant-time slices to `Space.laplacian` [32], and deriving Poisson's equation in the weak-field
Newtonian limit [33]{4}. Newton's universal gravitational constant G carries dimension L³ M⁻¹ T⁻² and
CODATA 2022 SI value 6.67430 × 10⁻¹¹ m³ kg⁻¹ s⁻², and admits natural and geometric unit systems
in which c, G, and k_B are simultaneously equal to 1 (see the Units API map) [34]{1}.

### Exact black-hole and cosmological spacetimes

Flat Minkowski spacetime has vanishing Ricci tensor, scalar curvature, and Einstein tensor both
algebraically and from the coordinate metric [35]. A general static spherically symmetric metric
with radial metric function f(r) (line element diag(-f(r), f(r)⁻¹, r², r² sin²θ)) carries a
certified `MetricTensor` and `CoordinateMetric` [36], explicit coordinate Christoffel symbols and
derivatives [37], and closed-form Riemann, Ricci, and Einstein curvature evaluation [38].
The orthonormal Schwarzschild Weyl electric tidal tensor yields the Kretschmann scalar 48 M² / r⁶
and proves purely electric Weyl curvature [39], while `SchwarzschildSpacetime` with metric
function f(r) = 1 - 2 M / r gives direct metric-derivative Christoffel and Riemann components and
matches the exterior of `IncompressibleSphere` [40], with vacuum flatness proved by specializing
the Schwarzschild-de Sitter coordinate metric at Λ = 0 [41]. Inside the fluid sphere,
`IncompressibleSphere` formalizes Schwarzschild's 1916 constant-density interior pressure profile,
surface continuity/differentiability junction properties, and compactness bound `α < (8 / 9) Ra`
[42]. Including a cosmological constant Λ in the
Schwarzschild-de Sitter (Kottler) metric f(r) = 1 - 2 M / r - Λ r² / 3 yields constant-curvature
de Sitter frame components, Kretschmann invariant 48 M² / r⁶ + 8 Λ² / 3, and frame Bianchi
conservation [43], Λ-independent Weyl electric components [44], and full coordinate-metric
verification of R_{ij} = Λ g_{ij}, R = 4 Λ, and G_{ij} = -Λ g_{ij} [45]. Adding electric charge
yields the Reissner-Nordström electrovacuum metric f(r) = 1 - 2 M / r + Q² / r², the radial
Coulomb-Maxwell field strength tensor F_{ab}, and the trace-free electromagnetic stress-energy
tensor satisfying the Einstein-Maxwell equations [46]. Rotating black holes are represented by
`KerrSpacetime` in Boyer-Lindquist coordinates (t, r, θ, φ) with spin a, polynomial functions
Σ = r² + a² cos²θ and Δ = r² - r_s r + a², and exact block inverse metric [47], metric coordinate
partial derivatives [48], all 64 Levi-Civita Christoffel symbols and contracted trace [49], and
full verification that the Ricci tensor, Ricci scalar, and Einstein tensor vanish identically in
vacuum [50]. Homogeneous and isotropic cosmology is formalized on `FLRWSpacetime` with scale
factor a(t) and spatial curvature k [51], evaluating all FLRW Christoffel symbols, Ricci
components, scalar curvature, and Einstein tensor from the coordinate metric [52][84], proving
equivalence with the Friedmann equations for a comoving perfect fluid with arbitrary speed of
light c and gravitational constant G [53][81], and bridging directly to Physlib's `Cosmology.FLRW`
[54].

### Scalar-tensor, higher-curvature, and screening gravity theories

Historically, Nordström's relativistic scalar gravity restricts the spacetime metric of a
`NordstromSpacetime` to the conformally flat form φ(x)² η_{μν}, preserving null cones (producing
zero gravitational light deflection) while evaluating its Christoffel symbols and proving the
four-dimensional Einstein-Fokker curvature identity R = -6 □_η φ / φ³ and its equivalence to the
nonlinear scalar wave equation □_η φ = -4 π φ³ T [55]. Brans-Dicke scalar-tensor gravity couples a
scalar mode to curvature with dimensionless parameter ω on `BransDickeTheory`, yielding the
post-Newtonian parameter γ(ω) = (1 + ω) / (2 + ω) approaching the General Relativity value 1 under
the Cassini bound ω > 40000{7}, the weak-field effective gravitational coupling
`coupling(ω) = (4 + 2ω) / (3 + 2ω) = 1 + 1 / (3 + 2ω)` bounded in `[1, 4/3]` for ω ≥ 0, and the
ω = 0 metric f(R) value γ = 1 / 2 [56]. Non-linear f(R) gravity (`FRTheory`) replaces the
Einstein-Hilbert density R with f(R), modifying the algebraic field equations, recovering General
Relativity with Λ via `FRTheory.generalRelativity Λ`, deriving the `n`-dimensional and 4D `3 □f'`
trace identities, and supplying Starobinsky's `R + α R²` Legendre potential `(φ - 1)² / (8 α)` and
normalized Einstein-frame slow-roll plateau `V(φ) / φ² → 1 / (8 α)` [57]. By Ostrogradsky's
theorem (`HigherDerivativeOscillator`), a second-order higher-derivative benchmark Lagrangian
`L = ½ q̈² - ½ m² q²` has a degenerate kinetic Hessian matrix `Matrix.det oscillatorKineticHessian = 0` in
`(q̇, q̈)` and a canonical Hamiltonian linear in the position-conjugate momentum `p₁`, making it
unbounded below for any `v ≠ 0` in contrast to positive-definite first-order kinetic energy [58].
Cubic Galileon scalar-tensor theories (`CubicGalileon`) achieve second-order equations of motion
because their one-dimensional cubic density reduces to a total time derivative even under constant
velocity shifts `φ' ↦ φ' + c`, whereas exact shift symmetry forbids a non-trivial potential term
[59]. Chameleon scalar-tensor theories (`ChameleonModel`) feature an environment-dependent mass
that grows monotonically with ambient matter density, shrinking the Compton range and suppressing
fifth forces for screened bodies via the thin-shell parameter Δ = |δφ| / (2 β M_pl |Φ_N|) [60].

### Torsion, teleparallel, higher-dimensional, Lorentz-violating, massive, and PPN formalisms

Einstein-Cartan-Sciama-Kibble theory (`EinsteinCartanData`) relaxes the torsion-free constraint on
the affine connection, proving that any metric-compatible connection decomposes uniquely into the
Levi-Civita connection plus the contorsion tensor built from torsion, and inverting the algebraic
4D Palatini spin-torsion equation [61][86][87]. In the Teleparallel Equivalent of General Relativity
(TEGR), gravity is carried by the curvature-free Weitzenböck connection of an orthonormal `Tetrad`
and its torsion `superpotential` [62]; on flat FLRW cosmologies the general `torsionScalar` matches
`flrwTorsionScalar = 6 H²` and the Levi-Civita scalar curvature satisfies R_LC = -T + B up to the
total-divergence boundary term B [63], while non-linear f(T) = T + F(T) models (`FTTheory`) modify
the Friedmann expansion equation [64]. Lovelock higher-curvature gravity constructs the generalized
Kronecker delta `generalizedKroneckerDelta` and proves dimensional pigeonhole vanishing alongside antisymmetric
permutation-sum coset splits [65], defines `AlgebraicCurvature`, the quadratic Gauss-Bonnet scalar
𝒢 = R² - 4 R^a_b R^b_a + R^{cd}_{ab} R^{ab}_{cd}, and Lanczos variation tensor H^i_j [66], proves via
`lovelockContract5 = -8 H^i_j` that H^i_j vanishes identically in dimension n ≤ 4 (the 4D
Bach-Lanczos theorem) [88], and contrasts the 4D topological invariant with non-zero 5D dynamics on
`constantCurvature` spaces [89]. Five-dimensional Kaluza-Klein theory (`KaluzaKleinData`) unifies
4D General Relativity and Maxwell electromagnetism inside a 5D metric G_{AB} built from g_{μν},
four-potential A_μ, and dilaton φ, establishing the exact 5D inverse metric and `MetricTensor 5`
[67], unit-determinant upper-unitriangular vielbein factorization [68], diffeomorphism-to-U(1)
gauge equivalence under compact-circle shifts [69], and 4D Maxwell stress-energy tracelessness
together with the Kaluza miracle R^{(5)} = R^{(4)} - ¼ F_{ab} F^{ab} [70]. Einstein-Aether theory
(`AetherCouplings`) breaks local Lorentz boost invariance with a unit-timelike vector field u^a
(g_{ab} u^a u^b = -1) governed by four Jacobson-Mattingly couplings (c₁, c₂, c₃, c₄), yielding
explicit squared propagation speeds for the spin-2, spin-1, and spin-0 modes, the GW170817 luminal
graviton constraint s₂² = 1 ↔ c₁ + c₃ = 0, and the renormalized Newtonian constant
G_N = G_bare / (1 - (c₁ + c₄) / 2) [71]. Fierz-Pauli and de Rham-Gabadadze-Tolley (dRGT) massive
gravity formalize the Lorentz-invariant mass term -(m² / 4)(h_{ab} h^{ab} + α h²) on
`FierzPauliTheory`, proving that the ghost-free tuning α = -1 uniquely eliminates the sixth
longitudinal derivative mode and enforces vacuum tracelessness h = 0 [72], derive the van
Dam-Veltman-Zakharov (vDVZ) 4 / 3 static coupling ratio and 3 / 4 light-deflection discontinuity
between `massivePropagatorCoupling` and `grPropagatorCoupling`, both built on the shared
`MassiveGravityTheory` core [73][80], and construct the ghost-free
dRGT potential on `DRGTTheory` from elementary symmetric polynomials of trace powers [74]. Galactic
rotation-curve alternatives without non-baryonic dark matter are represented by Milgrom's Modified
Newtonian Dynamics (`MONDTheory`), which interpolates between the Newtonian regime a ≫ a₀ and the
deep-MOND regime a = √(a_N a₀) to produce asymptotically flat circular velocities v⁴ = G M a₀ and
bridges directly to Physlib's `pairGravityAcceleration` [75]{8}, by Bekenstein's relativistic
Tensor-Vector-Scalar (`TeVeSMetric`) disformal physical metric and its exact analytical
inverse [76], and by Moffat's Scalar-Tensor-Vector Gravity (`MOGTheory`) Yukawa-enhancement factor
`1 + α (1 - e^{-μ r})` and Yukawa-enhanced gravitational potential
`Φ(r) = -(G M / r) (1 + α (1 - e^{-μ r}))` [77]. Finally, the Will-Nordtvedt Parameterized
Post-Newtonian (PPN) formalism unifies solar-system tests across metric theories via ten
dimensionless parameters (γ, β, ξ, α₁, α₂, α₃, ζ₁, ζ₂, ζ₃, ζ₄), classifying fully conservative and
semiconservative theories, embedding General Relativity, `BransDickeTheory`, metric f(R), and
Nordström gravity, and evaluating light deflection, Shapiro time delay, perihelion precession, and
the Nordtvedt Strong Equivalence Principle violation parameter η_N [78]{5}{6}.

## Lean References

1. PhyslibAlpha/Relativity/Tensors/Tensor2.lean — `Tensor2`, `IsSymm`
2. PhyslibAlpha/Relativity/Metrics/Basic.lean — `MetricTensor`, `MetricTensor.ginv_symm`,
   `MetricTensor.sum_ginv_mul_g_left`, `MetricTensor.sum_ginv_mul_g_right`,
   `MetricTensor.sum_ginv_mul_g_apply`, `MetricTensor.sum_mul_ginv_g_apply`
3. PhyslibAlpha/Relativity/Metrics/Minkowski.lean — `minkowskiMetric4`, `minkowskiMetric4_symm`,
   `minkowskiMetric4_mul_self`, `minkowskiMetric4_eq_neg_coMetric_repr`, `minkowski`,
   `minkowski_ginv_offdiag`, `metricTrace_minkowski`, `minkowskiMetricField`
4. PhyslibAlpha/Relativity/Metrics/ConformalMetric.lean — `conformalRescaleMetric`,
   `conformalRescaleMetricInv`, `conformalMetric`
5. PhyslibAlpha/Relativity/Metrics/NullVector.lean — `NullVector`, `nullVector_conformal_iff`
6. PhyslibAlpha/Relativity/Tensors/RiemannTensor.lean — `RiemannTensor`, `RiemannTensor.ext`,
   `skew_first`, `zero_of_repeated_first`, `zero_of_repeated_last`, `swap_mixed`, `flat`
7. PhyslibAlpha/Relativity/Tensors/RicciTensor.lean — `ricci`, `ricci_symm`, `ricci_of_diag`,
   `ricci_flat`
8. PhyslibAlpha/Relativity/Metrics/MetricTrace.lean — `metricTrace`, `metricTrace_diag`,
   `sum_ginv_mul_g`, `metricTrace_mul_g`
9. PhyslibAlpha/Relativity/Metrics/RicciScalar.lean — `ricciScalar`, `ricciScalar_eq_metricTrace`,
   `ricciScalar_flat`
10. PhyslibAlpha/Mathematics/Calculus/CoordDeriv.lean — `coordDeriv`, `coordDeriv_of_hasDerivAt`,
    `coordDeriv_const_slice`, `coordDeriv_const`, `coordDeriv_congr`, `coordDeriv_congr_nhds`,
    `coordDeriv_eq_fderiv`, `coordDeriv_comm`
11. PhyslibAlpha/Relativity/Metrics/CoordinateMetric.lean — `CoordinateMetric`,
    `CoordinateMetric.metricTensor`, `CoordinateMetric.christoffel`, `CoordinateMetric.riemann`,
    `CoordinateMetric.ricciTensor`, `CoordinateMetric.ricciScalar`,
    `CoordinateMetric.einsteinTensor`
12. PhyslibAlpha/Relativity/Metrics/RiemannFromData.lean — `riemannFromData`,
    `riemannFromData_congr`
13. PhyslibAlpha/Relativity/Metrics/Christoffel.lean — namespace `CoordinateCurvature`:
    `christoffel`, `christoffel_diag`, and `CoordinateMetric.christoffel`. The companion Riemann,
    Ricci, and Einstein modules supply the remaining coordinate curvature operators and the
    constant-metric vanishing lemmas.
14. PhyslibAlpha/Relativity/Tensors/EinsteinTensor.lean — `einstein`, `einstein_symm`,
    `einstein_flat`, `metricTrace_einstein`, `ricciScalar_eq_zero_of_einstein_eq_zero`,
    `vacuum_iff_ricci_flat`, `einsteinSpace_iff`
15. PhyslibAlpha/Relativity/Metrics/CurvatureDerivatives.lean — `CurvatureDerivatives`,
    `CurvatureDerivatives.einsteinDeriv`, `inertialDivergence`, `inertialDivergence_combination`,
    `inertialDivergence_einstein_eq_zero`, `combination_conserved_iff`
16. PhyslibAlpha/Relativity/Tensors/MaxwellStressEnergy.lean — `maxwellFieldInvariant`,
    `metricTrace_maxwellQuad`, `maxwellStressEnergy`, `maxwellStressEnergy_trace_zero`
17. PhyslibAlpha/Relativity/Tensors/EMFieldStrength.lean — `emFieldStrengthComponents`,
    `emFieldStrengthComponents_antisymm`
18. PhyslibAlpha/Relativity/General/GeodesicSystem.lean — `Christoffel`, `GeodesicSystem`,
    `GeodesicSystem.accel`, `GeodesicSystem.field`, `IsGeodesic`, `contDiffAt_geodesicField`,
    `geodesic_ivp_exists`, `geodesic_ivp_exists_curve`, `geodesic_ivp_unique`,
    `GeodesicSystem.flat`, `geodesicField_zero`, `flat_geodesic`
19. PhyslibAlpha/Relativity/General/InitialData/Basic.lean — `InitialData`,
    `InitialData.momentumConstraint`,
    `InitialData.hamiltonianConstraint`, `InitialData.IsVacuumData`,
    `InitialData.hamiltonianConstraint_eq_ricciScalar_of_K_zero`,
    `InitialData.hamiltonianConstraint_eq_of_trace_zero`
20. PhyslibAlpha/Relativity/General/InitialData/FlatSlice.lean — `euclideanMetric3`, `flatInitialData`,
    `flatInitialData_hamiltonianConstraint_zero`, `flatInitialData_momentumConstraint_zero`, `flatInitialData_isVacuum`
21. PhyslibAlpha/Relativity/General/InitialData/AnisotropicSlice.lean —
    `anisotropicExtrinsicCurvature`, `anisotropicSliceData`,
    `anisotropicSliceData_hamiltonianConstraint`,
    `anisotropicSliceData_hamiltonianConstraint_ne_zero`
22. PhyslibAlpha/Relativity/General/Linearized/Basic.lean — `MetricPerturbation`,
    `MetricPerturbation.symm_apply`, `MetricPerturbation.IsC2At`, `MetricPerturbation.add`
23. PhyslibAlpha/Relativity/General/Linearized/TraceReversed.lean — `perturbationTrace`,
    `perturbationTrace_eq_metricTrace`, `traceReversed`, `traceReversed_trace`,
    `traceReversed_involutive`, `MetricPerturbation.traceReversed`
24. PhyslibAlpha/Relativity/General/Linearized/MinkowskiDalembertian.lean — `minkowskiDalembertian`,
    `minkowskiDalembertian_zero`, `minkowskiDalembertian_const_mul`,
    `minkowskiDalembertian_neg`, `minkowskiDalembertian_add`,
    `minkowskiDalembertian_eq_laplacian3_of_static`
25. PhyslibAlpha/Relativity/General/Linearized/LinearizedChristoffel.lean —
    `linearizedChristoffel`, `linearizedChristoffel_symm`,
    `differentiableAt_linearizedChristoffel`, `linearizedChristoffel_add_eventuallyEq`
26. PhyslibAlpha/Relativity/General/Linearized/LinearizedRiemann.lean — `linearizedRiemann`,
    `linearizedRiemann_antisymm`, `linearizedRiemann_add`
27. PhyslibAlpha/Relativity/General/Linearized/LinearizedRicci.lean — `linearizedRicci`,
    `linearizedRicciScalar`
28. PhyslibAlpha/Relativity/General/Linearized/LinearizedEinstein.lean — `linearizedEinstein`
29. PhyslibAlpha/Relativity/General/Linearized/GaugeTransform.lean — `pureGauge`, `gaugeTransform`,
    `linearizedRiemann_pureGauge`, `linearizedRiemann_gauge_invariant`,
    `linearizedRicci_gauge_invariant`, `linearizedEinstein_gauge_invariant`
30. PhyslibAlpha/Relativity/General/Linearized/LorenzGauge.lean — `lorenzDivergence`,
    `IsLorenzGauge`, `linearizedRicci_in_traceReversed`, `linearizedEinstein_in_traceReversed`,
    `linearizedEinstein_lorenz_gauge`
31. PhyslibAlpha/Relativity/General/Linearized/TTWave.lean — `ttWave`, `ttWave_trace_zero`,
    `traceReversed_ttWave`, `ttWave_lorenz_gauge`, `ttWave_linearizedEinstein_zero`
32. PhyslibAlpha/Relativity/General/Linearized/Laplacian3.lean — `laplacian3`,
    `spatialSliceEmbedding`, `spaceDeriv_comp_spatialSliceEmbedding`,
    `laplacian3_eq_space_laplacian`
33. PhyslibAlpha/Relativity/General/Linearized/NewtonianPerturbation.lean —
    `newtonianPerturbation`, `traceReversed_newtonianPerturbation`,
    `newtonianPerturbation_lorenz_gauge`, `newtonianPerturbation_linearizedEinstein_00`,
    `newtonianPerturbation_poisson_iff`
34. PhyslibAlpha/Relativity/General/GravitationalConstant.lean — `GravitationalConstant`,
    `gravitationalConstantDimension`, `gravitationalConstant`, `gravitationalConstant_in_SI`,
    `toWithDim`, `toWithDim_scaleUnit`, `exists_units_c_G_kB_eq_one`
35. PhyslibAlpha/Relativity/General/MinkowskiCoordinateMetric.lean — `minkowskiCoordinateMetric`,
    `minkowskiCoordinateMetric_christoffel`, `minkowskiCoordinateMetric_riemann`,
    `minkowskiCoordinateMetric_einsteinTensor`, `minkowskiCoordinateMetric_riemannFromData`,
    `minkowski_ricci_eq_zero`, `minkowski_ricciScalar_eq_zero`,
    `minkowski_einstein_eq_zero`, `minkowski_vacuum_iff_ricci_flat`
36. PhyslibAlpha/Relativity/Metrics/StaticSphericalMetric/Basic.lean — `StaticSphericalMetric`,
    `StaticSphericalMetric.metric`, `StaticSphericalMetric.metricInv`,
    `StaticSphericalMetric.metric_symm`, `StaticSphericalMetric.metric_mul_inv`,
    `StaticSphericalMetric.metricTensor`, `StaticSphericalMetric.toCoordinateMetric`
37. PhyslibAlpha/Relativity/Metrics/StaticSphericalMetric/Christoffel.lean —
    `StaticSphericalMetric.christoffel`, `StaticSphericalMetric.christoffel_eq`,
    `StaticSphericalMetric.eventually_christoffel_eq`, `StaticSphericalMetric.christoffelDeriv`,
    `StaticSphericalMetric.pd_christoffel_eq_deriv`
38. PhyslibAlpha/Relativity/Metrics/StaticSphericalMetric/RicciCurvature.lean —
    `StaticSphericalMetric.riemann_eq_data`, `StaticSphericalMetric.ricciTensor`,
    `StaticSphericalMetric.ricciScalar`, `StaticSphericalMetric.einsteinTensor`
39. PhyslibAlpha/Relativity/General/Schwarzschild/ElectricWeyl.lean — `electricPart`,
    `electricPart_symm`, `electricPart_trace`, `electricWeylRiemann`, `ricci_eq_zero`,
    `electricWeyl_frameKretschmannScalar_eq`, `kretschmann_scalar`, `weyl_purely_electric`,
    `electricPart_from_metric`
40. PhyslibAlpha/Relativity/General/Schwarzschild/Basic.lean — `SchwarzschildSpacetime`,
    `SchwarzschildSpacetime.metricFn`, `SchwarzschildSpacetime.metric`,
    `SchwarzschildSpacetime.toStaticSpherical`, `SchwarzschildSpacetime.toCoordinateMetric`,
    `SchwarzschildSpacetime.metricFn_ofIncompressibleSphere`,
    `SchwarzschildSpacetime.christoffelTtr_from_metric`,
    `SchwarzschildSpacetime.christoffelRrr_from_metric`
41. PhyslibAlpha/Relativity/General/Schwarzschild/CoordinateCurvature.lean —
    `SchwarzschildSpacetime.toDeSitter`, `SchwarzschildSpacetime.toDeSitter_metric`,
    `SchwarzschildSpacetime.riemann_components_from_coordinateMetric`,
    `SchwarzschildSpacetime.ricciTensor`,
    `SchwarzschildSpacetime.ricciScalar`, `SchwarzschildSpacetime.einsteinTensor`
42. PhyslibAlpha/Relativity/General/Schwarzschild/IncompressibleSphere.lean —
    `IncompressibleSphere`, `rs`, `chia`, `cosChia`, `cosChia_sq`, `cosChia_pos`,
    `cosChia_lt_one`, `rs_div_Ra`, `one_third_lt_cosChia_iff_rs`
43. PhyslibAlpha/Relativity/General/SchwarzschildDeSitter/DeSitterFrame.lean — `deSitterPart`,
    `SchwarzschildDeSitterSpacetime.frameSumOfSquares`, `SchwarzschildDeSitterSpacetime.frameSumOfSquares_eq`,
    `SchwarzschildDeSitterSpacetime.kretschmann`, `SchwarzschildDeSitterSpacetime.frameRicciTensor_eq`,
    `SchwarzschildDeSitterSpacetime.frameScalar_eq`,
    `SchwarzschildDeSitterSpacetime.frameEinstein_eq`,
    `SchwarzschildDeSitterSpacetime.frame_bianchi`,
    `SchwarzschildDeSitterSpacetime.frame_einstein_conserved`
44. PhyslibAlpha/Relativity/General/SchwarzschildDeSitter/Basic.lean —
    `SchwarzschildDeSitterSpacetime`, `SchwarzschildDeSitterSpacetime.metricFn`,
    `SchwarzschildDeSitterSpacetime.metricFnHalfDeriv`,
    `SchwarzschildDeSitterSpacetime.metric`, `SchwarzschildDeSitterSpacetime.metricInv`,
    `SchwarzschildDeSitterSpacetime.toStaticSpherical`,
    `SchwarzschildDeSitterSpacetime.toCoordinateMetric`,
    `SchwarzschildDeSitterSpacetime.christoffelTtr`,
    `SchwarzschildDeSitterSpacetime.christoffelRrr`, `SchwarzschildDeSitterSpacetime.weyl_rr`,
    `SchwarzschildDeSitterSpacetime.weyl_thetatheta`, `SchwarzschildDeSitterSpacetime.weyl_phiphi`
45. PhyslibAlpha/Relativity/General/SchwarzschildDeSitter/CoordinateCurvature.lean —
    `SchwarzschildDeSitterSpacetime.christoffel`, `SchwarzschildDeSitterSpacetime.christoffelDeriv`,
    `SchwarzschildDeSitterSpacetime.christoffel_eq`,
    `SchwarzschildDeSitterSpacetime.riemann_components_from_metric`,
    `SchwarzschildDeSitterSpacetime.ricciTensor`,
    `SchwarzschildDeSitterSpacetime.ricciScalar`,
    `SchwarzschildDeSitterSpacetime.einsteinTensor`
46. PhyslibAlpha/Relativity/General/ReissnerNordstrom/Basic.lean —
    `ReissnerNordstromSpacetime`, `ReissnerNordstromSpacetime.metricFn`,
    `ReissnerNordstromSpacetime.metric`, `ReissnerNordstromSpacetime.metricInv`,
    `ReissnerNordstromSpacetime.toStaticSpherical`,
    `ReissnerNordstromSpacetime.toCoordinateMetric`,
    `ReissnerNordstromSpacetime.coulombFieldStrength`,
    `ReissnerNordstromSpacetime.coulombFieldStrength_antisymm`,
    `ReissnerNordstromSpacetime.maxwellStressEnergy`,
    `ReissnerNordstromSpacetime.einsteinTensor_eq_maxwell`
47. PhyslibAlpha/Relativity/General/Kerr/Basic.lean — `KerrSpacetime`, `KerrSpacetime.sigma`,
    `KerrSpacetime.delta`, `KerrSpacetime.axialFactor`, `KerrSpacetime.axialFactor_eq_sigma`,
    `KerrSpacetime.tphi_det_id`, `KerrSpacetime.metric`, `KerrSpacetime.metricInv`,
    `KerrSpacetime.metric_symm`, `KerrSpacetime.metricInv_mul_metric`,
    `KerrSpacetime.metric_mul_metricInv`, `KerrSpacetime.metricTensor`,
    `KerrSpacetime.metric_zero_spin`
48. PhyslibAlpha/Relativity/General/Kerr/MetricDeriv.lean — `KerrSpacetime.metricCoordDeriv`,
    `KerrSpacetime.hasDerivAt_sigma_r`, `KerrSpacetime.hasDerivAt_sigma_theta`,
    `KerrSpacetime.hasDerivAt_delta_r`, `KerrSpacetime.pd_metric_eq`
49. PhyslibAlpha/Relativity/General/Kerr/Christoffel.lean — `KerrSpacetime.christoffel`,
    `KerrSpacetime.christoffel_symm`, `KerrSpacetime.christoffel_eq`,
    `KerrSpacetime.eventually_christoffel_eq`, `KerrSpacetime.christoffelTrace`,
    `KerrSpacetime.sum_christoffel_trace`
50. PhyslibAlpha/Relativity/General/Kerr/RicciCurvature.lean — `KerrSpacetime.ricci`,
    `KerrSpacetime.einstein`, `KerrSpacetime.christoffelTraceDeriv_rr`,
    `KerrSpacetime.christoffelTraceDeriv_thetar`, `KerrSpacetime.christoffelTraceDeriv_rtheta`,
    `KerrSpacetime.christoffelTraceDeriv_thetatheta`, `KerrSpacetime.ricciTensor_eq_zero`,
    `KerrSpacetime.ricciScalar_eq_zero`, `KerrSpacetime.einsteinTensor_eq_zero`
51. PhyslibAlpha/Cosmology/FLRW/Basic.lean — `FLRWSpacetime`, `FLRWSpacetime.metric`,
    `FLRWSpacetime.metricInv`, `FLRWSpacetime.metric_symm`, `FLRWSpacetime.metric_mul_inv`,
    `FLRWSpacetime.metricTensor`, `FLRWSpacetime.toCoordinateMetric`
52. PhyslibAlpha/Cosmology/FLRW/Christoffel.lean — `FLRWSpacetime.christoffel`,
    `FLRWSpacetime.christoffelDeriv`, `FLRWSpacetime.christoffel_eq`,
    `FLRWSpacetime.eventually_christoffel_eq`, `FLRWSpacetime.pd_christoffel_eq_deriv`,
    `FLRWSpacetime.riemann_eq_data`
53. PhyslibAlpha/Cosmology/FLRW/PerfectFluid.lean —
    `FLRWSpacetime.einsteinTensor_00_iff_friedmann`,
    `FLRWSpacetime.einsteinTensor_spatial_iff_friedmann`,
    `FLRWSpacetime.einsteinTensor_iff_friedmann`
54. PhyslibAlpha/Cosmology/FLRW/FriedmannEquations.lean — `flrwScaleFactorOfReal`,
    `FLRWSpacetime.ofCosmology`, `einsteinTensor_ofCosmology_iff_friedmann`,
    `friedmannSolution_of_einsteinTensor`
55. PhyslibAlpha/Relativity/Modified/Nordstrom.lean — `NordstromSpacetime`,
    `NordstromSpacetime.metric`, `NordstromSpacetime.metricInv`, `NordstromSpacetime.metricTensor`,
    `NordstromSpacetime.toCoordinateMetric`, `NordstromSpacetime.light_deflection_zero`,
    `NordstromSpacetime.christoffel`, `NordstromSpacetime.christoffel_eq`,
    `NordstromSpacetime.ricciScalar`, `NordstromSpacetime.einsteinFokker_iff`
56. PhyslibAlpha/Relativity/Modified/BransDicke.lean — `BransDickeTheory`,
    `BransDickeTheory.gamma`, `BransDickeTheory.gamma_eq_one_sub`,
    `BransDickeTheory.gamma_bounds`, `BransDickeTheory.cassini_deviation`,
    `BransDickeTheory.coupling`, `BransDickeTheory.coupling_eq_one_add`,
    `BransDickeTheory.coupling_bounds`, `BransDickeTheory.fR`, `BransDickeTheory.fR_gamma`,
    `gamma_tendsto_atTop`
57. PhyslibAlpha/Relativity/Modified/FRGravity.lean — `FRTheory`,
    `FRTheory.generalRelativity`, `FRTheory.starobinsky`, `FRTheory.algebraicFieldEqn`,
    `linear_is_einstein`, `trace_algebraicFieldEqn`, `trace_algebraicFieldEqn_four`,
    `starobinskyPotential`, `starobinsky_scalar_inversion`, `starobinskyPotential_eq`,
    `starobinsky_nonconstant_deriv`, `einsteinFramePotential`, `starobinsky_einsteinFrame`,
    `starobinsky_plateau`
58. PhyslibAlpha/Relativity/Modified/Ostrogradsky.lean — `HigherDerivativeOscillator`,
    `oscillatorKineticHessian`, `oscillatorKineticHessian_degenerate`,
    `HigherDerivativeOscillator.hamiltonian`,
    `HigherDerivativeOscillator.hamiltonian_add`,
    `HigherDerivativeOscillator.ostrogradsky_unbounded_below`
59. PhyslibAlpha/Relativity/Modified/Galileon.lean — `CubicGalileon`,
    `CubicGalileon.density`, `cubic_total_derivative`, `CubicGalileon.density_hasDerivAt`,
    `shift_total_derivative`
60. PhyslibAlpha/Relativity/Modified/ChameleonScreening.lean — `ChameleonModel`,
    `ChameleonModel.massSq`, `ChameleonModel.mass`, `ChameleonModel.mass_mono`,
    `ChameleonModel.range`, `ChameleonModel.range_shrinks`, `ChameleonModel.suppression`,
    `comptonRange`, `comptonRange_antitone`, `yukawaSuppression`, `yukawaSuppression_lt_half`,
    `thinShellParameter`, `screeningFactor`, `thin_shell_suppressed`
61. PhyslibAlpha/Relativity/Modified/EinsteinCartan/Basic.lean — `AffineConnection`,
    `EinsteinCartanData`, `EinsteinCartanData.torsion`, `EinsteinCartanData.torsion_antisymm`,
    `EinsteinCartanData.torsion_diag`, `torsion`, `torsion_antisymm`
62. PhyslibAlpha/Relativity/Modified/Teleparallel/Basic.lean — `Tetrad`,
    `Tetrad.weitzenbockConnection`, `Tetrad.mul_weitzenbockConnection`,
    `Tetrad.weitzenbockTorsion`, `Tetrad.weitzenbockTorsion_eq`,
    `Tetrad.weitzenbockTorsion_antisymm`, `superpotential`, `superpotential_antisymm`,
    `torsionScalar`
63. PhyslibAlpha/Relativity/Modified/Teleparallel/FLRWTorsion.lean — `flrwTetrad`,
    `flrwTetradInv`, `flrwTetrad_mul_inv`, `flrwTetradFrame`, `flrwWeitzenbock_hubble`,
    `flrwTorsionScalar`, `torsionScalar_flrw_eq_flrwTorsionScalar`,
    `flrwTorsionScalar_ofCosmology`, `flrwBoundaryTerm`,
    `ricciScalar_flrw_flat_eq_neg_torsion_add_boundary`
64. PhyslibAlpha/Relativity/Modified/Teleparallel/FTGravity.lean — `FTTheory`,
    `FTTheory.tegr`, `FTTheory.quadratic`, `FTTheory.friedmannLHS`, `FTTheory.friedmannLHS_tegr`,
    `FTTheory.friedmannLHS_quadratic`
65. PhyslibAlpha/Mathematics/GeneralizedKronecker.lean — `generalizedKroneckerDelta`,
    `generalizedKroneckerDelta_eq_zero_of_lt`, `generalizedKroneckerDelta_five_eq_sum_perm`, `perm_fin5_fiber_split`
66. PhyslibAlpha/Relativity/Modified/Lovelock/Basic.lean — `AlgebraicCurvature`,
    `AlgebraicCurvature.ricciMixed`, `AlgebraicCurvature.ricciScalar`, `AlgebraicCurvature.ricciSq`,
    `AlgebraicCurvature.riemannSq`, `AlgebraicCurvature.gaussBonnetScalar`,
    `AlgebraicCurvature.lanczosTensor`
67. PhyslibAlpha/Relativity/Modified/KaluzaKlein/Basic.lean — `KaluzaKleinData`,
    `KaluzaKleinData.metric`, `KaluzaKleinData.metric_symm`, `KaluzaKleinData.metricInv`,
    `KaluzaKleinData.metricInv_symm`, `KaluzaKleinData.gaugeShift`,
    `KaluzaKleinData.toMetricTensor`, `extendedPotential`, `metric4Ext`, `kkMetric`,
    `kkMetric_symm`, `contravariantPotential`, `kkMetricInv`, `kkMetricInv_mul_kkMetric`,
    `kkMetricInv_symm`, `kkMetric_mul_kkMetricInv`, `kkMetricTensor`
68. PhyslibAlpha/Relativity/Modified/KaluzaKlein/TriangularFactorization.lean —
    `kkTriangular`, `kkBlockDiag`, `det_kkTriangular`, `kkMetric_eq_triangular_conj`,
    `KaluzaKleinData.metric_eq_triangular_conj`
69. PhyslibAlpha/Relativity/Modified/KaluzaKlein/GaugeTransform.lean —
    `kkGaugeJacobian`, `det_kkGaugeJacobian`, `kkGaugeJacobian_pullback`,
    `KaluzaKleinData.gaugeJacobian_pullback`
70. PhyslibAlpha/Relativity/Modified/KaluzaKlein/KaluzaMiracle.lean — `maxwellFieldInvariant`,
    `maxwellStressEnergy`, `maxwellStressEnergy_trace_zero`, `KaluzaKleinData.ricci44`,
    `KaluzaKleinData.ricci5DHorizontal`, `KaluzaKleinData.scalar5D`, `KaluzaKleinData.kaluza_miracle`,
    `KaluzaKleinData.einstein4D_eq_zero_iff`
71. PhyslibAlpha/Relativity/Modified/EinsteinAether.lean — `AetherCouplings`,
    `AetherCouplings.c13`, `AetherCouplings.c14`, `AetherCouplings.c123`,
    `AetherCouplings.c1Sub3`, `IsUnitTimelike`, `minkowskiRestAether`,
    `minkowskiRestAether_unitTimelike`, `linUnitTimelike_time_zero`,
    `AetherCouplings.kineticTensor`, `AetherCouplings.kineticInvariant`,
    `AetherCouplings.lagrangian`, `AetherCouplings.lagrangian_on_shell`,
    `AetherCouplings.spin2SpeedSq`, `AetherCouplings.spin1SpeedSq`,
    `AetherCouplings.spin0SpeedSq`, `AetherCouplings.spin2SpeedSq_eq_one_iff`,
    `AetherCouplings.spin1SpeedSq_luminal_graviton`,
    `AetherCouplings.spin0SpeedSq_luminal_graviton`, `AetherCouplings.effectiveNewtonG`,
    `AetherCouplings.effectiveNewtonG_eq_bare_iff`
72. PhyslibAlpha/Relativity/Modified/MassiveGravity/FierzPauli.lean —
    `FierzPauliTheory`, `FierzPauliTheory.ghostFree`, `minkowskiContractionSq`,
    `FierzPauliTheory.lagrangian`, `FierzPauliTheory.massTensor`,
    `FierzPauliTheory.massTensor_trace`, `FierzPauliTheory.massTensor_trace_tuned`,
    `FierzPauliTheory.longitudinal_time_ghost_free_iff`,
    `FierzPauliTheory.traceless_of_zero_trace_source`
73. PhyslibAlpha/Relativity/Modified/MassiveGravity/VDVZ.lean — `grPropagatorCoupling`,
    `massivePropagatorCoupling`, `staticSource`, `vdvz_static_ratio`,
    `vdvz_light_deflection_ratio`
74. PhyslibAlpha/Relativity/Modified/MassiveGravity/DRGT.lean — `DRGTTheory`, `traceK`,
`traceKSq`, `traceKCube`, `elemSymm0`, `elemSymm1`, `elemSymm2`, `elemSymm3`, `elemSymm_isotropic3`,
    `DRGTTheory.potential`, `DRGTTheory.potential_vacuum_zero`
75. PhyslibAlpha/Relativity/Modified/MOND.lean — `MONDTheory`, `newtonianAcceleration`,
    `MONDTheory.deepMONDAcceleration`, `MONDTheory.Relation`, `MONDTheory.newtonian_limit`,
    `MONDTheory.deepMONDAcceleration_sq`, `MONDTheory.flat_rotation`, `newtonian_velocity_ne`,
    `simpleMu`, `standardMu`, `simpleMu_bounds`,
    `norm_pairGravityAcceleration_eq_newtonianAcceleration`
76. PhyslibAlpha/Relativity/Modified/TeVeS.lean — `TeVeSMetric`, `TeVeSMetric.metric`,
    `TeVeSMetric.metricInv`, `TeVeSMetric.symm`, `TeVeSMetric.lorentzian`,
    `TeVeSMetric.spatial`, `TeVeSMetric.mul_inv`, `TeVeSMetric.inv_mul`,
    `TeVeSMetric.metricTensor`
77. PhyslibAlpha/Relativity/Modified/MOG.lean — `MOGTheory`,
    `MOGTheory.yukawaEnhancementFactor`, `MOGTheory.potential`,
    `MOGTheory.yukawaEnhancementFactor_zero`, `MOGTheory.yukawaEnhancementFactor_alpha_zero`,
    `MOGTheory.yukawaEnhancementFactor_mu_zero`, `MOGTheory.yukawaEnhancementFactor_bounds`,
    `MOGTheory.yukawaEnhancementFactor_tendsto_atTop`
78. PhyslibAlpha/Relativity/Modified/PPNParameters.lean — `PPNParameters`,
    `IsFullyConservative`, `IsSemiconservative`, `IsFullyConservative.isSemiconservative`,
    `grPPN`, `bransDickePPN`, `fRMetricPPN`, `nordstromPPN`, `grPPN_isFullyConservative`,
    `bransDickePPN_isFullyConservative`, `bransDickePPN_zero_eq_fRMetricPPN`,
    `lightDeflectionFactor`, `shapiroDelayFactor`, `perihelionPrecessionFactor`,
    `nordtvedtParameter`, `lightDeflectionFactor_gr`, `lightDeflectionFactor_nordstrom`,
    `lightDeflectionFactor_fRMetric`, `perihelionPrecessionFactor_gr`,
    `perihelionPrecessionFactor_nordstrom`, `perihelionPrecessionFactor_bransDicke`,
    `nordtvedtParameter_gr`, `nordtvedtParameter_bransDicke`, `nordtvedtParameter_fRMetric`,
    `cassini_deviation_bransDickePPN`
79. PhyslibAlpha/Relativity/Metrics/CurvatureBridge.lean — `CoordinateMetric.loweredRiemann`,
    `CoordinateMetric.riemann_skew_last`, `CoordinateMetric.loweredRiemann_skew_last`,
    `CoordinateMetric.toRiemannTensor`, `ricci_lowered`,
    `CoordinateMetric.ricci_toRiemannTensor`, `CoordinateMetric.ricciScalar_toRiemannTensor`,
    `CoordinateMetric.einstein_toRiemannTensor`, `CoordinateMetric.toRiemannTensorConst`,
    `CoordinateMetric.toRiemannTensorConst_eq_flat`,
    `CoordinateMetric.ricci_toRiemannTensorConst`,
    `CoordinateMetric.ricciScalar_toRiemannTensorConst`,
    `CoordinateMetric.einstein_toRiemannTensorConst`
80. PhyslibAlpha/Relativity/Modified/MassiveGravity/Basic.lean — `MassiveGravityTheory`,
    `MassiveGravityTheory.massSq`, `MassiveGravityTheory.propagatorCoupling`,
    `MassiveGravityTheory.generalRelativity`, `MassiveGravityTheory.fierzPauli`
81. PhyslibAlpha/Relativity/Tensors/PerfectFluidStressEnergy.lean — `perfectFluidStressEnergy`
82. PhyslibAlpha/Relativity/General/FrameKretschmann.lean —
    `RiemannTensor.frameKretschmannScalar`
83. PhyslibAlpha/Relativity/Metrics/CovariantDerivTensor2.lean —
    `InitialData.covariantDerivTensor2`
84. PhyslibAlpha/Cosmology/FLRW/Curvature.lean — `FLRWSpacetime.ricciTensor`,
    `FLRWSpacetime.ricciScalar`, `FLRWSpacetime.einsteinTensor`
85. PhyslibAlpha/Relativity/Metrics/CoordDeriv.lean — `coordDeriv_eq_spaceTime_deriv`
86. PhyslibAlpha/Relativity/Modified/EinsteinCartan/Contorsion.lean —
    `EinsteinCartanData.MetricCompatible`, `EinsteinCartanData.connection_unique`,
    `MetricCompatible`, `leviCivitaOfDeriv`, `leviCivitaOfDeriv_compatible`, `contorsion`,
    `contorsion_antisymm_outer`, `contorsion_torsion`, `connection_unique`
87. PhyslibAlpha/Relativity/Modified/EinsteinCartan/ModifiedTorsion.lean — `modifiedTorsion`,
    `invertModifiedTorsion`
88. PhyslibAlpha/Relativity/Modified/Lovelock/Contract5.lean — `lovelockContract5`,
    `lovelockContract5_eq_kronecker_sum`, `lovelockContract5_eq_zero_of_lt`,
    `lovelockContract5_eq_neg_eight_lanczos`, `bach_lanczos_lt_five`, `bach_lanczos_four`
89. PhyslibAlpha/Relativity/Modified/Lovelock/ConstantCurvature.lean — `constantCurvature`,
    `gaussBonnetScalar_constantCurvature_four`, `lanczosTensor_constantCurvature_five`

## References

1. Units API map — Physlib/Units/API-map.md
2. R. M. Wald, *General Relativity*, University of Chicago Press, 1984.
3. C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation*, W. H. Freeman, 1973.
4. S. M. Carroll, *Lecture Notes on General Relativity*, 1997, https://arxiv.org/abs/gr-qc/9712019.
5. C. M. Will, *Theory and Experiment in Gravitational Physics*, 2nd ed., Cambridge University
   Press, 2018.
6. C. M. Will, *The Confrontation between General Relativity and Experiment*, *Living Reviews in
   Relativity* 17 (2014), 4, doi:10.12942/lrr-2014-4.
7. B. Bertotti, L. Iess, and P. Tortora, *A Test of General Relativity Using Radio Links with the
   Cassini Spacecraft*, *Nature* 425 (2003), 374–376, doi:10.1038/nature01997.
8. B. Famaey and S. S. McGaugh, *Modified Newtonian Dynamics (MOND): Observational Phenomenology and
   Relativistic Extensions*, *Living Reviews in Relativity* 15 (2012), 10, doi:10.12942/lrr-2012-10.
