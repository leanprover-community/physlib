# General Relativity and Modified Gravity

## Abstract (Alpha)

General Relativity models gravitation as the pseudo-Riemannian geometry of a four-dimensional
spacetime manifold carrying a Lorentzian metric of signature (-, +, +, +) governed by the Einstein
field equations. This API formalizes the coordinate differential-geometry pipeline from a spacetime
metric and its analytical inverse through the Levi-Civita Christoffel symbols, Riemann curvature,
Ricci tensor, Ricci scalar, and Einstein tensor, together with covariant conservation, geodesic
dynamics, the ADM 3+1 initial-value formulation, linearized gravitational waves, Newton's
gravitational constant in arbitrary and natural unit systems, exact black-hole and cosmological
solutions (Minkowski, Schwarzschild, interior Schwarzschild, Schwarzschild-de Sitter,
Reissner-Nordström, Kerr, and Friedmann-Lemaître-Robertson-Walker), and sixteen modified or
alternative theories of gravitation.

## Content (Alpha)

### Metric geometry, curvature, differential pipeline, and Einstein field equations

A pseudo-Riemannian spacetime metric at a point is represented by a symmetric rank-2 matrix paired
with its two-sided inverse, with the four-dimensional Minkowski metric η = diag(-1, 1, 1, 1) as the
flat reference background and conformal rescalings g ↦ Ω g preserving invertibility. [1] Algebraic
(1, 3) Riemann curvature tensors satisfy antisymmetry in their first and last index pairs and the
first Bianchi identity, and contract with the inverse metric to the symmetric Ricci tensor and
scalar curvature. [2] The coordinate partial-derivative pipeline computes the Levi-Civita
Christoffel symbols directly from first partial derivatives of the metric, constructs the Riemann
curvature tensor, Ricci tensor, Ricci scalar, and Einstein tensor, and establishes that any
spatially and temporally constant metric has identically vanishing connection and curvature. [3]
From any metric and curvature tensor, the Einstein tensor G_{ij} = R_{ij} - ½ R g_{ij} is symmetric,
its metric trace in n dimensions is (1 - n / 2) R, and vacuum Einstein equations are equivalent to
Ricci flatness in dimensions n ≠ 2, while contracted second-Bianchi curvature derivatives ensure
covariant divergence-freeness of the Einstein tensor and stress-energy conservation. [4][5]
Coordinate-free covariant differentiation on general smooth manifolds is a planned extension. [TODO]

### Geodesics, ADM 3+1 decomposition, linearized gravity, and physical constants

Test-particle trajectories satisfy the second-order geodesic differential equation driven by the
Christoffel symbols, whose first-order phase-space vector field is smooth and admits unique local
solutions by the Picard-Lindelöf theorem, reducing to straight lines when the connection vanishes.
[6] In the Arnowitt-Deser-Misner 3+1 initial-value formulation, spatial slices carry a Riemannian
3-metric and symmetric extrinsic curvature tensor K_{ij} subject to the Hamiltonian and momentum
constraint equations, which simplify on time-symmetric (K_{ij} = 0) and maximal (tr K = 0) slices
and distinguish flat vacuum data from non-trivial squeezed initial data. [7] Around the Minkowski
background g = η + h, first-order perturbation theory defines the trace-reversed perturbation
h̄_{ij} = h_{ij} - ½ η_{ij} h, the linearized Christoffel symbols, Riemann tensor, Ricci tensor,
d'Alembertian wave operator □_η, and Einstein tensor, and proves that in Lorenz gauge the
linearized Einstein tensor reduces to -½ □_η h̄_{ij} and vanishes on plane gravitational waves. [8]
Newton's universal gravitational constant G carries dimension L³ M⁻¹ T⁻² and CODATA 2022 SI value
6.67430 × 10⁻¹¹ m³ kg⁻¹ s⁻², and admits natural and geometric unit systems in which c, G, and k_B
are simultaneously equal to 1 {1}. [9]

### Exact black-hole and cosmological spacetimes

For flat Minkowski spacetime, the metric tensor package has vanishing off-diagonal inverse
components, and its Ricci tensor, scalar curvature, and Einstein tensor vanish identically. [10] A
general static spherically symmetric metric with lapse profile A(r) and radial profile B(r) = A(r)⁻¹
has explicit Christoffel symbols and diagonal/off-diagonal Ricci components evaluated through the
coordinate differential pipeline {2}. [11] Specializing to the Schwarzschild exterior metric with
f(r) = 1 - 2 M / r yields the orthonormal Weyl electric tidal curvature frame, Kretschmann scalar
48 M² / r⁶, and exact metric-derivative Christoffel and Riemann components, while the interior
incompressible fluid sphere exhibits the Tolman-Oppenheimer-Volkoff pressure profile and Buchdahl
compactness bound r_s < (8 / 9) R. [12][13][14] Including a cosmological constant Λ in the
Schwarzschild-de Sitter (Kottler) metric f(r) = 1 - 2 M / r - Λ r² / 3 yields constant-curvature
de Sitter frame components, Kretschmann invariant 48 M² / r⁶ + 8 Λ² / 3, frame Bianchi
conservation, and full coordinate-pipeline verification of R_{ij} = Λ g_{ij}, R = 4 Λ, and
G_{ij} = -Λ g_{ij}. [15][16][17] Adding electric charge yields the Reissner-Nordström electrovacuum
metric f(r) = 1 - r_s / r + r_Q² / r², the radial Coulomb-Maxwell field strength tensor F_{ab}, and
the trace-free electromagnetic stress-energy tensor satisfying the Einstein-Maxwell equations
through the coordinate pipeline. [18] Rotating black holes are represented by the axisymmetric Kerr
metric in Boyer-Lindquist coordinates (t, r, θ, φ) with spin a, polynomial functions
Σ = r² + a² cos²θ and Δ = r² - r_s r + a², exact block inverse metric, all 64 Levi-Civita
Christoffel symbols, and full differential pipeline verification that the Ricci tensor, Ricci
scalar, and Einstein tensor vanish identically in vacuum {2}{3}. [19][20][21] Homogeneous and
isotropic cosmology is formalized through the Friedmann-Lemaître-Robertson-Walker metric with scale
factor a(t) and spatial curvature k, evaluating all FLRW Christoffel symbols, Ricci components,
scalar curvature, and Friedmann Einstein equations through the coordinate pipeline. [22]

### Scalar-tensor, higher-curvature, and screening gravity theories

Historically, Nordström's relativistic scalar gravity restricts the spacetime metric to the
conformally flat form φ(x)² η_{μν}, preserving null cones (producing zero gravitational light
deflection) while the differential pipeline evaluates its Christoffel symbols and proves the
four-dimensional Einstein-Fokker curvature identity R = -6 □_η φ / φ³ and its equivalence to the
nonlinear scalar wave equation □_η φ = -4 π φ³ T. [23] Brans-Dicke scalar-tensor gravity couples a
dynamical scalar field φ to curvature with dimensionless parameter ω, yielding the post-Newtonian
parameter γ = (1 + ω) / (2 + ω) approaching the General Relativity value 1 under the Cassini bound
ω > 40000, the effective scalar coupling 1 / (2 ω + 3), and the ω = 0 metric f(R) value γ = 1 / 2.
[24] Non-linear f(R) gravity replaces the Einstein-Hilbert density R with a smooth function f(R),
modifying the field equations and their four-dimensional trace while supplying the Starobinsky
R + α R² inflationary potential, positive scalaron mass squared, and Einstein-frame plateau. [25]
By Ostrogradsky's theorem, non-degenerate higher-derivative Lagrangians possess a Hamiltonian
linear in an unconstrained momentum that is unbounded above and below unless the kinetic matrix is
degenerate. [26] Cubic Galileon scalar-tensor theories achieve second-order equations of motion
because the variation of the cubic action under constant-gradient shifts is a total derivative,
whereas shift symmetry forbids a non-trivial potential term. [27] Chameleon scalar-tensor theories
feature an effective mass squared that grows monotonically with ambient matter density, shrinking
the Yukawa interaction range and suppressing fifth forces for screened bodies via the thin-shell
factor ΔR / R. [28]

### Torsion, teleparallel, higher-dimensional, Lorentz-violating, massive, and PPN formalisms

Einstein-Cartan-Sciama-Kibble theory relaxes the torsion-free constraint on the affine connection,
proving that any metric-compatible connection decomposes uniquely into the Levi-Civita connection
plus the contorsion tensor built from torsion, and inverting the algebraic Cartan modified torsion
tensor in terms of spin density. [29] In the Teleparallel Equivalent of General Relativity (TEGR),
gravity is carried by the curvature-free Weitzenböck connection of an orthonormal tetrad and its
torsion superpotential; on flat FLRW cosmologies the Levi-Civita scalar curvature satisfies
R_LC = -T + B with torsion scalar T = 6 H² and total-divergence boundary term B, while non-linear
f(T) = T + F(T) extensions modify the Friedmann expansion equation. [30] Lovelock higher-curvature
gravity constructs the quadratic Gauss-Bonnet scalar 𝒢 = R² - 4 R^a_b R^b_a + R^{cd}_{ab} R^{ab}_{cd}
and Lanczos variation tensor H^i_j, proves via the five-index generalized Kronecker contraction
L^i_j = -8 H^i_j and the pigeonhole principle that H^i_j vanishes identically in dimension n ≤ 4,
and contrasts the four-dimensional topological invariant with the non-vanishing five-dimensional
variation. [31] Five-dimensional Kaluza-Klein theory unifies four-dimensional General Relativity and
Maxwell electromagnetism inside a 5D metric G_{AB} built from g_{μν}, the gauge potential A_μ, and a
dilaton φ, establishing the exact 5D inverse metric, unit-determinant upper-triangular veilbein
congruence factorization, diffeomorphism-to-U(1) gauge equivalence under compact-circle shifts,
four-dimensional Maxwell stress-energy tracelessness, and the Kaluza miracle R^{(5)} = R^{(4)} -
¼ F_{ab} F^{ab}. [32] Einstein-Aether theory breaks local Lorentz boost invariance with a
unit-timelike vector field u^a (g_{ab} u^a u^b = -1) governed by four Jacobson-Mattingly couplings
(c₁, c₂, c₃, c₄), yielding explicit squared propagation speeds for the spin-2, spin-1, and spin-0
modes, the GW170817 luminal graviton constraint s₂² = 1 ↔ c₁ + c₃ = 0, and the renormalized
Newtonian constant G_N = G_bare / (1 - (c₁ + c₄) / 2). [33] Fierz-Pauli and de Rham-Gabadadze-Tolley
(dRGT) massive gravity formalize the Lorentz-invariant mass term -(m² / 4)(h_{ab} h^{ab} + α h²),
prove that the ghost-free tuning α = -1 uniquely eliminates the sixth Boulware-Deser longitudinal
mode and forces vacuum tracelessness h = 0, derive the van Dam-Veltman-Zakharov (vDVZ) 4 / 3 static
coupling ratio and 3 / 4 light-deflection discontinuity, and construct the ghost-free dRGT potential
from elementary symmetric polynomials of K. [34] Galactic rotation-curve alternatives without
non-baryonic dark matter are represented by Milgrom's Modified Newtonian Dynamics (MOND), which
interpolates between the Newtonian regime a ≫ a₀ and the deep-MOND regime a = √(a_N a₀) to produce
asymptotically flat circular velocities v⁴ = G M a₀, by Bekenstein's relativistic
Tensor-Vector-Scalar (TeVeS) disformal physical metric and its exact analytical inverse, and by
Moffat's Scalar-Tensor-Vector Gravity (MOG) Yukawa-modified acceleration factor. [35][36][37]
Finally, the Will-Nordtvedt Parameterized Post-Newtonian (PPN) formalism unifies solar-system tests
across metric theories via ten dimensionless parameters (γ, β, ξ, α₁, α₂, α₃, ζ₁, ζ₂, ζ₃, ζ₄),
classifying fully conservative and semiconservative theories, embedding General Relativity,
Brans-Dicke, metric f(R), and Nordström gravity, and evaluating light deflection, Shapiro time
delay, perihelion precession, and the Nordtvedt Strong Equivalence Principle violation parameter
η_N {3}{4}. [38]

## Lean References

1. PhyslibAlpha/Relativity/General/Basic.lean — `Tensor2`, `IsSymm`, `isSymm_zero`, `isSymm_one`,
   `eta4`, `eta4_symm`, `eta4_mul_self`, `MetricTensor`, `MetricTensor.ginv_symm`, `conformalG`,
   `conformalGinv`, `conformalMetric`
2. PhyslibAlpha/Relativity/General/Curvature.lean — `RiemannTensor`, `skew_first`,
   `zero_of_repeated_first`, `zero_of_repeated_last`, `swap_mixed`, `flat`, `ricci`, `ricci_symm`,
   `ricci_of_diag`, `ricci_flat`, `scalarCurv`
3. PhyslibAlpha/Relativity/General/Pipeline.lean — `pd`, `pd_const`, `pd_congr`, `christoffel`,
   `riemann`, `ricciOf`, `scalarOf`, `einsteinOf`, `christoffel_const`, `riemann_const`
4. PhyslibAlpha/Relativity/General/Einstein.lean — `metricTrace`, `sum_ginv_mul_g`,
   `metricTrace_mul_g`, `einstein`, `einstein_symm`, `metricTrace_einstein`,
   `scalarCurv_eq_zero_of_einstein_eq_zero`, `vacuum_iff_ricci_flat`, `einsteinSpace_iff`
5. PhyslibAlpha/Relativity/General/Conservation.lean — `CurvDeriv`, `CurvDeriv.dEinstein`,
   `divergence`, `sum_eta_mul`, `divergence_combination`, `divergence_einstein_eq_zero`,
   `combination_conserved_iff`
6. PhyslibAlpha/Relativity/General/Geodesics.lean — `Christoffel`, `geodesicAccel`,
   `geodesicField`, `contDiffAt_geodesicField`, `geodesic_ivp_exists`,
   `geodesic_ivp_exists_curve`, `geodesic_ivp_unique`, `flat_geodesic`
7. PhyslibAlpha/Relativity/General/InitialValue.lean — `InitialData`, `momConstraint`, `ham`,
   `IsVacuumData`, `ham_eq_scalarCurv_of_K_zero`, `ham_eq_of_trace_zero`, `euclid3`,
   `flatData_isVacuum`, `squeezedData_ham`
8. PhyslibAlpha/Relativity/General/Linearized.lean — `pd_congr_nhds`, `pd_eq_fderiv`, `pd_comm`,
   `hTrace`, `traceReversed`, `traceReversed_trace`, `traceReversed_involutive`, `linChristoffel`,
   `linChristoffel_symm`, `linRiemann`, `boxEta`, `linRicci`, `linEinstein`,
   `linRiemann_gauge_invariant`, `linEinstein_gauge_invariant`, `linEinstein_lorenz_gauge`,
   `ttWave`, `ttWave_linEinstein_zero`, `newtonianPerturb`, `newtonianPerturb_poisson_iff`
9. PhyslibAlpha/Relativity/General/GravitationalConstant.lean — `GravitationalConstant`,
   `gravitationalConstantDimension`, `gravitationalConstant`, `gravitationalConstant_in_SI`,
   `toWithDim`, `toWithDim_scaleUnit`, `exists_units_c_G_kB_eq_one`
10. PhyslibAlpha/Relativity/General/Minkowski.lean — `minkowski`, `minkowski_ginv_offdiag`,
    `minkowski_ricci_eq_zero`, `minkowski_scalarCurv_eq_zero`, `minkowski_einstein_eq_zero`,
    `minkowski_vacuum_iff_ricci_flat`
11. PhyslibAlpha/Relativity/General/StaticSpherical.lean — `staticSphericalMetric`,
    `staticSphericalMetricInv`, `staticSphericalMetric_symm`, `staticSphericalMetric_mul_inv`,
    `staticSphericalMetricTensor`, `staticSphericalG`, `christoffel_eq_staticSphericalG`,
    `staticSphericalDG`
12. PhyslibAlpha/Relativity/General/Schwarzschild/Frame.lean — `electricPart`,
    `electricPart_symm`, `electricPart_trace`, `frameSqSum`, `schwarzschild`, `ricci_eq_zero`,
    `frameSqSum_eq`, `kretschmann_scalar`, `weyl_purely_electric`, `schwarzschildMetric`
13. PhyslibAlpha/Relativity/General/Schwarzschild/Metric.lean — `schwarzschildF`,
    `schwarzschildMetric_rr`, `gammaTtr_from_metric`, `gammaRrr_from_metric`,
    `riemann_t_rtr_from_metric`, `electric_r_from_metric`, `electricPart_from_metric`,
    `riemann_components_from_metric`
14. PhyslibAlpha/Relativity/General/Schwarzschild/IncompressibleSphere.lean —
    `IncompressibleSphere`, `rs`, `chia`, `cosChia`, `cosChia_sq`, `cosChia_pos`,
    `cosChia_lt_one`, `rs_div_Ra`
15. PhyslibAlpha/Relativity/General/SchwarzschildDeSitter/Frame.lean — `deSitterPart`,
    `sdsFrameSqSum`, `sdsFrameSqSum_eq`, `kretschmann_sds`, `sdsFrameComp`, `sdsRic`,
    `weylRic_zero`, `sds_frame_bianchi`, `sds_frame_einstein_conserved`
16. PhyslibAlpha/Relativity/General/SchwarzschildDeSitter/Metric.lean — `sdsF`, `sdsHalf`,
    `sdsF_zero_lambda`, `deriv_sdsF`, `gammaTtr_sds`, `gammaRrr_sds`, `weyl_rr_sds`,
    `weyl_thetatheta_sds`, `weyl_phiphi_sds`
17. PhyslibAlpha/Relativity/General/SchwarzschildDeSitter/Pipeline.lean — `sdsMetric`,
    `sdsMetricInv`, `sdsG`, `sdsDGFull`, `christoffel_eq_sdsG`, `riemann_sds_components`,
    `ricciOf_sds`, `scalarOf_sds`, `einsteinOf_sds`, `ricciOf_schwarzschild`,
    `scalarOf_schwarzschild`, `einsteinOf_schwarzschild`
18. PhyslibAlpha/Relativity/General/ReissnerNordstrom/Basic.lean — `rnF`, `rnMetric`,
    `rnMetricInv`, `rnF_zero_charge`, `maxwellF`, `maxwellF_antisymm`, `maxwellStressEnergy`
19. PhyslibAlpha/Relativity/General/Kerr/Basic.lean — `sigma`, `delta`, `bigB`, `bigB_eq_sigma`,
    `kerr_tphi_det_id`, `kerrMetric`, `kerrMetricInv`, `kerrMetric_symm`,
    `kerrMetricInv_mul_kerrMetric`, `kerrMetric_mul_kerrMetricInv`, `kerrMetricTensor`,
    `kerrMetric_zero_spin`
20. PhyslibAlpha/Relativity/General/Kerr/Christoffel.lean — `kerrMetricD`, `pd_kerrMetric_eq`,
    `kerrG`, `kerrG_symm`, `christoffel_kerr_eq`, `eventually_christoffel_kerr_eq`, `kerrTr`,
    `sum_kerrG_trace`
21. PhyslibAlpha/Relativity/General/Kerr/Vacuum.lean — `pd_kerrTr_11`, `pd_kerrTr_21`,
    `pd_kerrTr_12`, `pd_kerrTr_22`, `ricciOf_kerr_eq_zero`, `scalarOf_kerr_eq_zero`,
    `einsteinOf_kerr_eq_zero`
22. PhyslibAlpha/Relativity/General/FLRW/Pipeline.lean — `flrwMetric`, `flrwMetricInv`,
    `flrwMetric_symm`, `flrwMetric_mul_inv`, `flrwMetricTensor`, `flrwG`, `flrwDG`,
    `christoffel_eq_flrwG`, `scalarOf_flrw`
23. PhyslibAlpha/Relativity/General/Modified/Nordstrom.lean — `nordstromMetric`,
    `nordstromMetricInv`, `nordstromMetricTensor`, `NullVector`, `nullVector_conformal_iff`,
    `light_deflection_zero`, `nordstromG`, `christoffel_nordstrom_eq`, `scalarOf_nordstrom`,
    `einsteinFokker_iff`
24. PhyslibAlpha/Relativity/General/Modified/BransDicke.lean — `gamma`, `gamma_eq_one_sub`,
    `gamma_bounds`, `cassini_deviation`, `gamma_tendsto_atTop`, `fR_gamma`, `coupling`,
    `coupling_eq_one_add`, `coupling_bounds`, `coupling_pole`
25. PhyslibAlpha/Relativity/General/Modified/FRGravity.lean — `fieldEqn`, `linear_is_einstein`,
    `trace_fieldEqn`, `trace_fieldEqn_four`, `starobinskyPotential`, `phi_inverse`,
    `potential_eq`, `mass_sq`, `not_gr`, `einsteinFrameV`, `starobinsky_einsteinFrame`,
    `starobinsky_plateau`
26. PhyslibAlpha/Relativity/General/Modified/Ostrogradsky.lean — `kineticMatrix`,
    `kineticMatrix_degenerate`, `hamiltonian`, `hamiltonian_add`, `unbounded_below`,
    `kinetic_bounded`, `kinetic_zero_iff`
27. PhyslibAlpha/Relativity/General/Modified/Galileon.lean — `cubic_total_derivative`,
    `shift_total_derivative`, `shift_forbids_potential`
28. PhyslibAlpha/Relativity/General/Modified/ChameleonScreening.lean — `chameleonMassSq`,
    `chameleonMass`, `chameleonMass_mono`, `range`, `range_antitone`, `chameleon_range_shrinks`,
    `yukawaRatio`, `exp_neg_one_lt_half`, `yukawaRatio_lt_half`, `thinShell`, `screeningFactor`,
    `thin_shell_suppressed`
29. PhyslibAlpha/Relativity/General/Modified/EinsteinCartan.lean — `Conn`, `torsion`,
    `torsion_antisymm`, `MetricCompatible`, `leviCivitaOfDeriv`, `leviCivitaOfDeriv_compatible`,
    `contorsion`, `contorsion_antisymm_outer`, `contorsion_torsion`, `connection_unique`,
    `modifiedTorsion`, `invertModifiedTorsion`, `modifiedTorsion_invert`
30. PhyslibAlpha/Relativity/General/Modified/Teleparallel.lean — `weitzenbockConn`,
    `weitzenbockTorsion`, `weitzenbockTorsion_eq`, `weitzenbockTorsion_antisymm`,
    `superpotential`, `superpotential_antisymm`, `torsionScalar`, `flrwTetrad`, `flrwTetradInv`,
    `flrwTetrad_mul_inv`, `flrwWeitzenbock_hubble`, `flrwTorsionScalar`, `flrwBoundaryTerm`,
    `scalarOf_flrw_flat_eq_neg_torsion_add_boundary`, `fTFriedmannLHS`, `fTFriedmannLHS_tegr`,
    `fTFriedmannLHS_quadratic`
31. PhyslibAlpha/Relativity/General/Modified/Lovelock.lean — `genKronecker`,
    `genKronecker_eq_zero_of_lt`, `AlgCurvature`, `AlgCurvature.ricciMixed`,
    `AlgCurvature.scalarCurv`, `AlgCurvature.ricciSq`, `AlgCurvature.riemannSq`,
    `AlgCurvature.gaussBonnetScalar`, `AlgCurvature.gaussBonnetTensor`, `lovelockContract5`,
    `lovelockContract5_eq_kronecker_sum`, `lovelockContract5_eq_zero_of_lt`,
    `lovelockContract5_eq_neg_eight_gaussBonnet`, `gaussBonnetTensor_eq_zero_of_lt_five`,
    `gaussBonnetTensor_four_eq_zero`, `constCurv`, `gaussBonnetScalar_constCurv_four`,
    `gaussBonnetTensor_constCurv_five`
32. PhyslibAlpha/Relativity/General/Modified/KaluzaKlein.lean — `potExt`, `metric4Ext`, `kkMetric`,
    `kkMetric_symm`, `potUp`, `kkMetricInv`, `kkMetricInv_mul_kkMetric`, `kkMetricInv_symm`,
    `kkMetric_mul_kkMetricInv`, `kkMetricTensor`, `kkTriangular`, `kkBlockDiag`,
    `det_kkTriangular`, `kkMetric_eq_triangular_conj`, `kkGaugeJacobian`, `det_kkGaugeJacobian`,
    `kkGaugeJacobian_pullback`, `maxwellF2`, `maxwellStressEnergy`,
    `maxwellStressEnergy_trace_zero`, `kkRicci44`, `kkRicci4D`, `kkScalar5D`, `kkScalar5D_eq`,
    `kkEinstein4D_eq_zero_iff`
33. PhyslibAlpha/Relativity/General/Modified/EinsteinAether.lean — `AetherCouplings`,
    `AetherCouplings.c13`, `AetherCouplings.c14`, `AetherCouplings.c123`,
    `AetherCouplings.c1Sub3`, `IsUnitTimelike`, `minkowskiRestAether`,
    `minkowskiRestAether_unitTimelike`, `linUnitTimelike_time_zero`, `kineticTensor`,
    `aetherKineticInvariant`, `aetherLagrangian`, `aetherLagrangian_on_shell`, `spin2SpeedSq`,
    `spin1SpeedSq`, `spin0SpeedSq`, `spin2SpeedSq_eq_one_iff`, `spin1SpeedSq_luminal_graviton`,
    `spin0SpeedSq_luminal_graviton`, `effectiveNewtonG`, `effectiveNewtonG_eq_bare_iff`
34. PhyslibAlpha/Relativity/General/Modified/MassiveGravity.lean — `hTraceEta`, `hContractionSq`,
    `fierzPauliLagrangian`, `fpMassTensor`, `fpMassTensor_trace`, `fpMassTensor_trace_tuned`,
    `longitudinal_time_ghost_free_iff`, `fp_traceless_of_zero_trace_source`, `stressTrace`,
    `grPropagatorCoupling`, `massivePropagatorCoupling`, `staticSource`, `vdvz_static_ratio`,
    `vdvz_light_deflection_ratio`, `trK1`, `trK2`, `trK3`, `elemSymm0`, `elemSymm1`, `elemSymm2`,
    `elemSymm3`, `elemSymm_isotropic3`, `dRGTPotential`, `dRGTPotential_vacuum_zero`
35. PhyslibAlpha/Relativity/General/Modified/MOND.lean — `newtonAccel`, `deepAccel`, `Relation`,
    `newtonian_limit`, `deep_accel_sq`, `flat_rotation`, `newtonian_velocity_ne`, `simpleMu`,
    `standardMu`, `simpleMu_bounds`
36. PhyslibAlpha/Relativity/General/Modified/TeVeS.lean — `metric`, `metricInv`, `metric_symm`,
    `metric_lorentzian`, `metric_spatial`, `metric_mul_inv`, `metricInv_mul`, `metricTensor`
37. PhyslibAlpha/Relativity/General/Modified/MOG.lean — `factor`, `potential`, `factor_zero`,
    `factor_alpha_zero`, `factor_mu_zero`, `factor_bounds`, `factor_tendsto_atTop`
38. PhyslibAlpha/Relativity/General/Modified/PPN.lean — `PPNParameters`, `IsFullyConservative`,
    `IsSemiconservative`, `IsFullyConservative.isSemiconservative`, `grPPN`, `bransDickePPN`,
    `fRMetricPPN`, `nordstromPPN`, `grPPN_isFullyConservative`,
    `bransDickePPN_isFullyConservative`, `bransDickePPN_zero_eq_fRMetricPPN`,
    `lightDeflectionFactor`, `shapiroDelayFactor`, `perihelionPrecessionFactor`,
    `nordtvedtParameter`, `lightDeflectionFactor_gr`, `lightDeflectionFactor_nordstrom`,
    `lightDeflectionFactor_fRMetric`, `perihelionPrecessionFactor_gr`,
    `perihelionPrecessionFactor_nordstrom`, `perihelionPrecessionFactor_bransDicke`,
    `nordtvedtParameter_gr`, `nordtvedtParameter_bransDicke`, `nordtvedtParameter_fRMetric`,
    `cassini_deviation_bransDickePPN`

## References

1. Units API map — Physlib/Units/API-map.md
2. R. M. Wald, *General Relativity*, University of Chicago Press, 1984.
3. C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation*, W. H. Freeman, 1973.
4. C. M. Will, *Theory and Experiment in Gravitational Physics*, 2nd ed., Cambridge University
   Press, 2018.
