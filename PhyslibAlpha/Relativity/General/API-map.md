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

A rank-2 covariant tensor is represented as an n × n matrix of components [1], paired with a
nondegenerate metric carrying its explicit two-sided inverse [2], with the four-dimensional
Minkowski metric η = diag(-1, 1, 1, 1) as the flat reference background [3] and conformal
rescalings g ↦ Ω g preserving invertibility [4]. Algebraic (1, 3) Riemann curvature tensors satisfy
antisymmetry in their first and last index pairs and the first Bianchi identity [5], and contract
with the inverse metric to the symmetric Ricci tensor [6] and scalar curvature defined as its metric
trace [7][8]. The coordinate partial-derivative pipeline computes the Levi-Civita Christoffel
symbols directly from first partial derivatives of a bundled coordinate metric field, constructs the
Riemann curvature tensor, Ricci tensor, Ricci scalar, and Einstein tensor, and establishes that any
spatially and temporally constant metric has identically vanishing connection and curvature [9]. From
any metric and curvature tensor, the Einstein tensor G_{{ij}} = R_{{ij}} - ½ R g_{{ij}} is symmetric, its
metric trace in n dimensions is (1 - n / 2) R, and vacuum Einstein equations are equivalent to
Ricci flatness in dimensions n ≠ 2 [10], while contracted second-Bianchi curvature derivatives
ensure covariant divergence-freeness of the Einstein tensor and stress-energy conservation [11].
Coordinate-free covariant differentiation on general smooth manifolds is a planned extension. [TODO]

### Geodesics, ADM 3+1 decomposition, linearized gravity, and physical constants

Test-particle trajectories satisfy the second-order geodesic differential equation driven by a
bundled geodesic system, whose first-order phase-space vector field is smooth and admits unique
local solutions by the Picard-Lindelöf theorem, reducing to straight lines when the connection
vanishes [12]. In the Arnowitt-Deser-Misner 3+1 initial-value formulation, spatial slices carry a
Riemannian 3-metric and symmetric extrinsic curvature tensor K_{{ij}} subject to the Hamiltonian and
momentum constraint equations, which simplify on time-symmetric (K_{{ij}} = 0) and maximal (tr K = 0)
slices and distinguish flat vacuum data from non-trivial squeezed initial data [13]. Around the
Minkowski background g = η + h, first-order perturbation theory defines the trace-reversed
perturbation h̄_{{ij}} = h_{{ij}} - ½ η_{{ij}} h and wave operator □_η [14], the linearized Christoffel
symbols, Riemann tensor, Ricci tensor, and Einstein tensor with diffeomorphism gauge invariance
[15], proves that in Lorenz gauge the linearized Einstein tensor reduces to -½ □_η h̄_{{ij}} [16],
verifies that transverse-traceless gravitational waves solve the linearized vacuum equations [17],
and derives Poisson's equation in the weak-field Newtonian limit [18]. Newton's universal
gravitational constant G carries dimension L³ M⁻¹ T⁻² and CODATA 2022 SI value
6.67430 × 10⁻¹¹ m³ kg⁻¹ s⁻², and admits natural and geometric unit systems in which c, G, and k_B
are simultaneously equal to 1 {{1}}. [19]

### Exact black-hole and cosmological spacetimes

Flat Minkowski spacetime has vanishing Ricci tensor, scalar curvature, and Einstein tensor both
algebraically and through the coordinate differential pipeline [20]. A general static spherically
symmetric metric with lapse profile A(r) and radial profile B(r) = A(r)⁻¹ has explicit Christoffel
symbols and diagonal/off-diagonal Ricci components evaluated through the coordinate differential
pipeline {{2}}. [21] Specializing to the Schwarzschild exterior metric with f(r) = 1 - 2 M / r yields
the orthonormal Weyl electric tidal curvature frame, Kretschmann scalar 48 M² / r⁶ [22], exact
metric-derivative Christoffel and Riemann components [23], and full coordinate-pipeline vacuum
flatness [24], while the interior incompressible fluid sphere exhibits the Tolman-Oppenheimer-Volkoff
pressure profile and Buchdahl compactness bound r_s < (8 / 9) R [25]. Including a cosmological
constant Λ in the Schwarzschild-de Sitter (Kottler) metric f(r) = 1 - 2 M / r - Λ r² / 3 yields
constant-curvature de Sitter frame components, Kretschmann invariant 48 M² / r⁶ + 8 Λ² / 3, frame
Bianchi conservation [26], Λ-independent Weyl electric eigenvalues [27], and full coordinate-pipeline
verification of R_{{ij}} = Λ g_{{ij}}, R = 4 Λ, and G_{{ij}} = -Λ g_{{ij}} [28]. Adding electric charge yields
the Reissner-Nordström electrovacuum metric f(r) = 1 - r_s / r + r_Q² / r², the radial
Coulomb-Maxwell field strength tensor F_{{ab}}, and the trace-free electromagnetic stress-energy tensor
satisfying the Einstein-Maxwell equations through the coordinate pipeline [29]. Rotating black holes
are represented by the axisymmetric Kerr metric in Boyer-Lindquist coordinates (t, r, θ, φ) with
spin a, polynomial functions Σ = r² + a² cos²θ and Δ = r² - r_s r + a², and exact block inverse
metric [30], all 64 Levi-Civita Christoffel symbols [31], and full differential pipeline
verification that the Ricci tensor, Ricci scalar, and Einstein tensor vanish identically in vacuum
{{2}}{{3}}. [32] Homogeneous and isotropic cosmology is formalized through the
Friedmann-Lemaître-Robertson-Walker metric with scale factor a(t) and spatial curvature k,
evaluating all FLRW Christoffel symbols, Ricci components, scalar curvature, and Friedmann Einstein
equations through the coordinate pipeline and bridging directly to `Cosmology.FLRW` [33].

### Scalar-tensor, higher-curvature, and screening gravity theories

Historically, Nordström's relativistic scalar gravity restricts the spacetime metric to the
conformally flat form φ(x)² η_{{μν}}, preserving null cones (producing zero gravitational light
deflection) while the differential pipeline evaluates its Christoffel symbols and proves the
four-dimensional Einstein-Fokker curvature identity R = -6 □_η φ / φ³ and its equivalence to the
nonlinear scalar wave equation □_η φ = -4 π φ³ T [34]. Brans-Dicke scalar-tensor gravity couples a
dynamical scalar field φ to curvature with dimensionless parameter ω, yielding the post-Newtonian
parameter γ = (1 + ω) / (2 + ω) approaching the General Relativity value 1 under the Cassini bound
ω > 40000, the effective scalar coupling 1 / (2 ω + 3), and the ω = 0 metric f(R) value γ = 1 / 2
[35]. Non-linear f(R) gravity replaces the Einstein-Hilbert density R with a smooth function f(R),
modifying the field equations and their four-dimensional trace while supplying the Starobinsky
R + α R² inflationary potential, positive scalaron mass squared, and Einstein-frame plateau [36].
By Ostrogradsky's theorem, non-degenerate higher-derivative Lagrangians possess a Hamiltonian
linear in an unconstrained momentum that is unbounded above and below unless the kinetic matrix is
degenerate [37]. Cubic Galileon scalar-tensor theories achieve second-order equations of motion
because the variation of the cubic action under constant-gradient shifts is a total derivative,
whereas shift symmetry forbids a non-trivial potential term [38]. Chameleon scalar-tensor theories
feature an effective mass squared that grows monotonically with ambient matter density, shrinking
the Yukawa interaction range and suppressing fifth forces for screened bodies via the thin-shell
factor ΔR / R [39].

### Torsion, teleparallel, higher-dimensional, Lorentz-violating, massive, and PPN formalisms

Einstein-Cartan-Sciama-Kibble theory relaxes the torsion-free constraint on the affine connection,
proving that any metric-compatible connection decomposes uniquely into the Levi-Civita connection
plus the contorsion tensor built from torsion, and inverting the algebraic Cartan modified torsion
tensor in terms of spin density [40]. In the Teleparallel Equivalent of General Relativity (TEGR),
gravity is carried by the curvature-free Weitzenböck connection of an orthonormal tetrad and its
torsion superpotential [41]; on flat FLRW cosmologies the Levi-Civita scalar curvature satisfies
R_LC = -T + B with torsion scalar T = 6 H² and total-divergence boundary term B [42], while
non-linear f(T) = T + F(T) extensions modify the Friedmann expansion equation [43]. Lovelock
higher-curvature gravity constructs the generalized Kronecker delta and proves dimensional
pigeonhole vanishing alongside antisymmetric permutation-sum coset splits [44], defines the
quadratic Gauss-Bonnet scalar 𝒢 = R² - 4 R^a_b R^b_a + R^{{cd}}_{{ab}} R^{{ab}}_{{cd}} and Lanczos
variation tensor H^i_j, proves via L^i_j = -8 H^i_j that H^i_j vanishes identically in dimension
n ≤ 4, and contrasts the four-dimensional topological invariant with the non-vanishing
five-dimensional variation [45]. Five-dimensional Kaluza-Klein theory unifies four-dimensional
General Relativity and Maxwell electromagnetism inside a 5D metric G_{{AB}} built from g_{{μν}}, the
gauge potential A_μ, and a dilaton φ, establishing the exact 5D inverse metric [46],
unit-determinant upper-triangular veilbein congruence factorization [47], diffeomorphism-to-U(1)
gauge equivalence under compact-circle shifts [48], and four-dimensional Maxwell stress-energy
tracelessness together with the Kaluza miracle R^{{(5)}} = R^{{(4)}} - ¼ F_{{ab}} F^{{ab}} [49].
Einstein-Aether theory breaks local Lorentz boost invariance with a unit-timelike vector field u^a
(g_{{ab}} u^a u^b = -1) governed by four Jacobson-Mattingly couplings (c₁, c₂, c₃, c₄), yielding
explicit squared propagation speeds for the spin-2, spin-1, and spin-0 modes, the GW170817 luminal
graviton constraint s₂² = 1 ↔ c₁ + c₃ = 0, and the renormalized Newtonian constant
G_N = G_bare / (1 - (c₁ + c₄) / 2) [50]. Fierz-Pauli and de Rham-Gabadadze-Tolley (dRGT) massive
gravity formalize the Lorentz-invariant mass term -(m² / 4)(h_{{ab}} h^{{ab}} + α h²) proving that the
ghost-free tuning α = -1 uniquely eliminates the sixth Boulware-Deser longitudinal mode and forces
vacuum tracelessness h = 0 [51], derive the van Dam-Veltman-Zakharov (vDVZ) 4 / 3 static coupling
ratio and 3 / 4 light-deflection discontinuity [52], and construct the ghost-free dRGT potential
from elementary symmetric polynomials of K [53]. Galactic rotation-curve alternatives without
non-baryonic dark matter are represented by Milgrom's Modified Newtonian Dynamics (MOND), which
interpolates between the Newtonian regime a ≫ a₀ and the deep-MOND regime a = √(a_N a₀) to produce
asymptotically flat circular velocities v⁴ = G M a₀ [54], by Bekenstein's relativistic
Tensor-Vector-Scalar (TeVeS) disformal physical metric and its exact analytical inverse [55], and by
Moffat's Scalar-Tensor-Vector Gravity (MOG) Yukawa-modified acceleration factor [56]. Finally, the
Will-Nordtvedt Parameterized Post-Newtonian (PPN) formalism unifies solar-system tests across
metric theories via ten dimensionless parameters (γ, β, ξ, α₁, α₂, α₃, ζ₁, ζ₂, ζ₃, ζ₄),
classifying fully conservative and semiconservative theories, embedding General Relativity,
Brans-Dicke, metric f(R), and Nordström gravity, and evaluating light deflection, Shapiro time
delay, perihelion precession, and the Nordtvedt Strong Equivalence Principle violation parameter η_N
{{3}}{{4}}{{5}}. [57]

## Lean References

1. PhyslibAlpha/Relativity/Tensors/Tensor2.lean — `Tensor2`, `IsSymm`, `isSymm_zero`,
   `isSymm_one`, `IsSymm.transpose`
2. PhyslibAlpha/Relativity/Metrics/Basic.lean — `MetricTensor`, `MetricTensor.ginv_symm`
3. PhyslibAlpha/Relativity/Metrics/Minkowski.lean — `eta4`, `eta4_symm`, `eta4_mul_self`,
   `eta4_eq_neg_coMetric_repr`, `minkowski`, `minkowski_ginv_offdiag`, `minkowskiG`
4. PhyslibAlpha/Relativity/Metrics/ConformalMetric.lean — `conformalG`, `conformalGinv`,
   `conformalMetric`
5. PhyslibAlpha/Relativity/Tensors/RiemannTensor.lean — `RiemannTensor`, `skew_first`,
   `zero_of_repeated_first`, `zero_of_repeated_last`, `swap_mixed`, `flat`
6. PhyslibAlpha/Relativity/Tensors/RicciTensor.lean — `ricci`, `ricci_symm`, `ricci_of_diag`,
   `ricci_flat`
7. PhyslibAlpha/Relativity/Metrics/MetricTrace.lean — `metricTrace`, `metricTrace_diag`,
   `sum_ginv_mul_g`, `MetricTensor.sum_ginv_mul_g_left`, `MetricTensor.sum_ginv_mul_g_right`,
   `metricTrace_mul_g`
8. PhyslibAlpha/Relativity/Metrics/ScalarCurvature.lean — `scalarCurv`,
   `scalarCurv_eq_metricTrace`
9. PhyslibAlpha/Relativity/Metrics/CoordinateMetric.lean — `CoordinateMetric`,
   `CoordinateMetric.metricTensor`, `pd`, `pd_const`, `pd_congr`, `pd_congr_nhds`,
   `pd_eq_fderiv`, `pd_eq_spaceTime_deriv`, `pd_comm`, `christoffel`, `riemann`,
   `ricciOf`, `scalarOf`, `einsteinOf`, `christoffel_const`, `riemann_const`
10. PhyslibAlpha/Relativity/Tensors/EinsteinTensor.lean — `einstein`, `einstein_symm`,
    `metricTrace_einstein`, `scalarCurv_eq_zero_of_einstein_eq_zero`, `vacuum_iff_ricci_flat`,
    `einsteinSpace_iff`
11. PhyslibAlpha/Relativity/Metrics/CurvDeriv.lean — `CurvDeriv`, `CurvDeriv.dEinstein`,
    `divergence`, `sum_eta_mul`, `divergence_combination`, `divergence_einstein_eq_zero`,
    `combination_conserved_iff`
12. PhyslibAlpha/Relativity/General/GeodesicSystem.lean — `Christoffel`, `GeodesicSystem`,
    `geodesicAccel`, `geodesicField`, `contDiffAt_geodesicField`, `geodesic_ivp_exists`,
    `geodesic_ivp_exists_curve`, `geodesic_ivp_unique`, `flat_geodesic`
13. PhyslibAlpha/Relativity/General/InitialData.lean — `InitialData`, `momConstraint`, `ham`,
    `IsVacuumData`, `ham_eq_scalarCurv_of_K_zero`, `ham_eq_of_trace_zero`, `euclid3`,
    `flatData_isVacuum`, `squeezedData_ham`
14. PhyslibAlpha/Relativity/General/Linearized/TraceReversed.lean — `hTrace`, `hTrace_eq_metricTrace`,
    `traceReversed`, `traceReversed_trace`, `traceReversed_involutive`, `boxEta`
15. PhyslibAlpha/Relativity/General/Linearized/LinearizedCurvature.lean — `linChristoffel`,
    `linChristoffel_symm`, `linRiemann`, `linRicci`, `linScalar`, `linEinstein`,
    `linRiemann_gauge_invariant`, `linRicci_gauge_invariant`, `linEinstein_gauge_invariant`
16. PhyslibAlpha/Relativity/General/Linearized/LorenzGauge.lean — `lorenzDiv`,
    `lorenzGaugeCond`, `linRicci_in_traceReversed`, `linEinstein_in_traceReversed`,
    `linEinstein_lorenz_gauge`
17. PhyslibAlpha/Relativity/General/Linearized/TTWave.lean — `ttWave`, `ttWave_symm`,
    `ttWave_trace_zero`, `traceReversed_ttWave`, `ttWave_lorenz_gauge`, `ttWave_linEinstein_zero`
18. PhyslibAlpha/Relativity/General/Linearized/NewtonianPerturb.lean — `newtonianPerturb`,
    `newtonianPerturb_symm`, `traceReversed_newtonianPerturb`, `newtonianPerturb_lorenz_gauge`,
    `laplacian3`, `newtonianPerturb_linEinstein_00`, `newtonianPerturb_poisson_iff`
19. PhyslibAlpha/Relativity/General/GravitationalConstant.lean — `GravitationalConstant`,
    `gravitationalConstantDimension`, `gravitationalConstant`, `gravitationalConstant_in_SI`,
    `toWithDim`, `toWithDim_scaleUnit`, `exists_units_c_G_kB_eq_one`
20. PhyslibAlpha/Relativity/General/MinkowskiVacuum.lean — `minkowskiFlatRiemann`,
    `minkowski_ricci_eq_zero`, `minkowski_scalarCurv_eq_zero`, `minkowski_einstein_eq_zero`,
    `minkowski_vacuum_iff_ricci_flat`, `minkowskiCoordinateMetric`
21. PhyslibAlpha/Relativity/Metrics/StaticSphericalMetric.lean — `StaticSphericalMetric`,
    `staticSphericalMetric`, `staticSphericalMetricInv`, `staticSphericalMetric_symm`,
    `staticSphericalMetric_mul_inv`, `staticSphericalMetricTensor`, `staticSphericalG`,
    `christoffel_eq_staticSphericalG`, `staticSphericalDG`
22. PhyslibAlpha/Relativity/General/Schwarzschild/ElectricWeyl.lean — `electricPart`,
    `electricPart_symm`, `electricPart_trace`, `frameSqSum`, `schwarzschild`, `ricci_eq_zero`,
    `frameSqSum_eq`, `kretschmann_scalar`, `weyl_purely_electric`
23. PhyslibAlpha/Relativity/General/Schwarzschild/Basic.lean — `SchwarzschildSpacetime`,
    `SchwarzschildSpacetime.lapse`, `SchwarzschildSpacetime.metric`, `schwarzschildMetric`,
    `schwarzschildF`, `schwarzschildF_of_incompressibleSphere`, `schwarzschildMetric_rr`,
    `gammaTtr_from_metric`, `gammaRrr_from_metric`, `riemann_t_rtr_from_metric`,
    `electric_r_from_metric`, `electricPart_from_metric`, `riemann_components_from_metric`
24. PhyslibAlpha/Relativity/General/Schwarzschild/CoordinateCurvature.lean — `schwarzschildG`,
    `schwarzschildGinv`, `riemann_schwarzschild_components`, `ricciOf_schwarzschild`,
    `scalarOf_schwarzschild`, `einsteinOf_schwarzschild`
25. PhyslibAlpha/Relativity/General/Schwarzschild/IncompressibleSphere.lean —
    `IncompressibleSphere`, `rs`, `chia`, `cosChia`, `cosChia_sq`, `cosChia_pos`,
    `cosChia_lt_one`, `rs_div_Ra`
26. PhyslibAlpha/Relativity/General/SchwarzschildDeSitter/DeSitterFrame.lean — `deSitterPart`,
    `sdsFrameSqSum`, `sdsFrameSqSum_eq`, `kretschmann_sds`, `sdsFrameComp`, `sdsRic`,
    `weylRic_zero`, `sds_frame_bianchi`, `sds_frame_einstein_conserved`
27. PhyslibAlpha/Relativity/General/SchwarzschildDeSitter/Basic.lean —
    `SchwarzschildDeSitterSpacetime`, `sdsF`, `sdsHalf`, `sdsMetric`, `sdsMetricInv`,
    `sdsF_zero_lambda`, `hasDerivAt_sdsF`, `gammaTtr_sds`, `gammaRrr_sds`, `weyl_rr_sds`,
    `weyl_thetatheta_sds`, `weyl_phiphi_sds`
28. PhyslibAlpha/Relativity/General/SchwarzschildDeSitter/CoordinateCurvature.lean — `sdsG`,
    `sdsDGFull`, `christoffel_eq_sdsG`, `riemann_sds_components`, `ricciOf_sds`, `scalarOf_sds`,
    `einsteinOf_sds`
29. PhyslibAlpha/Relativity/General/ReissnerNordstrom/Basic.lean — `ReissnerNordstromSpacetime`,
    `rnF`, `rnMetric`, `rnMetricInv`, `rnF_zero_charge`, `maxwellF`, `maxwellF_antisymm`,
    `maxwellStressEnergy`, `einsteinOf_rn_eq_maxwell`
30. PhyslibAlpha/Relativity/General/Kerr/Basic.lean — `KerrSpacetime`, `sigma`, `delta`, `bigB`,
    `bigB_eq_sigma`, `kerr_tphi_det_id`, `kerrMetric`, `kerrMetricInv`, `kerrMetric_symm`,
    `kerrMetricInv_mul_kerrMetric`, `kerrMetric_mul_kerrMetricInv`, `kerrMetricTensor`,
    `kerrMetric_zero_spin`
31. PhyslibAlpha/Relativity/General/Kerr/Christoffel.lean — `kerrMetricD`, `pd_kerrMetric_eq`,
    `kerrG`, `kerrG_symm`, `christoffel_kerr_eq`, `eventually_christoffel_kerr_eq`, `kerrTr`,
    `sum_kerrG_trace`
32. PhyslibAlpha/Relativity/General/Kerr/RicciCurvature.lean — `kerrRicci`, `kerrEinstein`,
    `pd_kerrTr_11`, `pd_kerrTr_21`, `pd_kerrTr_12`, `pd_kerrTr_22`, `ricciOf_kerr_eq_zero`,
    `scalarOf_kerr_eq_zero`, `einsteinOf_kerr_eq_zero`
33. PhyslibAlpha/Cosmology/FLRW/Metric.lean — `FLRWSpacetime`, `FLRWSpacetime.ofCosmology`,
    `FLRWSpacetime.metric`, `flrwMetric`, `flrwMetricInv`, `flrwMetric_symm`,
    `flrwMetric_mul_inv`, `flrwMetricTensor`, `flrwG`, `flrwDG`, `christoffel_eq_flrwG`,
    `scalarOf_flrw`, `friedmannSolution_of_einsteinOf_flrw_G`
34. PhyslibAlpha/Relativity/General/Modified/Nordstrom.lean — `NordstromSpacetime`,
    `nordstromMetric`, `nordstromMetricInv`, `nordstromMetricTensor`, `NullVector`,
    `nullVector_conformal_iff`, `light_deflection_zero`, `nordstromG`, `christoffel_nordstrom_eq`,
    `scalarOf_nordstrom`, `einsteinFokker_iff`
35. PhyslibAlpha/Relativity/General/Modified/BransDicke.lean — `BransDickeTheory`, `gamma`,
    `gamma_eq_one_sub`, `gamma_bounds`, `cassini_deviation`, `gamma_tendsto_atTop`, `fR_gamma`,
    `coupling`, `coupling_eq_one_add`, `coupling_bounds`, `coupling_pole`
36. PhyslibAlpha/Relativity/General/Modified/FRGravity.lean — `FRTheory`, `fieldEqn`,
    `linear_is_einstein`, `trace_fieldEqn`, `trace_fieldEqn_four`, `starobinskyPotential`,
    `phi_inverse`, `potential_eq`, `mass_sq`, `not_gr`, `einsteinFrameV`,
    `starobinsky_einsteinFrame`, `starobinsky_plateau`
37. PhyslibAlpha/Relativity/General/Modified/Ostrogradsky.lean — `HigherDerivModel`,
    `kineticMatrix`, `kineticMatrix_degenerate`, `hamiltonian`, `hamiltonian_add`,
    `unbounded_below`, `kinetic_bounded`, `kinetic_zero_iff`
38. PhyslibAlpha/Relativity/General/Modified/Galileon.lean — `CubicGalileon`,
    `cubicGalileonDensity`, `cubic_total_derivative`, `shift_total_derivative`,
    `shift_forbids_potential`
39. PhyslibAlpha/Relativity/General/Modified/ChameleonScreening.lean — `ChameleonModel`,
    `ChameleonModel.massSq`, `ChameleonModel.mass`, `chameleonMassSq`, `chameleonMass`,
    `chameleonMass_mono`, `range`, `range_antitone`, `chameleon_range_shrinks`, `yukawaRatio`,
    `yukawaRatio_lt_half`, `thinShell`, `screeningFactor`, `thin_shell_suppressed`
40. PhyslibAlpha/Relativity/General/Modified/EinsteinCartan.lean — `Conn`, `EinsteinCartanData`,
    `torsion`, `torsion_antisymm`, `MetricCompatible`, `leviCivitaOfDeriv`,
    `leviCivitaOfDeriv_compatible`, `contorsion`, `contorsion_antisymm_outer`,
    `contorsion_torsion`, `connection_unique`, `modifiedTorsion`, `invertModifiedTorsion`
41. PhyslibAlpha/Relativity/General/Modified/Teleparallel/Basic.lean — `Tetrad`,
    `weitzenbockConn`, `weitzenbockTorsion`, `weitzenbockTorsion_eq`,
    `weitzenbockTorsion_antisymm`, `superpotential`, `superpotential_antisymm`, `torsionScalar`
42. PhyslibAlpha/Relativity/General/Modified/Teleparallel/FLRWTorsion.lean — `flrwTetrad`,
    `flrwTetradInv`, `flrwTetrad_mul_inv`, `flrwWeitzenbock_hubble`, `flrwTorsionScalar`,
    `flrwTorsionScalar_ofCosmology`, `flrwBoundaryTerm`,
    `scalarOf_flrw_flat_eq_neg_torsion_add_boundary`
43. PhyslibAlpha/Relativity/General/Modified/Teleparallel/FTGravity.lean — `FTTheory`,
    `fTFriedmannLHS`, `fTFriedmannLHS_tegr`, `fTFriedmannLHS_quadratic`
44. PhyslibAlpha/Relativity/General/Modified/Lovelock/GeneralizedKronecker.lean — `genKronecker`,
    `genKronecker_eq_zero_of_lt`, `perm_fin5_fiber_split`
45. PhyslibAlpha/Relativity/General/Modified/Lovelock/Basic.lean — `AlgCurvature`,
    `AlgCurvature.ricciMixed`, `AlgCurvature.scalarCurv`, `AlgCurvature.ricciSq`,
    `AlgCurvature.riemannSq`, `AlgCurvature.gaussBonnetScalar`, `AlgCurvature.gaussBonnetTensor`,
    `lovelockContract5`, `lovelockContract5_eq_kronecker_sum`, `lovelockContract5_eq_zero_of_lt`,
    `lovelockContract5_eq_neg_eight_gaussBonnet`, `gaussBonnetTensor_eq_zero_of_lt_five`,
    `gaussBonnetTensor_four_eq_zero`, `constCurv`, `gaussBonnetScalar_constCurv_four`,
    `gaussBonnetTensor_constCurv_five`
46. PhyslibAlpha/Relativity/General/Modified/KaluzaKlein/Basic.lean — `KaluzaKleinData`, `potExt`,
    `metric4Ext`, `kkMetric`, `kkMetric_symm`, `potUp`, `kkMetricInv`,
    `kkMetricInv_mul_kkMetric`, `kkMetricInv_symm`, `kkMetric_mul_kkMetricInv`, `kkMetricTensor`
47. PhyslibAlpha/Relativity/General/Modified/KaluzaKlein/TriangularFactorization.lean —
    `kkTriangular`, `kkBlockDiag`, `det_kkTriangular`, `kkMetric_eq_triangular_conj`
48. PhyslibAlpha/Relativity/General/Modified/KaluzaKlein/GaugeTransform.lean — `kkGaugeJacobian`,
    `det_kkGaugeJacobian`, `kkGaugeJacobian_pullback`
49. PhyslibAlpha/Relativity/General/Modified/KaluzaKlein/KaluzaMiracle.lean — `maxwellF2`,
    `maxwellStressEnergy`, `maxwellStressEnergy_trace_zero`, `kkRicci44`, `kkRicci4D`,
    `kkScalar5D`, `kkScalar5D_eq`, `kkEinstein4D_eq_zero_iff`
50. PhyslibAlpha/Relativity/General/Modified/EinsteinAether.lean — `AetherCouplings`,
    `AetherCouplings.c13`, `AetherCouplings.c14`, `AetherCouplings.c123`,
    `AetherCouplings.c1Sub3`, `IsUnitTimelike`, `minkowskiRestAether`,
    `minkowskiRestAether_unitTimelike`, `linUnitTimelike_time_zero`, `kineticTensor`,
    `aetherKineticInvariant`, `aetherLagrangian`, `aetherLagrangian_on_shell`, `spin2SpeedSq`,
    `spin1SpeedSq`, `spin0SpeedSq`, `spin2SpeedSq_eq_one_iff`, `spin1SpeedSq_luminal_graviton`,
    `spin0SpeedSq_luminal_graviton`, `effectiveNewtonG`, `effectiveNewtonG_eq_bare_iff`
51. PhyslibAlpha/Relativity/General/Modified/MassiveGravity/FierzPauli.lean — `FierzPauliTheory`,
    `FierzPauliTheory.lagrangian`, `FierzPauliTheory.massTensor`, `hTraceEta`,
    `hTraceEta_eq_metricTrace`, `hContractionSq`, `fierzPauliLagrangian`, `fpMassTensor`,
    `fpMassTensor_trace`, `fpMassTensor_trace_tuned`, `longitudinal_time_ghost_free_iff`,
    `fp_traceless_of_zero_trace_source`
52. PhyslibAlpha/Relativity/General/Modified/MassiveGravity/VDVZ.lean — `stressTrace`,
    `stressTrace_eq_metricTrace`, `grPropagatorCoupling`, `massivePropagatorCoupling`,
    `staticSource`, `vdvz_static_ratio`, `vdvz_light_deflection_ratio`
53. PhyslibAlpha/Relativity/General/Modified/MassiveGravity/DRGT.lean — `DRGTTheory`, `trK1`,
    `trK2`, `trK3`, `elemSymm0`, `elemSymm1`, `elemSymm2`, `elemSymm3`, `elemSymm_isotropic3`,
    `dRGTPotential`, `dRGTPotential_vacuum_zero`
54. PhyslibAlpha/Relativity/General/Modified/MOND.lean — `MONDTheory`, `MONDTheory.deepAccel`,
    `MONDTheory.Relation`, `newtonAccel`, `newtonAccel_G`,
    `norm_pairGravityAcceleration_eq_newtonAccel`, `deepAccel`, `Relation`, `newtonian_limit`,
    `deep_accel_sq`, `flat_rotation`, `newtonian_velocity_ne`, `simpleMu`, `standardMu`,
    `simpleMu_bounds`
55. PhyslibAlpha/Relativity/General/Modified/TeVeS.lean — `TeVeSMetric`, `metric`, `metricInv`,
    `metric_symm`, `metric_lorentzian`, `metric_spatial`, `metric_mul_inv`, `metricInv_mul`,
    `metricTensor`
56. PhyslibAlpha/Relativity/General/Modified/MOG.lean — `MOGTheory`, `MOGTheory.factor`,
    `MOGTheory.potential`, `factor`, `potential`, `potential_G`, `factor_zero`,
    `factor_alpha_zero`, `factor_mu_zero`, `factor_bounds`, `factor_tendsto_atTop`
57. PhyslibAlpha/Relativity/General/Modified/PPNParameters.lean — `PPNParameters`,
    `IsFullyConservative`, `IsSemiconservative`, `IsFullyConservative.isSemiconservative`,
    `grPPN`, `bransDickePPN`, `fRMetricPPN`, `nordstromPPN`, `grPPN_isFullyConservative`,
    `bransDickePPN_isFullyConservative`, `bransDickePPN_zero_eq_fRMetricPPN`,
    `lightDeflectionFactor`, `shapiroDelayFactor`, `perihelionPrecessionFactor`,
    `nordtvedtParameter`, `lightDeflectionFactor_gr`, `lightDeflectionFactor_nordstrom`,
    `lightDeflectionFactor_fRMetric`, `perihelionPrecessionFactor_gr`,
    `perihelionPrecessionFactor_nordstrom`, `perihelionPrecessionFactor_bransDicke`,
    `nordtvedtParameter_gr`, `nordtvedtParameter_bransDicke`, `nordtvedtParameter_fRMetric`,
    `cassini_deviation_bransDickePPN`
58. PhyslibAlpha/Relativity/Tensors/MaxwellStressEnergy.lean — `maxwellFieldInvariant`,
    `maxwellStressEnergyRaw`, `maxwellStressEnergyRaw_trace_zero`, `emFieldStrengthComponents`,
    `emFieldStrengthComponents_antisymm`

## References

1. Units API map — Physlib/Units/API-map.md
2. R. M. Wald, *General Relativity*, University of Chicago Press, 1984.
3. C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation*, W. H. Freeman, 1973.
4. C. M. Will, *Theory and Experiment in Gravitational Physics*, 2nd ed., Cambridge University
   Press, 2018.
5. C. M. Will, *The Confrontation between General Relativity and Experiment*, *Living Reviews in
   Relativity* 17 (2014), 4, doi:10.12942/lrr-2014-4.
