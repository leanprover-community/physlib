# Operator algebra

## Abstract (Alpha)

An observable of a quantum system is a self-adjoint operator on the Hilbert space of states, and the
observables of interest are almost never defined on the whole space: position multiplies a
wavefunction by a coordinate and momentum differentiates it, and both send square-integrable
functions out of the space unless the wavefunction decays or is smooth enough. The objects are
therefore partially defined linear maps with a dense domain, together with symmetry of the
inner-product pairing on that domain and self-adjointness, which is strictly stronger than symmetry
once the domain is a proper subspace. On an arbitrary complex Hilbert space this gives the adjoint
calculus, multiplication operators, and the statistics of an observable in a state, culminating in
the Robertson and Robertson-Schrödinger uncertainty bounds; on the Hilbert space on space it gives
the standard observables of non-relativistic quantum mechanics on space — position, powers of the
radius, momentum -iℏ∂ᵢ and angular momentum 𝐋ᵢⱼ = xᵢpⱼ - xⱼpᵢ — with their canonical commutation
relations. The spectrum, the resolvent, the numerical range and spectral measures belong to spectral
theory instead.

## Content (Alpha)

### Unbounded operators

An operator on a Hilbert space is a partially defined linear map. It has a dense domain when its
domain is a dense subspace, and it is unbounded, in the technical sense used here, when it is
densely defined and closable. [1] It is symmetric when the inner-product pairing is symmetric on its
domain, which happens exactly when the pairing of each vector with its own image is real. [2]
Symmetry is stable under sums, powers and closures, and a self-adjoint operator is symmetric and
closed. [3] An operator is essentially self-adjoint when its closure is self-adjoint; such an
operator is unbounded, and its closure is its only self-adjoint extension. [4]

The adjoint is antitone and conjugate-linear in non-zero scalars, the sum of two adjoints is a
restriction of the adjoint of the sum, and likewise for compositions; the adjoint of an unbounded
operator is again unbounded, and its second adjoint is its closure. [5] A symmetric densely defined
operator for which T + i and T - i both have the whole space as range is self-adjoint. [6]
Conjugation by a unitary preserves formal adjoints, dense domains and surjectivity of T - z. [7] The
standard examples separating the classes of symmetric, essentially self-adjoint and self-adjoint
operators make the distinction between symmetry and self-adjointness visible. [TODO] These
definitions follow the standard treatments of unbounded operators by Hall {1}, Reed and Simon {2},
and Schmüdgen {3}. The spectrum, the resolvent, the numerical range and spectral measures of these
operators belong to spectral theory {4}.

### Multiplication operators

A complex function on space {5} gives a multiplication operator on the Hilbert space on space {6},
defined on its maximal domain, the vectors whose product with the function is still
square-integrable; for an almost everywhere strongly measurable multiplier the operator is densely
defined. [8] For a bounded multiplier the domain is the whole
space, and for a multiplier of temperate growth it contains the Schwartz maps. [9] The adjoint of a
multiplication operator is multiplication by the conjugate function, so a real multiplier gives a
self-adjoint operator; multiplication operators are closed and unbounded. [10] They behave
predictably under scalar multiples, sums and composition. [11]

### Position and momentum

Each component of the position operator is multiplication by a coordinate, first on Schwartz maps
and then as a partially defined operator on the Hilbert space, where it is densely defined,
self-adjoint and unbounded. [12] Multiplication by a power of the radius, and by its smooth
regularization, supplies the multipliers of central potentials; the product stays square-integrable
under an explicit condition, and the regularized operators converge to the unregularized one. [13]

Each component of the momentum operator is -iℏ∂ᵢ, first on Schwartz maps and then as a partially
defined operator, which is densely defined, symmetric and unbounded on the Schwartz submodule; the
momentum squared acts on the same domain. [14] On the Sobolev space H¹ the momentum operator is
self-adjoint, and not merely symmetric, and likewise the momentum squared on H². [TODO]

### Commutation relations

Position and momentum satisfy the canonical commutation relation [xᵢ, pⱼ] = iℏ δᵢⱼ on Schwartz maps,
and Leibniz rules reduce a commutator of products to commutators of the factors. [15] The position
components commute among themselves, as do the momentum components, and the commutator of a position
component with the momentum squared is 2iℏ pᵢ. [16] A regularized power of the radius commutes with
itself and with each position component, and its commutators with a momentum component and with the
momentum squared are explicit. [17]

### Angular momentum

The components 𝐋ᵢⱼ = xᵢpⱼ - xⱼpᵢ of the angular momentum operator and the scalar 𝐋² act on Schwartz
maps; the components are antisymmetric in the two indices and vanish for a repeated index, and the
one-, two- and three-dimensional cases each have their own description. [18] Position and momentum
transform as vectors under the angular momenta, which close into the Lie algebra of rotations. [19]
The scalar 𝐋² commutes with every angular momentum component, with the momentum squared and with any
regularized power of the radius. [20]

Each angular momentum component acts on the Hilbert space with dense Schwartz domain, agrees almost
everywhere with its action on Schwartz maps, preserves the Schwartz submodule, and is symmetric and
closable. [21] Angular momentum squared acts on the Hilbert space with invariant dense Schwartz
domain, equals half the sum of the squares of the components, and is symmetric and closable. [22] In
three dimensions the right-handed Cartesian components act on the invariant Schwartz domain, satisfy
the Levi-Civita and cyclic commutation relations, and their three squares sum to angular momentum
squared. [23] The ladder operators L± = Lx ± i Ly act on Schwartz maps and on the Hilbert space with
invariant dense Schwartz domain, where [Lz, L±] = ±ℏ L± and [L², L±] = 0. [24]

Angular momentum extends from its Schwartz domain to self-adjoint operators on the Hilbert space,
whose spectra consist of the eigenvalues ℏ² l (l + 1) of the scalar and ℏ m of a chosen component,
with the spherical harmonics as the corresponding eigenfunctions. [TODO]

### Statistics of observables

The expectation value of an observable T in a state ψ is ⟨T⟩ = re ⟪ψ, T ψ⟫, and the centered vector
is T ψ - ⟨T⟩ψ; for a symmetric operator the pairing is already real. [25] The variance is ‖T ψ -
⟨T⟩ψ‖², given for a unit vector and a symmetric operator by the second-order formula ⟨T²⟩ - ⟨T⟩²,
and the standard deviation is its square root; for a unit vector the variance vanishes exactly when
the vector is an eigenvector. [26] A vector is an eigenvector of a partially defined operator when
it is a non-zero element of the domain sent to a multiple of itself. [27] The covariance of two
observables in a state is symmetric and reduces to the variance on a single observable. [28]

The product of the standard deviations of two observables is at least half the size of their
expected commutator, in both the Robertson and the Robertson-Schrödinger forms, stated for both a
centered and a raw commutator identity. [29] In particular position and momentum obey the Heisenberg
uncertainty relation: in any unit state of a common domain the product of their standard deviations
is at least ℏ/2. [TODO]

These are the textbook notions of Sakurai and Napolitano {7}, Griffiths and Schroeter {8}, and
Hall {1}. The uncertainty bounds go back to Robertson {9} and Schrödinger {10}.

## Lean References

1. Physlib/QuantumMechanics/Operators/Unbounded.lean — `HasDenseDomain`, `IsUnbounded`,
   `isClosable_of_continuous`, `IsClosed.continuous_of_isClosed_domain`
2. Physlib/QuantumMechanics/Operators/Unbounded.lean — `IsSymmetric`,
   `isSymmetric_iff_inner_map_self_real`
3. Physlib/QuantumMechanics/Operators/Unbounded.lean — `IsSymmetric.isClosable`,
   `IsSymmetric.closure`, `IsSymmetric.add`, `IsSymmetric.pow`, `IsSelfAdjoint.isSymmetric`,
   `IsSelfAdjoint.isClosed`
4. Physlib/QuantumMechanics/Operators/Unbounded.lean — `IsEssentiallySelfAdjoint`,
   `IsEssentiallySelfAdjoint.isUnbounded`,
   `IsEssentiallySelfAdjoint.unique_self_adjoint_extension`
5. Physlib/QuantumMechanics/Operators/Unbounded.lean — `adjoint_smul`, `adjoint_neg`,
   `adjoint_antitone`, `adjoint_add_le_add_adjoint`,
   `adjoint_compRestricted_le_compRestricted_adjoint`, `IsUnbounded.adjoint`,
   `IsUnbounded.adjoint_closure_eq_adjoint`, `IsUnbounded.adjoint_adjoint_eq_closure`
6. Physlib/QuantumMechanics/Operators/Unbounded.lean — `IsSymmetric.isSelfAdjoint_of_range_eq_top`,
   `IsSymmetric.isSelfAdjoint_iff`, `IsSymmetric.isEssentiallySelfAdjoint_iff`
7. Physlib/QuantumMechanics/Operators/Unbounded.lean — `unitaryConj`,
   `mem_unitaryConj_domain_iff`, `unitaryConj_apply`, `IsFormalAdjoint.unitaryConj`,
   `HasDenseDomain.unitaryConj_dense_domain`, `unitaryConj_sub_smul_surjective`
8. Physlib/QuantumMechanics/Operators/Multiplication.lean — `mulOperator`, `notation 𝓜`,
   `mem_mulOperator_domain_iff`, `mulOperator_apply_ae`, `mulOperator_hasDenseDomain`
9. Physlib/QuantumMechanics/Operators/Multiplication.lean — `mulOperator_domain_eq_top`,
   `mulOperator_domain_antitone`, `mulOperator_conj_domain`,
   `mulOperator_domain_ge_of_hasTemperateGrowth`
10. Physlib/QuantumMechanics/Operators/Multiplication.lean — `mulOperator_adjoint_eq_conj`,
   `mulOperator_isSelfAdjoint_ofReal`, `mulOperator_isClosable`, `mulOperator_isUnbounded`,
   `mulOperator_isClosed`
11. Physlib/QuantumMechanics/Operators/Multiplication.lean — `mulOperator_const_smul_eq`,
   `mulOperator_add_ge`, `mulOperator_add_eq`, `mulOperator_sub_ge`, `mulOperator_smul_ge`
12. Physlib/QuantumMechanics/Operators/Position.lean — `positionCLM`, `notation 𝐱`,
   `positionCLM_apply`, `positionSqCLM_eq`, `positionOperator`, `notation 𝓧`,
   `positionOperator_hasDenseDomain`, `positionOperator_isSelfAdjoint`,
   `positionOperator_isUnbounded`
13. Physlib/QuantumMechanics/Operators/Position.lean — `radiusRegPowCLM`, `notation 𝐫₀`,
   `radiusRegPowCLM_comp_eq`, `radiusPowLM`, `notation 𝐫`, `radiusPowLM_apply_memHS`,
   `radiusRegPow_tendsto_radiusPow`, `radiusRegPowOperator`,
   `radiusRegPowOperator_isSelfAdjoint`, `radiusPowOperator`, `radiusPowOperator_isSelfAdjoint`,
   `radiusPowOperator_domain_ge`
14. Physlib/QuantumMechanics/Operators/Momentum.lean — `momentumCLM`, `notation 𝐩`,
   `momentumCLM_apply`, `momentumOperator`, `notation 𝓟`, `momentumOperator_apply`,
   `momentumOperator_hasDenseDomain`, `momentumOperator_isSymmetric`,
   `momentumOperator_isUnbounded`, `momentumSqOperator`, `momentumSqOperator_domain_eq`
15. Physlib/QuantumMechanics/Operators/Commutation.lean — `leibniz_lie`, `lie_leibniz`,
   `comp_eq_comp_add_commute`, `comp_eq_comp_sub_commute`, `position_commutation_momentum`,
   `momentum_comp_position_eq`, `position_position_commutation_momentum`,
   `position_commutation_momentum_momentum`
16. Physlib/QuantumMechanics/Operators/Commutation.lean — `position_commutation_position`,
   `position_comp_commute`, `momentum_commutation_momentum`, `momentumSqr_commutation_momentum`,
   `position_commutation_momentumSqr`
17. Physlib/QuantumMechanics/Operators/Commutation.lean — `position_commutation_radiusRegPow`,
   `radiusRegPow_commutation_radiusRegPow`, `radiusRegPow_commutation_momentum`,
   `momentum_comp_radiusRegPow_eq`, `radiusRegPow_commutation_momentumSqr`
18. Physlib/QuantumMechanics/Operators/AngularMomentum.lean — `angularMomentumCLM`,
   `notation 𝐋`, `angularMomentumCLM_apply`, `angularMomentumCLM_antisymm`,
   `angularMomentumCLM_eq_zero`, `angularMomentumOperatorSqr`, `notation 𝐋²`,
   `angularMomentumOperatorSqr_apply`, `angularMomentumOperator1D_trivial`,
   `angularMomentumOperator2D`, `angularMomentumOperator3D`
19. Physlib/QuantumMechanics/Operators/AngularMomentum.lean — `angularMomentum_commutation_position`,
   `angularMomentum_commutation_momentum`, `angularMomentum_commutation_angularMomentum`
20. Physlib/QuantumMechanics/Operators/AngularMomentum.lean — `angularMomentumSqr_commutation_angularMomentum`,
   `angularMomentumSqr_commutation_momentumSqr`, `angularMomentumSqr_commutation_radiusRegPow`,
   `angularMomentum_commutation_momentumSqr`, `angularMomentum_commutation_radiusRegPow`
21. Physlib/QuantumMechanics/Operators/AngularMomentum.lean — `angularMomentumOperator`,
   `angularMomentumOperator_domain_eq`, `angularMomentumOperator_apply`,
   `angularMomentumOperator_apply_ae`, `angularMomentumOperator_range`,
   `angularMomentumOperator_hasDenseDomain`, `angularMomentumCLM_eq_momentum_position`,
   `angularMomentumOperator_isSymmetric`, `angularMomentumOperator_isUnbounded`
22. Physlib/QuantumMechanics/Operators/AngularMomentum.lean — `angularMomentumSqOperator`,
   `angularMomentumSqOperator_apply`, `angularMomentumSqOperator_apply_ae`,
   `angularMomentumSqOperator_range`, `angularMomentumSqOperator_apply_eq_sum`,
   `angularMomentumSqOperator_hasDenseDomain`, `angularMomentumSqr_inner`,
   `angularMomentumSqOperator_isSymmetric`, `angularMomentumSqOperator_isUnbounded`
23. Physlib/QuantumMechanics/Operators/AngularMomentum/DimThree.lean — `angularMomentumDimThreeOperator`,
   `angularMomentumDimThreeOperator_isSymmetric`, `angularMomentumOperatorSqr_eq_sum_dimThree`,
   `angularMomentumSqOperator_apply_eq_sum_dimThree`, `angularMomentumDimThree_commutation`,
   `angularMomentumDimThree_commutation_xy`, `angularMomentumDimThree_commutation_yz`,
   `angularMomentumDimThree_commutation_zx`, `angularMomentumDimThreeOperator_commutation`,
   `angularMomentumSqOperator_commutation_dimThree`
24. Physlib/QuantumMechanics/Operators/AngularMomentum/DimThree.lean — `angularMomentumRaisingCLM`,
   `angularMomentumLoweringCLM`, `angularMomentumRaisingOperator`,
   `angularMomentumLoweringOperator`, `angularMomentumZ_commutation_raising`,
   `angularMomentumZ_commutation_lowering`, `angularMomentumSqr_commutation_raising`,
   `angularMomentumSqr_commutation_lowering`, `angularMomentumZOperator_commutation_raising`,
   `angularMomentumZOperator_commutation_lowering`,
   `angularMomentumSqOperator_commutation_raising`,
   `angularMomentumSqOperator_commutation_lowering`
25. Physlib/QuantumMechanics/Operators/StateObservables/ExpectedValue.lean — `expectedValue`,
   `expectedValue_eq_inner`, `centered`, `centered_eq_zero_iff`, `inner_state_centered_eq_zero`,
   `inner_centered_state_eq_zero`
26. Physlib/QuantumMechanics/Operators/StateObservables/Variance.lean — `variance`,
   `variance_eq_centered_norm_sq`, `variance_eq_norm_sq_sub_expectedValue_sq`,
   `variance_eq_re_inner_sub_expectedValue_sq`, `variance_nonneg`,
   `variance_eq_zero_iff_isEigenvector`, `standardDeviation`,
   `standardDeviation_eq_zero_iff_isEigenvector`
27. Physlib/QuantumMechanics/Operators/StateObservables/IsEigenvector.lean — `IsEigenvector`,
   `IsEigenvector.apply_eq`, `IsEigenvector.ne_zero`
28. Physlib/QuantumMechanics/Operators/Covariance.lean — `covariance`, `covariance_comm`,
   `covariance_eq_re_symm_centered`, `covariance_self_eq_variance`
29. Physlib/QuantumMechanics/Operators/Uncertainty.lean — `centeredCommutatorExpectation`,
   `rawCommutatorExpectation`, `inner_centered_commutator_of_raw_commutator`,
   `state_uncertainty_squared_of_centered_commutator`,
   `state_uncertainty_squared_with_covariance_of_centered_commutator`,
   `state_uncertainty_of_centered_commutator`, `state_uncertainty_squared_of_raw_commutator`,
   `state_uncertainty_squared_with_covariance_of_raw_commutator`,
   `state_uncertainty_of_raw_commutator`

## References

1. B. C. Hall, *Quantum Theory for Mathematicians*, Springer (2013), Chapters 9 and 10 (unbounded
   self-adjoint operators) and Chapter 12 (position, momentum, expectation values and the
   uncertainty principle).
2. M. Reed and B. Simon, *Methods of Modern Mathematical Physics I. Functional Analysis*, Academic
   Press (1980), Chapter VIII (unbounded operators).
3. K. Schmüdgen, *Unbounded Self-Adjoint Operators on Hilbert Space*, Springer (2012), Chapters 1
   to 3 (closed, symmetric and self-adjoint operators, and examples 1.3 and 3.8 on multiplication
   operators).
4. Spectral theory API map — Physlib/QuantumMechanics/Operators/SpectralTheory/API-map.md
5. Space API map — Physlib/SpaceAndTime/Space/API-map.md
6. Hilbert space on space API map — Physlib/QuantumMechanics/HilbertSpaces/SpaceD/API-map.md
7. J. J. Sakurai and J. Napolitano, *Modern Quantum Mechanics*, 2nd ed., Cambridge University Press
   (2017), Chapter 1 (observables, expectation values, the canonical commutation relation, the
   uncertainty relation) and Chapter 3 (angular momentum).
8. D. J. Griffiths and D. F. Schroeter, *Introduction to Quantum Mechanics*, 3rd ed., Cambridge
   University Press (2018), Chapter 3 (observables, eigenfunctions of hermitian operators, the
   generalized uncertainty principle) and Chapter 4 (angular momentum).
9. H. P. Robertson, *The Uncertainty Principle*, Phys. Rev. 34, 163 (1929).
10. E. Schrödinger, *Zum Heisenbergschen Unschärfeprinzip*, Sitzungsberichte der Preussischen
    Akademie der Wissenschaften 19, 296 (1930).
