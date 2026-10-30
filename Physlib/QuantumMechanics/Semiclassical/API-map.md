# Semiclassical Weyl quantization and exact free propagation

## Abstract (Alpha)

Weyl quantization assigns operators to phase-space observables with a variable reduced Planck
parameter. Quadratic symbols act on Schwartz maps, and Schwartz symbols give bounded operators
on the full Hilbert space. The free quantum propagator transports both classes of observables
exactly along the classical free flow.

## Content (Alpha)

The scaled momentum acts as $-ih\partial_i$ on Schwartz maps. It agrees with the physical
momentum at $h=\hbar$, is symmetric on the Schwartz domain, and becomes a multiplier under
the Fourier transform. [1] Quadratic phases preserve the Hilbert-space norm. Their parameter
dependence and product rule with momentum control the free propagator. [2]

For a quadratic symbol, Weyl ordering replaces each product with the average of its two
orders. The same expression evaluates the classical polynomial and its quantum operator. [3]
The free flow sends $(q,p)$ to $(q+tp/m,p)$. The free Hamiltonian is symmetric on the Schwartz
domain and is a kinetic-energy multiplier in Fourier coordinates. [4]

The free propagator is a quadratic Fourier multiplier on Schwartz maps. It extends to a
strongly continuous unitary group on the full Hilbert space and preserves the Schwartz
submodule. The Schrodinger equation holds at each Fourier coordinate on Schwartz vectors.
Conjugation by the propagator gives the exact Egorov identity for quadratic symbols on the
common Schwartz domain. [5] General Egorov correspondence relates quantum conjugation to
transport along a classical flow. {1}

For a Schwartz phase-space symbol, Fourier synthesis integrates the symbol's Fourier
coefficients against Weyl displacements applied to a vector. {2} The displacements preserve
the norm and the Schwartz submodule, depend strongly continuously on frequency, and satisfy
the adjoint identity with the opposite displacement. [6] The resulting operator is complex
linear in its symbol. Its norm is bounded by the Fourier $L^1$ norm uniformly in $h$, and
real symbols give symmetric operators. [7]

The free flow and its transpose preserve phase-space volume. Fourier transformation turns
symbol pullback along the free flow into pullback along the inverse transpose. Free propagation
conjugates the displacements by the transpose shear. This proves exact free Egorov transport
for Schwartz symbols on the full Hilbert space and gives the corresponding expectation
identity. [8]

The coordinate kernel formula and Wigner pairing express the same observables in position
and phase space, respectively. {3} [TODO] For nonquadratic potentials, a remainder estimate
compares quantum propagation with classical transport. {3} [TODO]

## Lean References

1. Physlib/QuantumMechanics/Semiclassical/Basic.lean — `momentumCLM`, `momentumCLM_hbar`,
   `momentumCLM_apply`, `momentumCLM_inner`, `fourier_momentumCLM`, `momentumCLM_fourier`,
   `fourier_positionCLM`
2. Physlib/QuantumMechanics/Semiclassical/QuadraticPhase.lean — `quadraticPhaseCLM`,
   `quadraticPhaseCLM_momentum`, `quadraticPhaseCLM_norm`, `quadraticPhaseCLM_sub_norm_le`,
   `quadraticPhaseCLM_lipschitz`
3. Physlib/QuantumMechanics/Semiclassical/Quadratic.lean — `quadraticPolynomial`,
   `map_quadraticPolynomial`, `quadraticSymbol`, `quadraticSymbol_apply`, `weylQuadraticCLM`
4. Physlib/QuantumMechanics/Semiclassical/FreeParticle.lean — `freeFlow`,
   `quadraticSymbol_freeFlow`, `freeHamiltonianCLM`, `freeHamiltonianCLM_inner`,
   `fourier_freeHamiltonianCLM`
5. Physlib/QuantumMechanics/Semiclassical/FreeParticle.lean — `freeEvolutionCLM`,
   `freeEvolutionCLM_add`, `freeEvolutionCLE`, `freeEvolution`, `freeEvolution_schwartzIncl`,
   `freeEvolution_add`, `freeEvolution_mem_schwartzSubmodule`, `freeEvolution_continuous`,
   `freeEvolutionCLM_fourier_hasDerivAt`, `freeEvolutionCLM_fourier_schrodinger`,
   `freeEgorov_position`, `freeEgorov_momentum`, `freeEgorov_quadratic`,
   `freeEgorov_quadratic_hilbert`
6. Physlib/QuantumMechanics/Semiclassical/Weyl.lean — `PhaseSpace`, `weylCLM`, `weyl`,
   `weyl_norm`, `weyl_schwartzIncl`, `weyl_continuous`, `weyl_neg_apply`, `weyl_inner`
7. Physlib/QuantumMechanics/Semiclassical/Weyl.lean — `weyl_integrable`, `weylQuantization`,
   `weylQuantization_apply`, `weylQuantization_norm_le`, `weylQuantization_add`,
   `weylQuantization_smul`, `weylQuantization_inner`
8. Physlib/QuantumMechanics/Semiclassical/FreeEgorov.lean — `freeFlowCLE`, `freeDualFlowCLE`,
   `freeFlowCLE_measurePreserving`, `freeDualFlowCLE_measurePreserving`, `freeSymbol`,
   `fourier_freeSymbol`, `weyl_freeEvolution`, `weylQuantization_freeSymbol`, `freeEgorov`,
   `freeEgorov_expectation`

## References

1. S. Dyatlov, *Notes on fractal uncertainty principle* (2017), Proposition 1.1.3.
   https://math.mit.edu/~dyatlov/files/2017/fupnotes.pdf
2. V. Guillemin and S. Sternberg, *Semi-classical analysis* (2010), Section 15.11.2.
   https://math.mit.edu/~vwg/semiclassGuilleminSternberg.pdf
3. J. Keller and C. Lasser, *Propagation of Quantum Expectations with Husimi Functions*
   (2013), arXiv:1207.7211v2. https://arxiv.org/abs/1207.7211
