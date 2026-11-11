# Hamiltonian mechanics

## Abstract (Alpha)

Hamiltonian mechanics separates the kinematics of a system, described by its phase space, from
its dynamics, specified by a Hamiltonian. Hamilton's equations determine the motion, and Poisson
brackets describe the evolution of observables. Symmetries give conserved quantities, while
Liouville integrability requires sufficiently many independent conserved quantities in involution.
The coordinate formulations of the harmonic oscillator, simple pendulum and central-force systems
provide examples, alongside a symplectic vector-space formulation of moment maps and conservation.

## Content (Alpha)

### Phase space and observables

A configuration space Q is a smooth manifold without boundary {1}. [1] For finite-dimensional Q,
its canonical Hamiltonian phase space is the cotangent bundle T*Q: a state consists of a
configuration q and a momentum covector at q. [TODO] This space carries a canonical symplectic form,
independently of the choice of Hamiltonian {6}. [TODO] In the coordinate formulation on a complete
real inner-product space X, states are pairs (p, q) in X × X, and observables are real-valued
functions f(p, q), with momentum first. [2] Identifying the cotangent phase space of a Euclidean
configuration space with this coordinate representation uses the inner product to represent
covectors as momentum vectors. [TODO]

### Hamiltonians and Hamiltonian trajectories

A Hamiltonian system consists of a phase space and a smooth real-valued Hamiltonian, possibly
time-dependent and defined on an open domain. [TODO] The phase space describes kinematics; choosing the
Hamiltonian specifies dynamics through the symplectic form {2}{6}. [TODO] In coordinates, curves
p(t) and q(t) satisfy Hamilton's equations q̇ = ∇ₚH and ṗ = −∇qH exactly when the Hamilton
equation operator vanishes. [3] The symplectic definition of Hamiltonian trajectories agrees with
these coordinate equations. [TODO] For a smooth Hamiltonian and a smooth phase-space curve, the
variational gradient of the action ∫ (⟨p, q̇⟩ − H(t, p, q)) dt is that operator. [4]

For a finite-dimensional real normed configuration space E, an open domain U in E* × E and a
smooth Hamiltonian H on Time × U determine a Hamiltonian system on U with the canonical symplectic
form; E* denotes the continuous dual, containing the momenta {6}. [TODO]

Taking E = ℝ, positive mass m and spring constant k gives the harmonic-oscillator Hamiltonian
H(p, q) = p²/(2m) + k q²/2, which is smooth on the whole phase space. [12] Taking E = ℝ³, positive
mass m and a radial potential V smooth at positive radii gives the central-force Hamiltonian
H(p, q) = ‖p‖²/(2m) + V(‖q‖), smooth on the open domain U = {(p, q) | q ≠ 0}. [14] Using the
Euclidean inner product to identify momenta with vectors, both are Hamiltonian systems obtained
by the preceding construction. [TODO]

The Legendre map sends a velocity v to its conjugate momentum p = ∂L/∂v. If this map has a smooth
inverse over time and configuration space, the Hamiltonian H(t, p, q) = p(v) − L(t, q, v), with
v recovered from (t, p, q), gives the equivalent Hamiltonian description of a Lagrangian system
{5}{6}. [TODO]

### Poisson brackets and observable evolution

The coordinate Poisson bracket is {f, g} = ⟨∇qf, ∇ₚg⟩ − ⟨∇ₚf, ∇qg⟩. [2] It is antisymmetric,
bilinear and satisfies the Leibniz rule, with the differentiability assumptions needed for the
gradient rules. [5] Along a differentiable solution of Hamilton's equations, a time-independent
observable differentiable at the current state satisfies d f(p(t), q(t))/dt = {f, H(t)}(p(t), q(t)).
[6] The canonical coordinate relations are {qᵢ, pⱼ} = δᵢⱼ, {qᵢ, qⱼ} = {pᵢ, pⱼ} = 0, and smooth
observables satisfy the Jacobi identity. [TODO]

### Symmetries and conserved quantities

For a time-independent differentiable observable along a differentiable Hamiltonian trajectory,
a vanishing Poisson bracket with the Hamiltonian implies zero time derivative. [6] A smooth
autonomous Hamiltonian Poisson-commutes with itself and has zero time derivative along its
Hamiltonian trajectories. [5][6] These quantities are constant on connected time intervals,
giving energy conservation in the autonomous case. [TODO]

On a finite-dimensional real symplectic vector space, an affine infinitesimally symplectic Lie
algebra action has a moment map whose components generate the action's vector fields through
their symplectic gradients. [7] If an autonomous Hamiltonian is invariant under a generator, the
corresponding moment-map component is constant along its Hamiltonian trajectories. [8]

### Integrability

For an autonomous Hamiltonian on a 2d-dimensional Euclidean phase space, Liouville integrability
on an open dense domain U consists of d smooth observables, including the Hamiltonian, that
pairwise Poisson-commute and whose phase-space gradients are linearly independent on U. [9] Each
has zero time derivative along a differentiable Hamiltonian trajectory at times when the state
lies in U. [10] With one degree of freedom, the Hamiltonian alone gives integrability on any open
dense domain where it is smooth and its phase-space gradient is nonzero. [11] The Liouville–Arnold
theorem identifies compact connected regular common level sets as invariant tori and supplies
local action–angle coordinates {6}. [TODO]

### Existing examples and their connections

The harmonic oscillator {3} and simple pendulum {4} have explicit canonical momenta and
Hamiltonians, with Hamiltonian, Newtonian and variational descriptions agreeing for smooth
trajectories. The pendulum is expressed using a real lift of its angle. [12][13]

Three-dimensional central-force systems have Hamiltonians smooth away from the centre. [14]
Their angular-momentum observables L² and Lz Poisson-commute with each other and with the
Hamiltonian away from the centre. [15] Their functional independence on a suitable open dense
domain gives central-force Liouville integrability. [TODO]

A point particle of positive mass m in a Euclidean configuration space with a smooth potential V
has Lagrangian L(q, v) = m ‖v‖²/2 − V(q) and Hamiltonian H(p, q) = ‖p‖²/(2m) + V(q), linked by
the momentum p = m v. [TODO]

## Lean References

1. Physlib/ClassicalMechanics/ConfigurationSpace/Basic.lean — `ConfigurationSpace`
2. Physlib/ClassicalMechanics/HamiltonianMechanics/PoissonBracket.lean — `poissonBracket`
3. Physlib/ClassicalMechanics/HamiltonianMechanics/HamiltonsEquations.lean —
   `hamiltonEqOp`, `hamiltonEqOp_eq_zero_iff_hamiltons_equations`
4. Physlib/ClassicalMechanics/HamiltonianMechanics/HamiltonsEquations.lean —
   `hamiltons_equations_varGradient`
5. Physlib/ClassicalMechanics/HamiltonianMechanics/PoissonBracket.lean —
   `poissonBracket_antisymm`, `poissonBracket_self`, `poissonBracket_add_left`,
   `poissonBracket_add_right`, `poissonBracket_const_mul_left`, `poissonBracket_const_mul_right`,
   `poissonBracket_mul_left`, `poissonBracket_mul_right`
6. Physlib/ClassicalMechanics/HamiltonianMechanics/PoissonBracket.lean —
   `deriv_comp_eq_poissonBracket`
7. PhyslibAlpha/ClassicalMechanics/MomentMap/Basic.lean — `IsSymplecticForm`,
   `AffineSymplecticAction`, `IsSymplecticGradient`,
   `AffineSymplecticAction.vectorField_isSymplecticGradient`
8. PhyslibAlpha/ClassicalMechanics/MomentMap/Basic.lean —
   `AffineSymplecticAction.noether`, `AffineSymplecticAction.noether_const`
9. PhyslibAlpha/ClassicalMechanics/LiouvilleIntegrable/Basic.lean — `LiouvilleIntegrableOn`
10. PhyslibAlpha/ClassicalMechanics/LiouvilleIntegrable/Basic.lean —
    `LiouvilleIntegrableOn.deriv_comp_eq_zero`
11. PhyslibAlpha/ClassicalMechanics/LiouvilleIntegrable/Basic.lean —
    `LiouvilleIntegrableOn.oneDegreeOfFreedom`
12. Physlib/ClassicalMechanics/HarmonicOscillator/Basic.lean — `toCanonicalMomentum_eq`,
    `hamiltonian_eq`, `hamiltonian_contDiff`, `equationOfMotion_tfae`
13. Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Hamiltonian.lean — `canonicalMomentum_eq`,
    `hamiltonian_eq`, `equationOfMotion_tfae`
14. PhyslibAlpha/ClassicalMechanics/CentralForce/Basic.lean — `CentralForce`, `hamiltonian`,
    `contDiffOn_hamiltonian`
15. PhyslibAlpha/ClassicalMechanics/CentralForce/AngularMomentum.lean — `angularMomentum`,
    `angularMomentumSq`, `angularMomentumZ`, `poissonBracket_angularMomentumSq_angularMomentumZ`,
    `poissonBracket_angularMomentumSq_hamiltonian`, `poissonBracket_angularMomentumZ_hamiltonian`

## References

1. Configuration Space API map — Physlib/ClassicalMechanics/ConfigurationSpace/API-map.md
2. Physlib GitHub issue #2003, Foundations for Hamiltonian Systems,
   https://github.com/leanprover-community/physlib/issues/2003
3. Configuration space of the harmonic oscillator API map —
   Physlib/ClassicalMechanics/HarmonicOscillator/Geometric/API-map.md
4. Simple pendulum API map — Physlib/ClassicalMechanics/Pendulum/SimplePendulum/API-map.md
5. Lagrangian mechanics API map — Physlib/ClassicalMechanics/Lagrangian/API-map.md
6. V. I. Arnold, *Mathematical Methods of Classical Mechanics*.
