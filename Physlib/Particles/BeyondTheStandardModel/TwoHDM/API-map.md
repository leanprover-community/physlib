# Two Higgs Doublet Model

The two Higgs doublet model extends the Standard Model with a second Higgs doublet, so a
configuration is a pair of Higgs vectors. That pair is the key data structure here.

The API gives the action of the gauge group on such a configuration, and the invariants that
pin down its gauge orbit: the Gram matrix of the pair and, equivalently, the Gram vector of its
components in the Pauli basis. Both are shown to characterize orbits and to be surjective onto
the matrices or vectors satisfying the obvious constraints. On top of those sit the potential
of the model, its invariance under the gauge group, its expression in terms of the Gram vector,
and its stability theory — including an explicit counterexample to a step in one of the
references.

## Built on

- Higgs Field — `Physlib/Particles/StandardModel/HiggsBoson`
- Pauli matrices — `Physlib/Relativity/PauliMatrices`

## Requirements

The key data structure is defined: a configuration of the model, a pair of Higgs vectors. [1]

The global gauge group acts on such a pair. [2]

A configuration will be a real vector space. [planned]

A group of order two will act by swapping the two Higgs vectors. [planned]

The Gram matrix of a configuration is defined, is self-adjoint, and has nonnegative determinant
and trace. [3]

Two configurations lie in the same gauge orbit exactly when they have the same Gram
matrix. [4]

The Gram matrix is surjective: every self-adjoint matrix with nonnegative determinant and trace
is the Gram matrix of some configuration. [5]

The Gram vector, the components of the Gram matrix in the Pauli basis, is defined, with its own
gauge-orbit characterization and surjectivity. [6]

The parameters of the potential are defined, together with their reparameterization adapted to
the Gram vector. [7]

The potential of the two Higgs doublets is defined, built from its mass and quartic terms. [8]

The potential, and each of its two terms, is invariant under the global gauge group. [9]

The potential and its terms are expressed in terms of the Gram vector. [10]

Stability of the potential — that it is bounded below — is defined, and characterized in terms
of the Gram vector. [11]

Strong stability, the positivity of the reduced quartic term, implies stability. [12]

A step in one of the references is refuted by an explicit counterexample: an unstable potential
whose reduced quartic term is nonnegative, and whose reduced mass term is nonnegative wherever
the reduced quartic term vanishes. [13]

## Further reading

- https://arxiv.org/abs/hep-ph/0605184
- https://arxiv.org/abs/1605.03237

## Lean declarations

1. Physlib/Particles/BeyondTheStandardModel/TwoHDM/Basic.lean — `TwoHiggsDoublet`
2. Physlib/Particles/BeyondTheStandardModel/TwoHDM/Basic.lean — `SMul GaugeGroupI TwoHiggsDoublet`,
   `MulAction GaugeGroupI TwoHiggsDoublet`
3. Physlib/Particles/BeyondTheStandardModel/TwoHDM/GramMatrix.lean — `gramMatrix`,
   `gramMatrix_selfAdjoint`, `gramMatrix_det_nonneg`, `gramMatrix_tr_nonneg`
4. Physlib/Particles/BeyondTheStandardModel/TwoHDM/GramMatrix.lean — `mem_orbit_gaugeGroupI_iff_gramMatrix`
5. Physlib/Particles/BeyondTheStandardModel/TwoHDM/GramMatrix.lean — `gramMatrix_surjective_det_tr`
6. Physlib/Particles/BeyondTheStandardModel/TwoHDM/GramMatrix.lean — `gramVector`,
   `mem_orbit_gaugeGroupI_iff_gramVector`, `gramVector_surjective`
7. Physlib/Particles/BeyondTheStandardModel/TwoHDM/Potential.lean — `PotentialParameters`,
   `PotentialParameters.ξ`, `PotentialParameters.η`
8. Physlib/Particles/BeyondTheStandardModel/TwoHDM/Potential.lean — `potential`, `massTerm`,
   `quarticTerm`
9. Physlib/Particles/BeyondTheStandardModel/TwoHDM/Potential.lean — `gaugeGroupI_smul_potential`,
   `gaugeGroupI_smul_massTerm`, `gaugeGroupI_smul_quarticTerm`
10. Physlib/Particles/BeyondTheStandardModel/TwoHDM/Potential.lean — `potential_eq_gramVector`,
   `massTerm_eq_gramVector`, `quarticTerm_eq_gramVector`
11. Physlib/Particles/BeyondTheStandardModel/TwoHDM/Potential.lean — `PotentialIsStable`,
   `potentialIsStable_iff_massTermReduced_sq_le_quarticTermReduced`
12. Physlib/Particles/BeyondTheStandardModel/TwoHDM/Potential.lean — `potentialIsStable_of_strong`
13. Physlib/Particles/BeyondTheStandardModel/TwoHDM/Potential.lean — `stabilityCounterExample`,
   `stabilityCounterExample_not_potentialIsStable`,
   `forall_reduced_exists_not_potentialIsStable`
