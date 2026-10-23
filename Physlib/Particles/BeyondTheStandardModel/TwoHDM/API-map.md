# Two Higgs Doublet Model

## Abstract (Alpha)

The two Higgs doublet model extends the Standard Model with a second Higgs doublet, so that a
configuration is a pair of Higgs vectors. The global gauge group acts on such pairs, and their gauge
orbits are pinned down by the Gram matrix of the pair or, equivalently, by the Gram vector of its
components in the Pauli basis; both invariants characterize orbits and are surjective onto the
matrices or vectors satisfying the obvious constraints. On top of these sit the potential of the
model, its gauge invariance, its expression in terms of the Gram vector, and its stability theory,
including an explicit counterexample to a step in one of the references.

## Content (Alpha)

### Configurations and the gauge action

A configuration of the two Higgs doublet model is a pair of Higgs vectors {1}. [1] The global gauge
group of the Standard Model acts on such a pair. [2] Configurations form a real vector
space. [TODO] A group of order two acts by swapping the two Higgs vectors. [TODO]

### Gram matrix and Gram vector

The Gram matrix of a configuration is self-adjoint, with nonnegative determinant and
trace. [3] Two configurations lie in the same gauge orbit exactly when they have the same Gram
matrix. [4] Conversely, every self-adjoint matrix with nonnegative determinant and trace is the
Gram matrix of some configuration. [5] Expanding the Gram matrix in the basis of Pauli matrices
gives the Gram vector, which likewise characterizes gauge orbits and is surjective onto the
vectors satisfying the corresponding constraints. [6]

### The potential and its stability

The potential is parameterized following the convention of {2}; these parameters are related to the
reparameterization adapted to the Gram vector used in {3}. [7] The potential of the two Higgs
doublets is the sum of a mass term and a quartic term. [8] The potential, and each of its two terms,
is invariant under the global gauge group. [9] Each of them is a function of the Gram vector
alone. [10]

The potential is stable when it is bounded below. Stability is characterized through the reduced
mass and quartic terms, functions on the unit ball of normalized Gram-vector directions: the reduced
quartic term is nonnegative there and, wherever the reduced mass term is negative, its square is
bounded by a fixed multiple of the reduced quartic term. [11] Strong stability, the positivity of
the reduced quartic term, implies stability. [12] The stability arguments follow, in part, those of
{3}, but one of its steps is false: there is an unstable potential whose reduced quartic term is
nonnegative, and whose reduced mass term is nonnegative wherever the reduced quartic term
vanishes. [13]

## Lean References

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

## References

1. Higgs field API map — Physlib/Particles/StandardModel/HiggsBoson/API-map.md
2. arXiv:1605.03237, https://arxiv.org/abs/1605.03237
3. arXiv:hep-ph/0605184, https://arxiv.org/abs/hep-ph/0605184
