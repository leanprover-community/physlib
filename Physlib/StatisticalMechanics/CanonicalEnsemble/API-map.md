# Canonical ensemble

## Abstract (Alpha)

A canonical ensemble describes a system in thermal equilibrium with a heat bath at a fixed
temperature. Its data is
a measurable type of microstates, an energy function on them, and the semi-classical bookkeeping
(the number of degrees of freedom and the phase-space unit) needed to turn thermodynamic
quantities into dimensionless ones. The treatment is measure-theoretic, so that discrete and
continuous models are handled uniformly: the partition function is an integral, which becomes a
finite sum when the microstates are finitely many. On that footing the Boltzmann and probability
measures, the mean energy, the entropies and the Helmholtz free energy are tied together by the
free energy as energy minus temperature times entropy, the mean energy as a derivative of the
logarithm of the partition function, and the fluctuation–dissipation theorem relating the heat
capacity to the variance of the energy; ensembles also compose, with independent systems adding
and a system being copied or transported along a measurable equivalence.

## Content (Alpha)

### Ensembles and their measures

A canonical ensemble {1} is given by its microstates, its energy function, its degrees of freedom,
its phase-space unit and a σ-finite measure; independent ensembles add, a system has several
non-interacting copies, and an ensemble transports along a measurable equivalence. [1] The
temperature enters through the inverse temperature {2}. An ensemble carries an
unnormalized Boltzmann measure and a normalized probability measure, together with pointwise
mathematical and physical probability densities. [2] The mathematical partition function is the
integral of the Boltzmann factor, and the physical one is that divided by the phase-space unit
raised to the degrees of freedom; both are positive. [3]

### Thermodynamic quantities

An ensemble has a mean energy, a mean square energy and an energy variance, [4] and the
variance is the mean square minus the square of the mean. [5] The Helmholtz free energy comes
from the partition function. [6] An ensemble has a differential entropy and an absolute
thermodynamic entropy, [7] and for finitely many microstates the thermodynamic entropy is the
Shannon entropy. [8]

The fundamental thermodynamic identity holds: the free energy is the mean energy less the
temperature times the entropy. [9] The mean energy is minus the derivative of the logarithm of
the partition function with respect to the inverse temperature. [10] The heat capacity is the
derivative of the mean energy with respect to temperature, and whenever the energy variance is
minus the derivative of the mean energy with respect to the inverse temperature, the heat
capacity is the energy variance divided by the Boltzmann constant times the square of the
temperature. [11] For a finite ensemble at positive temperature this fluctuation–dissipation
theorem holds outright. [12] These identities are developed in Tong's lectures {3}.

### Finite ensembles and the two-state system

For systems with finitely many discrete microstates the integral definitions reduce to finite
sums. [13] The two-state ensemble has closed forms for its partition function, its state
probabilities and its mean energy. [14] Its thermodynamic entropy has a closed form. [TODO]
Its Helmholtz free energy has a closed form. [TODO]

## Lean References

1. Physlib/StatisticalMechanics/CanonicalEnsemble/Basic.lean — `CanonicalEnsemble`,
   `HAdd instance`, `nsmul`, `congr`
2. Physlib/StatisticalMechanics/CanonicalEnsemble/Basic.lean — `μBolt`, `μProd`, `probability`,
   `physicalProbability`
3. Physlib/StatisticalMechanics/CanonicalEnsemble/Basic.lean — `mathematicalPartitionFunction`,
   `partitionFunction`
4. Physlib/StatisticalMechanics/CanonicalEnsemble/Basic.lean — `meanEnergy`, `meanSquareEnergy`,
   `energyVariance`
5. Physlib/StatisticalMechanics/CanonicalEnsemble/Lemmas.lean — `energyVariance_eq_meanSquareEnergy_sub_meanEnergy_sq`
6. Physlib/StatisticalMechanics/CanonicalEnsemble/Basic.lean — `helmholtzFreeEnergy`
7. Physlib/StatisticalMechanics/CanonicalEnsemble/Basic.lean — `differentialEntropy`,
   `thermodynamicEntropy`
8. Physlib/StatisticalMechanics/CanonicalEnsemble/Finite.lean — `shannonEntropy`,
   `thermodynamicEntropy_eq_shannonEntropy`
9. Physlib/StatisticalMechanics/CanonicalEnsemble/Lemmas.lean — `helmholtzFreeEnergy_eq_meanEnergy_sub_temp_mul_thermodynamicEntropy`
10. Physlib/StatisticalMechanics/CanonicalEnsemble/Lemmas.lean — `meanEnergy_eq_neg_deriv_log_Z_of_beta`
11. Physlib/StatisticalMechanics/CanonicalEnsemble/Lemmas.lean — `heatCapacity`,
   `fluctuation_dissipation_energy_parametric`
12. Physlib/StatisticalMechanics/CanonicalEnsemble/Finite.lean — `fluctuation_dissipation_theorem_finite`
13. Physlib/StatisticalMechanics/CanonicalEnsemble/Finite.lean — `IsFinite`,
   `partitionFunction_of_fintype`, `meanEnergy_of_fintype`
14. Physlib/StatisticalMechanics/CanonicalEnsemble/TwoState.lean — `twoState`,
   `twoState_partitionFunction_apply`, `twoState_probability_fst`, `twoState_probability_snd`,
   `twoState_meanEnergy_eq`

## References

1. L. D. Landau and E. M. Lifshitz, *Statistical Physics, Part 1*, §31.
2. Temperature API map — Physlib/Thermodynamics/Temperature/API-map.md
3. D. Tong, *Lectures on Statistical Physics* (Cambridge),
   https://www.damtp.cam.ac.uk/user/tong/statphys/one.pdf and
   https://www.damtp.cam.ac.uk/user/tong/statphys/two.pdf
