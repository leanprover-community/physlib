# Canonical ensemble

A canonical ensemble describes a system in thermal equilibrium with a heat bath at a fixed
temperature. Its data is a measurable type of microstates, an energy function on them, and the
semi-classical bookkeeping — the number of degrees of freedom and the phase-space unit — needed
to turn thermodynamic quantities into dimensionless ones.

The treatment is measure-theoretic, so that discrete and continuous models are handled
uniformly: the partition function is an integral, which becomes a finite sum when the
microstates are finitely many. On that footing the API builds the Boltzmann and probability
measures, the mean energy, the entropies and the Helmholtz free energy, and proves the
identities tying them together — the free energy as energy minus temperature times entropy, the
mean energy as a derivative of the logarithm of the partition function, and the
fluctuation–dissipation theorem relating the heat capacity to the variance of the energy.
Ensembles can also be composed: independent systems add, and a system can be copied or
transported along a measurable equivalence.

## Built on

- Temperature — `Physlib/Thermodynamics/Temperature`

## Requirements

The key data structure is defined: a canonical ensemble, given by its microstates, its energy
function, its degrees of freedom, its phase-space unit and a σ-finite measure — together with
the ways of composing ensembles, by adding independent ones, by taking several non-interacting
copies, and by transporting along a measurable equivalence. [1]

The unnormalized Boltzmann measure and the normalized probability measure are defined, as are
the pointwise mathematical and physical probability densities. [2]

The mathematical partition function is the integral of the Boltzmann factor, and the physical
one is that divided by the phase-space unit raised to the degrees of freedom; both are
positive. [3]

The mean energy, the mean square energy and the energy variance are defined, and the variance
is the mean square minus the square of the mean. [4][5]

The Helmholtz free energy is defined from the partition function. [6]

The differential entropy and the absolute thermodynamic entropy are defined, and for finitely
many microstates the thermodynamic entropy is the Shannon entropy. [7][8]

The fundamental thermodynamic identity holds: the free energy is the mean energy less the
temperature times the entropy. [9]

The mean energy is minus the derivative of the logarithm of the partition function with respect
to the inverse temperature. [10]

The heat capacity is defined, and for a finite ensemble the fluctuation–dissipation theorem
holds: it is the energy variance divided by the Boltzmann constant times the square of the
temperature. [11][12]

For systems with finitely many discrete microstates the framework specializes, and the integral
definitions reduce to finite sums. [13]

The two-state ensemble is constructed, with closed forms for its partition function, its state
probabilities and its mean energy. [14]

The thermodynamic entropy of the two-state ensemble will be given in closed form. [planned]

The Helmholtz free energy of the two-state ensemble will be given in closed form. [planned]

## Further reading

- L. D. Landau & E. M. Lifshitz, Statistical Physics, Part 1 (§31).
- D. Tong, Lectures on Statistical Physics (Cambridge), https://www.damtp.cam.ac.uk/user/tong/statphys/one.pdf and https://www.damtp.cam.ac.uk/user/tong/statphys/two.pdf

## Lean declarations

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
