# Feynman diagrams

A Feynman diagram, as understood here, is a partition of a multiset of field operators into
disjoint pairs. That is the multiset counterpart of a Wick contraction, which pairs up
positions in a list of field operators; the intended relation is that the permissible
contractions — those contributing a nonzero amount to the vacuum expectation value — embed into
Feynman diagrams. Passing from lists to multisets is what makes a diagram independent of the
order in which the operators were written down, and it is the resulting many-to-one map from
contractions to diagrams that a symmetry factor has to account for.

The API is to be built on the perturbation-theory material the library already has. A field
specification fixes the fields of a theory, their bosonic or fermionic statistics, and the
labels from which field operators and their creation and annihilation parts are built; the free
operator algebra and the Wick algebra supply the algebra in which the value of a diagram is to
be computed; and Wick contractions supply the pairings of a list together with their signs,
time contractions and the machinery behind Wick's theorem. A position field operator carries a
point of spacetime, which is a Lorentz vector carrying an action of the Lorentz group, so the
Lorentz group is a parent of this API too, reached through the field specification.

This is a tracking map for issue #882. The directory holds a single Lean file, which states the
intended design in its module documentation and declares nothing; it marks the directory as a
work in progress. Every requirement below is therefore still planned.

## Built on

- Field specification — `Physlib/QFT/PerturbationTheory/FieldSpecification`
- Field operator free algebra — `Physlib/QFT/PerturbationTheory/FieldOpFreeAlgebra`
- Wick algebra — `Physlib/QFT/PerturbationTheory/WickAlgebra`
- Wick contractions — `Physlib/QFT/PerturbationTheory/WickContraction`
- Koszul signs — `Physlib/QFT/PerturbationTheory/Koszul`
- Field statistics — `Physlib/QFT/PerturbationTheory/FieldStatistics`
- Lorentz group — `Physlib/Relativity/LorentzGroup`

## Requirements

The key data structure will be defined: a Feynman diagram, a partition of a multiset of field
operators into disjoint pairs. [planned]

That definition will be general enough to accept any Feynman diagram of any theory. [planned]

All Feynman diagrams up to a given order for a given amplitude will be generated, provably. [planned]

The symmetry factor of a Feynman diagram will be computable. [planned]

A Feynman diagram will be convertible into the algebraic expression underlying it. [planned]

The permissible Wick contractions, those which do not contribute zero to the vacuum expectation
value, will embed into Feynman diagrams. [planned]

## Further reading

- https://en.wikipedia.org/wiki/Feynman_diagram
- M. E. Peskin and D. V. Schroeder, An Introduction to Quantum Field Theory, chapter 4.

## Lean declarations

*None yet.*
