# Hilbert spaces on Space

## Abstract (Alpha)

The Hilbert space on space with a given measure is the L² space: the complex functions that are
square-integrable against that measure, taken up to equality almost everywhere, with the volume as
the default measure. These are the spaces non-relativistic quantum mechanics works in, and they
come together with the subspaces singled out by regularity, support and boundary conditions, and
with the multiplication and derivative operators that quantum mechanics needs on them.

## Content (Alpha)

The Hilbert space on space {1} with respect to a measure is the space of square-integrable complex
functions modulo equality almost everywhere, and the volume is the default measure. [1] A
function can be read as an element of such a Hilbert space exactly when it is almost everywhere
strongly measurable and square-integrable. [2]

Several subspaces carry the extra regularity that differential operators need. The complex
Schwartz maps on space form a subspace, and a map passes in either direction between a Schwartz
map and the class it represents. [3] The Sobolev spaces are subspaces too. [TODO] The Fourier
transform is a unitary map from the Hilbert space to itself. [4]

Restricting attention to a region of space gives further structure. The functions supported in a
given subset of space form a Hilbert space of their own, with an inclusion into the full space
and a projection onto it. [5] The elements satisfying homogeneous Dirichlet boundary conditions
on a subset of space form a subspace. [6] So do the elements satisfying homogeneous Neumann
boundary conditions [TODO], and those satisfying homogeneous mixed boundary conditions.
[TODO]

Operators on these spaces come in two families. Any complex function of position gives a
multiplication operator with maximal domain [7], and the position operators are such
multiplication operators. [8] Any complex function of the wavenumber gives a derivative operator
with maximal domain [TODO], and the momentum and momentum-squared operators are such
derivative operators. [TODO] The angular momentum and angular momentum-squared operators act
on the Hilbert space [TODO], as does the reflection through a general hyperplane. [TODO]
The general theory of these operators lives in the operator algebra {2}.

## Lean References

1. Physlib/QuantumMechanics/HilbertSpaces/SpaceD/Basic.lean — `SpaceDHilbertSpace`
2. Physlib/QuantumMechanics/HilbertSpaces/SpaceD/Basic.lean — `MemHS`
3. Physlib/QuantumMechanics/HilbertSpaces/SpaceD/SchwartzSubmodule.lean — `SchwartzSubmodule`,
   `schwartzIncl`, `schwartzEquiv`
4. Physlib/QuantumMechanics/HilbertSpaces/SpaceD/Fourier.lean — `fourierUnitary`
5. Physlib/QuantumMechanics/HilbertSpaces/SpaceD/Basic.lean — `SpaceDHilbertSpaceOn`,
   `subspaceIncl`, `subspaceProjection`
6. Physlib/QuantumMechanics/HilbertSpaces/SpaceD/DirichletSubmodule.lean — `DirichletSubmoduleOn`
7. Physlib/QuantumMechanics/Operators/Multiplication.lean — `mulOperator`
8. Physlib/QuantumMechanics/Operators/Position.lean — `positionOperator`

## References

1. Space API map — Physlib/SpaceAndTime/Space/API-map.md
2. Operator algebra API map — Physlib/QuantumMechanics/Operators/API-map.md
