# Hilbert spaces on Space

The Hilbert space on space with a given measure is the L² space: the complex functions that
are square-integrable against that measure, taken up to equality almost everywhere. The
default measure is the volume. These are the spaces non-relativistic quantum mechanics works
in, and this API builds them together with the subspaces and the operators that quantum
mechanics needs on them.

## Built on

- Space — `Physlib/SpaceAndTime/Space`

## Requirements

The key data structure is defined: the Hilbert space on space with respect to a measure, with
the volume as the default. [1]

A condition says when a function can be read as an element of such a Hilbert space. [2]

The complex Schwartz maps on space form a subspace, and a map can be passed in either
direction between a Schwartz map and the class it represents. [3]

The Fourier transform is a unitary map from the Hilbert space to itself. [4]

The Sobolev subspaces will be defined. [planned]

The functions supported in a given subset of space form a Hilbert space of their own. [5]

The elements satisfying homogeneous Dirichlet boundary conditions on a subset of space form a
subspace. [6]

The elements satisfying homogeneous Neumann boundary conditions on a subset of space will form
a subspace. [planned]

The elements satisfying homogeneous mixed boundary conditions on a subset of space will form a
subspace. [planned]

Any complex function of position gives a multiplication operator with maximal domain. [7]

The position operators are such multiplication operators. [8]

Any complex function of the wavenumber will give a derivative operator with maximal
domain. [planned]

The momentum and momentum-squared operators will be such derivative operators. [planned]

The angular momentum and angular momentum-squared operators will be defined. [planned]

The reflection operator through a general hyperplane will be defined. [planned]

## Lean declarations

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
