# Hilbert space tensor products

The Hilbert space of a composite quantum system is usually built by taking the tensor product
of the Hilbert spaces of its parts. The algebraic tensor product of two Hilbert spaces is an
inner-product space but need not be complete, so the object wanted here is its completion.
This API supplies that completion, for a pair of Hilbert spaces and for an indexed family of
them, with the structure maps relating the various ways of bracketing and ordering the factors.

## Requirements

The complete tensor product of a pair of Hilbert spaces is defined. [1]

The complete tensor product of a pair is commutative, by a linear isometry equivalence. [2]

The complete tensor product of pairs is associative, by a linear isometry equivalence. [3]

The complete tensor product will be shown isometrically equivalent to the algebraic one
whenever either factor is finite-dimensional. [planned]

The complete tensor product of an indexed family of Hilbert spaces will be defined. [planned]

The complete tensor power of a single Hilbert space will be defined. [planned]

The Fock space of a seed Hilbert space will be defined. [planned]

## Lean declarations

1. Physlib/QuantumMechanics/HilbertSpaces/TensorProducts/CompleteTensorProduct.lean — `CompleteTensorProduct`
2. Physlib/QuantumMechanics/HilbertSpaces/TensorProducts/CompleteTensorProduct.lean — `CompleteTensorProduct.comm`
3. Physlib/QuantumMechanics/HilbertSpaces/TensorProducts/CompleteTensorProduct.lean — `CompleteTensorProduct.assoc`
