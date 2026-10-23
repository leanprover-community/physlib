# Hilbert space tensor products

## Abstract (Alpha)

The Hilbert space of a composite quantum system is the tensor product of the Hilbert spaces of
its parts. The algebraic tensor product of two Hilbert spaces is an inner-product space but need
not be complete, so the right object is its completion, the complete tensor product, taken for a
pair of Hilbert spaces and for an indexed family of them, together with the structure maps
relating the various ways of bracketing and ordering the factors.

## Content (Alpha)

Two Hilbert spaces have a complete tensor product, the completion of their algebraic tensor
product. [1] It is commutative, by a linear isometry equivalence exchanging the factors [2], and
associative, by a linear isometry equivalence rebracketing three factors. [3] Whenever either
factor is finite-dimensional, the complete tensor product is isometrically equivalent to the
algebraic one. [TODO]

The construction extends beyond pairs. An indexed family of Hilbert spaces has a complete tensor
product [TODO], and a single Hilbert space has complete tensor powers. [TODO] A seed Hilbert
space has a Fock space built from its tensor powers. [TODO]

## Lean References

1. Physlib/QuantumMechanics/HilbertSpaces/TensorProducts/CompleteTensorProduct.lean — `CompleteTensorProduct`
2. Physlib/QuantumMechanics/HilbertSpaces/TensorProducts/CompleteTensorProduct.lean — `CompleteTensorProduct.comm`
3. Physlib/QuantumMechanics/HilbertSpaces/TensorProducts/CompleteTensorProduct.lean — `CompleteTensorProduct.assoc`
