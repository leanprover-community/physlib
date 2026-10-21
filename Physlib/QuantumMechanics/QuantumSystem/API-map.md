# QuantumSystem

## Abstract (Alpha)

A quantum system in non-relativistic quantum mechanics is fixed by two choices: a complex
Hilbert space, and a self-adjoint Hamiltonian operator on it. Everything else is built from that
pair: the trivial system on the zero-dimensional space, unitary equivalence of systems, the sum
of two systems, and the dynamics, namely the Schrödinger equation, the time evolution operator,
the energy eigenvalues and eigenbases, and the passage to the Heisenberg picture.

## Content (Alpha)

A quantum system consists of a complete complex inner-product space together with a
self-adjoint Hamiltonian operator on it. [1] The trivial, zero-dimensional Hilbert space carries
a unique quantum system, the zero system. [2] Two systems are unitarily equivalent when some
unitary map between their Hilbert spaces carries one Hamiltonian to the other by conjugation, and
unitary equivalence is an equivalence relation on quantum systems. [3] Two quantum systems add,
giving the system on the product of their Hilbert spaces whose Hamiltonian is, schematically, the
sum of theirs. [TODO]

The dynamics of a quantum system is governed by its Hamiltonian. The Schrödinger equation is an
equation for a wavefunction depending on time and valued in the domain of the Hamiltonian.
[TODO] The time evolution operator is a bounded operator on the Hilbert space for each time.
[TODO] The Hamiltonian has energy eigenspaces, eigenvectors and eigenvalues [TODO], and a
system may admit an energy eigenbasis. [TODO] Conjugation with the time evolution operator
moves an operator into and out of the Heisenberg picture. [TODO]

## Lean References

1. Physlib/QuantumMechanics/QuantumSystem/Basic.lean — `QuantumSystem`
2. Physlib/QuantumMechanics/QuantumSystem/Basic.lean — `Zero QuantumSystem`
3. Physlib/QuantumMechanics/QuantumSystem/Basic.lean — `UnitaryRelation`,
   `unitaryRelation_equiv`
