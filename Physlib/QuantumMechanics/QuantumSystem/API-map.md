# QuantumSystem

A quantum system in non-relativistic quantum mechanics is fixed by two choices: a complex
Hilbert space, and a self-adjoint Hamiltonian operator on it. The key data structure here
carries exactly that — the Hilbert space, complete and with its inner product, together with
the Hamiltonian and the proof that it is self-adjoint.

Everything else the API offers is built from that pair: the trivial system on the
zero-dimensional space, unitary equivalence of systems, and, in time, the dynamics — the
Schrödinger equation, the time evolution operator, the energy eigenvalues and eigenbases, and
the passage to the Heisenberg picture.

## Requirements

The key data structure is defined: a quantum system, carrying a Hilbert space and a
self-adjoint Hamiltonian operator on it. [1]

There is a zero system, the unique quantum system on the trivial, zero-dimensional Hilbert
space. [2]

Unitary equivalence is an equivalence relation on quantum systems: two systems are unitarily
equivalent when some unitary map between their Hilbert spaces carries one Hamiltonian to the
other by conjugation. [3]

Two quantum systems will add, giving the system on the product of their Hilbert spaces whose
Hamiltonian is, schematically, the sum of theirs. [planned]

The Schrödinger equation will be defined, for a wavefunction depending on time and valued in
the domain of the Hamiltonian. [planned]

The time evolution operator will be defined, a bounded operator on the Hilbert space for each
time. [planned]

The energy eigenspaces, eigenvectors and eigenvalues will be defined. [planned]

Energy eigenbases will be defined. [planned]

An operator will move into and out of the Heisenberg picture by conjugation with the time
evolution operator. [planned]

## Lean declarations

1. Physlib/QuantumMechanics/QuantumSystem/Basic.lean — `QuantumSystem`
2. Physlib/QuantumMechanics/QuantumSystem/Basic.lean — `Zero QuantumSystem`
3. Physlib/QuantumMechanics/QuantumSystem/Basic.lean — `UnitaryRelation`,
   `unitaryRelation_equiv`
