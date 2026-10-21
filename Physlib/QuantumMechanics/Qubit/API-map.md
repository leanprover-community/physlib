# Qubits

## Abstract (Alpha)

A qubit is a two-level quantum system, labelled by the two-element type of its computational basis.
A pure state of a qubit is a ket on that type, and a general state is a density matrix on it, both
coming from the theory of finite dimensional systems. What is specific to qubits is the standard
single-qubit gates, the controlled version of a unitary with a qubit as control, the Bloch sphere
with its angular parameterization and the geometric phase of triples of states, and, for pairs and
registers of qubits, entanglement and universality.

## Content (Alpha)

### States

A qubit {1} is labelled by the two-element type indexing its computational basis. [1] Its pure
states are kets of a finite dimensional system: functions on the basis normalized to unit length, with dual
bras, the bra-ket pairing, the normalization condition in both its componentwise and its
inner-product form, the computational basis states and the uniform superposition. [2] The product of
two systems carries product and entangled kets and the maximally entangled state, so that Bell-type
states of a pair of qubits can be written. [6] Two kets that differ by a unit complex number
represent the same physical state, and the quotient by this relation gives states up to a global
phase. [7]

### Gates

The standard single-qubit gates are the three Pauli gates, the Hadamard gate and the two phase
gates, each an element of the unitary group on a qubit. [3] Each squares to a known gate, the three
Pauli gates anticommute, the phase gates commute with the Pauli gate they are built from and with
each other, and conjugation by the Hadamard gate exchanges two of the Pauli gates. [4] A unitary on
an arbitrary register has a controlled version with a qubit as control; it acts as the unitary on
the block where the control is one, the controlled-NOT gate is the controlled Pauli X gate with its
familiar matrix, controlled gates compose as their targets do, and conjugating the control by a
Pauli gate has an explicit effect. [5]

The rotation gates about the three coordinate axes, together with a phase, decompose an arbitrary
single-qubit unitary, and conjugation by a single-qubit unitary is a rotation of the Bloch sphere.
[TODO]

### The Bloch sphere and geometric phase

The Bloch sphere is the unit sphere of three-dimensional Euclidean space, parameterized by a polar
and an azimuthal angle, and the dot product of two of its points is given in terms of those angles.
[8] A geodesic triangle on the Bloch sphere has a solid angle, and three pure states have a
Bargmann invariant, whose phase is invariant under cyclic permutation and negated under reversal of
the order, as an equation of angles, and whose norm is at most one. [9][10] This phase is
the geometric phase of Pancharatnam {2} and Berry {3}.

The Bloch vector of a state of a qubit is the triple of expectation values of the Pauli gates, and
it is a bijection from states onto the closed unit ball of three-dimensional Euclidean space.
[TODO] It restricts to a bijection from pure states up to a global phase onto the Bloch sphere,
so that the angular parameterization presents the pure state with the given polar and azimuthal
angles. [TODO] Every state of a qubit is one half of the identity plus a real combination of the
Pauli gates, and the identity together with the three Pauli gates is a basis of the self-adjoint two
by two complex matrices. [TODO]

### Measurement and distinguishability

Measuring a qubit in the computational basis gives the two outcomes with probabilities, by the Born
rule, equal to the squared norms of the components of the state. [TODO] The fidelity of two
states of a qubit has a closed form in terms of their traces and determinants. [TODO]

### Pairs and registers of qubits

The Bell basis of the states of a pair of qubits is orthonormal, and the standard gates have an
explicit action on it. [TODO] The singlet and triplet states of a pair of qubits split their
state space into an antisymmetric line and a symmetric plane. [TODO] The positive partial
transpose test is complete for a pair of qubits: such a state is separable exactly when its partial
transpose is positive semidefinite. [TODO]

The state space of a register of several qubits is an iterated product, and a single-qubit gate
extends to a gate acting on one component of a register. [TODO] The Hadamard gate, one phase gate
and the controlled-NOT gate generate a dense subgroup of the special unitary group of a register, so
that they are universal for quantum computation. [TODO] Kets on a qubit are the unit vectors of
the finite dimensional Hilbert space of a two-element type. [TODO]

## Lean References

1. QuantumInfo/States/Pure/Qubit.lean — `Qubit`
2. QuantumInfo/States/Pure/Braket.lean — `Ket`, `Bra`, `FunLike (Ket d) d ℂ`,
   `FunLike (Bra d) d ℂ`, `Coe (Ket d) (Bra d)`, `Coe (Bra d) (Ket d)`,
   `FunLike (Bra d) (Ket d) ℂ`, `dot`, `Ket.normalized`, `Ket.basis`, `uniform_superposition`,
   `Braket.dot_self_eq_one`
3. QuantumInfo/States/Pure/Qubit.lean — `Z`, `X`, `Y`, `H`, `S`, `T`
4. QuantumInfo/States/Pure/Qubit.lean — `Z_sq`, `X_sq`, `Y_sq`, `H_sq`, `S_sq`, `T_sq`,
   `X_Y_anticomm`, `Y_Z_anticomm`, `Z_X_anticomm`, `H_mul_X_eq_Z_mul_H`, `H_mul_Z_eq_X_mul_H`,
   `S_Z_comm`, `T_Z_comm`, `S_T_comm`
5. QuantumInfo/States/Pure/Qubit.lean — `controllize`, `CNOT`, `CNOT_matrix`,
   `controllize_apply_one_one`, `controllize_mul`, `controllize_one`, `controllize_mul_inv`,
   `X_controllize_X`
6. QuantumInfo/States/Pure/Braket.lean — `Ket.prod`, `Ket.IsProd`, `Ket.IsEntangled`, `Ket.MES`,
   `Ket.MES_isEntangled`
7. QuantumInfo/States/Pure/Braket.lean — `Ket.PhaseEquiv`, `KetUpToPhase`, `KetUpToPhase.mk`,
   `KetUpToPhase.lift`
8. QuantumInfo/States/Pure/BlochSphere.lean — `BlochSphere`, `blochPoint`, `blochPoint_val`,
   `dot_blochPoint`
9. QuantumInfo/States/Pure/BlochSphere.lean — `solidAngle`
10. QuantumInfo/States/Pure/BargmannInvariant.lean — `bargmannInvariantThree`,
   `bargmannPhaseThree`, `bargmannPhaseThree_cyclic`, `bargmannPhaseThree_reverse`,
   `norm_bargmannInvariantThree_le_one`

## References

1. M. A. Nielsen and I. L. Chuang, *Quantum Computation and Quantum Information*, Chapters 1, 2, 4
   and 9.
2. S. Pancharatnam, *Generalized theory of interference, and its applications*, Proc. Indian Acad.
   Sci. A 44, 247 (1956).
3. M. V. Berry, *Quantal phase factors accompanying adiabatic changes*, Proc. R. Soc. London A 392,
   45 (1984).
