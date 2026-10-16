# Qubits

A qubit is a two-level quantum system, and the data structure standing for one here is simply
the two element type labelling its computational basis. What is specific to qubits is the
standard single-qubit gates, the controlled version of a unitary with a qubit as control
register, and the Bloch sphere with its angular parameterization.

Qubit states are not built separately. A pure state of a qubit is a ket on the two element
type, defined for an arbitrary finite index type elsewhere, and a general state is a density
matrix on it. The ambient theory of a finite dimensional system — density matrices with their
evolution, measurements and distinguishability measures — is left to an API map of its own.

Two modules of the source directory, on the Bloch sphere and on the Bargmann invariant, are not
imported by the library root and so are not built with it. The two requirements citing them
record that, and are marked planned for that reason.

## Built on

- Kets and bras of a finite dimensional system — `QuantumInfo/States/Pure`
- Mixed states — `QuantumInfo/States/Mixed`

## Requirements

The key data structure is defined: the two element type labelling the computational basis of a
two-level quantum system. [1]

Kets and bras of a finite dimensional system are defined, with coercions to functions and to
each other, the bra-ket pairing, the normalization condition in both its componentwise and its
inner product form, the computational basis states and the uniform superposition. [2]

The standard single-qubit gates — the three Pauli gates, the Hadamard gate and the two phase
gates — are defined, each as an element of the unitary group on a qubit. [3]

Their squares are computed, the three Pauli gates anticommute, the phase gates commute with the
Pauli gate they are built from and with each other, and conjugation by the Hadamard gate
exchanges two of the Pauli gates. [4]

A unitary on an arbitrary register has a controlled version with a qubit as control, with its
entries on the block where the control is one, the controlled-NOT gate and its matrix, the
composition rules for controlled gates, and the effect of conjugating the control by a Pauli
gate. [5]

The Bloch sphere will be the unit sphere of three-dimensional Euclidean space, parameterized by
a polar and an azimuthal angle, with the dot product of two of its points given in terms of
those angles. It is stated already, in a module the library root does not import and which is
therefore not built. [8][planned]

The solid angle of a geodesic triangle on the Bloch sphere will be defined, together with the
Bargmann invariant of three pure states, its phase, the invariance of that phase under cyclic
permutation, its negation under reversal of the order as an equation of angles, and the bound
of one on the norm of the invariant. These too are stated in modules the library root does not
import. [9][10][planned]

The product of two systems carries product and entangled kets and the maximally entangled
state, so that Bell-type states of a pair of qubits can be written. [6]

States up to a global phase are defined, as the quotient of kets by the relation of differing
by a unit complex number. [7]

The Bloch vector of a state of a qubit, the triple of expectation values of the Pauli gates,
will be defined and shown to be a bijection from states onto the closed unit ball of
three-dimensional Euclidean space. [planned]

The Bloch vector will be shown to restrict to a bijection from pure states up to a global phase
onto the Bloch sphere, so that the parameterization above presents the pure state with the
given polar and azimuthal angles. [planned]

A state of a qubit will be decomposed as one half of the identity plus a real combination of
the Pauli gates, and the identity together with the three Pauli gates will be shown to be a
basis of the self-adjoint two by two complex matrices. [planned]

The rotation gates about the three coordinate axes will be defined, with the decomposition of
an arbitrary single-qubit unitary into such rotations and a phase, and the identification of
conjugation by a single-qubit unitary with a rotation of the Bloch sphere. [planned]

Measurement of a qubit in the computational basis will be defined, with the Born rule giving
the two outcome probabilities as the squared norms of the components of the state. [planned]

The Bell basis of the states of a pair of qubits will be defined, with its orthonormality and
the action of the standard gates on it. [planned]

The singlet and triplet states of a pair of qubits will be defined, with the splitting of their
state space into an antisymmetric line and a symmetric plane. [planned]

The fidelity of two states of a qubit will be given in closed form, in terms of their traces
and determinants. [planned]

The positive partial transpose test will be shown complete for a pair of qubits: such a state
is separable exactly when its partial transpose is positive semidefinite. [planned]

Registers of several qubits will be defined, the state space of a register being an iterated
product, and a single-qubit gate will extend to a gate acting on one component of a
register. [planned]

The Hadamard gate, one phase gate and the controlled-NOT gate will be shown to generate a dense
subgroup of the special unitary group of a register, so that they are universal for quantum
computation. [planned]

Qubits will be related to the finite dimensional Hilbert space of a two element target
elsewhere in the library, identifying kets on a qubit with the unit vectors of that Hilbert
space. [planned]

## Further reading

- M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum Information, Chapters 1, 2, 4 and 9
- S. Pancharatnam, Generalized theory of interference, and its applications, Proc. Indian Acad. Sci. A 44, 247 (1956)
- M. V. Berry, Quantal phase factors accompanying adiabatic changes, Proc. R. Soc. London A 392, 45 (1984)

## Lean declarations

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
