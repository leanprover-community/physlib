/-
Copyright (c) 2026 Samyak Rai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samyak Rai
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.ZMod.Basic

/-!

# Pauli groups

The binary symplectic representation of the `n`-qubit Pauli group.

## i. Overview

An `n`-qubit Pauli operator is, up to a phase in `{1, -1, i, -i}`, a tensor product of the
single-qubit Pauli matrices `I`, `X`, `Y` and `Z`. The Pauli group `Gₙ` is the group these
operators generate under matrix multiplication. It has order `4^(n+1)`, and any two of its
elements either commute or anticommute.

Ignoring phases, a Pauli operator is described by two bit strings `x` and `z` of length `n`:
qubit `i` carries an `X` when `x i = 1` and a `Z` when `z i = 1`, so it carries a `Y` when both
are `1`. This identifies the quotient of the Pauli group by its phases with `(ℤ/2ℤ)^(2n)`,
represented here by the structure `PauliOp`. Under this identification, multiplication of Pauli
operators becomes componentwise addition of the bit strings, up to phase, and the commutator of
two operators is recorded by the symplectic product `PauliOp.symplectic`.

## ii. Key results

- `PauliOp` : the phase-free binary representation of an `n`-qubit Pauli operator.
- `PauliOp.symplectic` : the symplectic product detecting whether two Pauli operators commute.
- `PauliOp.symplectic_self` : the symplectic product of an operator with itself is zero.

## iii. Table of contents

- A. The binary representation of Pauli operators
- B. The symplectic product

## iv. References

- [Pauli group, Wikipedia](https://en.wikipedia.org/wiki/Pauli_group)
- [Nielsen and Chuang, Quantum Computation and Quantum Information][nielsen2010]

## A. The binary representation of Pauli operators

-/

/-- The binary symplectic representation of an `n`-qubit Pauli operator.

The fields `x` and `z` encode, for each qubit, the presence of an `X` and a `Z` factor:
qubit `i` carries `X` when `x i = 1`, `Z` when `z i = 1`, `Y` when both are `1`, and `I` when
both are `0`. The phase of the operator, an element of `{1, -1, i, -i}`, is not recorded. -/
@[ext]
structure PauliOp (n : ℕ) where
  /-- The `X` component of the Pauli operator. -/
  x : Fin n → ZMod 2
  /-- The `Z` component of the Pauli operator. -/
  z : Fin n → ZMod 2

namespace PauliOp

variable {n : ℕ}

/-!

## B. The symplectic product

-/

/-- The symplectic product of two Pauli operators.

Two `n`-qubit Pauli operators commute if and only if their symplectic product is `0`, and
anticommute if and only if it is `1`. -/
def symplectic (P Q : PauliOp n) : ZMod 2 :=
  ∑ i, (P.x i * Q.z i - P.z i * Q.x i)

/-- The symplectic product of a Pauli operator with itself is zero. -/
lemma symplectic_self (P : PauliOp n) : P.symplectic P = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  rw [mul_comm (P.z i) (P.x i), sub_self]

end PauliOp

/-
TODO:
- The additive group structure on `PauliOp n`, corresponding to multiplication of Pauli
  operators up to phase.
- Bilinearity and symmetry of the symplectic product.
- The interpretation map sending `PauliOp n` to a unitary on `n` qubits, a group homomorphism
  up to phase, and the lemma that `P.symplectic Q = 0` if and only if the operators commute.
-/
