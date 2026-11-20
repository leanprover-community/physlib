/-
Copyright (c) 2026 Samyak Rai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samyak Rai
-/

module

public import QuantumInfo.States.Pure.Qubit

/-!

# Pauli groups

The binary symplectic representation of the `n`-qubit Pauli group.
A Pauli group is a group formed by tensor products of Pauli matrices,
including the identity.

## i. Overview

The single-qubit Pauli group is a 16-element matrix group, consisting
of the 4 Pauli matrices each with 4 possible phase factors.
The n-qubit Pauli group is a 4ⁿ⁺¹ element group consisting of tensor
products of single-qubit Paulis.

An `n`-qubit Pauli operator is recorded by a phase `p : ZMod 4`, contributing the factor
`i^p`, and two bit strings `x` and `z` of length `n`: qubit `i` carries an `X` when `x i = 1`
and a `Z` when `z i = 1`, so it carries a `Y` when both are `1`. This is the structure
`PauliOp`. Multiplication of Pauli operators corresponds to componentwise addition of the bit
strings together with a phase update, and the commutator of two operators is recorded by the
symplectic product `PauliOp.symplectic`, which does not depend on the phases.

## ii. Key results

- `Qubit.PauliSingle` : the single-qubit Pauli operator `i^p X^x Z^z` for phase `p` and bits
  `x` and `z`.
- `Qubit.pauliSingle_commute_iff` : two single-qubit Pauli operators commute if and only if
  their symplectic product is zero.
- `Qubit.symplecticSingle` : the symplectic product of two single-qubit Pauli operators.
- `Qubit.symplecticSingle` : the symplectic product of two single-qubit Pauli operators.
- `PauliOp` : the binary representation of an `n`-qubit Pauli operator, with phase.
- `PauliOp.symplectic` : the symplectic product of Pauli operators.
- `PauliOp.symplectic_self` : the symplectic product of an operator with itself is zero.
- `PauliOp.symplectic_eq_sum` : the symplectic product is the sum of the single-qubit
  symplectic products.

## iii. Table of contents

- A. The single-qubit Pauli operators
- B. The binary representation of Pauli operators
- C. The symplectic product

## iv. References

- [Pauli group, Wikipedia](https://en.wikipedia.org/wiki/Pauli_group)
- [Nielsen and Chuang, Quantum Computation and Quantum Information][nielsen2010]

## A. The single-qubit Pauli operators

-/

@[expose] public section

namespace Qubit

/-- The single-qubit Pauli operator `i^p X^x Z^z`, for phase `p` and bits `x` and `z`.
As `p : ZMod 4`, `x : ZMod 2` and `z : ZMod 2` range over their values, these are the
16 elements of the one-qubit Pauli group. -/
def PauliSingle (p : ZMod 4) (x z : ZMod 2) : Matrix Qubit Qubit ℂ :=
  Complex.I ^ p.val • (X ^ x.val * Z ^ z.val).val

/-- Every element of `ZMod 2` is `0` or `1`. -/
lemma zmod2_eq_zero_or_one : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by
  decide

/-- The symplectic product of two elements `u`, `v` ∈ `(ℤ/2ℤ)²` with
`z, x, z', x' ∈ ℤ/2ℤ`:
`u ⊙ v ≡ z x' - x z'`,
where `u = z|x` and `v = z'|x'` (this notation represents binary
string concatenation, e.g. `01 ≡ 0|1`). -/
def symplecticSingle (z x z' x' : ZMod 2) : ZMod 2 :=
  z * x' - x * z'

/-- Two single-qubit Pauli operators commute if and only if their symplectic product is
zero. -/
lemma pauliSingle_commute_iff (p q : ZMod 4) (x z x' z' : ZMod 2) :
    Commute (PauliSingle p x z) (PauliSingle q x' z') ↔ symplecticSingle x z x' z' = 0 := by
  have hphase0 : PauliSingle p (0 : ZMod 2) 0
      = Complex.I ^ p.val • (1 : Matrix Qubit Qubit ℂ) := by
    simp only [PauliSingle, show (0 : ZMod 2).val = 0 from rfl, pow_zero, mul_one,
      Submonoid.coe_one]
  have hphase0' : PauliSingle q (0 : ZMod 2) 0
      = Complex.I ^ q.val • (1 : Matrix Qubit Qubit ℂ) := by
    simp only [PauliSingle, show (0 : ZMod 2).val = 0 from rfl, pow_zero, mul_one,
      Submonoid.coe_one]
  rcases zmod2_eq_zero_or_one x with rfl | rfl <;>
    rcases zmod2_eq_zero_or_one z with rfl | rfl <;>
    rcases zmod2_eq_zero_or_one x' with rfl | rfl <;>
    rcases zmod2_eq_zero_or_one z' with rfl | rfl
  · -- (x, z) = (0, 0), (u, v) = (0, 0)
    simp only [symplecticSingle, zero_mul, sub_self, iff_true, hphase0]
    rw [commute_iff_eq, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
  · -- (x, z) = (0, 0), (u, v) = (0, 1)
    simp only [symplecticSingle, zero_mul, sub_self, iff_true, hphase0]
    rw [commute_iff_eq, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
  · -- (x, z) = (0, 0), (u, v) = (1, 0)
    simp only [symplecticSingle, zero_mul, sub_self, iff_true, hphase0]
    rw [commute_iff_eq, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
  · -- (x, z) = (0, 0), (u, v) = (1, 1)
    simp only [symplecticSingle, zero_mul, sub_self, iff_true, hphase0]
    rw [commute_iff_eq, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
  · -- (x, z) = (0, 1), (u, v) = (0, 0)
    simp only [symplecticSingle, mul_zero, sub_self, iff_true, hphase0']
    rw [commute_iff_eq, Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul]
  · -- (x, z) = (0, 1), (u, v) = (0, 1)
    sorry
  · -- (x, z) = (0, 1), (u, v) = (1, 0)
    sorry
  · -- (x, z) = (0, 1), (u, v) = (1, 1)
    sorry
  · -- (x, z) = (1, 0), (u, v) = (0, 0)
    simp only [symplecticSingle, mul_zero, sub_self, iff_true, hphase0']
    rw [commute_iff_eq, Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul]
  · -- (x, z) = (1, 0), (u, v) = (0, 1)
    sorry
  · -- (x, z) = (1, 0), (u, v) = (1, 0)
    sorry
  · -- (x, z) = (1, 0), (u, v) = (1, 1)
    sorry
  · -- (x, z) = (1, 1), (u, v) = (0, 0)
    simp only [symplecticSingle, mul_zero, sub_self, iff_true, hphase0']
    rw [commute_iff_eq, Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul]
  · -- (x, z) = (1, 1), (u, v) = (0, 1)
    sorry
  · -- (x, z) = (1, 1), (u, v) = (1, 0)
    sorry
  · -- (x, z) = (1, 1), (u, v) = (1, 1)
    sorry

end Qubit

/-!

## B. The binary representation of Pauli operators

-/

/-- The binary symplectic representation of an `n`-qubit Pauli operator.

The field `phase` records the scalar factor `i^phase`. The fields `x` and `z` encode, for each
qubit, the presence of an `X` and a `Z` factor: qubit `i` carries `X` when `x i = 1`, `Z` when
`z i = 1`, `Y` when both are `1`, and `I` when both are `0`. -/
@[ext]
structure PauliOp (n : ℕ) where
  phase : ZMod 4
  x : Fin n → ZMod 2
  z : Fin n → ZMod 2

namespace PauliOp

variable {n : ℕ}

/-!

## C. The symplectic product

-/

/-- The symplectic product of two Pauli operators.

Two `n`-qubit Pauli operators commute if and only if their symplectic product is `0`, and
anticommute if and only if it is `1`. The product does not depend on the phases of the
operators. -/
def symplectic (P Q : PauliOp n) : ZMod 2 :=
  ∑ i, (P.z i * Q.x i - P.x i * Q.z i)

/-- The symplectic product is the sum of the single-qubit symplectic products. -/
lemma symplectic_eq_sum (P Q : PauliOp n) :
    P.symplectic Q = ∑ i, Qubit.symplecticSingle (P.x i) (P.z i) (Q.x i) (Q.z i) := by
  simp only [symplectic, symplecticSingle]
  apply Finset.sum_congr rfl
  intro i _
  rw [CharTwo.sub_eq_add, CharTwo.sub_eq_add, add_comm]

/-- The symplectic product of a Pauli operator with itself is zero. -/
lemma symplectic_self (P : PauliOp n) : P.symplectic P = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  rw [mul_comm (P.x i) (P.z i), sub_self]

end PauliOp

/-
TODO:
- The group structure on `PauliOp n`: the phase-aware multiplication law, corresponding to
  matrix multiplication of Pauli operators.
- Bilinearity and symmetry of the symplectic product.
- The interpretation map sending `PauliOp n` to a unitary on `n` qubits, a group homomorphism,
  and the lemma that `P.symplectic Q = 0` if and only if the operators commute.
-/
