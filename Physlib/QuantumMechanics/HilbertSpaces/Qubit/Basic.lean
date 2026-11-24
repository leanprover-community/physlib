/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import Physlib.QuantumMechanics.HilbertSpaces.Basic
public import Physlib.QuantumMechanics.HilbertSpaces.FiniteTarget.Basic
/-!

# The qubit

## i. Overview

A qubit is a quantum system with two basis states. Its Hilbert space is `𝓗[Fin 2]`, the finite
target Hilbert space over the two-element type `Fin 2`. The type `Qubit` is an abbreviation for
it, so the instances of a complex Hilbert space (`QuantumHilbertSpace`) and the lemmas about
`𝓗[Fin 2]` apply to `Qubit` directly. `Qubit.basis` is its standard orthonormal basis.

## ii. Key results

- `Qubit` : the Hilbert space of a qubit.
- `Qubit.basis` : its standard orthonormal basis, indexed by `Fin 2`.
- `Qubit.finrank_eq_two` : it has dimension two.

## iii. Table of contents

- A. The qubit and its basis

## iv. References

* None.

-/

@[expose] public section

namespace QuantumMechanics

/-!

## A. The qubit and its basis

-/

/-- The Hilbert space of a qubit, the quantum system with two basis states: `𝓗[Fin 2]`. -/
abbrev Qubit : Type := 𝓗[Fin 2]

namespace Qubit

/-- The standard orthonormal basis of the qubit, indexed by `Fin 2`. -/
noncomputable abbrev basis : OrthonormalBasis (Fin 2) ℂ Qubit :=
  FiniteHilbertSpace.basisFun (Fin 2)

lemma basis_apply (i : Fin 2) : basis i = ⟨EuclideanSpace.single i 1⟩ :=
  FiniteHilbertSpace.basisFun_apply i

/-- The Hilbert space of the qubit is two-dimensional. -/
lemma finrank_eq_two : Module.finrank ℂ Qubit = 2 := by
  rw [Module.finrank_eq_card_basis basis.toBasis, Fintype.card_fin]

end Qubit

end QuantumMechanics
