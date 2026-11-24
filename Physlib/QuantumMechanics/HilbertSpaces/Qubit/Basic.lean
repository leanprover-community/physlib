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
target Hilbert space over the two-element type `Fin 2`. The type `QubitSpace` is an abbreviation for
it, so the instances of a complex Hilbert space (`QuantumHilbertSpace`) and the lemmas about
`𝓗[Fin 2]` apply to `QubitSpace` directly. `QubitSpace.basis` is its standard orthonormal basis.

## ii. Key results

- `QubitSpace` : the Hilbert space of a qubit.
- `QubitSpace.basis` : its standard orthonormal basis, indexed by `Fin 2`.
- `QubitSpace.finrank_eq_two` : it has dimension two.

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
abbrev QubitSpace : Type := 𝓗[Fin 2]

namespace QubitSpace

/-- The standard orthonormal basis of the qubit, indexed by `Fin 2`. -/
noncomputable def basis : OrthonormalBasis (Fin 2) ℂ QubitSpace :=
  FiniteHilbertSpace.basisFun (Fin 2)

lemma basis_apply (i : Fin 2) : basis i = ⟨EuclideanSpace.single i 1⟩ :=
  FiniteHilbertSpace.basisFun_apply i

/-- The Hilbert space of the qubit is two-dimensional. -/
lemma finrank_eq_two : Module.finrank ℂ QubitSpace = 2 := by
  rw [Module.finrank_eq_card_basis basis.toBasis, Fintype.card_fin]

end QubitSpace

end QuantumMechanics
