/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Physlib.Meta.TODO.Basic
public import Physlib.ProbabilisticTheory.CStarAlgebra.CompletelyPositive
/-!

# The Hilbert space of a quantum system

## i. Overview

A quantum system is specified first of all by its Hilbert space of states: a complex Hilbert
space, that is a normed additive commutative group with a complex inner product, complete for
the induced norm.

`QuantumHilbertSpace HS` is a `variable_alias` for this collection of instances on a type `HS`.
It carries no data and is not a class. Its purpose is to state the assumptions of a quantum
system in one place: one only types

```
variable? (HS : Type*) [QuantumHilbertSpace HS]
```

and Lean inserts the instances `NormedAddCommGroup HS`, `InnerProductSpace ℂ HS` and
`CompleteSpace HS` itself, offering a `Try this` suggestion that appends them after `=>`.
Accepting it records the expanded form, which Lean then checks if the instances change.
A concrete system is given by its type, for example `Qubit`, on which these instances are found
directly.

The bounded operators `𝓑(H)` on a Hilbert space `H` form a C⋆-algebra. Its self-adjoint elements
are the bounded observables of the system. A quantum channel between two systems is a completely
positive channel between their bounded operators.

## ii. Key results

- `QuantumHilbertSpace` : the instances making a type a complex Hilbert space, the space of
  states of a quantum system.
- `𝓑(H)` : the bounded operators on a Hilbert space.
- `ProbabilisticTheory.quantum` : the probabilistic theory of the bounded observables.
- `QuantumMechanics.QuantumChannel` : the quantum channels between two quantum systems.

## iii. Table of contents

- A. The variable alias `QuantumHilbertSpace`
- B. The quantum theory of bounded observables

## iv. References

* None.

-/

@[expose] public section

open ProbabilisticTheory

namespace QuantumMechanics

/-!

## A. The variable alias `QuantumHilbertSpace`

-/

/-- The Hilbert space of a quantum system: the instances making `HS` a complex Hilbert space.
  This is a `variable_alias`, to be used with `variable?`. -/
@[variable_alias]
structure QuantumHilbertSpace (HS : Type*) [NormedAddCommGroup HS] [InnerProductSpace ℂ HS]
    [CompleteSpace HS]

TODO "Define kets and bras of a Hilbert space of states in a namespace `QuantumHilbertSpace`,
  e.g. `QuantumHilbertSpace.Ket` and `QuantumHilbertSpace.Bra`, with bra-ket notation."

TODO "Restate `QuantumSystem` as a Hilbert space of states, given via `QuantumHilbertSpace`,
  together with a choice of Hamiltonian."

/-!

## B. The quantum theory of bounded observables

-/

/-- The bounded operators `𝓑(H)` on a Hilbert space `H`. -/
scoped notation "𝓑(" H ")" => H →L[ℂ] H

variable? (H K : Type*) [QuantumHilbertSpace H] [QuantumHilbertSpace K] =>
  (H K : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The quantum theory whose observables are the self-adjoint bounded operators on the Hilbert
space `H`. -/
noncomputable abbrev _root_.ProbabilisticTheory.quantum : ProbabilisticTheory :=
  ofCStarAlgebra 𝓑(H)

/-- A quantum channel is a completely positive channel from `quantum H` to `quantum K`. -/
abbrev QuantumChannel := {Φ : Channel (quantum H) (quantum K) // Φ.IsCompletelyPositive}

end QuantumMechanics
