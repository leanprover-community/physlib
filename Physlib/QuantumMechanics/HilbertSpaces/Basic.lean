/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Tactic.Variable
public import Physlib.Meta.TODO.Basic
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

## ii. Key results

- `QuantumHilbertSpace` : the instances making a type a complex Hilbert space, the space of
  states of a quantum system.

## iii. Table of contents

- A. The variable alias `QuantumHilbertSpace`

## iv. References

* None.

-/

@[expose] public section

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

TODO "Associate to a Hilbert space of states the `ProbabilisticTheory` of its bounded operators,
  giving states, effects and channels."

TODO "Restate `QuantumSystem` as a Hilbert space of states, given via `QuantumHilbertSpace`,
  together with a choice of Hamiltonian."

end QuantumMechanics
