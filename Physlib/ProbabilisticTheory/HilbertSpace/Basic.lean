/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Physlib.ProbabilisticTheory.CStarAlgebra.OrderUnit
public import Physlib.ProbabilisticTheory.StarAlgebra.State

/-!
# Bounded operators on a Hilbert space

The bounded operators `𝓑(H)` on a Hilbert space `H` describe a quantum system.

## i. Overview

A quantum system has a complex Hilbert space `H`. Its operators are the bounded linear maps
`𝓑(H)` a C⋆-algebra.
Its observables are the self-adjoint operators `Observable 𝓑(H)`. They form an
Archimedean order-unit space with the identity as unit.

## ii. Key results

- `𝓑(H)` : the bounded operators on `H`.

## iii. Table of contents

- A. Bounded operators

## iv. References

* None.
-/

@[expose] public section

/-! ## A. Bounded operators -/

/-- The bounded operators `𝓑(H)` on a complex inner product space `H`. -/
notation "𝓑(" H ")" => H →L[ℂ] H
