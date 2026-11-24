/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import Physlib.QuantumMechanics.HilbertSpaces.Basic
public import Physlib.QuantumMechanics.HilbertSpaces.FiniteTarget.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!

# Matrices as operators on a finite target Hilbert space

## i. Overview

A square matrix indexed by `d` acts on `𝓗[d]` through the standard basis. `toOperator` packages
this as a star algebra equivalence between `Matrix d d ℂ` and the bounded operators `𝓑(𝓗[d])`, so
that products, adjoints and unitaries of matrices correspond to those of operators. Identities
between operators can then be proved by computing with matrices, and general results such as
`IsSelfAdjoint.map` and `Unitary.map_mem` transfer self-adjointness and unitarity.

## ii. Key results

- `FiniteHilbertSpace.toOperator` : square matrices as operators on `𝓗[d]`.

## iii. Table of contents

- A. Matrices as operators

## iv. References

* None.

-/

@[expose] public section

namespace QuantumMechanics

namespace FiniteHilbertSpace

variable {d : Type*} [Fintype d] [DecidableEq d]

/-!

## A. Matrices as operators

-/

/-- Square matrices as operators on `𝓗[d]`, via the standard basis. This is a star algebra
equivalence, so products, adjoints and unitaries correspond. -/
noncomputable def toOperator : Matrix d d ℂ ≃⋆ₐ[ℂ] 𝓑(FiniteHilbertSpace d) :=
  Matrix.toEuclideanCLM.trans (isometryEquivEuclidean (d := d)).symm.conjStarAlgEquiv

end FiniteHilbertSpace

end QuantumMechanics
