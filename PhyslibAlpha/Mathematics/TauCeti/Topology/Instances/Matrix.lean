/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import Mathlib.Topology.Instances.Matrix

/-!

# Entrywise convergence of matrix series

A series of matrices converges if and only if every entry converges.

## i. Overview

The topology on `Matrix m n R` is the product topology, so a series of matrices `∑ₓ f x` has sum
`a` exactly when, for all indices `i` and `j`, the series of entries `∑ₓ f x i j` has sum
`a i j`. The same holds for summability. These statements are the matrix versions of
`Pi.hasSum` and `Pi.summable`, applied once for the rows and once for the columns.

## ii. Key results

- `Matrix.hasSum_iff` : a matrix series has sum `a` if and only if every entry series has the
  corresponding entry of `a` as its sum.
- `Matrix.summable_iff` : a matrix series is summable if and only if every entry series is.

## iii. Table of contents

- A. Entrywise convergence

## iv. References

There are no references for this file.

-/

@[expose] public section

namespace Matrix

variable {X m n R : Type*} [AddCommMonoid R] [TopologicalSpace R] {L : SummationFilter X}

/-!

## A. Entrywise convergence

-/

/-- A series of matrices has sum `a` if and only if, for every entry `(i, j)`, the series of
entries has sum `a i j`. -/
lemma hasSum_iff {f : X → Matrix m n R} {a : Matrix m n R} :
    HasSum f a L ↔ ∀ i j, HasSum (fun x => f x i j) (a i j) L :=
  Pi.hasSum.trans <| forall_congr' fun _ => Pi.hasSum

/-- A series of matrices is summable if and only if, for every entry `(i, j)`, the series of
entries is summable. -/
lemma summable_iff {f : X → Matrix m n R} :
    Summable f L ↔ ∀ i j, Summable (fun x => f x i j) L :=
  Pi.summable.trans <| forall_congr' fun _ => Pi.summable

end Matrix
