/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Mathlib.Algebra.Lie.Basic
/-!
# The zero Lie algebra on `Unit`

## i. Overview

`Unit` with the zero bracket is a Lie ring, and a Lie algebra over any commutative ring.
It is the Lie algebra of the trivial group, for example the gauge data of an empty list of
gauge factors.

## ii. Key results

- `instLieRingUnit`, `instLieAlgebraUnit` : the zero Lie algebra on `Unit`.

## iii. Table of contents

- A. The zero Lie algebra

-/

@[expose] public section

/-!

## A. The zero Lie algebra

-/

instance : Bracket Unit Unit := ⟨fun _ _ => ()⟩

instance instLieRingUnit : LieRing Unit where
  add_lie _ _ _ := rfl
  lie_add _ _ _ := rfl
  lie_self _ := rfl
  leibniz_lie _ _ _ := rfl

instance instLieAlgebraUnit {R : Type*} [CommRing R] : LieAlgebra R Unit where
  lie_smul _ _ _ := rfl
