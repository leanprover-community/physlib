/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LorentzGroup.Boosts.Axis
/-!
# Entries of an axis boost

The Hermiticity of a coordinate-axis boost in `SL(2, ℂ)`, read on its entries.

## i. Overview

A boost along a coordinate axis, `boostAxis i t ht`, is a Hermitian element of `SL(2, ℂ)`:
`Physlib.Relativity.LorentzGroup.Boosts.Axis` states this as the matrix equation
`(boostAxis i t ht).1ᴴ = (boostAxis i t ht).1`. Contracting an axis boost against a family
of tensor components needs that equation one entry at a time, which is what
`star_boostAxis_apply` provides: conjugating an entry transposes it.

## ii. Key results

- `Lorentz.SL2C.star_boostAxis_apply` : conjugating an entry of an axis boost transposes it.

## iii. Table of contents

- A. Hermiticity on the entries

## iv. References

The matrix form of the axis boosts is fixed in `Physlib.Relativity.LorentzGroup.Boosts.Axis`.

-/

@[expose] public section

open Matrix MatrixGroups

namespace Lorentz.SL2C

/-!

## A. Hermiticity on the entries

-/

/-- Hermiticity read on the entries: conjugating an entry of an axis boost transposes it. -/
lemma star_boostAxis_apply (i : Fin 3) (t : ℝ) (ht : t ≠ 0) (β α : Fin 2) :
    star ((boostAxis i t ht).1 β α) = (boostAxis i t ht).1 α β := by
  have h := congrFun (congrFun (boostAxis_conjTranspose i t ht) α) β
  rwa [Matrix.conjTranspose_apply] at h

end Lorentz.SL2C
