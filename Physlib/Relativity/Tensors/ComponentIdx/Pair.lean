/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Relativity.Tensors.ComponentIdx.Basic
/-!

# Component indices for two-index tensors

Component indices of two-index tensors as pairs of basis indices.

## i. Overview

This file defines the equivalence between component indices for two colors and pairs of basis
indices of those colors.

## ii. Key results

- `TensorSpecies.Tensor.ComponentIdx.pair` is the equivalence between `ComponentIdx cs` and
  `basisIdx (cs 0) × basisIdx (cs 1)`.

## iii. Table of contents

- A. The two-index equivalence

## iv. References

There are no known references for the material in this module.

-/

@[expose] public section

namespace TensorSpecies

variable {k : Type} [CommRing k] {C G : Type} [Group G]
  {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
  {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
  {rep : (c : C) → Representation k G (V c)}
  {b : (c : C) → Module.Basis (basisIdx c) k (V c)}
  {S : TensorSpecies k C G V basisIdx rep b}

namespace Tensor

/-!

## A. The two-index equivalence

-/

/-- The equivalence between component indices for two colors and pairs of basis indices of
those colors. -/
def ComponentIdx.pair {cs : Fin 2 → C} :
    ComponentIdx (S := S) cs ≃ basisIdx (cs 0) × basisIdx (cs 1) :=
  piFinTwoEquiv fun j => basisIdx (cs j)

lemma ComponentIdx.pair_apply {cs : Fin 2 → C} (b : ComponentIdx (S := S) cs) :
    ComponentIdx.pair (S := S) b = (b 0, b 1) := rfl

@[simp]
lemma ComponentIdx.pair_symm_apply_zero {cs : Fin 2 → C}
    (x : basisIdx (cs 0) × basisIdx (cs 1)) :
    (ComponentIdx.pair (S := S) (cs := cs)).symm x 0 = x.1 := rfl

@[simp]
lemma ComponentIdx.pair_symm_apply_one {cs : Fin 2 → C}
    (x : basisIdx (cs 0) × basisIdx (cs 1)) :
    (ComponentIdx.pair (S := S) (cs := cs)).symm x 1 = x.2 := rfl

end Tensor

end TensorSpecies
