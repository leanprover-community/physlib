/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Relativity.Tensors.ComponentIdx.Basic
/-!

# Component indices split at a single slot

Component-index insertion and evaluation at a distinguished slot.

## i. Overview

`ComponentIdx c` is `∀ j, basisIdx (c j)`, so singling out one slot `i` splits a component index
into the label there and a component index for the remaining colours `c ∘ i.succAbove`. That is
mathlib's `Fin.insertNthEquiv` read at the family `fun j => basisIdx (c j)`, and it carries no
transports of its own.

This is the one-slot counterpart of the two-slot `DropPairSection.ofFinEquiv`, which singles out
the pair a contraction consumes, and of `ComponentIdx.prod`, which splits a concatenated colour
list into its two halves. Where those two are shaped by the operation that produced the colour
list, this one is shaped by a slot the caller names, which is what a general-rank component formula
needs: an operation acting at slot `i` leaves the other slots alone, and the formula should say so
at every rank rather than at the rank where the colour list happens to be a literal.

## ii. Key results

- `TensorSpecies.Tensor.ComponentIdx.insert` : the equivalence splitting a component index at a
    named slot.
- `TensorSpecies.Tensor.ComponentIdx.insert_apply_self` and
    `TensorSpecies.Tensor.ComponentIdx.insert_apply_succAbove` : the two directions, slotwise.

## iii. Table of contents

- A. The single-slot equivalence

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

namespace ComponentIdx

/-!

## A. The single-slot equivalence

-/

/-- Splitting a component index at a named slot: the label at slot `i`, together with a component
index for the colours of the remaining slots. The dependent counterpart of `Fin.cons`, and the
single-slot analogue of the two-slot `DropPairSection.ofFinEquiv`. -/
def insert {n : ℕ} {c : Fin (n + 1) → C} (i : Fin (n + 1)) :
    basisIdx (c i) × ComponentIdx (S := S) (c ∘ i.succAbove) ≃ ComponentIdx (S := S) c :=
  Fin.insertNthEquiv (fun j => basisIdx (c j)) i

@[simp]
lemma insert_apply_self {n : ℕ} {c : Fin (n + 1) → C} (i : Fin (n + 1))
    (x : basisIdx (c i) × ComponentIdx (S := S) (c ∘ i.succAbove)) :
    insert (S := S) i x i = x.1 :=
  Fin.insertNth_apply_same (α := fun j => basisIdx (c j)) i x.1 x.2

@[simp]
lemma insert_apply_succAbove {n : ℕ} {c : Fin (n + 1) → C} (i : Fin (n + 1))
    (x : basisIdx (c i) × ComponentIdx (S := S) (c ∘ i.succAbove)) (m : Fin n) :
    insert (S := S) i x (i.succAbove m) = x.2 m :=
  Fin.insertNth_apply_succAbove (α := fun j => basisIdx (c j)) i x.1 x.2 m

end ComponentIdx

end Tensor

end TensorSpecies
