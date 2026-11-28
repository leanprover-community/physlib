/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic

/-!

# Splitting a sum over `Fin 5`

A sum over `Fin 5` written as a sum over `Fin 4` plus its last term.

## i. Overview

`Fin.sum_univ_castSucc` splits the sum of a family over `Fin (n + 1)` into the sum over the
first `n` indices and the last term. Specialised to `n = 4` this is the form needed when a
five-dimensional expression is cut into four directions and one extra direction, as in the
Kaluza–Klein metric.

## ii. Key results

- `sum_fin5_split` : a sum over `Fin 5` as a sum over `Fin 4` plus the last term.

## iii. Table of contents

- A. Splitting a sum over `Fin 5`

## iv. References

* None.

-/

@[expose] public section

/-!

## A. Splitting a sum over `Fin 5`

-/

/-- Split a sum over `Fin 5` into its first four terms and the last term. -/
lemma sum_fin5_split (f : Fin 5 → ℝ) :
    (∑ k : Fin 5, f k) = (∑ k : Fin 4, f ⟨k.val, by omega⟩) + f 4 := by
  rw [Fin.sum_univ_castSucc]
  rfl
