/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Basic

/-!

# Rank-2 component tensors and symmetry

Rank-2 covariant tensor components in a fixed frame or coordinate chart and symmetry predicates.

## i. Overview

A rank-2 covariant tensor in an `n`-dimensional coordinate chart or frame is represented as a real
`n × n` matrix of components (`Tensor2 n`). This module defines `Tensor2`, component symmetry
`IsSymm`, and basic symmetry lemmas used across `PhyslibAlpha.Relativity.Metrics` and
`PhyslibAlpha.Relativity.General`.

## ii. Key results

- `Tensor2` : rank-2 covariant tensor components in `n` dimensions.
- `IsSymm` : component symmetry of a rank-2 tensor.
- `isSymm_zero`, `isSymm_one`, `IsSymm.transpose` : basic symmetry properties.

## iii. Table of contents

- A. Rank-2 tensors and symmetry

## iv. References

* R. M. Wald, *General Relativity* (1984). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973). [ref: mtw_1973_gravitation]
* B. O'Neill, *Semi-Riemannian Geometry With Applications to Relativity* (1983).
  [ref: oneill_1983_semi_riemannian]

-/

@[expose] public section

namespace GeneralRelativity

/-!

## A. Rank-2 tensors and symmetry

-/

/-- A rank-2 covariant tensor in a fixed frame or coordinate basis: a real matrix of
components. -/
abbrev Tensor2 (n : ℕ) : Type := Matrix (Fin n) (Fin n) ℝ

/-- Symmetry of a rank-2 tensor: `T i j = T j i` for all indices `i` and `j`. -/
def IsSymm {n : ℕ} (T : Tensor2 n) : Prop := ∀ i j, T i j = T j i

/-- The zero tensor is symmetric. -/
lemma isSymm_zero {n : ℕ} : IsSymm (0 : Tensor2 n) := fun _ _ => rfl

/-- The identity tensor is symmetric. -/
lemma isSymm_one {n : ℕ} : IsSymm (1 : Tensor2 n) := by
  intro i j
  simp only [Matrix.one_apply]
  by_cases h : i = j
  · subst h
    simp only [↓reduceIte]
  · have h' : j ≠ i := fun hji => h hji.symm
    simp only [h, h', ↓reduceIte]

/-- A symmetric matrix equals its transpose. -/
lemma IsSymm.transpose {n : ℕ} {T : Tensor2 n} (h : IsSymm T) :
    Matrix.transpose T = T := by
  ext i j
  exact (h i j).symm

end GeneralRelativity
