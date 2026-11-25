/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!

# Rank-2 component tensors and symmetry

Rank-2 covariant tensor components in a fixed frame or coordinate chart and symmetry predicates.

## i. Overview

A rank-2 covariant tensor in an `n`-dimensional coordinate chart or frame is represented as a real
`n × n` matrix of components (`Tensor2 n`). This module defines `Tensor2` and aliases `IsSymm` to
Mathlib's `Matrix.IsSymm` for use across `PhyslibAlpha.Relativity.Metrics` and
`PhyslibAlpha.Relativity.General`.

## ii. Key results

- `Tensor2` : rank-2 covariant tensor components in `n` dimensions.
- `IsSymm` : component symmetry of a rank-2 tensor (reusing `Matrix.IsSymm`).

## iii. Table of contents

- A. Rank-2 tensors and symmetry

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 2 (Sec. 2.3). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 3.
  [ref: mtw_1973_gravitation]
* B. O'Neill, *Semi-Riemannian Geometry With Applications to Relativity* (1983), Ch. 2.
  [ref: oneill_1983_semi_riemannian]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 1
  (https://arxiv.org/pdf/gr-qc/9712019#page=21). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

/-!

## A. Rank-2 tensors and symmetry

-/

/-- A rank-2 covariant tensor in a fixed frame or coordinate basis: a real matrix of
components. -/
abbrev Tensor2 (n : ℕ) : Type := Matrix (Fin n) (Fin n) ℝ

/-- Symmetry of a rank-2 tensor: `Tᵀ = T` (equivalently `T j i = T i j` for all indices `i`
and `j`). -/
abbrev IsSymm {n : ℕ} (T : Tensor2 n) : Prop := Matrix.IsSymm T

end GeneralRelativity
