/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.Tensors.Tensor2

/-!

# Nondegenerate metric tensors with explicit inverses

Pseudo-Riemannian metric components paired with a certified two-sided inverse matrix.

## i. Overview

A nondegenerate metric (`MetricTensor n`) bundles covariant metric components `g : Tensor2 n`
together with an explicit two-sided inverse matrix `ginv : Tensor2 n` and component symmetry,
so contractions and trace operations use an inverse certified for that metric.

## ii. Key results

- `MetricTensor` : nondegenerate metric bundled with its two-sided inverse.
- `MetricTensor.ginv_symm` : the inverse of a symmetric metric is symmetric.

## iii. Table of contents

- A. Metric tensors with explicit inverses

## iv. References

* R. M. Wald, *General Relativity* (1984). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973). [ref: mtw_1973_gravitation]
* B. O'Neill, *Semi-Riemannian Geometry With Applications to Relativity* (1983).
  [ref: oneill_1983_semi_riemannian]

-/

@[expose] public section

namespace GeneralRelativity

/-!

## A. Metric tensors with explicit inverses

-/

/-- A nondegenerate metric in components, carried together with an explicit two-sided
inverse. -/
structure MetricTensor (n : ℕ) where
  /-- The covariant metric components `g_{ij}`. -/
  g : Tensor2 n
  /-- The contravariant inverse metric components `g^{ij}`. -/
  ginv : Tensor2 n
  /-- Symmetry of the covariant metric components. -/
  symm : IsSymm g
  /-- Left-to-right inverse relation `g * ginv = 1`. -/
  inv_left : g * ginv = 1
  /-- Right-to-left inverse relation `ginv * g = 1`. -/
  inv_right : ginv * g = 1

/-- The inverse of a symmetric metric is itself symmetric. -/
lemma MetricTensor.ginv_symm {n : ℕ} (M : MetricTensor n) : IsSymm M.ginv := by
  have htrans : Matrix.transpose M.ginv * M.g = 1 := by
    have h := congrArg Matrix.transpose M.inv_left
    rwa [Matrix.transpose_mul, Matrix.transpose_one, IsSymm.transpose M.symm] at h
  have hsq : Matrix.transpose M.ginv * M.g = M.ginv * M.g := by
    rw [htrans, M.inv_right]
  have hEq : Matrix.transpose M.ginv = M.ginv := by
    have h := congrArg (fun X : Tensor2 n => X * M.ginv) hsq
    simpa [Matrix.mul_assoc, M.inv_left, M.inv_right] using h
  intro i j
  exact (congrFun (congrFun hEq i) j).symm

end GeneralRelativity
