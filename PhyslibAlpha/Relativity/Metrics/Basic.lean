/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import PhyslibAlpha.Relativity.Tensors.Tensor2
import Mathlib.Tactic.Ring

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
- `MetricTensor.sum_ginv_mul_g_left`, `MetricTensor.sum_ginv_mul_g_right`,
  `MetricTensor.sum_ginv_mul_g_apply`, `MetricTensor.sum_mul_ginv_g_apply` :
  componentwise inverse-metric contraction identities.

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
    rwa [Matrix.transpose_mul, Matrix.transpose_one, M.symm.eq] at h
  have hsq : Matrix.transpose M.ginv * M.g = M.ginv * M.g := by
    rw [htrans, M.inv_right]
  have hEq := congrArg (fun X : Tensor2 n => X * M.ginv) hsq
  simpa [IsSymm, Matrix.IsSymm, Matrix.mul_assoc, M.inv_left, M.inv_right] using hEq

/-- Left inverse contraction componentwise: `∑ k, g^{ik} g_{kj} = δ^i_j`. -/
lemma MetricTensor.sum_ginv_mul_g_left {n : ℕ} (M : MetricTensor n) (i j : Fin n) :
    (∑ k : Fin n, M.ginv i k * M.g k j) = if i = j then 1 else 0 := by
  simpa [Matrix.mul_apply, Matrix.one_apply] using congrFun (congrFun M.inv_right i) j

/-- Right inverse contraction componentwise: `∑ k, g_{ik} g^{kj} = δ_i^j`. -/
lemma MetricTensor.sum_ginv_mul_g_right {n : ℕ} (M : MetricTensor n) (i j : Fin n) :
    (∑ k : Fin n, M.g i k * M.ginv k j) = if i = j then 1 else 0 := by
  simpa [Matrix.mul_apply, Matrix.one_apply] using congrFun (congrFun M.inv_left i) j

/-- Vector-valued inverse-metric contraction `∑ k, g^{pk} ∑ m, g_{km} f(m) = f(p)`. -/
lemma MetricTensor.sum_ginv_mul_g_apply {n : ℕ} (M : MetricTensor n) (p : Fin n) (f : Fin n → ℝ) :
    (∑ k : Fin n, M.ginv p k * (∑ m : Fin n, M.g k m * f m)) = f p := by
  calc (∑ k : Fin n, M.ginv p k * (∑ m : Fin n, M.g k m * f m))
      = ∑ m : Fin n, f m * ∑ k : Fin n, M.ginv p k * M.g k m := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun m _ =>
          Finset.sum_congr rfl fun k _ => by ring
    _ = f p := by
        simp [M.sum_ginv_mul_g_left p]

/-- Lowering a raised vector via left-multiplication by `g`:
`∑ k, (∑ m, g^{km} f(m)) g_{kj} = f(j)`. -/
lemma MetricTensor.sum_mul_ginv_g_apply {n : ℕ} (M : MetricTensor n) (j : Fin n) (f : Fin n → ℝ) :
    (∑ k : Fin n, (∑ m : Fin n, M.ginv k m * f m) * M.g k j) = f j := by
  calc (∑ k : Fin n, (∑ m : Fin n, M.ginv k m * f m) * M.g k j)
      = ∑ k : Fin n, ∑ m : Fin n, f m * (M.g j k * M.ginv k m) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun m _ => by rw [M.symm.apply j k]; ring
    _ = ∑ m : Fin n, f m * ∑ k : Fin n, M.g j k * M.ginv k m := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun m _ => by rw [Finset.mul_sum]
    _ = f j := by
        simp [M.sum_ginv_mul_g_right j]

end GeneralRelativity
