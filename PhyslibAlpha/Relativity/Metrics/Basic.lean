/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Set.Basic
public import PhyslibAlpha.Relativity.Tensors.Tensor2
import Mathlib.Tactic.Ring

/-!

# Nondegenerate metric tensors with explicit inverses

Pseudo-Riemannian metric components paired with a certified two-sided inverse matrix, and
coordinate metric fields on a regular chart.

## i. Overview

A nondegenerate metric (`MetricTensor n`) consists of covariant metric components `g : Tensor2 n`
together with an explicit two-sided inverse matrix `ginv : Tensor2 n` and component symmetry,
so contractions and trace operations use an inverse certified for that metric.

## ii. Key results

- `MetricTensor` : nondegenerate metric with its explicit two-sided inverse.
- `MetricTensor.ginv_symm` : the inverse of a symmetric metric is symmetric.
- `MetricTensor.sum_ginv_mul_g_left`, `MetricTensor.sum_ginv_mul_g_right`,
  `MetricTensor.sum_ginv_mul_g_apply`, `MetricTensor.sum_mul_ginv_g_apply` :
  componentwise inverse-metric contraction identities.
- `CoordinateMetric`, `CoordinateMetric.metricTensor` : coordinate metric field with its regular
  domain and pointwise `MetricTensor` restriction.

## iii. Table of contents

- A. Metric tensors with explicit inverses
- B. Coordinate metrics

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 2 (Sec. 2.3). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 13.
  [ref: mtw_1973_gravitation]
* B. O'Neill, *Semi-Riemannian Geometry With Applications to Relativity* (1983), Ch. 2.
  [ref: oneill_1983_semi_riemannian]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 2
  (https://arxiv.org/pdf/gr-qc/9712019#page=48). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

/-!

## A. Metric tensors with explicit inverses

Packaging the covariant metric and its two-sided inverse in `MetricTensor` supplies symmetric
index-contraction lemmas used throughout curvature calculations.

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

/-!

## B. Coordinate metrics

A `CoordinateMetric n` bundles a coordinate-dependent symmetric metric field with its inverse and
the chart domain on which they are two-sided inverses.

-/

/-- A coordinate-chart metric field `g` paired with its inverse `ginv` and regularity domain. -/
structure CoordinateMetric (n : ℕ) where
  /-- The covariant metric component field `g_{ij}(x)`. -/
  g : (Fin n → ℝ) → Tensor2 n
  /-- The contravariant inverse metric component field `g^{ij}(x)`. -/
  ginv : (Fin n → ℝ) → Tensor2 n
  /-- Regular coordinate domain where `g` is nondegenerate. -/
  domain : Set (Fin n → ℝ)
  /-- Symmetry of the covariant metric at every point. -/
  symm : ∀ x, IsSymm (g x)
  /-- Left-to-right inverse relation `g(x) * ginv(x) = 1` on `domain`. -/
  inv_left : ∀ x ∈ domain, g x * ginv x = 1
  /-- Right-to-left inverse relation `ginv(x) * g(x) = 1` on `domain`. -/
  inv_right : ∀ x ∈ domain, ginv x * g x = 1

/-- Restrict a coordinate metric to a pointwise `MetricTensor` at a regular point in its
domain. -/
def CoordinateMetric.metricTensor {n : ℕ} (C : CoordinateMetric n) (x : Fin n → ℝ)
    (hx : x ∈ C.domain) : MetricTensor n where
  g := C.g x
  ginv := C.ginv x
  symm := C.symm x
  inv_left := C.inv_left x hx
  inv_right := C.inv_right x hx

end GeneralRelativity
