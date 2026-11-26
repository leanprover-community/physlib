/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import PhyslibAlpha.Relativity.Metrics.Basic
import Mathlib.Tactic.Ring

/-!

# Metric trace of rank-2 tensors

Full contraction `g^{ij} T_{ij}` of a rank-2 tensor against a nondegenerate inverse metric.

## i. Overview

Given a nondegenerate metric `M : MetricTensor n`, the metric trace `metricTrace M T` contracts
`M.ginv` with `T`. This module establishes its linearity under pointwise sums, differences, and
scalar multiples, as well as the dimension identity `g^{ij} g_{ij} = n`.

## ii. Key results

- `metricTrace`, `metricTrace_zero`, `metricTrace_diag` : full contraction `g^{ij} T_{ij}`,
  vanishing on the zero tensor, and diagonal reduction.
- `metricTrace_add_fun`, `metricTrace_sub_fun`, `metricTrace_smul` : linearity of the trace.
- `sum_ginv_mul_g`, `metricTrace_mul_g` : `g^{ij} g_{ij} = n`.

## iii. Table of contents

- A. Metric trace and linearity

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 2 (Sec. 2.3). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 3 & Ch. 13.
  [ref: mtw_1973_gravitation]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 2
  (https://arxiv.org/pdf/gr-qc/9712019#page=48). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

variable {n : ℕ}

/-!

## A. Metric trace and linearity

-/

/-- Full contraction of the inverse metric with a rank-2 tensor, `g^{ij} T_{ij}`. -/
def metricTrace (M : MetricTensor n) (T : Tensor2 n) : ℝ := ∑ i, ∑ j, M.ginv i j * T i j

/-- The metric trace of the zero tensor vanishes identically. -/
@[simp]
lemma metricTrace_zero {n : ℕ} (M : MetricTensor n) : metricTrace M 0 = 0 := by
  simp [metricTrace]

/-- `metricTrace` is additive over pointwise sums. -/
lemma metricTrace_add_fun {n : ℕ} (M : MetricTensor n) (A B : Tensor2 n) :
    metricTrace M (fun i j => A i j + B i j) = metricTrace M A + metricTrace M B := by
  simp only [metricTrace]
  have h : ∀ i, (∑ j, M.ginv i j * (A i j + B i j))
      = (∑ j, M.ginv i j * A i j) + (∑ j, M.ginv i j * B i j) := by
    intro i
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_add_distrib]

/-- `metricTrace` preserves pointwise differences. -/
lemma metricTrace_sub_fun {n : ℕ} (M : MetricTensor n) (A B : Tensor2 n) :
    metricTrace M (fun i j => A i j - B i j) = metricTrace M A - metricTrace M B := by
  simp only [metricTrace]
  have h : ∀ i, (∑ j, M.ginv i j * (A i j - B i j))
      = (∑ j, M.ginv i j * A i j) - (∑ j, M.ginv i j * B i j) := by
    intro i
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_sub_distrib]

/-- `metricTrace` pulls out a scalar factor. -/
lemma metricTrace_smul {n : ℕ} (M : MetricTensor n) (c : ℝ) (A : Tensor2 n) :
    metricTrace M (fun i j => c * A i j) = c * metricTrace M A := by
  simp only [metricTrace]
  have h : ∀ i, (∑ j, M.ginv i j * (c * A i j)) = c * (∑ j, M.ginv i j * A i j) := by
    intro i
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [Finset.sum_congr rfl (fun i _ => h i), ← Finset.mul_sum]

/-- `∑ i j, g^{ij} g_{ij} = n`, i.e. the trace of `g^{-1} g` is the dimension. -/
lemma sum_ginv_mul_g (M : MetricTensor n) :
    (∑ i, ∑ j, M.ginv i j * M.g i j) = (n : ℝ) := by
  have h1 : ∀ i, (∑ j, M.ginv i j * M.g i j) = (M.ginv * M.g) i i := by
    intro i
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl (fun j _ => by rw [M.symm.apply j i])
  calc (∑ i, ∑ j, M.ginv i j * M.g i j)
      = ∑ i, (M.ginv * M.g) i i := Finset.sum_congr rfl (fun i _ => h1 i)
    _ = ∑ i, (1 : Tensor2 n) i i := by rw [M.inv_right]
    _ = (n : ℝ) := by simp

/-- Tracing a scalar multiple of the metric against itself yields `c * n`. -/
lemma metricTrace_mul_g {n : ℕ} (M : MetricTensor n) (c : ℝ) :
    metricTrace M (fun i j => c * M.g i j) = c * (n : ℝ) := by
  rw [metricTrace_smul]
  simp only [metricTrace]
  rw [sum_ginv_mul_g]

/-- For an inverse metric whose off-diagonal entries vanish, `metricTrace` collapses to the
diagonal sum `∑ i, M.ginv i i * T i i`. -/
lemma metricTrace_diag {n : ℕ} (M : MetricTensor n) (T : Tensor2 n)
    (hdiag : ∀ i j : Fin n, i ≠ j → M.ginv i j = 0) :
    metricTrace M T = ∑ i : Fin n, M.ginv i i * T i i := by
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Finset.sum_eq_single i (fun j _ hj => by simp [hdiag i j hj.symm]) (by simp)

end GeneralRelativity
