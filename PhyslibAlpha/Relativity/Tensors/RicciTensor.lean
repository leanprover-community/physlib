/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import PhyslibAlpha.Relativity.Metrics.Basic
public import PhyslibAlpha.Relativity.Tensors.RiemannTensor

/-!

# The Ricci curvature tensor

Contraction of the algebraic Riemann tensor against a nondegenerate metric to form the symmetric
Ricci tensor.

## i. Overview

The Ricci tensor `ricci M R` performs the fully general contraction
`Ric_{ij} = ∑ k l, g^{kl} R_{kilj}` against an arbitrary metric `M : MetricTensor n`. It proves
symmetry of `ricci`, shows that `ricci_of_diag` simplifies to the single sum `∑ k, g^{kk} R_{kikj}`
when `M.ginv` is diagonal, and verifies that the flat curvature tensor is Ricci flat.

## ii. Key results

- `ricci` : general Ricci contraction `Ric_{ij} = ∑ k l, g^{kl} R_{kilj}`.
- `ricci_symm` : symmetry of the Ricci tensor.
- `ricci_of_diag` : reduction on diagonal inverse metrics.
- `ricci_flat` : the flat curvature tensor is Ricci flat.

## iii. Table of contents

- A. The Ricci tensor

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 3 (Sec. 3.2). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 13.
  [ref: mtw_1973_gravitation]
* B. O'Neill, *Semi-Riemannian Geometry With Applications to Relativity* (1983), Ch. 3.
  [ref: oneill_1983_semi_riemannian]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 3
  (https://arxiv.org/pdf/gr-qc/9712019#page=78). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

/-!

## A. The Ricci tensor

Contracting the first and third indices of a `RiemannTensor` against `M.ginv` yields the symmetric
Ricci curvature tensor `ricci M R`.

-/

/-- The general Ricci tensor `Ric_{ij} = ∑ k l, g^{kl} R_{kilj}` obtained by contracting the
first and third indices against the inverse metric. -/
noncomputable def ricci {n : ℕ} (M : MetricTensor n) (R : RiemannTensor n) : Tensor2 n :=
  fun i j => ∑ k, ∑ l, M.ginv k l * R.comp k i l j

/-- The Ricci tensor is symmetric, by symmetry of the inverse metric and pair symmetry of the
Riemann tensor. -/
lemma ricci_symm {n : ℕ} (M : MetricTensor n) (R : RiemannTensor n) : IsSymm (ricci M R) := by
  ext i j
  simp only [Matrix.transpose_apply, ricci]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [M.ginv_symm.apply l k, R.pair_symm k j l i]

/-- For a metric with a diagonal inverse (`g^{kl} = 0` for `k ≠ l`), the Ricci contraction
reduces to the single sum `∑ k, g^{kk} R_{kikj}`. -/
lemma ricci_of_diag {n : ℕ} (M : MetricTensor n) (R : RiemannTensor n)
    (hdiag : ∀ k l, k ≠ l → M.ginv k l = 0) (i j : Fin n) :
    ricci M R i j = ∑ k, M.ginv k k * R.comp k i k j := by
  simp only [ricci]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k]
  · intro l _ hlk
    rw [hdiag k l hlk.symm, zero_mul]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- The flat curvature tensor is Ricci flat. -/
@[simp]
lemma ricci_flat (n : ℕ) (M : MetricTensor n) : ricci M (RiemannTensor.flat n) = 0 := by
  ext i j
  simp [ricci]

end GeneralRelativity
