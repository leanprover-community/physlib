/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.Metrics.Riemann

/-!

# Coordinate Ricci tensor

The Ricci tensor obtained by contracting the coordinate Riemann tensor.

## i. Overview

The Ricci tensor `Ric_{σν} = ∑ ρ, R^ρ_{σρν}` contracts the coordinate Riemann tensor in its first
and third indices.  Its contraction with the inverse metric, the scalar curvature, lives in
`Metrics/RicciScalar.lean`, and the chart-level wrappers `CoordinateMetric.ricciTensor` and
`CoordinateMetric.ricciScalar` live in `Metrics/CoordinateMetric.lean`.

## ii. Key results

- `CoordinateCurvature.ricciTensor` : coordinate Ricci tensor.
- `CoordinateCurvature.ricciTensor_const` : vanishing Ricci tensor for a constant metric.

## iii. Table of contents

- A. The Ricci tensor

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 3 (Sec. 3.2). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 8 & Ch. 13.
  [ref: mtw_1973_gravitation]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 3 (Sec. 3.7)
  (https://arxiv.org/pdf/gr-qc/9712019#page=80). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

namespace CoordinateCurvature

/-!

## A. The Ricci tensor

Contracting the Riemann tensor in its first and third indices gives the Ricci tensor.

-/

/-- The coordinate Ricci tensor `Ric_{σν} = ∑ ρ, R^ρ_{σρν}`. -/
noncomputable def ricciTensor {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n)
    (x : Fin n → ℝ) (σ ν : Fin n) : ℝ :=
  ∑ ρ, riemann g ginv x ρ σ ρ ν

/-- A constant metric is Ricci flat. -/
lemma ricciTensor_const {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) (G : Tensor2 n)
    (hg : ∀ x, g x = G) (x : Fin n → ℝ) (σ ν : Fin n) :
    ricciTensor g ginv x σ ν = 0 := by
  simp only [ricciTensor]
  apply Finset.sum_eq_zero
  intro ρ _
  exact riemann_const g ginv G hg x ρ σ ρ ν

end CoordinateCurvature


end GeneralRelativity
