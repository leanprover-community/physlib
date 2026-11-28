/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.Metrics.Basic
import Mathlib.Tactic.Ring

/-!

# Conformal rescalings of a metric tensor

Conformal transformations `g̃ = φ g` preserving nondegeneracy and inverse symmetry.

## i. Overview

A conformal rescaling multiplies a spacetime metric `g` by a nowhere-vanishing scalar factor `φ`.
This module defines `conformalMetric` packaging the rescaled metric and inverse as a `MetricTensor`,
together with the underlying componentwise rescalings `conformalRescaleMetric` and
`conformalRescaleMetricInv` and their two-sided inverse relations.

## ii. Key results

- `conformalMetric` : conformal rescaling `g̃ = φ g` packaged as a `MetricTensor`.
- `conformalRescaleMetric`, `conformalRescaleMetricInv` : componentwise conformal rescalings of a
  metric and its inverse.
- `conformalRescaleMetric_mul`, `conformalRescaleMetricInv_mul` : two-sided inverse relations for
  `φ ≠ 0`.

## iii. Table of contents

- A. Conformal rescalings

## iv. References

* R. M. Wald, *General Relativity* (1984), App. D. [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 13.
  [ref: mtw_1973_gravitation]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 3
  (https://arxiv.org/pdf/gr-qc/9712019#page=84). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

/-!

## A. Conformal rescalings

Rescaling a metric by a nowhere-vanishing scalar factor `φ` preserves symmetry and scales the
inverse metric by `φ⁻¹`.

-/

/-- A conformal rescaling `g̃ = φ g` of a metric, with inverse `φ⁻¹ g⁻¹`, underlying the
Jordan-to-Einstein frame transformation. -/
noncomputable def conformalMetric {n : ℕ} (M : MetricTensor n) (φ : ℝ) (hφ : φ ≠ 0) :
    MetricTensor n where
  g := Matrix.of fun i j => φ * M.g i j
  ginv := Matrix.of fun i j => φ⁻¹ * M.ginv i j
  symm := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    rw [M.symm.apply j i]
  inv_left := by
    ext i j
    rw [Matrix.mul_apply]
    have hterm : ∀ k, (Matrix.of fun i j => φ * M.g i j) i k *
        (Matrix.of fun i j => φ⁻¹ * M.ginv i j) k j = M.g i k * M.ginv k j := by
      intro k
      simp only [Matrix.of_apply]
      calc (φ * M.g i k) * (φ⁻¹ * M.ginv k j)
          = (φ * φ⁻¹) * (M.g i k * M.ginv k j) := by ring
        _ = M.g i k * M.ginv k j := by rw [mul_inv_cancel₀ hφ, one_mul]
    rw [Finset.sum_congr rfl (fun k _ => hterm k)]
    simpa only [Matrix.mul_apply] using congrFun (congrFun M.inv_left i) j
  inv_right := by
    ext i j
    rw [Matrix.mul_apply]
    have hterm : ∀ k, (Matrix.of fun i j => φ⁻¹ * M.ginv i j) i k *
        (Matrix.of fun i j => φ * M.g i j) k j = M.ginv i k * M.g k j := by
      intro k
      simp only [Matrix.of_apply]
      calc (φ⁻¹ * M.ginv i k) * (φ * M.g k j)
          = (φ⁻¹ * φ) * (M.ginv i k * M.g k j) := by ring
        _ = M.ginv i k * M.g k j := by rw [inv_mul_cancel₀ hφ, one_mul]
    rw [Finset.sum_congr rfl (fun k _ => hterm k)]
    simpa only [Matrix.mul_apply] using congrFun (congrFun M.inv_right i) j

/-- Componentwise conformal rescaling `g̃ = φ g` of a rank-2 tensor. -/
def conformalRescaleMetric {n : ℕ} (g : Tensor2 n) (φ : ℝ) : Tensor2 n := fun i j => φ * g i j

/-- Componentwise conformal inverse rescaling `g̃⁻¹ = φ⁻¹ g⁻¹`. -/
noncomputable def conformalRescaleMetricInv {n : ℕ} (ginv : Tensor2 n) (φ : ℝ) : Tensor2 n :=
  fun i j => φ⁻¹ * ginv i j

/-- The rescaled metric times its rescaled inverse equals the identity. -/
lemma conformalRescaleMetric_mul {n : ℕ} (M : MetricTensor n) (φ : ℝ) (hφ : φ ≠ 0) :
    conformalRescaleMetric M.g φ * conformalRescaleMetricInv M.ginv φ = 1 :=
  (conformalMetric M φ hφ).inv_left

/-- The rescaled inverse times the rescaled metric equals the identity. -/
lemma conformalRescaleMetricInv_mul {n : ℕ} (M : MetricTensor n) (φ : ℝ) (hφ : φ ≠ 0) :
    conformalRescaleMetricInv M.ginv φ * conformalRescaleMetric M.g φ = 1 :=
  (conformalMetric M φ hφ).inv_right

end GeneralRelativity
