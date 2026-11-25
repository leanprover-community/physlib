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
This module defines the rescaled metric and inverse components (`conformalRescaleMetric` and
`conformalRescaleMetricInv`),
proves their two-sided inverse relations, and packages the rescaled `MetricTensor` as
`conformalMetric`.

## ii. Key results

- `conformalRescaleMetric`, `conformalRescaleMetricInv` : componentwise conformal rescalings of a
  metric and its inverse.
- `conformalG_mul`, `conformalGinv_mul` : two-sided inverse relations for `φ ≠ 0`.
- `conformalMetric` : conformal rescaling `g̃ = φ g` packaged as a `MetricTensor`.

## iii. Table of contents

- A. Conformal rescalings

## iv. References

* R. M. Wald, *General Relativity* (1984). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973). [ref: mtw_1973_gravitation]

-/

@[expose] public section

namespace GeneralRelativity

/-!

## A. Conformal rescalings

-/

/-- Componentwise conformal rescaling of a metric, `g̃ = φ g`. Kept as a standalone matrix
operation separately from `conformalMetric` so coordinate metric fields such as `nordstromMetric`
can reuse the formula before packaging a `MetricTensor`. -/
def conformalRescaleMetric {n : ℕ} (g : Tensor2 n) (φ : ℝ) : Tensor2 n := fun i j => φ * g i j

/-- Corresponding inverse metric components `g̃⁻¹ = φ⁻¹ g⁻¹`, kept alongside
`conformalRescaleMetric` for coordinate metric fields prior to `MetricTensor` bundling. -/
noncomputable def conformalRescaleMetricInv {n : ℕ} (ginv : Tensor2 n) (φ : ℝ) : Tensor2 n :=
  fun i j => φ⁻¹ * ginv i j

/-- The rescaled metric times its rescaled inverse equals the identity. -/
lemma conformalG_mul {n : ℕ} (M : MetricTensor n) (φ : ℝ) (hφ : φ ≠ 0) :
    conformalRescaleMetric M.g φ * conformalRescaleMetricInv M.ginv φ = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have hterm : ∀ k,
      conformalRescaleMetric M.g φ i k * conformalRescaleMetricInv M.ginv φ k j
        = M.g i k * M.ginv k j := by
    intro k
    simp only [conformalRescaleMetric, conformalRescaleMetricInv]
    calc (φ * M.g i k) * (φ⁻¹ * M.ginv k j)
        = (φ * φ⁻¹) * (M.g i k * M.ginv k j) := by ring
      _ = M.g i k * M.ginv k j := by rw [mul_inv_cancel₀ hφ, one_mul]
  have h1 : (∑ k, M.g i k * M.ginv k j) = (1 : Tensor2 n) i j := by
    have hinv := congrFun (congrFun M.inv_left i) j
    simpa only [Matrix.mul_apply] using hinv
  have hsum : (∑ k, conformalRescaleMetric M.g φ i k * conformalRescaleMetricInv M.ginv φ k j)
      = ∑ k, M.g i k * M.ginv k j := Finset.sum_congr rfl (fun k _ => hterm k)
  rw [hsum]
  exact h1

/-- The rescaled inverse times the rescaled metric equals the identity. -/
lemma conformalGinv_mul {n : ℕ} (M : MetricTensor n) (φ : ℝ) (hφ : φ ≠ 0) :
    conformalRescaleMetricInv M.ginv φ * conformalRescaleMetric M.g φ = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have hterm : ∀ k,
      conformalRescaleMetricInv M.ginv φ i k * conformalRescaleMetric M.g φ k j
        = M.ginv i k * M.g k j := by
    intro k
    simp only [conformalRescaleMetric, conformalRescaleMetricInv]
    calc (φ⁻¹ * M.ginv i k) * (φ * M.g k j)
        = (φ⁻¹ * φ) * (M.ginv i k * M.g k j) := by ring
      _ = M.ginv i k * M.g k j := by rw [inv_mul_cancel₀ hφ, one_mul]
  have h1 : (∑ k, M.ginv i k * M.g k j) = (1 : Tensor2 n) i j := by
    have hinv := congrFun (congrFun M.inv_right i) j
    simpa only [Matrix.mul_apply] using hinv
  have hsum : (∑ k, conformalRescaleMetricInv M.ginv φ i k * conformalRescaleMetric M.g φ k j)
      = ∑ k, M.ginv i k * M.g k j := Finset.sum_congr rfl (fun k _ => hterm k)
  rw [hsum]
  exact h1

/-- A conformal rescaling `g̃ = φ g` of a metric, with inverse `φ⁻¹ g⁻¹`, underlying the
Jordan-to-Einstein frame transformation. -/
noncomputable def conformalMetric {n : ℕ} (M : MetricTensor n) (φ : ℝ) (hφ : φ ≠ 0) :
    MetricTensor n where
  g := conformalRescaleMetric M.g φ
  ginv := conformalRescaleMetricInv M.ginv φ
  symm := by
    intro i j
    show φ * M.g i j = φ * M.g j i
    rw [M.symm i j]
  inv_left := conformalG_mul M φ hφ
  inv_right := conformalGinv_mul M φ hφ

end GeneralRelativity
