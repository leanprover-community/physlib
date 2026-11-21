/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!

# Component tensors, metrics, and the Minkowski metric

Foundational layer of a coordinate (component) formalisation of general relativity.

## i. Overview

A rank-2 covariant tensor in a fixed frame or coordinate chart is represented as a real `n × n`
matrix of components (`Tensor2 n`). A nondegenerate metric (`MetricTensor n`) bundles its metric
components together with an explicit two-sided inverse matrix and symmetry proof, so contractions
and trace operations use an inverse certified for that metric.

**Signature convention.** Throughout `GeneralRelativity`, the Minkowski metric `eta4` uses the
mostly-plus Lorentzian signature `(-, +, +, +)` standard in general relativity (Wald / Misner–
Thorne–Wheeler). Note that `Physlib/Relativity/MinkowskiMatrix.lean` uses the particle-physics
mostly-minus convention `(+, -, -, -)`.

## ii. Key results

- `Tensor2` : rank-2 covariant tensor components in `n` dimensions.
- `IsSymm` : component symmetry of a rank-2 tensor.
- `eta4`, `eta4_symm`, `eta4_mul_self` : the 4D Minkowski metric `diag(-1, 1, 1, 1)` and its
  self-inverse property.
- `MetricTensor`, `MetricTensor.ginv_symm` : metric with certified two-sided inverse, whose
  inverse is symmetric.
- `conformalMetric` : conformal rescaling `g̃ = φ g` with inverse `φ⁻¹ g⁻¹` (for `φ ≠ 0`).

## iii. Table of contents

- A. Rank-2 tensors and symmetry
- B. The Minkowski metric
- C. Metric tensors with explicit inverses
- D. Conformal rescalings

## iv. References

* None.

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

/-!

## B. The Minkowski metric

-/

/-- The Minkowski metric of signature `(-, +, +, +)` in inertial coordinates. -/
def eta4 : Tensor2 4 := !![(-1 : ℝ), 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

/-- The Minkowski metric is symmetric. -/
lemma eta4_symm : IsSymm eta4 := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [eta4]

/-- The Minkowski metric is its own inverse: `η * η = 1`. -/
lemma eta4_mul_self : eta4 * eta4 = (1 : Tensor2 4) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eta4, Matrix.mul_apply, Fin.sum_univ_four]

/-!

## C. Metric tensors with explicit inverses

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

/-!

## D. Conformal rescalings

-/

/-- Componentwise conformal rescaling of a metric, `g̃ = φ g`. -/
def conformalG {n : ℕ} (g : Tensor2 n) (φ : ℝ) : Tensor2 n := fun i j => φ * g i j

/-- The corresponding inverse components, `g̃⁻¹ = φ⁻¹ g⁻¹`. -/
noncomputable def conformalGinv {n : ℕ} (ginv : Tensor2 n) (φ : ℝ) : Tensor2 n :=
  fun i j => φ⁻¹ * ginv i j

/-- The rescaled metric times its rescaled inverse equals the identity. -/
lemma conformalG_mul {n : ℕ} (M : MetricTensor n) (φ : ℝ) (hφ : φ ≠ 0) :
    conformalG M.g φ * conformalGinv M.ginv φ = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have hterm : ∀ k,
      conformalG M.g φ i k * conformalGinv M.ginv φ k j = M.g i k * M.ginv k j := by
    intro k
    simp only [conformalG, conformalGinv]
    calc (φ * M.g i k) * (φ⁻¹ * M.ginv k j)
        = (φ * φ⁻¹) * (M.g i k * M.ginv k j) := by ring
      _ = M.g i k * M.ginv k j := by rw [mul_inv_cancel₀ hφ, one_mul]
  have h1 : (∑ k, M.g i k * M.ginv k j) = (1 : Tensor2 n) i j := by
    have hinv := congrFun (congrFun M.inv_left i) j
    simpa only [Matrix.mul_apply] using hinv
  have hsum : (∑ k, conformalG M.g φ i k * conformalGinv M.ginv φ k j)
      = ∑ k, M.g i k * M.ginv k j := Finset.sum_congr rfl (fun k _ => hterm k)
  rw [hsum]
  exact h1

/-- The rescaled inverse times the rescaled metric equals the identity. -/
lemma conformalGinv_mul {n : ℕ} (M : MetricTensor n) (φ : ℝ) (hφ : φ ≠ 0) :
    conformalGinv M.ginv φ * conformalG M.g φ = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have hterm : ∀ k,
      conformalGinv M.ginv φ i k * conformalG M.g φ k j = M.ginv i k * M.g k j := by
    intro k
    simp only [conformalG, conformalGinv]
    calc (φ⁻¹ * M.ginv i k) * (φ * M.g k j)
        = (φ⁻¹ * φ) * (M.ginv i k * M.g k j) := by ring
      _ = M.ginv i k * M.g k j := by rw [inv_mul_cancel₀ hφ, one_mul]
  have h1 : (∑ k, M.ginv i k * M.g k j) = (1 : Tensor2 n) i j := by
    have hinv := congrFun (congrFun M.inv_right i) j
    simpa only [Matrix.mul_apply] using hinv
  have hsum : (∑ k, conformalGinv M.ginv φ i k * conformalG M.g φ k j)
      = ∑ k, M.ginv i k * M.g k j := Finset.sum_congr rfl (fun k _ => hterm k)
  rw [hsum]
  exact h1

/-- A conformal rescaling `g̃ = φ g` of a metric, with inverse `φ⁻¹ g⁻¹`, underlying the
Jordan-to-Einstein frame transformation. -/
noncomputable def conformalMetric {n : ℕ} (M : MetricTensor n) (φ : ℝ) (hφ : φ ≠ 0) :
    MetricTensor n where
  g := conformalG M.g φ
  ginv := conformalGinv M.ginv φ
  symm := by
    intro i j
    show φ * M.g i j = φ * M.g j i
    rw [M.symm i j]
  inv_left := conformalG_mul M φ hφ
  inv_right := conformalGinv_mul M φ hφ

end GeneralRelativity
