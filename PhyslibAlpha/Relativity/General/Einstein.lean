/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.General.Curvature
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!

# The Einstein tensor and the vacuum equations

`G_{ij} = Ric_{ij} - (1/2) S g_{ij}`, with `Ric` contracted against the inverse metric.

## i. Overview

This module defines the metric trace `g^{ij} T_{ij}`, establishes its linearity, defines the
Einstein tensor `einstein M R`, proves its symmetry and trace identity
`g^{ij} G_{ij} = (1 - n / 2) S`, and proves the four-dimensional equivalences between the
vacuum Einstein equations `G = 0` and Ricci flatness `Ric = 0`, as well as between the
cosmological Einstein-space equation `G + Λ g = 0` and `Ric = Λ g`.

## ii. Key results

- `metricTrace` : full contraction `g^{ij} T_{ij}` of a rank-2 tensor with the inverse metric.
- `einstein` : the Einstein tensor `G_{ij} = Ric_{ij} - (1/2) S g_{ij}`.
- `einstein_symm` : symmetry of the Einstein tensor.
- `metricTrace_einstein` : `g^{ij} G_{ij} = (1 - n/2) S`; in 4D the trace of `G` is `-S`.
- `vacuum_iff_ricci_flat` : in 4D, `G = 0 ↔ Ric = 0`.
- `einsteinSpace_iff` : in 4D, `G + Λ g = 0 ↔ Ric = Λ g`.

## iii. Table of contents

- A. Metric trace and linearity
- B. The Einstein tensor and its trace identity
- C. Four-dimensional vacuum and Einstein-space equations

## iv. References

* R. M. Wald, *General Relativity* (1984). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973). [ref: mtw_1973_gravitation]

-/

@[expose] public section

namespace GeneralRelativity

variable {n : ℕ}

/-!

## A. Metric trace and linearity

-/

/-- Full contraction of the inverse metric with a rank-2 tensor, `g^{ij} T_{ij}`. -/
def metricTrace (M : MetricTensor n) (T : Tensor2 n) : ℝ := ∑ i, ∑ j, M.ginv i j * T i j

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

/-- `metricTrace` is additive over pointwise differences. -/
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
    exact Finset.sum_congr rfl (fun j _ => by rw [M.symm j i])
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

/-!

## B. The Einstein tensor and its trace identity

-/

/-- The Einstein tensor `G_{ij} = Ric_{ij} - (1/2) S g_{ij}`. -/
noncomputable def einstein (M : MetricTensor n) (R : RiemannTensor n) : Tensor2 n :=
  fun i j => ricci M R i j - (1 / 2) * scalarCurv M R * M.g i j

/-- Scalar curvature is the metric trace of the Ricci tensor. -/
lemma scalarCurv_eq_metricTrace (M : MetricTensor n) (R : RiemannTensor n) :
    scalarCurv M R = metricTrace M (ricci M R) := rfl

/-- The Einstein tensor is symmetric. -/
lemma einstein_symm (M : MetricTensor n) (R : RiemannTensor n) : IsSymm (einstein M R) := by
  intro i j
  simp only [einstein]
  rw [ricci_symm M R i j, M.symm i j]

/-- Metric trace of the Einstein tensor: `g^{ij} G_{ij} = (1 - n/2) S`. -/
lemma metricTrace_einstein (M : MetricTensor n) (R : RiemannTensor n) :
    metricTrace M (einstein M R) = (1 - (n : ℝ) / 2) * scalarCurv M R := by
  have hsplit : ∀ i,
      (∑ j, M.ginv i j * (ricci M R i j - (1 / 2) * scalarCurv M R * M.g i j))
        = (∑ j, M.ginv i j * ricci M R i j)
          - (1 / 2) * scalarCurv M R * (∑ j, M.ginv i j * M.g i j) := by
    intro i
    have hterm : ∀ j,
        M.ginv i j * (ricci M R i j - (1 / 2) * scalarCurv M R * M.g i j)
          = M.ginv i j * ricci M R i j
            - (1 / 2) * scalarCurv M R * (M.ginv i j * M.g i j) := by
      intro j
      ring
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_sub_distrib,
      ← Finset.mul_sum]
  simp only [metricTrace, einstein]
  calc (∑ i, ∑ j, M.ginv i j * (ricci M R i j - (1 / 2) * scalarCurv M R * M.g i j))
      = ∑ i, ((∑ j, M.ginv i j * ricci M R i j)
          - (1 / 2) * scalarCurv M R * (∑ j, M.ginv i j * M.g i j)) :=
        Finset.sum_congr rfl (fun i _ => hsplit i)
    _ = (∑ i, ∑ j, M.ginv i j * ricci M R i j)
          - (1 / 2) * scalarCurv M R * (∑ i, ∑ j, M.ginv i j * M.g i j) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = scalarCurv M R - (1 / 2) * scalarCurv M R * (n : ℝ) := by
        rw [sum_ginv_mul_g]
        rfl
    _ = (1 - (n : ℝ) / 2) * scalarCurv M R := by ring

/-!

## C. Four-dimensional vacuum and Einstein-space equations

-/

/-- In four dimensions, `G = 0` forces the scalar curvature to vanish. -/
lemma scalarCurv_eq_zero_of_einstein_eq_zero (M : MetricTensor 4) (R : RiemannTensor 4)
    (h : einstein M R = 0) : scalarCurv M R = 0 := by
  have htr : metricTrace M (einstein M R) = 0 := by
    rw [h]
    simp [metricTrace]
  rw [metricTrace_einstein] at htr
  norm_num at htr
  linarith

/-- In four dimensions the vacuum Einstein equation `G = 0` is equivalent to Ricci flatness. -/
lemma vacuum_iff_ricci_flat (M : MetricTensor 4) (R : RiemannTensor 4) :
    einstein M R = 0 ↔ ricci M R = 0 := by
  constructor
  · intro h
    have hS := scalarCurv_eq_zero_of_einstein_eq_zero M R h
    ext i j
    have hij : ricci M R i j - (1 / 2) * scalarCurv M R * M.g i j = 0 := by
      have hc := congrFun (congrFun h i) j
      simpa [einstein] using hc
    rw [hS] at hij
    simpa using hij
  · intro h
    ext i j
    have hS : scalarCurv M R = 0 := by simp [scalarCurv, h]
    simp [einstein, h, hS]

/-- In four dimensions, the Einstein equation with cosmological constant `G + Λ g = 0` is
equivalent to the Einstein-space condition `Ric = Λ g` (with `S = 4 Λ`). -/
lemma einsteinSpace_iff (M : MetricTensor 4) (R : RiemannTensor 4) (Λ : ℝ) :
    (∀ i j, einstein M R i j + Λ * M.g i j = 0) ↔
      (∀ i j, ricci M R i j = Λ * M.g i j) := by
  constructor
  · intro h
    have htr : metricTrace M (fun i j => einstein M R i j + Λ * M.g i j) = 0 := by
      simp [metricTrace, h]
    rw [metricTrace_add_fun (A := einstein M R) (B := fun i j => Λ * M.g i j),
      metricTrace_einstein, metricTrace_mul_g] at htr
    have hS : scalarCurv M R = 4 * Λ := by linarith
    intro i j
    have hij := h i j
    simp only [einstein, hS] at hij
    linarith
  · intro h i j
    have hS : scalarCurv M R = 4 * Λ := by
      have htr : scalarCurv M R = metricTrace M (fun a b => Λ * M.g a b) := by
        simp only [scalarCurv, metricTrace, h]
      rw [htr, metricTrace_mul_g]
      ring
    simp only [einstein, h i j, hS]
    ring

end GeneralRelativity
