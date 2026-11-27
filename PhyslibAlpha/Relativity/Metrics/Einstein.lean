/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.Metrics.Ricci

/-!

# Coordinate Einstein tensor

Einstein tensor of a coordinate metric and vanishing of connection and curvature for constant
metrics.

## i. Overview

The Einstein tensor `G_{ij} = Ric_{ij} - (1/2) R g_{ij}` combines the coordinate Ricci tensor and
scalar curvature. When every metric component is constant, all coordinate partial derivatives
vanish, so the Christoffel symbols, Riemann tensor, Ricci tensor, scalar curvature, and Einstein
tensor vanish identically. The chart-level API is `CoordinateMetric.einsteinTensor`.

## ii. Key results

- `CoordinateCurvature.einsteinTensor` : coordinate Einstein tensor.
- `CoordinateMetric.einsteinTensor` : Einstein tensor of a `CoordinateMetric`.
- `CoordinateCurvature.christoffel_const`, `CoordinateCurvature.riemann_const`,
  `CoordinateCurvature.ricciTensor_const`, `CoordinateCurvature.ricciScalar_const`,
  `CoordinateCurvature.einsteinTensor_const` : vanishing connection and curvature for any constant
  metric.

## iii. Table of contents

- A. The Einstein tensor
- B. Flatness of constant metrics

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 3 (Sec. 3.2). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 8 & Ch. 13.
  [ref: mtw_1973_gravitation]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 3
  (https://arxiv.org/pdf/gr-qc/9712019#page=72). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

namespace CoordinateCurvature

/-!

## A. The Einstein tensor

The trace-reversed Ricci tensor defines the Einstein tensor of the coordinate metric.

-/

/-- The coordinate Einstein tensor `G_{ij} = Ric_{ij} - (1/2) R g_{ij}`. -/
noncomputable def einsteinTensor {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n)
    (x : Fin n → ℝ) (i j : Fin n) : ℝ :=
  ricciTensor g ginv x i j - (1 / 2) * ricciScalar g ginv x * g x i j

/-!

## B. Flatness of constant metrics

When all metric components are constant across spacetime, every partial derivative vanishes, so the
connection, Riemann, Ricci, scalar, and Einstein curvature tensors all vanish identically.

-/

/-- A constant metric has vanishing Christoffel symbols at every point. -/
lemma christoffel_const {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) (G : Tensor2 n)
    (hg : ∀ x, g x = G) (x : Fin n → ℝ) (k i j : Fin n) :
    christoffel g ginv x k i j = 0 := by
  have hpd : ∀ (μ a b : Fin n), coordDeriv μ (fun y => g y a b) x = 0 := by
    intro μ a b
    rw [coordDeriv_congr μ x (fun y => by rw [hg y])]
    exact coordDeriv_const μ (G a b) x
  simp only [christoffel]
  rw [Finset.sum_eq_zero (fun l _ => by rw [hpd i j l, hpd j i l, hpd l i j]; ring)]
  ring

/-- A constant metric has zero Riemann curvature at every point. -/
lemma riemann_const {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) (G : Tensor2 n)
    (hg : ∀ x, g x = G) (x : Fin n → ℝ) (ρ σ μ ν : Fin n) :
    riemann g ginv x ρ σ μ ν = 0 := by
  have hc := fun y => christoffel_const g ginv G hg y
  have h1 : coordDeriv μ (fun y => christoffel g ginv y ρ ν σ) x = 0 := by
    rw [coordDeriv_congr μ x (fun y => hc y ρ ν σ)]
    exact coordDeriv_const μ 0 x
  have h2 : coordDeriv ν (fun y => christoffel g ginv y ρ μ σ) x = 0 := by
    rw [coordDeriv_congr ν x (fun y => hc y ρ μ σ)]
    exact coordDeriv_const ν 0 x
  have h3 : (∑ l, (christoffel g ginv x ρ μ l * christoffel g ginv x l ν σ
              - christoffel g ginv x ρ ν l * christoffel g ginv x l μ σ)) = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    rw [hc x ρ μ l, hc x ρ ν l, hc x l ν σ, hc x l μ σ]
    ring
  rw [riemann, h1, h2, h3]
  ring

/-- A constant metric is Ricci flat. -/
lemma ricciTensor_const {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) (G : Tensor2 n)
    (hg : ∀ x, g x = G) (x : Fin n → ℝ) (σ ν : Fin n) :
    ricciTensor g ginv x σ ν = 0 := by
  simp only [ricciTensor]
  apply Finset.sum_eq_zero
  intro ρ _
  exact riemann_const g ginv G hg x ρ σ ρ ν

/-- A constant metric has zero scalar curvature. -/
lemma ricciScalar_const {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) (G : Tensor2 n)
    (hg : ∀ x, g x = G) (x : Fin n → ℝ) : ricciScalar g ginv x = 0 := by
  simp only [ricciScalar]
  apply Finset.sum_eq_zero
  intro σ _
  apply Finset.sum_eq_zero
  intro ν _
  rw [ricciTensor_const g ginv G hg x σ ν]
  ring

/-- A constant metric satisfies the vacuum Einstein equations (`G_{ij} = 0`). -/
lemma einsteinTensor_const {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) (G : Tensor2 n)
    (hg : ∀ x, g x = G) (x : Fin n → ℝ) (i j : Fin n) :
    einsteinTensor g ginv x i j = 0 := by
  simp only [einsteinTensor]
  rw [ricciTensor_const g ginv G hg x i j, ricciScalar_const g ginv G hg x]
  ring

end CoordinateCurvature

/-- Einstein tensor of a `CoordinateMetric`. -/
noncomputable def CoordinateMetric.einsteinTensor {n : ℕ} (C : CoordinateMetric n)
    (x : Fin n → ℝ) (i j : Fin n) : ℝ :=
  CoordinateCurvature.einsteinTensor C.g C.ginv x i j

/-- Unfolding lemma for `CoordinateMetric.einsteinTensor`. -/
@[simp] lemma CoordinateMetric.einsteinTensor_apply {n : ℕ} (C : CoordinateMetric n)
    (x : Fin n → ℝ) (i j : Fin n) :
    C.einsteinTensor x i j = CoordinateCurvature.einsteinTensor C.g C.ginv x i j := rfl

end GeneralRelativity
