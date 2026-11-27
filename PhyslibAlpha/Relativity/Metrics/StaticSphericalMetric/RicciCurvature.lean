/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.Metrics.StaticSphericalMetric.Christoffel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!

# Static spherically symmetric curvature tensors

Riemann, Ricci, scalar, and Einstein curvature tensors computed from any static spherically
symmetric coordinate metric `ds² = -f(r) dt² + f(r)⁻¹ dr² + r² dΩ²`.

## i. Overview

Evaluating `riemannFromData` on the closed-form static spherical Christoffel symbols and their
partial derivatives determines all 256 coordinate Riemann components and yields closed-form
expressions for the diagonal Ricci tensor, the Ricci scalar `R = -f'' - 4 f'/r + 2(1 - f)/r²`,
and the Einstein tensor in terms of `f`, `f'`, and `f''`.

## ii. Key results

- `StaticSphericalMetric.riemann_eq_data` : coordinate Riemann tensor via `riemannFromData`.
- `StaticSphericalMetric.ricciTensor`, `StaticSphericalMetric.ricciScalar`,
  `StaticSphericalMetric.einsteinTensor` : closed-form curvature formulas for arbitrary
  twice-differentiable radial metric functions.

## iii. Table of contents

- A. Riemann, Ricci, scalar, and Einstein tensors

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 6 (Sec. 6.1). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 23 (Sec. 23.2).
  [ref: mtw_1973_gravitation]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 7
  (https://arxiv.org/pdf/gr-qc/9712019#page=168). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

namespace StaticSpherical

open GeneralRelativity.CoordinateCurvature

namespace StaticSphericalMetric

/-!

## A. Riemann, Ricci, scalar, and Einstein tensors

Contracting the closed-form Riemann tensor gives a diagonal Ricci tensor, the spherical scalar
curvature `R = -f'' - 4 f'/r + 2 (1 - f) / r²`, and the Einstein tensor governing static
spherically symmetric spacetimes such as Schwarzschild, Kottler, and Reissner–Nordström.

-/

/-- The coordinate Riemann tensor of a static spherical metric agrees with
`riemannFromData S.christoffel S.christoffelDeriv` across all 256 components. -/
lemma riemann_eq_data (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.metricFn (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (hf_diff : ∀ᶠ s in nhds (x 1), DifferentiableAt ℝ S.metricFn s)
    (hf2 : DifferentiableAt ℝ (deriv S.metricFn) (x 1)) (ρ σ μ ν : Fin 4) :
    CoordinateCurvature.riemann S.metric S.metricInv x ρ σ μ ν
      = riemannFromData S.christoffel S.christoffelDeriv x ρ σ μ ν := by
  rw [riemann_eq_riemannFromData]
  have hf1 : DifferentiableAt ℝ S.metricFn (x 1) := hf_diff.self_of_nhds
  have hconv : ∀ y k i j, CoordinateCurvature.christoffel S.metric S.metricInv y k i j
      = S.toCoordinateMetric.christoffel y k i j := fun _ _ _ _ => rfl
  have h1 : coordDeriv μ (fun y =>
      CoordinateCurvature.christoffel S.metric S.metricInv y ρ ν σ) x
      = S.christoffelDeriv μ x ρ ν σ := by
    simp only [hconv]
    exact (S.pd_christoffel_eq x hr hf hsin hf_diff μ ρ ν σ).trans
      (S.pd_christoffel_eq_deriv x hr hf hsin hf1 hf2 μ ρ ν σ)
  have h2 : coordDeriv ν (fun y =>
      CoordinateCurvature.christoffel S.metric S.metricInv y ρ μ σ) x
      = S.christoffelDeriv ν x ρ μ σ := by
    simp only [hconv]
    exact (S.pd_christoffel_eq x hr hf hsin hf_diff ν ρ μ σ).trans
      (S.pd_christoffel_eq_deriv x hr hf hsin hf1 hf2 ν ρ μ σ)
  have hquad : ∀ k i j, CoordinateCurvature.christoffel S.metric S.metricInv x k i j
      = S.christoffel x k i j :=
    fun k i j => (hconv x k i j).trans (S.christoffel_eq x hr hf hsin hf1 k i j)
  simp only [riemannFromData, h1, h2, hquad]

private lemma ricciComponent_tt (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.metricFn (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (hf_diff : ∀ᶠ s in nhds (x 1), DifferentiableAt ℝ S.metricFn s)
    (hf2 : DifferentiableAt ℝ (deriv S.metricFn) (x 1)) :
    CoordinateCurvature.ricciTensor S.metric S.metricInv x 0 0
      = S.metricFn (x 1) * (deriv (deriv S.metricFn) (x 1) / 2
          + deriv S.metricFn (x 1) / x 1) := by
  simp [CoordinateCurvature.ricciTensor, Fin.sum_univ_four,
    S.riemann_eq_data x hr hf hsin hf_diff hf2,
    riemannFromData, christoffel, christoffelDeriv]
  field_simp [hr, hf]
  ring

private lemma ricciComponent_rr (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.metricFn (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (hf_diff : ∀ᶠ s in nhds (x 1), DifferentiableAt ℝ S.metricFn s)
    (hf2 : DifferentiableAt ℝ (deriv S.metricFn) (x 1)) :
    CoordinateCurvature.ricciTensor S.metric S.metricInv x 1 1
      = -(deriv (deriv S.metricFn) (x 1) / 2
          + deriv S.metricFn (x 1) / x 1) / S.metricFn (x 1) := by
  simp [CoordinateCurvature.ricciTensor, Fin.sum_univ_four,
    S.riemann_eq_data x hr hf hsin hf_diff hf2,
    riemannFromData, christoffel, christoffelDeriv]
  field_simp [hr, hf]
  ring

private lemma ricciComponent_thetatheta (S : StaticSphericalMetric) (x : Fin 4 → ℝ)
    (hr : x 1 ≠ 0) (hf : S.metricFn (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (hf_diff : ∀ᶠ s in nhds (x 1), DifferentiableAt ℝ S.metricFn s)
    (hf2 : DifferentiableAt ℝ (deriv S.metricFn) (x 1)) :
    CoordinateCurvature.ricciTensor S.metric S.metricInv x 2 2
      = 1 - S.metricFn (x 1) - x 1 * deriv S.metricFn (x 1) := by
  simp [CoordinateCurvature.ricciTensor, Fin.sum_univ_four,
    S.riemann_eq_data x hr hf hsin hf_diff hf2,
    riemannFromData, christoffel, christoffelDeriv]
  field_simp [hr, hf, hsin]
  rw [Real.sin_sq (x 2)]
  ring

private lemma ricciComponent_phiphi (S : StaticSphericalMetric) (x : Fin 4 → ℝ)
    (hr : x 1 ≠ 0) (hf : S.metricFn (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (hf_diff : ∀ᶠ s in nhds (x 1), DifferentiableAt ℝ S.metricFn s)
    (hf2 : DifferentiableAt ℝ (deriv S.metricFn) (x 1)) :
    CoordinateCurvature.ricciTensor S.metric S.metricInv x 3 3
      = (1 - S.metricFn (x 1) - x 1 * deriv S.metricFn (x 1)) * Real.sin (x 2) ^ 2 := by
  simp [CoordinateCurvature.ricciTensor, Fin.sum_univ_four,
    S.riemann_eq_data x hr hf hsin hf_diff hf2,
    riemannFromData, christoffel, christoffelDeriv]
  field_simp [hr, hf, hsin]
  ring

private lemma ricciComponent_offdiag (S : StaticSphericalMetric) (x : Fin 4 → ℝ)
    (hr : x 1 ≠ 0) (hf : S.metricFn (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (hf_diff : ∀ᶠ s in nhds (x 1), DifferentiableAt ℝ S.metricFn s)
    (hf2 : DifferentiableAt ℝ (deriv S.metricFn) (x 1)) {σ ν : Fin 4} (h : σ ≠ ν) :
    CoordinateCurvature.ricciTensor S.metric S.metricInv x σ ν = 0 := by
  fin_cases σ <;> fin_cases ν <;> try exact absurd rfl h
  all_goals
    simp [CoordinateCurvature.ricciTensor, Fin.sum_univ_four,
      S.riemann_eq_data x hr hf hsin hf_diff hf2,
      riemannFromData, christoffel, christoffelDeriv]
  ring

/-- Complete coordinate Ricci tensor for any static spherically symmetric metric
`ds² = -f(r) dt² + f(r)⁻¹ dr² + r² dΩ²`. -/
lemma ricciTensor (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.metricFn (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (hf_diff : ∀ᶠ s in nhds (x 1), DifferentiableAt ℝ S.metricFn s)
    (hf2 : DifferentiableAt ℝ (deriv S.metricFn) (x 1)) (σ ν : Fin 4) :
    CoordinateCurvature.ricciTensor S.metric S.metricInv x σ ν
      = if σ = ν then
          if σ = 0 then S.metricFn (x 1) * (deriv (deriv S.metricFn) (x 1) / 2
            + deriv S.metricFn (x 1) / x 1)
          else if σ = 1 then -(deriv (deriv S.metricFn) (x 1) / 2
            + deriv S.metricFn (x 1) / x 1) / S.metricFn (x 1)
          else if σ = 2 then 1 - S.metricFn (x 1) - x 1 * deriv S.metricFn (x 1)
          else (1 - S.metricFn (x 1) - x 1 * deriv S.metricFn (x 1)) * Real.sin (x 2) ^ 2
        else 0 := by
  by_cases h : σ = ν
  · subst h
    fin_cases σ
    · simpa using ricciComponent_tt S x hr hf hsin hf_diff hf2
    · simpa using ricciComponent_rr S x hr hf hsin hf_diff hf2
    · simpa using ricciComponent_thetatheta S x hr hf hsin hf_diff hf2
    · simpa using ricciComponent_phiphi S x hr hf hsin hf_diff hf2
  · simp [h, ricciComponent_offdiag S x hr hf hsin hf_diff hf2 h]

/-- Scalar curvature of a static spherical metric computed from the coordinate metric:
`R = -f'' - 4 f'/r + 2 (1 - f) / r²`. -/
lemma ricciScalar (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.metricFn (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (hf_diff : ∀ᶠ s in nhds (x 1), DifferentiableAt ℝ S.metricFn s)
    (hf2 : DifferentiableAt ℝ (deriv S.metricFn) (x 1)) :
    CoordinateCurvature.ricciScalar S.metric S.metricInv x
      = -deriv (deriv S.metricFn) (x 1) - 4 * deriv S.metricFn (x 1) / x 1
          + 2 * (1 - S.metricFn (x 1)) / (x 1) ^ 2 := by
  simp only [CoordinateCurvature.ricciScalar, S.ricciTensor x hr hf hsin hf_diff hf2]
  simp only [Fin.sum_univ_four, metricInv, Fin.reduceEq, ↓reduceIte,
    Fin.isValue, mul_zero, add_zero, zero_add, Matrix.of_apply]
  field_simp [hr, hf, hsin]
  ring

/-- Einstein tensor of a static spherical metric computed from the coordinate metric. -/
lemma einsteinTensor (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.metricFn (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (hf_diff : ∀ᶠ s in nhds (x 1), DifferentiableAt ℝ S.metricFn s)
    (hf2 : DifferentiableAt ℝ (deriv S.metricFn) (x 1)) (i j : Fin 4) :
    CoordinateCurvature.einsteinTensor S.metric S.metricInv x i j
      = if i = j then
          if i = 0 then
            S.metricFn (x 1) * (1 - S.metricFn (x 1) - x 1 * deriv S.metricFn (x 1)) / (x 1) ^ 2
          else if i = 1 then
            -(1 - S.metricFn (x 1) - x 1 * deriv S.metricFn (x 1)) /
              ((x 1) ^ 2 * S.metricFn (x 1))
          else if i = 2 then
            (x 1) ^ 2 * (deriv (deriv S.metricFn) (x 1) / 2 + deriv S.metricFn (x 1) / x 1)
          else (x 1) ^ 2 * Real.sin (x 2) ^ 2
            * (deriv (deriv S.metricFn) (x 1) / 2 + deriv S.metricFn (x 1) / x 1)
        else 0 := by
  simp only [CoordinateCurvature.einsteinTensor, S.ricciTensor x hr hf hsin hf_diff hf2,
    S.ricciScalar x hr hf hsin hf_diff hf2, metric]
  fin_cases i <;> fin_cases j <;> simp
  · field_simp [hr]; ring
  · field_simp [hr, hf]; ring
  · field_simp [hr]; ring
  · field_simp [hr]; ring

end StaticSphericalMetric

end StaticSpherical

end GeneralRelativity
