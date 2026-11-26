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

Coordinate-pipeline Riemann, Ricci, scalar, and Einstein tensors for any
`StaticSphericalMetric` `ds² = -f(r) dt² + f(r)⁻¹ dr² + r² dΩ²`.

## i. Overview

Feeding the closed-form static spherical Christoffel table and its derivative table into
`riemannFromData` evaluates all 256 components of `Pipeline.riemann` and produces closed-form
expressions for the diagonal Ricci tensor, the Ricci scalar `R = -f'' - 4 f'/r + 2(1 - f)/r²`,
and the Einstein tensor in terms of `S.metricFn`, `(S.metricFn)'`, and `(S.metricFn)''`.

## ii. Key results

- `StaticSphericalMetric.riemann_eq_data` : metric-to-Riemann bridge via `riemannFromData`.
- `StaticSphericalMetric.ricciTensorOf`, `StaticSphericalMetric.ricciScalarOf`,
  `StaticSphericalMetric.einsteinTensorOf` : pipeline curvature formulas for arbitrary
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

open GeneralRelativity.Pipeline

namespace StaticSphericalMetric

/-!

## A. Riemann, Ricci, scalar, and Einstein tensors

Contracting the closed-form Riemann tensor gives a diagonal Ricci tensor, the spherical scalar
curvature `R = -f'' - 4 f'/r + 2 (1 - f) / r²`, and the Einstein tensor governing static
spherically symmetric spacetimes such as Schwarzschild, Kottler, and Reissner–Nordström.

-/

/-- The pipeline Riemann tensor of a static spherical metric agrees with
`riemannFromData S.christoffel S.christoffelDeriv` across all 256 components. -/
lemma riemann_eq_data (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.metricFn (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (hf_diff : ∀ᶠ s in nhds (x 1), DifferentiableAt ℝ S.metricFn s)
    (hf2 : DifferentiableAt ℝ (deriv S.metricFn) (x 1)) (ρ σ μ ν : Fin 4) :
    Pipeline.riemann S.metric S.metricInv x ρ σ μ ν
      = riemannFromData S.christoffel S.christoffelDeriv x ρ σ μ ν := by
  rw [riemann_eq_riemannFromData]
  have hf1 : DifferentiableAt ℝ S.metricFn (x 1) := hf_diff.self_of_nhds
  have h1 : coordDeriv μ (fun y =>
      Pipeline.christoffel S.metric S.metricInv y ρ ν σ) x
      = S.christoffelDeriv μ x ρ ν σ :=
    (S.pd_christoffel_eq x hr hf hsin hf_diff μ ρ ν σ).trans
      (S.pd_christoffel_eq_deriv x hr hf hsin hf1 hf2 μ ρ ν σ)
  have h2 : coordDeriv ν (fun y =>
      Pipeline.christoffel S.metric S.metricInv y ρ μ σ) x
      = S.christoffelDeriv ν x ρ μ σ :=
    (S.pd_christoffel_eq x hr hf hsin hf_diff ν ρ μ σ).trans
      (S.pd_christoffel_eq_deriv x hr hf hsin hf1 hf2 ν ρ μ σ)
  simp only [riemannFromData, h1, h2, S.christoffel_eq x hr hf hsin hf1]

private lemma ricciComponent_tt (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.metricFn (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (hf_diff : ∀ᶠ s in nhds (x 1), DifferentiableAt ℝ S.metricFn s)
    (hf2 : DifferentiableAt ℝ (deriv S.metricFn) (x 1)) :
    Pipeline.ricciTensorOf S.metric S.metricInv x 0 0
      = S.metricFn (x 1) * (deriv (deriv S.metricFn) (x 1) / 2
          + deriv S.metricFn (x 1) / x 1) := by
  simp [Pipeline.ricciTensorOf, Fin.sum_univ_four,
    S.riemann_eq_data x hr hf hsin hf_diff hf2,
    riemannFromData, christoffel, christoffelDeriv]
  field_simp [hr, hf]
  ring

private lemma ricciComponent_rr (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.metricFn (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (hf_diff : ∀ᶠ s in nhds (x 1), DifferentiableAt ℝ S.metricFn s)
    (hf2 : DifferentiableAt ℝ (deriv S.metricFn) (x 1)) :
    Pipeline.ricciTensorOf S.metric S.metricInv x 1 1
      = -(deriv (deriv S.metricFn) (x 1) / 2
          + deriv S.metricFn (x 1) / x 1) / S.metricFn (x 1) := by
  simp [Pipeline.ricciTensorOf, Fin.sum_univ_four,
    S.riemann_eq_data x hr hf hsin hf_diff hf2,
    riemannFromData, christoffel, christoffelDeriv]
  field_simp [hr, hf]
  ring

private lemma ricciComponent_thetatheta (S : StaticSphericalMetric) (x : Fin 4 → ℝ)
    (hr : x 1 ≠ 0) (hf : S.metricFn (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (hf_diff : ∀ᶠ s in nhds (x 1), DifferentiableAt ℝ S.metricFn s)
    (hf2 : DifferentiableAt ℝ (deriv S.metricFn) (x 1)) :
    Pipeline.ricciTensorOf S.metric S.metricInv x 2 2
      = 1 - S.metricFn (x 1) - x 1 * deriv S.metricFn (x 1) := by
  simp [Pipeline.ricciTensorOf, Fin.sum_univ_four,
    S.riemann_eq_data x hr hf hsin hf_diff hf2,
    riemannFromData, christoffel, christoffelDeriv]
  field_simp [hr, hf, hsin]
  rw [Real.sin_sq (x 2)]
  ring

private lemma ricciComponent_phiphi (S : StaticSphericalMetric) (x : Fin 4 → ℝ)
    (hr : x 1 ≠ 0) (hf : S.metricFn (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (hf_diff : ∀ᶠ s in nhds (x 1), DifferentiableAt ℝ S.metricFn s)
    (hf2 : DifferentiableAt ℝ (deriv S.metricFn) (x 1)) :
    Pipeline.ricciTensorOf S.metric S.metricInv x 3 3
      = (1 - S.metricFn (x 1) - x 1 * deriv S.metricFn (x 1)) * Real.sin (x 2) ^ 2 := by
  simp [Pipeline.ricciTensorOf, Fin.sum_univ_four,
    S.riemann_eq_data x hr hf hsin hf_diff hf2,
    riemannFromData, christoffel, christoffelDeriv]
  field_simp [hr, hf, hsin]
  ring

private lemma ricciComponent_offdiag (S : StaticSphericalMetric) (x : Fin 4 → ℝ)
    (hr : x 1 ≠ 0) (hf : S.metricFn (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (hf_diff : ∀ᶠ s in nhds (x 1), DifferentiableAt ℝ S.metricFn s)
    (hf2 : DifferentiableAt ℝ (deriv S.metricFn) (x 1)) {σ ν : Fin 4} (h : σ ≠ ν) :
    Pipeline.ricciTensorOf S.metric S.metricInv x σ ν = 0 := by
  fin_cases σ <;> fin_cases ν <;> try exact absurd rfl h
  all_goals
    simp [Pipeline.ricciTensorOf, Fin.sum_univ_four,
      S.riemann_eq_data x hr hf hsin hf_diff hf2,
      riemannFromData, christoffel, christoffelDeriv]
  ring

/-- Complete coordinate-pipeline Ricci tensor for any static spherically symmetric metric
`ds² = -f(r) dt² + f(r)⁻¹ dr² + r² dΩ²`. -/
lemma ricciTensorOf (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.metricFn (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (hf_diff : ∀ᶠ s in nhds (x 1), DifferentiableAt ℝ S.metricFn s)
    (hf2 : DifferentiableAt ℝ (deriv S.metricFn) (x 1)) (σ ν : Fin 4) :
    Pipeline.ricciTensorOf S.metric S.metricInv x σ ν
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

/-- Scalar curvature computed by `Pipeline.ricciScalarOf` for a static spherical metric:
`R = -f'' - 4 f'/r + 2 (1 - f) / r²`. -/
lemma ricciScalarOf (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.metricFn (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (hf_diff : ∀ᶠ s in nhds (x 1), DifferentiableAt ℝ S.metricFn s)
    (hf2 : DifferentiableAt ℝ (deriv S.metricFn) (x 1)) :
    Pipeline.ricciScalarOf S.metric S.metricInv x
      = -deriv (deriv S.metricFn) (x 1) - 4 * deriv S.metricFn (x 1) / x 1
          + 2 * (1 - S.metricFn (x 1)) / (x 1) ^ 2 := by
  simp only [Pipeline.ricciScalarOf, S.ricciTensorOf x hr hf hsin hf_diff hf2]
  simp only [Fin.sum_univ_four, metricInv, Fin.reduceEq, ↓reduceIte,
    Fin.isValue, mul_zero, add_zero, zero_add, Matrix.of_apply]
  field_simp [hr, hf, hsin]
  ring

/-- Einstein tensor computed by `Pipeline.einsteinTensorOf` for a static spherical metric. -/
lemma einsteinTensorOf (S : StaticSphericalMetric) (x : Fin 4 → ℝ) (hr : x 1 ≠ 0)
    (hf : S.metricFn (x 1) ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (hf_diff : ∀ᶠ s in nhds (x 1), DifferentiableAt ℝ S.metricFn s)
    (hf2 : DifferentiableAt ℝ (deriv S.metricFn) (x 1)) (i j : Fin 4) :
    Pipeline.einsteinTensorOf S.metric S.metricInv x i j
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
  simp only [Pipeline.einsteinTensorOf, S.ricciTensorOf x hr hf hsin hf_diff hf2,
    S.ricciScalarOf x hr hf hsin hf_diff hf2, metric]
  fin_cases i <;> fin_cases j <;> simp
  · field_simp [hr]; ring
  · field_simp [hr, hf]; ring
  · field_simp [hr]; ring
  · field_simp [hr]; ring

end StaticSphericalMetric

end StaticSpherical

end GeneralRelativity
