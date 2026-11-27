/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.Metrics.Christoffel
public import PhyslibAlpha.Relativity.Metrics.RiemannFromData

/-!

# Coordinate Riemann curvature

Riemann curvature computed from a coordinate metric, its Christoffel symbols, and their
derivatives.

## i. Overview

The coordinate Riemann tensor
`R^ρ_{σμν} = ∂_μ Γ^ρ_{νσ} - ∂_ν Γ^ρ_{μσ} + Γ^ρ_{μλ} Γ^λ_{νσ} - Γ^ρ_{νλ} Γ^λ_{μσ}`
is assembled from `christoffel` and `coordDeriv`. It agrees definitionally with
`riemannFromData` when the latter is fed the metric's actual Christoffel derivatives, and the
chart-level API is `CoordinateMetric.riemann`.

## ii. Key results

- `CoordinateCurvature.riemann` : component-level Riemann curvature.
- `CoordinateCurvature.riemann_eq_riemannFromData`,
  `CoordinateCurvature.riemann_eq_riemannFromData_of_eventuallyEq` : identification with
  `riemannFromData`.
- `CoordinateMetric.riemann` : Riemann curvature of a `CoordinateMetric`.

## iii. Table of contents

- A. Riemann curvature from a coordinate metric

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

## A. Riemann curvature from a coordinate metric

The antisymmetrized derivative of the Christoffel symbols plus the quadratic connection terms gives
the Riemann tensor of the coordinate metric.

-/

/-- The Riemann curvature tensor
`R^ρ_{σμν} = ∂_μ Γ^ρ_{νσ} - ∂_ν Γ^ρ_{μσ} + Γ^ρ_{μλ} Γ^λ_{νσ} - Γ^ρ_{νλ} Γ^λ_{μσ}`. -/
noncomputable def riemann {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n)
    (x : Fin n → ℝ) (ρ σ μ ν : Fin n) : ℝ :=
  coordDeriv μ (fun y => christoffel g ginv y ρ ν σ) x
    - coordDeriv ν (fun y => christoffel g ginv y ρ μ σ) x
    + ∑ l, (christoffel g ginv x ρ μ l * christoffel g ginv x l ν σ
          - christoffel g ginv x ρ ν l * christoffel g ginv x l μ σ)

/-- Feeding `riemannFromData` the metric's actual partial derivatives of `christoffel` reproduces
`riemann` definitionally. -/
lemma riemann_eq_riemannFromData {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n)
    (x : Fin n → ℝ) (ρ σ μ ν : Fin n) :
    riemann g ginv x ρ σ μ ν =
      riemannFromData (christoffel g ginv)
        (fun μ y a b c => coordDeriv μ (fun z => christoffel g ginv z a b c) y)
        x ρ σ μ ν :=
  rfl

/-- Transport `CoordinateCurvature.riemann` to `riemannFromData` using local agreement of
Christoffel symbols around a point and matching coordinate partial derivatives at that point. -/
lemma riemann_eq_riemannFromData_of_eventuallyEq {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n)
    (G : (Fin n → ℝ) → Fin n → Fin n → Fin n → ℝ)
    (dG : Fin n → (Fin n → ℝ) → Fin n → Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hG_eq : ∀ a b c, (fun y => christoffel g ginv y a b c) =ᶠ[nhds x] fun y => G y a b c)
    (hdG : ∀ μ a b c, coordDeriv μ (fun y => G y a b c) x = dG μ x a b c)
    (ρ σ μ ν : Fin n) :
    riemann g ginv x ρ σ μ ν = riemannFromData G dG x ρ σ μ ν := by
  rw [riemann_eq_riemannFromData]
  simp only [riemannFromData, coordDeriv_congr_nhds _ x (hG_eq _ _ _), hdG,
    (hG_eq _ _ _).eq_of_nhds]

end CoordinateCurvature

/-- Riemann curvature tensor of a `CoordinateMetric`. -/
noncomputable def CoordinateMetric.riemann {n : ℕ} (C : CoordinateMetric n)
    (x : Fin n → ℝ) (ρ σ μ ν : Fin n) : ℝ :=
  CoordinateCurvature.riemann C.g C.ginv x ρ σ μ ν

end GeneralRelativity
