/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.Metrics.Basic
public import PhyslibAlpha.Relativity.Metrics.CoordDeriv

/-!

# Coordinate Christoffel symbols

Levi-Civita Christoffel symbols computed from a coordinate metric and its inverse.

## i. Overview

For a coordinate metric field `C : CoordinateMetric n`, the Levi-Civita connection
`Γ^k_{ij} = (1/2) g^{kl} (∂_i g_{jl} + ∂_j g_{il} - ∂_l g_{ij})` is evaluated from the metric
components and their coordinate partial derivatives. The chart-level API is
`CoordinateMetric.christoffel`; the component-level function `CoordinateCurvature.christoffel`
takes the metric and inverse as bare functions and is used by coordinate-chart proofs.

## ii. Key results

- `CoordinateCurvature.christoffel` : component-level Christoffel symbols.
- `CoordinateCurvature.christoffel_diag` : diagonal-inverse collapse of the contraction.
- `CoordinateMetric.christoffel` : Christoffel symbols of a `CoordinateMetric`.

## iii. Table of contents

- A. Christoffel symbols from a coordinate metric

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 3 (Sec. 3.1). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 8.
  [ref: mtw_1973_gravitation]
* B. O'Neill, *Semi-Riemannian Geometry With Applications to Relativity* (1983), Ch. 3.
  [ref: oneill_1983_semi_riemannian]
-/

@[expose] public section

namespace GeneralRelativity

namespace CoordinateCurvature

/-!

## A. Christoffel symbols from a coordinate metric

The coordinate partial derivatives `coordDeriv` and the inverse metric components contract to the
Levi-Civita connection of any nondegenerate coordinate metric field.

-/

/-- Christoffel symbols of the second kind,
`Γ^k_{ij} = (1/2) g^{kl} (∂_i g_{jl} + ∂_j g_{il} - ∂_l g_{ij})`. -/
noncomputable def christoffel {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n)
    (x : Fin n → ℝ) (k i j : Fin n) : ℝ :=
  (1 / 2) * ∑ l, ginv x k l *
    (coordDeriv i (fun y => g y j l) x + coordDeriv j (fun y => g y i l) x
      - coordDeriv l (fun y => g y i j) x)

/-- For a metric whose inverse is diagonal at a point, the Christoffel contraction collapses to
the single index `l = k`. -/
lemma christoffel_diag {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) (x : Fin n → ℝ)
    (k i j : Fin n) (hdiag : ∀ l : Fin n, l ≠ k → ginv x k l = 0) :
    christoffel g ginv x k i j =
      (1 / 2) * (ginv x k k *
        (coordDeriv i (fun y => g y j k) x + coordDeriv j (fun y => g y i k) x
          - coordDeriv k (fun y => g y i j) x)) := by
  simp only [christoffel]
  rw [Finset.sum_eq_single k (fun l _ hl => by simp [hdiag l hl]) (by simp)]

end CoordinateCurvature

/-- Christoffel symbols of a `CoordinateMetric`. -/
noncomputable def CoordinateMetric.christoffel {n : ℕ} (C : CoordinateMetric n)
    (x : Fin n → ℝ) (k i j : Fin n) : ℝ :=
  CoordinateCurvature.christoffel C.g C.ginv x k i j

end GeneralRelativity
