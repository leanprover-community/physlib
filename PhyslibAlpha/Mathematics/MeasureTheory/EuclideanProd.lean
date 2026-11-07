/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!

# Integration over the Euclidean product

The Euclidean product `WithLp 2 (E × F)` carries the product of the Lebesgue measures.

## i. Overview

The `L²` product of two finite dimensional inner product spaces is measure preservingly equivalent
to the plain product. Integrals over it are iterated integrals. The norm of a point dominates the
norm of each coordinate.

## ii. Key results

- `EuclideanProd.integral_withLp_prod` : integration over the Euclidean product.
- `EuclideanProd.integrable_withLp_prod` : integrability over the Euclidean product.

## iii. Table of contents

- A. Integration
- B. Norms

## iv. References

None.

## A. Integration

- `EuclideanProd.integral_withLp_prod` : integration over the Euclidean product.
- `EuclideanProd.integrable_withLp_prod` : integrability over the Euclidean product.

## B. Norms

- `EuclideanProd.norm_le_norm_toLp_right` : the second coordinate is dominated by the norm.
- `EuclideanProd.norm_toLp_zero` : the norm of a point with vanishing second coordinate.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace EuclideanProd

variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]

/-- Integration over the Euclidean product is iterated integration. -/
lemma integral_withLp_prod {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (φ : WithLp 2 (E × F) → G) :
    ∫ z, φ z = ∫ p : E × F, φ (WithLp.toLp 2 p) := by
  have h := (WithLp.volume_preserving_symm_measurableEquiv_toLp_prod E F).integral_comp'
    (g := fun p : E × F => φ (WithLp.toLp 2 p))
  simpa using h

/-- Integrability over the Euclidean product is integrability over the product. -/
lemma integrable_withLp_prod {G : Type*} [NormedAddCommGroup G] {φ : WithLp 2 (E × F) → G}
    (hφ : Integrable φ) : Integrable (fun p : E × F => φ (WithLp.toLp 2 p)) := by
  have h := (WithLp.volume_preserving_symm_measurableEquiv_toLp_prod E F).symm
  exact h.integrable_comp_emb (MeasurableEquiv.toLp 2 (E × F)).measurableEmbedding |>.2 hφ

omit [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] in
/-- The second coordinate is dominated by the norm of the point. -/
lemma norm_le_norm_toLp_right (x : E) (y : F) : ‖y‖ ≤ ‖WithLp.toLp 2 (x, y)‖ := by
  rw [WithLp.prod_norm_eq_of_L2]
  exact Real.le_sqrt_of_sq_le (by simp)

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] in
/-- The norm of a point with vanishing second coordinate. -/
lemma norm_toLp_zero (ξ : E) : ‖WithLp.toLp 2 (ξ, (0 : F))‖ = ‖ξ‖ := by
  rw [WithLp.prod_norm_eq_of_L2]
  simp

end EuclideanProd
