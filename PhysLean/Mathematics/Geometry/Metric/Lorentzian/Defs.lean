/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import PhysLean.Mathematics.Geometry.Metric.PseudoRiemannian.Defs

/-!
# Lorentzian metrics

This file records the Lorentzian condition (index `1`) for a pseudo-Riemannian metric.

## Main definitions

* `PseudoRiemannianMetric.IsLorentzianMetric`: the Prop-valued predicate asserting
  `(g.toQuadraticForm x).negDim = 1` for all `x`.

## Tags

Lorentzian, pseudo-Riemannian, index
-/

namespace PseudoRiemannianMetric

noncomputable section

open scoped Manifold

section

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type w} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}
variable [IsManifold I (n + 1) M]
variable [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)]

/-- Predicate asserting that a pseudo-Riemannian metric has index `1` at every point. -/
class IsLorentzianMetric (g : PseudoRiemannianMetric E H M n I) : Prop where
  negDim_eq_one : ∀ x : M, (g.toQuadraticForm x).negDim = 1

namespace IsLorentzianMetric

variable (g : PseudoRiemannianMetric E H M n I)

/-- For a Lorentzian metric, the index is `1` at every point. -/
lemma index_eq_one (x : M) [IsLorentzianMetric (g := g)] :
    g.index x = 1 := by
  simpa [PseudoRiemannianMetric.index] using
    (IsLorentzianMetric.negDim_eq_one (g := g) x)

end IsLorentzianMetric

end

end

end PseudoRiemannianMetric

#lint
