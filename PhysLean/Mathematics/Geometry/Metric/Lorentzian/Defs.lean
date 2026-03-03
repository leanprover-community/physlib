/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import PhysLean.Mathematics.Geometry.Metric.PseudoRiemannian.Defs

/-!
# Lorentzian metrics

This file defines Lorentzian metrics as pseudo-Riemannian metrics of index `1` (negative dimension
`1`), in the sense of Sylvester's law of inertia (`QuadraticForm.negDim`).

It provides a reusable definition that composes with the
existing pseudo-Riemannian API (musical isomorphisms, induced bilinear forms, etc.).
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

/-- Typeclass asserting that a pseudo-Riemannian metric is Lorentzian (index `1`). -/
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
