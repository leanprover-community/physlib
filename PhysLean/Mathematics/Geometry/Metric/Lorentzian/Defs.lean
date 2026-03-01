/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import PhysLean.Mathematics.Geometry.Metric.PseudoRiemannian.Defs

/-!
# Lorentzian metrics (PhysLean)

This file defines Lorentzian metrics as pseudo-Riemannian metrics of index `1` (negative dimension
`1`), in the sense of Sylvester's law of inertia (`QuadraticForm.negDim`).

This is intentionally lightweight: it provides a reusable definition that composes with the
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
variable [IsManifold I 1 M] [IsManifold I (n + 1) M]
variable [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)]

/-- A Lorentzian metric is a pseudo-Riemannian metric of (constant) index `1`, i.e. the associated
quadratic form has `negDim = 1` at every point. -/
@[ext]
structure LorentzianMetric extends PseudoRiemannianMetric E H M n I where
  negDim_eq_one : ∀ x : M, (toQuadraticForm toPseudoRiemannianMetric x).negDim = 1

namespace LorentzianMetric

variable (g : LorentzianMetric (E := E) (H := H) (M := M) (I := I) (n := n))

@[simp] lemma negDim_eq_one' (x : M) :
    (g.toPseudoRiemannianMetric.toQuadraticForm x).negDim = 1 :=
  g.negDim_eq_one x

instance : Coe (LorentzianMetric (E := E) (H := H) (M := M) (I := I) (n := n))
    (PseudoRiemannianMetric E H M n I) :=
  ⟨fun g => g.toPseudoRiemannianMetric⟩

end LorentzianMetric

end

end

end PseudoRiemannianMetric

