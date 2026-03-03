/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import PhysLean.Mathematics.Geometry.Metric.PseudoRiemannian.Defs
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
/-!
# Riemannian metrics (tangent bundle)

This file defines `RiemannianMetric` as the specialization of Mathlib's bundle-level
`Bundle.ContMDiffRiemannianMetric` to the tangent bundle, and provides a coercion to
`PseudoRiemannianMetric` by forgetting positivity.

## Main definitions

* `PseudoRiemannianMetric.RiemannianMetric`: a `C^n` Riemannian metric on `M`, packaged bundle-first.
* `PseudoRiemannianMetric.RiemannianMetric.toPseudoRiemannianMetric`: forget positivity to obtain a
  pseudo-Riemannian metric (index `0`).

## Tags

Riemannian, pseudo-Riemannian
-/

namespace PseudoRiemannianMetric

open Bundle ContinuousLinearMap
open scoped Manifold Bundle

noncomputable section

section

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type w} [TopologicalSpace H]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}
variable [IsManifold I (n + 1) M] [IsManifold I 1 M]

/-- A `C^n` Riemannian metric on `M`, packaged using Mathlib's modern bundle API. -/
abbrev RiemannianMetric
    (I : ModelWithCorners ℝ E H) (n : WithTop ℕ∞) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] :=
  Bundle.ContMDiffRiemannianMetric (IB := I) (n := n) (F := E) (E := fun x : M ↦ TangentSpace I x)

namespace RiemannianMetric

variable (g : RiemannianMetric (I := I) (n := n) M)
variable [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)]

/-- Forget the positivity to get a pseudo-Riemannian metric. The index is (locally constantly) `0`.
This is the bridge that makes pseudo-Riemannian API (musical isomorphisms, etc.) usable for a
Riemannian metric. -/
def toPseudoRiemannianMetric (g : RiemannianMetric (I := I) (n := n) M)  :
    PseudoRiemannianMetric E H M n I where
  val := g.inner
  symm := g.symm
  nondegenerate := by
    intro x v hv
    by_cases h : v = 0
    · simp [h]
    · have hp : 0 < g.inner x v v := g.pos x v h
      have h0 : g.inner x v v = 0 := hv v
      exact (ne_of_gt hp h0).elim
  contMDiff := g.contMDiff
  negDim_isLocallyConstant := by
    -- On a Riemannian metric, the associated quadratic form is positive definite, hence `negDim = 0`.
    refine IsLocallyConstant.of_constant _ (fun x y => ?_)
    have hx :
        (PseudoRiemannianMetric.valToQuadraticForm g.inner g.symm x).negDim = 0 := by
      apply QuadraticForm.negDim_posDef
      intro v hv
      simpa [PseudoRiemannianMetric.valToQuadraticForm] using g.pos x v hv
    have hy :
        (PseudoRiemannianMetric.valToQuadraticForm g.inner g.symm y).negDim = 0 := by
      apply QuadraticForm.negDim_posDef
      intro v hv
      simpa [PseudoRiemannianMetric.valToQuadraticForm] using g.pos y v hv
    have hx' :
        (-PseudoRiemannianMetric.valToQuadraticForm g.inner g.symm x).posIndex = 0 := by
      simpa [QuadraticForm.negDim] using hx
    have hy' :
        (-PseudoRiemannianMetric.valToQuadraticForm g.inner g.symm y).posIndex = 0 := by
      simpa [QuadraticForm.negDim] using hy
    simp [hx', hy']

@[simp]
lemma toPseudoRiemannianMetric_posIndex_neg_toQuadraticForm (g : RiemannianMetric (I := I) (n := n) M)
    (x : M) :
    (-(toPseudoRiemannianMetric (I := I) (n := n) (M := M) g).toQuadraticForm x).posIndex = 0 := by
  have hx : (PseudoRiemannianMetric.valToQuadraticForm g.inner g.symm x).negDim = 0 := by
    apply QuadraticForm.negDim_posDef
    intro v hv
    simpa [PseudoRiemannianMetric.valToQuadraticForm] using g.pos x v hv
  simpa [PseudoRiemannianMetric.toQuadraticForm, toPseudoRiemannianMetric, QuadraticForm.negDim] using hx

lemma toPseudoRiemannianMetric_index (g : RiemannianMetric (I := I) (n := n) M) (x : M) :
    (toPseudoRiemannianMetric (I := I) (n := n) (M := M) g).index x = 0 := by
  simp [PseudoRiemannianMetric.index, QuadraticForm.negDim]

instance :
    Coe (RiemannianMetric (I := I) (n := n) M)
      (PseudoRiemannianMetric E H M n I) :=
  ⟨fun g => toPseudoRiemannianMetric (I := I) (n := n) (M := M) g⟩

end RiemannianMetric

/-! ## Existence helper -/

/-- Existence of a Riemannian metric implies existence of a pseudo-Riemannian metric (of index `0`),
by forgetting positivity. -/
theorem nonempty_pseudoRiemannianMetric_of_nonempty_riemannianMetric
    [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)]
    (h : Nonempty (RiemannianMetric (I := I) (n := n) M)) :
    Nonempty (PseudoRiemannianMetric E H M n I) := by
  rcases h with ⟨g⟩
  exact ⟨RiemannianMetric.toPseudoRiemannianMetric (I := I) (n := n) (M := M) g⟩

end

end

end PseudoRiemannianMetric
