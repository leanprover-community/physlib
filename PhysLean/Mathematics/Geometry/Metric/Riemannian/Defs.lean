/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import PhysLean.Mathematics.Geometry.Metric.PseudoRiemannian.Defs
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
/-!
# Riemannian Metric Definitions

This file builds around the modern Mathlib Riemannian metric API.

Concretely, a `C^n` Riemannian metric on a manifold is a smooth section of the bundle of bilinear
forms on the tangent bundle, packaged as `Bundle.ContMDiffRiemannianMetric`.

We provide:
- an abbreviation `RiemannianMetric` for the tangent-bundle specialization, and
- a coercion to the PhysLean `PseudoRiemannianMetric` (by forgetting positivity and remembering
  nondegeneracy + constant index `0`).
-/

namespace PseudoRiemannianMetric

open Bundle ContinuousLinearMap
open scoped Manifold Bundle

noncomputable section

section

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type w} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}
variable [IsManifold I 1 M] [IsManifold I (n + 1) M]

/-- A `C^n` Riemannian metric on `M`, packaged using Mathlib's modern bundle API. -/
abbrev RiemannianMetric
    (I : ModelWithCorners ℝ E H) (n : WithTop ℕ∞) (M : Type w)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [IsManifold I (n + 1) M] :=
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
lemma toPseudoRiemannianMetric_index (g : RiemannianMetric (I := I) (n := n) M) (x : M) :
    (toPseudoRiemannianMetric (I := I) (n := n) (M := M) g).index x = 0 := by
  have hx : (PseudoRiemannianMetric.valToQuadraticForm g.inner g.symm x).negDim = 0 := by
    apply QuadraticForm.negDim_posDef
    intro v hv
    simpa [PseudoRiemannianMetric.valToQuadraticForm] using g.pos x v hv
  simpa [PseudoRiemannianMetric.index, PseudoRiemannianMetric.toQuadraticForm,
    toPseudoRiemannianMetric] using hx

instance :
    Coe (RiemannianMetric (I := I) (n := n) M)
      (PseudoRiemannianMetric E H M n I) :=
  ⟨fun g => toPseudoRiemannianMetric (I := I) (n := n) (M := M) g⟩

end RiemannianMetric

/-! ## Existence predicates (non-choosing) -/

/-- Prop-valued predicate recording existence of a `C^n` Riemannian metric (bundle-first), without
making any noncanonical choice. -/
class HasRiemannianMetric : Prop where
  out : Nonempty (RiemannianMetric (I := I) (n := n) M)

instance (g : RiemannianMetric (I := I) (n := n) M) :
    HasRiemannianMetric (I := I) (n := n) (M := M) :=
  ⟨⟨g⟩⟩

theorem hasRiemannianMetric_iff :
    HasRiemannianMetric (I := I) (n := n) (M := M) ↔
      Nonempty (RiemannianMetric (I := I) (n := n) M) :=
  ⟨fun h => h.out, fun h => ⟨h⟩⟩

/-- Any Riemannian metric gives a pseudo-Riemannian metric (of index `0`), hence existence of a
Riemannian metric implies existence of a pseudo-Riemannian metric. -/
instance [h : HasRiemannianMetric (I := I) (n := n) (M := M)]
    [∀ x : M, FiniteDimensional ℝ (TangentSpace I x)] :
    PseudoRiemannianMetric.HasPseudoRiemannianMetric (E := E) (H := H) (M := M) (n := n) (I := I) :=
  ⟨by
    rcases h.out with ⟨g⟩
    exact ⟨RiemannianMetric.toPseudoRiemannianMetric (I := I) (n := n) (M := M) g⟩⟩

end

end

end PseudoRiemannianMetric
