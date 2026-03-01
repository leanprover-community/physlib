/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import PhysLean.Mathematics.Geometry.Metric.PseudoRiemannian.Defs
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
/-!
# Riemannian Metric Definitions

This module defines the Riemannian metric, building on pseudo-Riemannian metrics.
-/

namespace PseudoRiemannianMetric
section RiemannianMetric

open Bundle Set Finset Function Filter Module Topology ContinuousLinearMap
open scoped Manifold Bundle LinearMap Dual
open PseudoRiemannianMetric InnerProductSpace

noncomputable section

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type w} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [ChartedSpace H E]
variable {I : ModelWithCorners ℝ E H} {n : ℕ∞}

/-- A `RiemannianMetric` on a manifold `M` modeled on `H` with corners `I` (over the model space `E`
, typically `ℝ^m`) is a family of inner products on the tangent spaces `TangentSpace I x`
for each `x : M`. This family is required to vary smoothly with `x`, specifically with smoothness
`C^n`.

This structure `extends` `PseudoRiemannianMetric`, inheriting the core properties of a
pseudo-Riemannian metric, such as being a symmetric, non-degenerate, `C^n`-smooth tensor field
of type `(0,2)`. The key distinguishing feature of a Riemannian metric is its positive-definiteness.

The `pos_def'` field ensures that for any point `x` on the manifold and any non-zero tangent
vector `v` at `x`, the inner product `gₓ(v, v)` (denoted `val x v v`) is strictly positive.
This condition makes each `val x` (the metric at point `x`) a positive-definite symmetric
bilinear form, effectively an inner product, on the tangent space `TangentSpace I x`.

Parameters:
- `I`: The `ModelWithCorners` for the manifold `M`. This defines the model space `E` (e.g., `ℝ^d`)
  and the model space for the boundary `H`.
- `n`: The smoothness class of the metric, an `ℕ∞` value. The metric tensor components are `C^n`
  functions.
- `M`: The type of the manifold.
- `[TopologicalSpace M]`: Assumes `M` has a topological structure.
- `[ChartedSpace H M]`: Assumes `M` is equipped with an atlas of charts to `H`.
- `[IsManifold I (n + 1) M]`: Assumes `M` is a manifold of smoothness `C^(n+1)`.
  The manifold needs to be slightly smoother than the metric itself for certain constructions.
- `[inst_tangent_findim : ∀ (x : M), FiniteDimensional ℝ (TangentSpace I x)]`:
  Ensures that each tangent space is a finite-dimensional real vector space.

Fields:
- `toPseudoRiemannianMetric`: The underlying pseudo-Riemannian metric. This provides the
  smooth family of symmetric bilinear forms `val : M → SymBilinForm ℝ (TangentSpace I ·)`.
- `pos_def'`: The positive-definiteness condition: `∀ x v, v ≠ 0 → val x v v > 0`. This asserts
  that for any point `x` and any non-zero tangent vector `v` at `x`, the metric evaluated
  on `(v, v)` is strictly positive. -/
@[ext]
structure RiemannianMetric
  (I : ModelWithCorners ℝ E H) (n : ℕ∞) (M : Type w)
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (n + 1) M]
  [inst_tangent_findim : ∀ (x : M), FiniteDimensional ℝ (TangentSpace I x)]
  extends PseudoRiemannianMetric E H M n I where
  /-- `gₓ(v, v) > 0` for all nonzero `v`. `val` is inherited from `PseudoRiemannianMetric`. -/
  pos_def' : ∀ x v, v ≠ 0 → val x v v > 0
namespace RiemannianMetric

variable {I : ModelWithCorners ℝ E H} {n : ℕ∞} {M : Type w}
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (n + 1) M]
variable [inst_tangent_findim : ∀ (x : M), FiniteDimensional ℝ (TangentSpace I x)]

/-- Coercion from RiemannianMetric to its underlying PseudoRiemannianMetric. -/
instance : Coe (RiemannianMetric I n M) (PseudoRiemannianMetric E H M (n) I) where
  coe g := g.toPseudoRiemannianMetric

@[simp]
lemma pos_def (g : RiemannianMetric I n M) (x : M) (v : TangentSpace I x)
    (hv : v ≠ 0) :
  (g.toPseudoRiemannianMetric.val x v) v > 0 := g.pos_def' x v hv

/-- The quadratic form associated with a Riemannian metric is positive definite. -/
@[simp]
lemma toQuadraticForm_posDef (g : RiemannianMetric I n M) (x : M) :
    (g.toQuadraticForm x).PosDef :=
  λ v hv => g.pos_def x v hv

lemma riemannian_metric_negDim_zero (g : RiemannianMetric I n M) (x : M) :
    (g.toQuadraticForm x).negDim = 0 := by
  apply QuadraticForm.rankNeg_eq_zero
  exact g.toQuadraticForm_posDef x

/-! ## InnerProductSpace structure from RiemannianMetric -/

section InnerProductSpace

variable (g : RiemannianMetric I n M) (x : M)

/-- The `InnerProductSpace.Core` structure for `TₓM` induced by a Riemannian metric `g`.
    This provides the properties of an inner product: symmetry,
    non-negativity, linearity, and definiteness.
    Each `gₓ` is an inner product on `TₓM` (O'Neill, p. 55). -/
noncomputable def tangentInnerCore (g : RiemannianMetric I n M) (x : M) :
    InnerProductSpace.Core ℝ (TangentSpace I x) where
  inner := λ v w => g.inner x v w
  conj_inner_symm := λ v w => by
    simp only [inner_apply, conj_trivial]
    exact g.toPseudoRiemannianMetric.symm x w v
  re_inner_nonneg := λ v => by
    simp only [inner_apply, RCLike.re_to_real]
    by_cases hv : v = 0
    · simp [hv, map_zero]
    · exact le_of_lt (g.pos_def x v hv)
  add_left := λ u v w => by
    simp only [inner_apply, map_add, ContinuousLinearMap.add_apply]
  smul_left := λ r u v => by
    simp only [inner_apply, map_smul, conj_trivial]
    rfl
  definite := fun v (h_inner_zero : g.inner x v v = 0) => by
    by_contra h_v_ne_zero
    have h_pos : g.inner x v v > 0 := g.pos_def x v h_v_ne_zero
    linarith [h_inner_zero, h_pos]

/-! ### Local `NormedAddCommGroup` and `InnerProductSpace` Instances

These instances are defined locally to be used when a specific Riemannian metric `g`
and point `x` are in context. They are not global instances to avoid typeclass conflicts
and to respect the fact that a manifold might not have a canonical Riemannian metric,
or might be studied with an indefinite (pseudo-Riemannian) metric where these
standard norm structures are not appropriate. -/

/-- Creates a `NormedAddCommGroup` structure on `TₓM` from a Riemannian metric `g`. -/
noncomputable def TangentSpace.metricNormedAddCommGroup (g : RiemannianMetric I n M) (x : M) :
    NormedAddCommGroup (TangentSpace I x) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℝ (TangentSpace I x) _ _ _ (tangentInnerCore g x)

/-- Creates an `InnerProductSpace` structure on `TₓM` from a Riemannian metric `g`.
    Alternative implementation using `letI`. -/
noncomputable def TangentSpace.metricInnerProductSpace' (g : RiemannianMetric I n M) (x : M) :
    letI := TangentSpace.metricNormedAddCommGroup g x
    InnerProductSpace ℝ (TangentSpace I x) :=
  InnerProductSpace.ofCore (tangentInnerCore g x).toCore

/-- Creates an `InnerProductSpace` structure on `TₓM` from a Riemannian metric `g`. -/
noncomputable def TangentSpace.metricInnerProductSpace (g : RiemannianMetric I n M) (x : M) :
    let _ := TangentSpace.metricNormedAddCommGroup g x
    InnerProductSpace ℝ (TangentSpace I x) :=
  let inner_core := tangentInnerCore g x
  let _ := TangentSpace.metricNormedAddCommGroup g x
  InnerProductSpace.ofCore inner_core.toCore

/-- The norm on a tangent space induced by a Riemannian metric, defined as the square root
    of the inner product of a vector with itself. -/
noncomputable def norm (g : RiemannianMetric I n M) (x : M) (v : TangentSpace I x) : ℝ :=
  Real.sqrt (g.inner x v v)

-- Example using the norm function
example (g : RiemannianMetric I n M) (x : M) (v : TangentSpace I x) :
    norm g x v ≥ 0 := Real.sqrt_nonneg _

-- Example showing how to use the metric inner product space
example (g : RiemannianMetric I n M) (x : M) (v w : TangentSpace I x) :
    (TangentSpace.metricInnerProductSpace g x).inner v w = g.inner x v w := by
  letI := TangentSpace.metricInnerProductSpace g x
  rfl

/-- Helper function to compute the norm on a tangent space from a Riemannian metric,
    using the underlying `NormedAddCommGroup` structure. -/
noncomputable def norm' (g : RiemannianMetric I n M) (x : M) (v : TangentSpace I x) : ℝ :=
  let normed_group := TangentSpace.metricNormedAddCommGroup g x
  @Norm.norm (TangentSpace I x) (@NormedAddCommGroup.toNorm (TangentSpace I x) normed_group) v

-- Example: Using a custom norm function instead of the notation
example (g : RiemannianMetric I n M) (x : M) (v : TangentSpace I x) :
    norm g x v ≥ 0 := by
  unfold norm
  apply Real.sqrt_nonneg

example (g : RiemannianMetric I n M) (x : M) (v : TangentSpace I x) : ℝ :=
  letI := TangentSpace.metricNormedAddCommGroup g x
  ‖v‖

example (g : RiemannianMetric I n M) (x : M) (v : TangentSpace I x) : ℝ :=
  let normed_group := TangentSpace.metricNormedAddCommGroup g x
  @Norm.norm (TangentSpace I x) (@NormedAddCommGroup.toNorm (TangentSpace I x) normed_group) v

lemma norm_eq_norm_of_metricNormedAddCommGroup (g : RiemannianMetric I n M) (x : M)
    (v : TangentSpace I x) : norm g x v = @Norm.norm (TangentSpace I x)
    (@NormedAddCommGroup.toNorm _ (TangentSpace.metricNormedAddCommGroup g x)) v := by
  unfold norm
  let normed_group := TangentSpace.metricNormedAddCommGroup g x
  unfold TangentSpace.metricNormedAddCommGroup
  simp only [inner_apply]
  rfl

end InnerProductSpace

/-! ## Curve -/

section Curve

/-- Calculates the length of a curve `γ` between parameters `t₀` and `t₁`
using the Riemannian metric `g`. This is defined as the integral of the norm of
the tangent vector along the curve. -/
def curveLength (g : RiemannianMetric I n M) (γ : ℝ → M) (t₀ t₁ : ℝ)
    {IDE : ModelWithCorners ℝ ℝ ℝ}[ChartedSpace ℝ ℝ] : ℝ :=
  ∫ t in t₀..t₁, norm g (γ t) ((mfderiv IDE I γ t) ((1 : ℝ) : TangentSpace IDE t))

end Curve

end RiemannianMetric
end
end RiemannianMetric
end PseudoRiemannianMetric
