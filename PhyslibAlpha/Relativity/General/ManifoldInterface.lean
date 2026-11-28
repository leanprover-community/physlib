/-
Copyright (c) 2026 The Gravitation formalisation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import PhyslibAlpha.Relativity.Metrics.CoordinateMetric
public import PhyslibAlpha.Relativity.Metrics.Minkowski
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!

# Chart-level spacetime interface

## i. Overview

This file provides the chart-level M1 layer supported by the current
component-based development: a spacetime chart domain, a metric field, the
coordinate connection and curvature, chart causal classification, and a
coordinate covariant derivative.  It proves torsion-freeness and Minkowski
metric compatibility.  It does not claim a smooth manifold, a general
Levi-Civita compatibility theorem, or global causality; those remain outside
this chart interface.

The point of the interface is to give the later layers a concrete type to extend,
with Minkowski spacetime as its first instance.

## ii. Key results

- `ChartSpacetime`, `minkowskiChart` : the chart domain and its Minkowski
  instance.
- `ChartSpacetime.christoffel`, `ChartSpacetime.riemann` : the coordinate
  connection and curvature pipeline on a chart.
- `ChartSpacetime.IsCauchySurface`, `ChartSpacetime.IsGloballyHyperbolic`,
  `minkowskiChart_globallyHyperbolic` : chart causal classification and the
  Minkowski instance.
- `ChartSpacetime.Isometry`, `ChartSpacetime.Embedding`,
  `ChartSpacetime.IsIsometric` : chart-level isometry and embedding API with
  identity, inverse and composition lemmas.
- `PartialChartSpacetime`, `PartialChartSpacetime.IsSmooth` : chart-level
  spacetime on a restricted open domain with a smoothness certificate.
- `PartialChartTransition`, `PartialChartTransition.refl` : isometric overlap
  certificate between partial charts (open overlap, smooth transition map,
  metric pullback through an explicit Jacobian) with the identity instance.

## iii. Table of contents

- A. Chart spacetime and the Minkowski model
- B. Partial charts on restricted domains
- C. Coordinate connection and curvature
- D. Chart causal classification
- E. Covariant derivatives and the Levi-Civita property
- F. Mathlib charted-manifold bridge and global hyperbolicity
- G. Chart-level isometries and embeddings

## iv. References

* S. M. Carroll, *Lecture Notes on General Relativity*, arXiv:gr-qc/9712019,
  §3.2, pp. 58 and 72–73. [ref: Carroll1997]
* B. O'Neill, *Semi-Riemannian Geometry With Applications to Relativity*,
  Ch. 3. [ref: oneill_1983_semi_riemannian]

-/
@[expose] public section

namespace GeneralRelativity

open scoped ContDiff

/-! ## A. Chart spacetime and the Minkowski model -/

/-- The coordinate model for a four-dimensional chart. -/
abbrev SpacetimeChart : Type := Fin 4 → ℝ

/-- A chart domain with a metric field.  This is the chart-level starting point
for the manifold layer, not a smooth manifold: `chart` is a global equivalence,
and no smoothness of the metric is asserted. -/
structure ChartSpacetime where
  /-- The underlying chart domain. -/
  carrier : Type
  /-- The topology carried by the domain. -/
  topology : TopologicalSpace carrier
  /-- A global chart equivalence to `Fin 4 → ℝ`. -/
  chart : carrier ≃ SpacetimeChart
  /-- The metric components at each point. -/
  metric : carrier → MetricTensor 4

/-- Minkowski spacetime as a chart domain. -/
def minkowskiChart : ChartSpacetime where
  carrier := SpacetimeChart
  topology := inferInstance
  chart := Equiv.refl SpacetimeChart
  metric := fun _ => minkowski

/-! ## B. Partial charts on restricted domains -/

/-- A chart-level spacetime interface on a restricted, open subset of
`SpacetimeChart`.  Unlike `ChartSpacetime`, whose `chart` is a global
equivalence to all of `Fin 4 → ℝ`, a partial chart is defined only on its
`domain`; the metric and its coordinate representatives are supplied there. -/
structure PartialChartSpacetime where
  /-- The open subset of `SpacetimeChart` on which the chart is defined. -/
  domain : Set SpacetimeChart
  /-- The chart domain is open. -/
  domain_open : IsOpen domain
  /-- The metric components at each point of the domain. -/
  metric : (x : SpacetimeChart) → x ∈ domain → MetricTensor 4

/-- The covariant metric components read on the partial chart domain. -/
noncomputable def PartialChartSpacetime.coordinateMetric (X : PartialChartSpacetime)
    (x : SpacetimeChart) (hx : x ∈ X.domain) : Tensor2 4 :=
  (X.metric x hx).g

/-- The inverse metric components read on the partial chart domain. -/
noncomputable def PartialChartSpacetime.coordinateInverseMetric
    (X : PartialChartSpacetime) (x : SpacetimeChart) (hx : x ∈ X.domain) :
    Tensor2 4 :=
  (X.metric x hx).ginv

/-- Smoothness of a partial chart: every metric component is `C^∞` on the
chart domain. -/
def PartialChartSpacetime.IsSmooth (X : PartialChartSpacetime) : Prop :=
  ∀ i j : Fin 4, ∃ f : SpacetimeChart → ℝ,
    ContDiffOn ℝ ∞ f X.domain ∧
      ∀ (x : SpacetimeChart) (hx : x ∈ X.domain),
        f x = X.coordinateMetric x hx i j

/-- Alias for `PartialChartSpacetime`. -/
abbrev PartialChart := PartialChartSpacetime

/-- Alias for `PartialChartSpacetime`. -/
abbrev RestrictedChart := PartialChartSpacetime

/-- Alias for `PartialChartSpacetime`. -/
abbrev RestrictedChartSpacetime := PartialChartSpacetime

/-- An isometric overlap between two partial charts: an open overlap set with
a smooth transition map under which the source metric is the pullback of the
target metric through an explicit Jacobian.  This is the chart-patching
certificate for partial charts: it records that two coordinate descriptions
agree where they overlap, without claiming a geometric manifold
amalgamation. -/
structure PartialChartTransition (X Y : PartialChartSpacetime) where
  /-- The open overlap set, contained in the source domain. -/
  overlap : Set SpacetimeChart
  /-- The overlap is open. -/
  overlap_open : IsOpen overlap
  /-- The overlap lies in the source chart domain. -/
  overlap_subset : overlap ⊆ X.domain
  /-- The transition map into target coordinates. -/
  toFun : SpacetimeChart → SpacetimeChart
  /-- The transition map is smooth on the overlap. -/
  smooth : ContDiffOn ℝ ∞ toFun overlap
  /-- The transition map lands in the target domain. -/
  maps_into : ∀ x ∈ overlap, toFun x ∈ Y.domain
  /-- The Jacobian of the transition map. -/
  jacobian : SpacetimeChart → Matrix (Fin 4) (Fin 4) ℝ
  /-- The source metric is the pullback of the target metric through the
  Jacobian: `g_X(x) = J(x)ᵀ · g_Y(Φ(x)) · J(x)` on the overlap. -/
  metric_pullback : ∀ (x : SpacetimeChart) (hx : x ∈ overlap),
    (X.metric x (overlap_subset hx)).g =
      (jacobian x).transpose * (Y.metric (toFun x) (maps_into x hx)).g * jacobian x

namespace PartialChartTransition

/-- The identity transition on a partial chart. -/
noncomputable def refl (X : PartialChartSpacetime) : PartialChartTransition X X where
  overlap := X.domain
  overlap_open := X.domain_open
  overlap_subset := Set.Subset.rfl
  toFun := id
  smooth := contDiffOn_id
  maps_into := fun x hx => hx
  jacobian := fun _ => 1
  metric_pullback := by
    intro x hx
    simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
    rfl

end PartialChartTransition

/-! ## C. Coordinate connection and curvature -/

/-- The Minkowski chart carries the Minkowski metric everywhere. -/
lemma minkowskiChart_metric (x : SpacetimeChart) :
    minkowskiChart.metric x = minkowski := rfl

/-- The Minkowski chart is the identity chart. -/
lemma minkowskiChart_chart (x : SpacetimeChart) :
    minkowskiChart.chart x = x := rfl

/-- The metric components read in the chosen chart. -/
noncomputable def ChartSpacetime.coordinateMetric (X : ChartSpacetime) :
    SpacetimeChart → Tensor2 4 :=
  fun x => (X.metric (X.chart.symm x)).g

/-- The inverse metric components read in the chosen chart. -/
noncomputable def ChartSpacetime.coordinateInverseMetric (X : ChartSpacetime) :
    SpacetimeChart → Tensor2 4 :=
  fun x => (X.metric (X.chart.symm x)).ginv

/-- Chart Christoffel symbols computed from the coordinate metric. -/
noncomputable def ChartSpacetime.christoffel (X : ChartSpacetime)
    (x : SpacetimeChart) (k i j : Fin 4) : ℝ :=
  CoordinateCurvature.christoffel X.coordinateMetric X.coordinateInverseMetric x k i j

/-- Chart Riemann curvature computed from the coordinate metric. -/
noncomputable def ChartSpacetime.riemann (X : ChartSpacetime)
    (x : SpacetimeChart) (ρ σ μ ν : Fin 4) : ℝ :=
  CoordinateCurvature.riemann X.coordinateMetric X.coordinateInverseMetric x ρ σ μ ν

/-- Chart Ricci tensor computed from the coordinate metric. -/
noncomputable def ChartSpacetime.ricci (X : ChartSpacetime)
    (x : SpacetimeChart) (σ ν : Fin 4) : ℝ :=
  CoordinateCurvature.ricciTensor X.coordinateMetric X.coordinateInverseMetric x σ ν

/-- Chart scalar curvature computed from the coordinate metric. -/
noncomputable def ChartSpacetime.scalarCurvature (X : ChartSpacetime)
    (x : SpacetimeChart) : ℝ :=
  CoordinateCurvature.ricciScalar X.coordinateMetric X.coordinateInverseMetric x

/-- Chart Einstein tensor computed from the coordinate metric. -/
noncomputable def ChartSpacetime.einstein (X : ChartSpacetime)
    (x : SpacetimeChart) (i j : Fin 4) : ℝ :=
  CoordinateCurvature.einsteinTensor X.coordinateMetric X.coordinateInverseMetric x i j

lemma minkowskiChart_christoffel_zero (x : SpacetimeChart) (k i j : Fin 4) :
    minkowskiChart.christoffel x k i j = 0 := by
  simpa [ChartSpacetime.christoffel] using
    CoordinateCurvature.christoffel_const minkowskiChart.coordinateMetric
      minkowskiChart.coordinateInverseMetric minkowskiMetric4 (fun _ => rfl) x k i j

lemma minkowskiChart_riemann_zero (x : SpacetimeChart)
    (ρ σ μ ν : Fin 4) :
    minkowskiChart.riemann x ρ σ μ ν = 0 := by
  simpa [ChartSpacetime.riemann] using
    CoordinateCurvature.riemann_const minkowskiChart.coordinateMetric
      minkowskiChart.coordinateInverseMetric minkowskiMetric4 (fun _ => rfl) x ρ σ μ ν

lemma minkowskiChart_ricci_zero (x : SpacetimeChart) (σ ν : Fin 4) :
    minkowskiChart.ricci x σ ν = 0 := by
  simpa [ChartSpacetime.ricci, ChartSpacetime.coordinateMetric,
    ChartSpacetime.coordinateInverseMetric, minkowskiChart, minkowski] using
    CoordinateCurvature.ricciTensor_const minkowskiChart.coordinateMetric
      minkowskiChart.coordinateInverseMetric minkowskiMetric4 (fun _ => rfl) x σ ν

lemma minkowskiChart_scalar_zero (x : SpacetimeChart) :
    minkowskiChart.scalarCurvature x = 0 := by
  simpa [ChartSpacetime.scalarCurvature, ChartSpacetime.coordinateMetric,
    ChartSpacetime.coordinateInverseMetric, minkowskiChart, minkowski] using
    CoordinateCurvature.ricciScalar_const minkowskiChart.coordinateMetric
      minkowskiChart.coordinateInverseMetric minkowskiMetric4 (fun _ => rfl) x

lemma minkowskiChart_einstein_zero (x : SpacetimeChart) (i j : Fin 4) :
    minkowskiChart.einstein x i j = 0 := by
  simpa [ChartSpacetime.einstein] using
    CoordinateCurvature.einsteinTensor_const minkowskiChart.coordinateMetric
      minkowskiChart.coordinateInverseMetric minkowskiMetric4 (fun _ => rfl) x i j

/-! ## D. Chart causal classification -/

/-- The squared Lorentzian norm of a chart tangent vector. -/
noncomputable def ChartSpacetime.normSq (X : ChartSpacetime)
    (x : SpacetimeChart) (v : Fin 4 → ℝ) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4, X.coordinateMetric x i j * v i * v j

/-- A chart vector is timelike when its squared Lorentzian norm is negative. -/
def ChartSpacetime.IsTimelike (X : ChartSpacetime)
    (x : SpacetimeChart) (v : Fin 4 → ℝ) : Prop :=
  X.normSq x v < 0

/-- A chart vector is null when its squared Lorentzian norm vanishes. -/
def ChartSpacetime.IsNull (X : ChartSpacetime)
    (x : SpacetimeChart) (v : Fin 4 → ℝ) : Prop :=
  X.normSq x v = 0

/-- A chart vector is spacelike when its squared Lorentzian norm is positive. -/
def ChartSpacetime.IsSpacelike (X : ChartSpacetime)
    (x : SpacetimeChart) (v : Fin 4 → ℝ) : Prop :=
  0 < X.normSq x v

lemma minkowskiChart_normSq (x : SpacetimeChart) (v : Fin 4 → ℝ) :
    minkowskiChart.normSq x v =
      -(v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 + (v 3) ^ 2 := by
  simp [ChartSpacetime.normSq, ChartSpacetime.coordinateMetric,
    minkowskiChart, minkowski, minkowskiMetric4_apply, Fin.sum_univ_four]
  ring

/-- The time basis vector is timelike in the Minkowski chart. -/
lemma minkowskiChart_timelike_time (x : SpacetimeChart) :
    minkowskiChart.IsTimelike x (Pi.single 0 1) := by
  rw [ChartSpacetime.IsTimelike, minkowskiChart_normSq]
  simp [Pi.single_eq_same, Pi.single_eq_of_ne]

/-- A spatial basis vector is spacelike in the Minkowski chart. -/
lemma minkowskiChart_spacelike_space (x : SpacetimeChart) :
    minkowskiChart.IsSpacelike x (Pi.single 1 1) := by
  rw [ChartSpacetime.IsSpacelike, minkowskiChart_normSq]
  simp [Pi.single_eq_same, Pi.single_eq_of_ne]

/-- The lightlike vector `(1, 1, 0, 0)`. -/
def lightlikeVector : Fin 4 → ℝ :=
  fun i => if i = 0 then 1 else if i = 1 then 1 else 0

/-- `(1, 1, 0, 0)` is null in the Minkowski chart. -/
lemma minkowskiChart_null_lightlike (x : SpacetimeChart) :
    minkowskiChart.IsNull x lightlikeVector := by
  rw [ChartSpacetime.IsNull, minkowskiChart_normSq]
  simp [lightlikeVector]

/-- The three causal characters of a Lorentzian tangent vector. -/
inductive CausalCharacter
  | timelike
  | null
  | spacelike
  deriving DecidableEq, Repr

/-- The causal character of a chart tangent vector. -/
noncomputable def ChartSpacetime.causalCharacter (X : ChartSpacetime)
    (x : SpacetimeChart) (v : Fin 4 → ℝ) : CausalCharacter := by
  classical
  exact if X.IsTimelike x v then .timelike
    else if X.IsNull x v then .null
    else .spacelike

lemma ChartSpacetime.causalCharacter_eq_timelike_of_neg
    (X : ChartSpacetime) (x : SpacetimeChart) (v : Fin 4 → ℝ)
    (h : X.IsTimelike x v) :
    X.causalCharacter x v = .timelike := by
  simp [ChartSpacetime.causalCharacter, h]

lemma ChartSpacetime.causalCharacter_eq_null_of_eq
    (X : ChartSpacetime) (x : SpacetimeChart) (v : Fin 4 → ℝ)
    (h : X.IsNull x v) :
    X.causalCharacter x v = .null := by
  have ht : ¬ X.IsTimelike x v := by
    intro ht
    rw [ChartSpacetime.IsTimelike] at ht
    rw [ChartSpacetime.IsNull] at h
    linarith
  simp [ChartSpacetime.causalCharacter, ht, h]

lemma ChartSpacetime.causalCharacter_eq_spacelike_of_pos
    (X : ChartSpacetime) (x : SpacetimeChart) (v : Fin 4 → ℝ)
    (h : X.IsSpacelike x v) :
    X.causalCharacter x v = .spacelike := by
  have ht : ¬ X.IsTimelike x v := by
    intro ht
    rw [ChartSpacetime.IsTimelike] at ht
    rw [ChartSpacetime.IsSpacelike] at h
    linarith
  have hn : ¬ X.IsNull x v := by
    intro hn
    rw [ChartSpacetime.IsNull] at hn
    rw [ChartSpacetime.IsSpacelike] at h
    linarith
  simp [ChartSpacetime.causalCharacter, ht, hn]

/-! ## E. Covariant derivatives and the Levi-Civita property -/

/-- The coordinate covariant derivative of a vector field,
`∇_i v^k = ∂_i v^k + Γ^k_{ij} v^j`. -/
noncomputable def ChartSpacetime.covariantDerivVector
    (X : ChartSpacetime) (v : SpacetimeChart → Fin 4 → ℝ)
    (x : SpacetimeChart) (i k : Fin 4) : ℝ :=
  fderiv ℝ (fun y => v y k) x (Pi.single i 1) +
    ∑ j : Fin 4, X.christoffel x k i j * v x j

/-- A constant vector field has vanishing coordinate covariant derivative in the
Minkowski chart. -/
lemma minkowskiChart_covariantDerivVector_const
    (v : Fin 4 → ℝ) (x : SpacetimeChart) (i k : Fin 4) :
    minkowskiChart.covariantDerivVector (fun _ => v) x i k = 0 := by
  simp [ChartSpacetime.covariantDerivVector, minkowskiChart_christoffel_zero]

/-- The chart Christoffel symbols are torsion-free: `Γ^k_{ij} = Γ^k_{ji}`. -/
lemma ChartSpacetime.christoffel_symm (X : ChartSpacetime)
    (x : SpacetimeChart) (k i j : Fin 4) :
    X.christoffel x k i j = X.christoffel x k j i := by
  simp only [ChartSpacetime.christoffel, CoordinateCurvature.christoffel]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  have hsymm : CoordinateCurvature.coordDeriv l (fun y => X.coordinateMetric y i j) x =
      CoordinateCurvature.coordDeriv l (fun y => X.coordinateMetric y j i) x := by
    apply CoordinateCurvature.coordDeriv_congr
    intro y
    exact (X.metric (X.chart.symm y)).symm.apply j i
  rw [hsymm]
  ring

/-- The coordinate covariant derivative of the metric,
`∇_i g_{jk} = ∂_i g_{jk} - Γ^l_{ij} g_{lk} - Γ^l_{ik} g_{jl}`. -/
noncomputable def ChartSpacetime.metricCovariantDeriv
    (X : ChartSpacetime) (x : SpacetimeChart) (i j k : Fin 4) : ℝ :=
  CoordinateCurvature.coordDeriv i (fun y => X.coordinateMetric y j k) x
    - ∑ l : Fin 4, X.christoffel x l i j * X.coordinateMetric x l k
    - ∑ l : Fin 4, X.christoffel x l i k * X.coordinateMetric x j l

/-- The Minkowski chart is metric compatible: the covariant derivative of the
metric vanishes. -/
lemma minkowskiChart_metricCovariantDeriv_zero
    (x : SpacetimeChart) (i j k : Fin 4) :
    minkowskiChart.metricCovariantDeriv x i j k = 0 := by
  rw [ChartSpacetime.metricCovariantDeriv]
  have hpd : CoordinateCurvature.coordDeriv i (fun y => minkowskiChart.coordinateMetric y j k) x = 0 := by
    have hconst : ∀ y, minkowskiChart.coordinateMetric y j k = minkowskiMetric4 j k := by
      intro y
      simp [ChartSpacetime.coordinateMetric, minkowskiChart, minkowski]
    rw [CoordinateCurvature.coordDeriv_congr i x hconst]
    exact CoordinateCurvature.coordDeriv_const i (minkowskiMetric4 j k) x
  have h1 :
      (∑ l : Fin 4,
        minkowskiChart.christoffel x l i j * minkowskiChart.coordinateMetric x l k) = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    rw [minkowskiChart_christoffel_zero]
    ring
  have h2 :
      (∑ l : Fin 4,
        minkowskiChart.christoffel x l i k * minkowskiChart.coordinateMetric x j l) = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    rw [minkowskiChart_christoffel_zero]
    ring
  rw [hpd, h1, h2]
  ring

/-- **General chart-level metric compatibility**: every `ChartSpacetime` has
vanishing coordinate covariant derivative of the metric, `∇_i g_{jk} = 0`. -/
lemma ChartSpacetime.metricCovariantDeriv_eq_zero (X : ChartSpacetime)
    (x : SpacetimeChart) (i j k : Fin 4) :
    X.metricCovariantDeriv x i j k = 0 := by
  have hInv : ∀ m q : Fin 4,
      (∑ l : Fin 4, X.coordinateInverseMetric x l m * X.coordinateMetric x l q) =
        if m = q then 1 else 0 := by
    intro m q
    have hinvR := congrFun (congrFun (X.metric (X.chart.symm x)).inv_right m) q
    have hgsym : ∀ a b, X.coordinateInverseMetric x a b = X.coordinateInverseMetric x b a :=
      fun a b => (X.metric (X.chart.symm x)).ginv_symm.apply b a
    calc
      ∑ l : Fin 4, X.coordinateInverseMetric x l m * X.coordinateMetric x l q
          = ∑ l : Fin 4, X.coordinateInverseMetric x m l * X.coordinateMetric x l q := by
            apply Finset.sum_congr rfl
            intro l _
            rw [hgsym l m]
      _ = if m = q then 1 else 0 := by
            simpa [ChartSpacetime.coordinateMetric, ChartSpacetime.coordinateInverseMetric,
              Matrix.mul_apply, Matrix.one_apply] using hinvR
  have hsum : ∀ p q : Fin 4,
      (∑ l : Fin 4, X.christoffel x l i p * X.coordinateMetric x l q) =
        (1 / 2) * (CoordinateCurvature.coordDeriv i (fun y => X.coordinateMetric y p q) x
          + CoordinateCurvature.coordDeriv p (fun y => X.coordinateMetric y i q) x
          - CoordinateCurvature.coordDeriv q (fun y => X.coordinateMetric y i p) x) := by
    intro p q
    simp only [ChartSpacetime.christoffel, CoordinateCurvature.christoffel,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    calc
      ∑ m : Fin 4, ∑ l : Fin 4, (1 / 2) * (X.coordinateInverseMetric x l m *
          (CoordinateCurvature.coordDeriv i (fun y => X.coordinateMetric y p m) x
            + CoordinateCurvature.coordDeriv p (fun y => X.coordinateMetric y i m) x
            - CoordinateCurvature.coordDeriv m (fun y => X.coordinateMetric y i p) x)) *
          X.coordinateMetric x l q
          = ∑ m : Fin 4, (1 / 2) * (CoordinateCurvature.coordDeriv i (fun y => X.coordinateMetric y p m) x
              + CoordinateCurvature.coordDeriv p (fun y => X.coordinateMetric y i m) x
              - CoordinateCurvature.coordDeriv m (fun y => X.coordinateMetric y i p) x) *
              (∑ l : Fin 4, X.coordinateInverseMetric x l m * X.coordinateMetric x l q) := by
            apply Finset.sum_congr rfl
            intro m _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro l _
            ring
      _ = (1 / 2) * (CoordinateCurvature.coordDeriv i (fun y => X.coordinateMetric y p q) x
            + CoordinateCurvature.coordDeriv p (fun y => X.coordinateMetric y i q) x
            - CoordinateCurvature.coordDeriv q (fun y => X.coordinateMetric y i p) x) := by
            simp_rw [hInv]
            simp
  have hg2 : (∑ l : Fin 4, X.christoffel x l i k * X.coordinateMetric x j l) =
      (1 / 2) * (CoordinateCurvature.coordDeriv i (fun y => X.coordinateMetric y k j) x
        + CoordinateCurvature.coordDeriv k (fun y => X.coordinateMetric y i j) x
        - CoordinateCurvature.coordDeriv j (fun y => X.coordinateMetric y i k) x) := by
    have hrewrite : (∑ l : Fin 4, X.christoffel x l i k * X.coordinateMetric x j l) =
        ∑ l : Fin 4, X.christoffel x l i k * X.coordinateMetric x l j := by
      apply Finset.sum_congr rfl
      intro l _
      have hsym : X.coordinateMetric x j l = X.coordinateMetric x l j :=
        (X.metric (X.chart.symm x)).symm.apply l j
      rw [hsym]
    rw [hrewrite, hsum k j]
  have hpd_sym : CoordinateCurvature.coordDeriv i (fun y => X.coordinateMetric y k j) x =
      CoordinateCurvature.coordDeriv i (fun y => X.coordinateMetric y j k) x :=
    CoordinateCurvature.coordDeriv_congr i x fun y => (X.metric (X.chart.symm y)).symm.apply j k
  rw [ChartSpacetime.metricCovariantDeriv, hsum j k, hg2, hpd_sym]
  ring

/-- A chart-level Levi-Civita certificate: torsion-freeness together with metric
compatibility. -/
structure ChartSpacetime.IsLeviCivita (X : ChartSpacetime) : Prop where
  /-- The coordinate connection is torsion-free. -/
  torsion_free : ∀ (x : SpacetimeChart) (k i j : Fin 4),
    X.christoffel x k i j = X.christoffel x k j i
  /-- The coordinate covariant derivative of the metric vanishes. -/
  metric_compatible : ∀ (x : SpacetimeChart) (i j k : Fin 4),
    X.metricCovariantDeriv x i j k = 0

/-- Every `ChartSpacetime` carries a canonical torsion-free, metric-compatible
Levi-Civita connection in its coordinate chart. -/
lemma ChartSpacetime.isLeviCivita (X : ChartSpacetime) : X.IsLeviCivita where
  torsion_free := X.christoffel_symm
  metric_compatible := X.metricCovariantDeriv_eq_zero

/-- The Minkowski chart carries a chart-level Levi-Civita connection. -/
lemma minkowskiChart_isLeviCivita : minkowskiChart.IsLeviCivita :=
  minkowskiChart.isLeviCivita

/-- Every chart tangent vector has one of the three causal characters. -/
lemma ChartSpacetime.causalCharacter_cases (X : ChartSpacetime)
    (x : SpacetimeChart) (v : Fin 4 → ℝ) :
    X.causalCharacter x v = .timelike ∨
      X.causalCharacter x v = .null ∨
      X.causalCharacter x v = .spacelike := by
  cases X.causalCharacter x v <;> simp

/-! ## F. Mathlib charted-manifold bridge and global hyperbolicity -/

/-- A `ChartSpacetime` whose chart bijection is a Mathlib homeomorphism,
equipping its carrier with a `ChartedSpace SpacetimeChart` manifold atlas. -/
structure SmoothChartSpacetime extends ChartSpacetime where
  /-- Global chart homeomorphism onto `ℝ⁴`. -/
  chartHomeo : @Homeomorph carrier SpacetimeChart topology inferInstance
  /-- Compatibility with `ChartSpacetime.chart`. -/
  chart_eq : ∀ p, chart p = chartHomeo p

/-- Construct a Mathlib `ChartedSpace SpacetimeChart` structure on any
`SmoothChartSpacetime` carrier. -/
@[instance_reducible]
noncomputable def SmoothChartSpacetime.chartedSpace (X : SmoothChartSpacetime) :
    @ChartedSpace SpacetimeChart _ X.carrier X.topology :=
  let _ : TopologicalSpace X.carrier := X.topology
  X.chartHomeo.symm.chartedSpace

/-- Minkowski spacetime as a `SmoothChartSpacetime`. -/
def minkowskiSmoothChart : SmoothChartSpacetime where
  toChartSpacetime := minkowskiChart
  chartHomeo := Homeomorph.refl SpacetimeChart
  chart_eq := fun _ => rfl

/-- A `C¹` future-directed timelike curve in a chart spacetime. -/
def ChartSpacetime.IsFutureTimelikeCurve (X : ChartSpacetime)
    (γ : ℝ → SpacetimeChart) : Prop :=
  (∀ t, DifferentiableAt ℝ γ t) ∧
  (∀ t, X.IsTimelike (γ t) (deriv γ t)) ∧
  (∀ t, 0 < deriv γ t 0)

/-- A `C¹` future-directed causal curve in a chart spacetime. -/
def ChartSpacetime.IsFutureCausalCurve (X : ChartSpacetime)
    (γ : ℝ → SpacetimeChart) : Prop :=
  (∀ t, DifferentiableAt ℝ γ t) ∧
  (∀ t, X.IsTimelike (γ t) (deriv γ t) ∨ X.IsNull (γ t) (deriv γ t)) ∧
  (∀ t, 0 ≤ deriv γ t 0)

/-- Causal precedence `p ≤ q` via a future-directed causal curve on `[0, 1]`. -/
def ChartSpacetime.CausalPrecedes (X : ChartSpacetime)
    (p q : SpacetimeChart) : Prop :=
  ∃ γ : ℝ → SpacetimeChart, X.IsFutureCausalCurve γ ∧ γ 0 = p ∧ γ 1 = q

/-- A set `S` is a chart Cauchy surface when every inextendible future-directed
timelike curve (with unbounded coordinate time) meets `S` at a unique parameter
value. -/
def ChartSpacetime.IsCauchySurface (X : ChartSpacetime)
    (S : Set SpacetimeChart) : Prop :=
  ∀ γ : ℝ → SpacetimeChart,
    X.IsFutureTimelikeCurve γ →
    Function.Surjective (fun t => γ t 0) →
    ∃! t : ℝ, γ t ∈ S

/-- A chart spacetime is globally hyperbolic when it admits a Cauchy surface. -/
def ChartSpacetime.IsGloballyHyperbolic (X : ChartSpacetime) : Prop :=
  ∃ S : Set SpacetimeChart, X.IsCauchySurface S

/-- Coordinate time along a future-directed timelike curve in `ℝ⁴` has positive
time derivative. -/
lemma hasDerivAt_coord_zero_pos {γ : ℝ → SpacetimeChart}
    (hdiff : ∀ t, DifferentiableAt ℝ γ t) (hpos : ∀ t, 0 < deriv γ t 0)
    (t : ℝ) :
    0 < deriv (fun s => γ s 0) t := by
  have hpi : HasDerivAt (fun s => γ s 0) (deriv γ t 0) t := by
    have hd := (hdiff t).hasDerivAt
    exact (hasDerivAt_pi.mp hd) 0
  simpa [hpi.deriv] using hpos t

/-- The constant-time slice `t = 0` is a Cauchy surface in `minkowskiChart`. -/
lemma minkowskiChart_t0_cauchySurface :
    minkowskiChart.IsCauchySurface {x : SpacetimeChart | x 0 = 0} := by
  intro γ ⟨hdiff, _htime, hpos⟩ hsurj
  obtain ⟨t₀, ht₀⟩ := hsurj 0
  have hmono : StrictMono (fun t => γ t 0) :=
    strictMono_of_deriv_pos (hasDerivAt_coord_zero_pos hdiff hpos)
  refine ⟨t₀, ht₀, ?_⟩
  intro t ht
  exact hmono.injective (by simpa [Set.mem_ofPred_eq, ht₀] using ht)

/-- Minkowski spacetime is globally hyperbolic. -/
lemma minkowskiChart_globallyHyperbolic :
    minkowskiChart.IsGloballyHyperbolic :=
  ⟨{x : SpacetimeChart | x 0 = 0}, minkowskiChart_t0_cauchySurface⟩

/-! ## G. Chart-level isometries and embeddings

These structures supply the isometry/embedding API needed by the maximal-
development layer at chart scope.  They preserve the chart coordinate and the
metric and inverse-metric components; they do not assert that a chart embeds
into a geometric 4D Lorentzian manifold.
-/

/-- A chart-level isometry between two chart spacetimes: an equivalence of
carriers that commutes with the charts and pulls back both metric components
and their inverse components. -/
structure ChartSpacetime.Isometry (X Y : ChartSpacetime) where
  /-- The underlying equivalence of carriers. -/
  toEquiv : X.carrier ≃ Y.carrier
  /-- The equivalence is compatible with the chosen charts. -/
  chart_comm : ∀ p : X.carrier, Y.chart (toEquiv p) = X.chart p
  /-- The covariant metric components are preserved. -/
  metric_pullback : ∀ p : X.carrier,
    (Y.metric (toEquiv p)).g = (X.metric p).g
  /-- The inverse metric components are preserved. -/
  inverse_pullback : ∀ p : X.carrier,
    (Y.metric (toEquiv p)).ginv = (X.metric p).ginv

namespace ChartSpacetime.Isometry

/-- The identity chart isometry. -/
def refl (X : ChartSpacetime) : ChartSpacetime.Isometry X X where
  toEquiv := Equiv.refl X.carrier
  chart_comm := fun _ => rfl
  metric_pullback := fun _ => rfl
  inverse_pullback := fun _ => rfl

/-- The inverse of a chart isometry. -/
def symm {X Y : ChartSpacetime} (e : ChartSpacetime.Isometry X Y) :
    ChartSpacetime.Isometry Y X where
  toEquiv := e.toEquiv.symm
  chart_comm := by
    intro p
    have h := e.chart_comm (e.toEquiv.symm p)
    simpa using h.symm
  metric_pullback := by
    intro p
    have h := e.metric_pullback (e.toEquiv.symm p)
    simpa using h.symm
  inverse_pullback := by
    intro p
    have h := e.inverse_pullback (e.toEquiv.symm p)
    simpa using h.symm

/-- Composition of chart isometries. -/
def trans {X Y Z : ChartSpacetime} (e : ChartSpacetime.Isometry X Y)
    (f : ChartSpacetime.Isometry Y Z) : ChartSpacetime.Isometry X Z where
  toEquiv := e.toEquiv.trans f.toEquiv
  chart_comm := by
    intro p
    simp [Equiv.trans_apply, f.chart_comm, e.chart_comm]
  metric_pullback := by
    intro p
    simp [Equiv.trans_apply, f.metric_pullback, e.metric_pullback]
  inverse_pullback := by
    intro p
    simp [Equiv.trans_apply, f.inverse_pullback, e.inverse_pullback]

end ChartSpacetime.Isometry

/-- Existence of a chart isometry. -/
def ChartSpacetime.IsIsometric (X Y : ChartSpacetime) : Prop :=
  Nonempty (ChartSpacetime.Isometry X Y)

/-- Chart isometry is reflexive. -/
lemma ChartSpacetime.isometric_refl (X : ChartSpacetime) :
    ChartSpacetime.IsIsometric X X :=
  ⟨ChartSpacetime.Isometry.refl X⟩

/-- Chart isometry is symmetric. -/
lemma ChartSpacetime.isometric_symm {X Y : ChartSpacetime}
    (h : ChartSpacetime.IsIsometric X Y) : ChartSpacetime.IsIsometric Y X :=
  h.elim fun e => ⟨e.symm⟩

/-- Chart isometry is transitive. -/
lemma ChartSpacetime.isometric_trans {X Y Z : ChartSpacetime}
    (hXY : ChartSpacetime.IsIsometric X Y) (hYZ : ChartSpacetime.IsIsometric Y Z) :
    ChartSpacetime.IsIsometric X Z :=
  hXY.elim fun e => hYZ.elim fun f => ⟨e.trans f⟩

/-- A chart-level embedding: an injective map that commutes with the charts
and preserves metric and inverse-metric components. -/
structure ChartSpacetime.Embedding (X Y : ChartSpacetime) where
  /-- The underlying map of carriers. -/
  toFun : X.carrier → Y.carrier
  /-- The map is injective. -/
  injective : Function.Injective toFun
  /-- The embedding is compatible with the chosen charts. -/
  chart_comm : ∀ p : X.carrier, Y.chart (toFun p) = X.chart p
  /-- The covariant metric components are preserved. -/
  metric_pullback : ∀ p : X.carrier,
    (Y.metric (toFun p)).g = (X.metric p).g
  /-- The inverse metric components are preserved. -/
  inverse_pullback : ∀ p : X.carrier,
    (Y.metric (toFun p)).ginv = (X.metric p).ginv

namespace ChartSpacetime.Embedding

/-- The identity embedding. -/
def refl (X : ChartSpacetime) : ChartSpacetime.Embedding X X where
  toFun := id
  injective := Function.injective_id
  chart_comm := fun _ => rfl
  metric_pullback := fun _ => rfl
  inverse_pullback := fun _ => rfl

/-- Composition of chart embeddings. -/
def trans {X Y Z : ChartSpacetime} (e : ChartSpacetime.Embedding X Y)
    (f : ChartSpacetime.Embedding Y Z) : ChartSpacetime.Embedding X Z where
  toFun := f.toFun ∘ e.toFun
  injective := f.injective.comp e.injective
  chart_comm := by
    intro p
    simp [Function.comp_apply, f.chart_comm, e.chart_comm]
  metric_pullback := by
    intro p
    simp [Function.comp_apply, f.metric_pullback, e.metric_pullback]
  inverse_pullback := by
    intro p
    simp [Function.comp_apply, f.inverse_pullback, e.inverse_pullback]

end ChartSpacetime.Embedding

end GeneralRelativity
