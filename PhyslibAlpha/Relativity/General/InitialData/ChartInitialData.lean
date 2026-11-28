/-
Copyright (c) 2026 Alex Vergara Gil.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/

module

public import PhyslibAlpha.Relativity.General.Bianchi
public import PhyslibAlpha.Relativity.General.ManifoldInterface
public import PhyslibAlpha.Relativity.General.InitialData.Basic
public import PhyslibAlpha.Relativity.General.InitialData.FlatSlice
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!

# Chart-level initial data

## i. Overview

This file connects a chart spacetime to the existing ADM `InitialData`
structure.  The induced spatial metric is read
from the `t = 0` slice of the chart metric.  The file packages smooth chart
regularity, the slice embedding and restriction of the metric to it, and the
constraint residual of bundled initial data.

The regularity here is smooth (`ContDiff`) component regularity on a chart, not
manifold Sobolev `H^s` theory: Sobolev spaces, trace/embedding estimates and
constraint solving remain outside this interface.

## ii. Key results

- `ChartSpacetime.spatialMetric`, `ChartSpacetime.spatialMetricField` : the
  spatial metric induced on the `t = 0` chart slice.
- `spatialRiemannTensorOf` : the 3D Riemann tensor derived from a metric field
  and packaged as a `RiemannTensor 3` using the coordinate skew, pair-symmetry
  and Bianchi theorems.
- `spatialRiemannTensorOfConstMetric` :
  the constant bundled-metric specialization, with symmetry and inverse
  hypotheses discharged by `MetricTensor`.
- `warpedSpatialMetric`, `warpedSpatialMetricInv`, `warpedSpatialRiemann` :
  a nonconstant warped metric, its inverse, and its derived Riemann tensor.
- `warpedRiemann_0101`, `spatialRiemannTensorOf_warped_nonconstant` :
  the derived `R_{0101}` is `-1`, complementing the flat constant-metric check.
- `extrinsicDerivativeOf` : the momentum-constraint table `dK_μij = ∂_μ K_ij`
  derived from an extrinsic-curvature field.
- `ChartInitialData`, `ChartInitialData.ofDerivedData` : bundled chart initial
  data and the constructor taking the derived curvature and derivative data.
- `ChartInitialData.ofFields` : field-level constructor computing `R3` and `dK`
  from metric and extrinsic-curvature fields.
- `ChartInitialData.ofChartData` : field-of-bundled-metrics constructor
  deriving the inverse relation and Christoffel symmetry from the
  `MetricTensor` fields and `Bianchi.christoffel_symm`.
- `ManifoldSpacetime`, `ManifoldInitialData` : global-chart manifold
  packaging of the derived chart curvature and momentum data.
- `ManifoldTransition` : an isometric transition between two global charts,
  preserving the metric and inverse metric.
- `ManifoldTransition.coordinateMetric_eq`, `coordinateInverseMetric_eq` : the
  transition preserves all coordinate metric and inverse-metric components.
- `ManifoldTransition.spatialMetric_eq`, `spatialMetricField_eq` : the
  transition preserves the induced spatial metric, pointwise and on the slice.
- `ManifoldInitialData.IsInduced` : the ADM metric agrees with the spatial
  metric induced by the chart metric.
- `ManifoldInitialData.IsCompatible` : induced initial data agree under a
  chart transition; it is reflexive, symmetric and transitive.
- `ManifoldInitialData.ham_zero`, `mom_zero`, `isVacuumData` : direct wrapper
  access to the Hamiltonian, momentum and vacuum-constraint facts.
- `minkowskiManifoldInitialData` : the Minkowski manifold-level instance.
- `minkowskiChartInitialDataDerived` : the Minkowski chart data reconstructed
  through the derived curvature and momentum constructors.
- `ChartInitialData.constraintResidual_eq_zero` : bundled vacuum data have zero
  constraint residual.

## iii. Table of contents

- A. The chart slice and its induced metric
- B. Derived curvature and extrinsic-curvature data
- C. Bundled chart initial data and constraints
- D. Manifold-level packaging

## iv. References

* S. M. Carroll, *Lecture Notes on General Relativity*, arXiv:gr-qc/9712019,
  Ch. 4, p. 104. [ref: Carroll1997, p. 104]
* R. Arnowitt, S. Deser, and C. W. Misner, *The Dynamics of General
  Relativity*, arXiv:gr-qc/0405109, p. 1. [ref: ADM1962, p. 1]

-/
@[expose] public section

namespace GeneralRelativity

open Filter Topology
open scoped ContDiff

/-! ## A. The chart slice and its induced metric -/

/-- The `t = 0` coordinate slice of a four-dimensional chart. -/
def spacetimeSlice (x : Fin 3 → ℝ) : SpacetimeChart :=
  Fin.cons 0 x

/-- The slice map is injective. -/
lemma spacetimeSlice_injective : Function.Injective spacetimeSlice := by
  change Function.Injective
    (Fin.cons (n := 3) (α := fun _ : Fin 4 => ℝ) (0 : ℝ))
  exact Fin.cons_right_injective 0

/-- The slice map is smooth as a map between chart coordinate spaces. -/
lemma contDiff_spacetimeSlice : ContDiff ℝ ∞ spacetimeSlice := by
  rw [contDiff_pi]
  intro i
  refine Fin.cases ?_ ?_ i
  · simpa [spacetimeSlice] using
      (contDiff_const : ContDiff ℝ ∞ fun _ : Fin 3 → ℝ => (0 : ℝ))
  · intro j
    simpa [spacetimeSlice] using
      (contDiff_apply (𝕜 := ℝ) (n := ∞) (F' := fun _ : Fin 3 => ℝ) j)

/-- Smoothness of the metric components in a chart.  This is the chart-level
regularity input; it is stronger than, and not a substitute for, manifold
Sobolev regularity. -/
def ChartSpacetime.IsSmooth (X : ChartSpacetime) : Prop :=
  ∀ i j : Fin 4, ContDiff ℝ ∞ fun x : SpacetimeChart => X.coordinateMetric x i j

/-- The spatial metric induced on the `t = 0` chart slice. -/
noncomputable def ChartSpacetime.spatialMetric (X : ChartSpacetime) : Tensor2 3 :=
  fun i j => X.coordinateMetric 0 (Fin.succ i) (Fin.succ j)

/-- The spatial metric as a field on the three-dimensional slice. -/
noncomputable def ChartSpacetime.spatialMetricField
    (X : ChartSpacetime) : (Fin 3 → ℝ) → Tensor2 3 :=
  fun y i j => X.coordinateMetric (spacetimeSlice y) (Fin.succ i) (Fin.succ j)

/-- The spatial metric field restricts to the previously defined slice metric at
the origin. -/
lemma ChartSpacetime.spatialMetricField_zero (X : ChartSpacetime) :
    X.spatialMetricField 0 = X.spatialMetric := by
  have hzero : spacetimeSlice (0 : Fin 3 → ℝ) = 0 := by
    funext k
    cases k using Fin.cases <;> simp [spacetimeSlice]
  ext i j
  simp [ChartSpacetime.spatialMetricField, ChartSpacetime.spatialMetric, hzero]

/-- Smooth chart metrics restrict to smooth spatial metric components on the
`t = 0` slice. -/
lemma ChartSpacetime.spatialMetricField_contDiff (X : ChartSpacetime)
    (hX : X.IsSmooth) (i j : Fin 3) :
    ContDiff ℝ ∞ fun y : Fin 3 → ℝ => X.spatialMetricField y i j := by
  change ContDiff ℝ ∞
    ((fun x : SpacetimeChart => X.coordinateMetric x (Fin.succ i) (Fin.succ j)) ∘
      spacetimeSlice)
  exact (hX (Fin.succ i) (Fin.succ j)).comp contDiff_spacetimeSlice

/-- Extensionality for covariant Riemann tensors: equality of all components
implies equality of the bundled tensor. -/
lemma riemannTensor_ext {n : ℕ} {R S : RiemannTensor n}
    (h : ∀ i j k l, R.comp i j k l = S.comp i j k l) : R = S := by
  cases R with
  | mk comp skew pair bianchi =>
    cases S with
    | mk comp' skew' pair' bianchi' =>
      have hcomp : comp = comp' := by
        funext i j k l
        exact h i j k l
      subst hcomp
      simp

/-! ## B. Derived curvature and extrinsic-curvature data -/

/-- The `R3` tensor derived from a 3-metric field: lower the mixed coordinate
Riemann tensor with the metric and use the coordinate skew, pair-symmetry and
Bianchi theorems to fill the `RiemannTensor` fields.
See arXiv:gr-qc/9712019, pp. 72–73. [ref: Carroll1997, pp. 72–73] -/
noncomputable def spatialRiemannTensorOf
    (h hinv : (Fin 3 → ℝ) → Tensor2 3) (x : Fin 3 → ℝ)
    (hgSymm : ∀ᶠ y in 𝓝 x, ∀ i j, h y i j = h y j i)
    (hInv : ∀ᶠ y in 𝓝 x, ∀ m j, ∑ a, hinv y a m * h y a j = if m = j then 1 else 0)
    (hgC2 : ∀ i j, ContDiffAt ℝ 2 (fun y => h y i j) x)
    (hΓD : ∀ k i j,
      DifferentiableAt ℝ (fun y => CoordinateCurvature.christoffel h hinv y k i j) x)
    (hΓ : ∀ᶠ y in 𝓝 x, ∀ k i j, CoordinateCurvature.christoffel h hinv y k i j =
      CoordinateCurvature.christoffel h hinv y k j i) : RiemannTensor 3 where
  comp := fun a b c d => ∑ e, h x a e * CoordinateCurvature.riemann h hinv x e b c d
  skew_last := by
    intro a b c d
    calc
      (∑ e, h x a e * CoordinateCurvature.riemann h hinv x e b c d)
          = ∑ e, h x a e * (-CoordinateCurvature.riemann h hinv x e b d c) := by
            apply Finset.sum_congr rfl
            intro e _
            rw [Bianchi.riemann_skew_last]
      _ = -∑ e, h x a e * CoordinateCurvature.riemann h hinv x e b d c := by
            simp_rw [mul_neg, Finset.sum_neg_distrib]
  pair_symm := by
    intro a b c d
    exact Bianchi.riemann_lower_pair_symm h hinv hgSymm hInv hgC2 hΓD hΓ a b c d
  bianchi := by
    intro a b c d
    exact Bianchi.riemann_lower_bianchi h hinv x hΓ a b c d

/-- The derived `R3` of a constant metric is the flat Riemann tensor. -/
lemma spatialRiemannTensorOf_const
    (G : Tensor2 3) (h hinv : (Fin 3 → ℝ) → Tensor2 3) (x : Fin 3 → ℝ)
    (hG : ∀ y, h y = G)
    (hgSymm : ∀ᶠ y in 𝓝 x, ∀ i j, h y i j = h y j i)
    (hInv : ∀ᶠ y in 𝓝 x, ∀ m j, ∑ a, hinv y a m * h y a j = if m = j then 1 else 0)
    (hgC2 : ∀ i j, ContDiffAt ℝ 2 (fun y => h y i j) x)
    (hΓD : ∀ k i j,
      DifferentiableAt ℝ (fun y => CoordinateCurvature.christoffel h hinv y k i j) x)
    (hΓ : ∀ᶠ y in 𝓝 x, ∀ k i j, CoordinateCurvature.christoffel h hinv y k i j =
      CoordinateCurvature.christoffel h hinv y k j i) :
    spatialRiemannTensorOf h hinv x hgSymm hInv hgC2 hΓD hΓ =
      RiemannTensor.flat 3 := by
  apply riemannTensor_ext
  intro a b c d
  change (∑ e, h x a e * CoordinateCurvature.riemann h hinv x e b c d) = 0
  apply Finset.sum_eq_zero
  intro e _
  rw [CoordinateCurvature.riemann_const h hinv G hG x e b c d]
  ring

/-- The derived Riemann tensor of a constant bundled metric.  Symmetry and the
inverse relation are discharged by the `MetricTensor` fields, so no hand
hypotheses are needed for the constant case. -/
noncomputable def spatialRiemannTensorOfConstMetric
    (M : MetricTensor 3) (x : Fin 3 → ℝ) : RiemannTensor 3 :=
  spatialRiemannTensorOf (fun _ => M.g) (fun _ => M.ginv) x
    (by
      filter_upwards with _ i j
      exact (M.symm.apply i j).symm)
    (by
      filter_upwards with _ m j
      calc
        (∑ a, M.ginv a m * M.g a j)
            = ∑ a, M.ginv m a * M.g a j := by
              apply Finset.sum_congr rfl
              intro a _
              rw [M.ginv_symm.apply m a]
        _ = if m = j then 1 else 0 := M.sum_ginv_mul_g_left m j)
    (fun _ _ => contDiffAt_const)
    (by
      intro k i j
      have hc : (fun y : Fin 3 → ℝ =>
          CoordinateCurvature.christoffel (fun _ => M.g) (fun _ => M.ginv) y k i j)
            = fun _ => 0 := by
        funext y
        exact CoordinateCurvature.christoffel_const (fun _ => M.g) (fun _ => M.ginv) M.g
          (fun _ => rfl) y k i j
      rw [hc]
      exact differentiableAt_const 0)
    (by
      filter_upwards with y k i j
      rw [CoordinateCurvature.christoffel_const (fun _ => M.g) (fun _ => M.ginv) M.g
          (fun _ => rfl) y k i j,
        CoordinateCurvature.christoffel_const (fun _ => M.g) (fun _ => M.ginv) M.g
          (fun _ => rfl) y k j i])

/-- A constant bundled metric has flat derived Riemann curvature. -/
lemma spatialRiemannTensorOfConstMetric_eq_flat
    (M : MetricTensor 3) (x : Fin 3 → ℝ) :
    spatialRiemannTensorOfConstMetric M x = RiemannTensor.flat 3 :=
  spatialRiemannTensorOf_const M.g (fun _ => M.g) (fun _ => M.ginv) x (fun _ => rfl)
    (by
      filter_upwards with _ i j
      exact (M.symm.apply i j).symm)
    (by
      filter_upwards with _ m j
      calc
        (∑ a, M.ginv a m * M.g a j)
            = ∑ a, M.ginv m a * M.g a j := by
              apply Finset.sum_congr rfl
              intro a _
              rw [M.ginv_symm.apply m a]
        _ = if m = j then 1 else 0 := M.sum_ginv_mul_g_left m j)
    (fun _ _ => contDiffAt_const)
    (by
      intro k i j
      have hc : (fun y : Fin 3 → ℝ =>
          CoordinateCurvature.christoffel (fun _ => M.g) (fun _ => M.ginv) y k i j)
            = fun _ => 0 := by
        funext y
        exact CoordinateCurvature.christoffel_const (fun _ => M.g) (fun _ => M.ginv) M.g
          (fun _ => rfl) y k i j
      rw [hc]
      exact differentiableAt_const 0)
    (by
      filter_upwards with y k i j
      rw [CoordinateCurvature.christoffel_const (fun _ => M.g) (fun _ => M.ginv) M.g
          (fun _ => rfl) y k i j,
        CoordinateCurvature.christoffel_const (fun _ => M.g) (fun _ => M.ginv) M.g
          (fun _ => rfl) y k j i])

/-- The momentum-constraint derivative table `dK_μij = ∂_μ K_ij` derived from
the extrinsic-curvature field. -/
noncomputable def extrinsicDerivativeOf
    (K : (Fin 3 → ℝ) → Tensor2 3) (x : Fin 3 → ℝ) : Fin 3 → Tensor2 3 :=
  fun μ i j => CoordinateCurvature.coordDeriv μ (fun y => K y i j) x

/-- A constant extrinsic curvature has vanishing derived derivative table. -/
lemma extrinsicDerivativeOf_const (K : Tensor2 3) (x : Fin 3 → ℝ) (μ : Fin 3) :
    extrinsicDerivativeOf (fun _ => K) x μ = 0 := by
  ext i j
  simp [extrinsicDerivativeOf, CoordinateCurvature.coordDeriv_const]

/-- The Minkowski chart induces the Euclidean spatial metric components on the
`t = 0` slice. -/
lemma minkowskiChart_spatialMetric :
    minkowskiChart.spatialMetric = euclideanMetric3.g := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ChartSpacetime.spatialMetric, ChartSpacetime.coordinateMetric,
      minkowskiChart, minkowski, euclideanMetric3, minkowskiMetric4_apply]

/-! ## C. Bundled chart initial data and constraints -/

/-- ADM data on a chart slice, together with the momentum-constraint derivative
and a proof that the vacuum constraints hold. -/
structure ChartInitialData (X : ChartSpacetime) where
  /-- The ADM metric, spatial curvature and extrinsic curvature. -/
  data : InitialData
  /-- The spatial Christoffel symbols `Γ^k_{ij}` at the slice point. -/
  Γ : Fin 3 → Fin 3 → Fin 3 → ℝ
  /-- The coordinate derivative `∂K` used by the momentum constraint. -/
  dK : Fin 3 → Tensor2 3
  /-- The vacuum constraint equations. -/
  vacuum : data.IsVacuumData Γ dK

/-- Chart initial data whose curvature and momentum derivative are supplied by
the derived constructors `spatialRiemannTensorOf` and `extrinsicDerivativeOf`.
The vacuum proof is still an input: no constraint-solving theorem is claimed. -/
noncomputable def ChartInitialData.ofDerivedData
    (X : ChartSpacetime) (h : MetricTensor 3) (K : Tensor2 3)
    (Ksymm : IsSymm K) (R3 : RiemannTensor 3) (Γ : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (dK : Fin 3 → Tensor2 3)
    (vacuum : (InitialData.mk h R3 K Ksymm).IsVacuumData Γ dK) :
    ChartInitialData X where
  data := InitialData.mk h R3 K Ksymm
  Γ := Γ
  dK := dK
  vacuum := vacuum

/-- Chart initial data whose `R3` and `dK` are computed from metric and
extrinsic-curvature fields.  The vacuum proof remains an explicit input: this
constructor packages the geometric data, it does not solve the constraints. -/
noncomputable def ChartInitialData.ofFields
    (X : ChartSpacetime) (M : MetricTensor 3)
    (h hinv : (Fin 3 → ℝ) → Tensor2 3) (K : (Fin 3 → ℝ) → Tensor2 3) (x : Fin 3 → ℝ)
    (hgSymm : ∀ᶠ y in 𝓝 x, ∀ i j, h y i j = h y j i)
    (hInv : ∀ᶠ y in 𝓝 x, ∀ m j,
      ∑ a, hinv y a m * h y a j = if m = j then 1 else 0)
    (hgC2 : ∀ i j, ContDiffAt ℝ 2 (fun y => h y i j) x)
    (hΓD : ∀ k i j,
      DifferentiableAt ℝ (fun y => CoordinateCurvature.christoffel h hinv y k i j) x)
    (hΓ : ∀ᶠ y in 𝓝 x, ∀ k i j,
      CoordinateCurvature.christoffel h hinv y k i j
        = CoordinateCurvature.christoffel h hinv y k j i)
    (Ksymm : IsSymm (K x))
    (vacuum : (InitialData.mk M
      (spatialRiemannTensorOf h hinv x hgSymm hInv hgC2 hΓD hΓ)
      (K x) Ksymm).IsVacuumData
      (fun k i j => CoordinateCurvature.christoffel h hinv x k i j)
      (extrinsicDerivativeOf K x)) :
    ChartInitialData X :=
  ChartInitialData.ofDerivedData X M (K x) Ksymm
    (spatialRiemannTensorOf h hinv x hgSymm hInv hgC2 hΓD hΓ)
    (fun k i j => CoordinateCurvature.christoffel h hinv x k i j)
    (extrinsicDerivativeOf K x) vacuum

/-- A field of bundled metrics is symmetric near every point. -/
lemma metricField_symm (M : (Fin 3 → ℝ) → MetricTensor 3) (x : Fin 3 → ℝ) :
    ∀ᶠ y in 𝓝 x, ∀ i j, (M y).g i j = (M y).g j i := by
  filter_upwards with y i j
  exact ((M y).symm.apply i j).symm

/-- A field of bundled metrics satisfies the component inverse relation. -/
lemma metricField_inv (M : (Fin 3 → ℝ) → MetricTensor 3) (x : Fin 3 → ℝ) :
    ∀ᶠ y in 𝓝 x, ∀ m j,
      ∑ a, (M y).ginv a m * (M y).g a j = if m = j then 1 else 0 := by
  filter_upwards with y m j
  calc
    (∑ a, (M y).ginv a m * (M y).g a j)
        = ∑ a, (M y).ginv m a * (M y).g a j := by
          apply Finset.sum_congr rfl
          intro a _
          rw [(M y).ginv_symm.apply m a]
    _ = if m = j then 1 else 0 := (M y).sum_ginv_mul_g_left m j

/-- The Christoffel symbols of a field of bundled metrics are symmetric. -/
lemma metricField_christoffel_symm (M : (Fin 3 → ℝ) → MetricTensor 3)
    (x : Fin 3 → ℝ) :
    ∀ᶠ y in 𝓝 x, ∀ k i j,
      CoordinateCurvature.christoffel (fun z => (M z).g) (fun z => (M z).ginv) y k i j =
        CoordinateCurvature.christoffel (fun z => (M z).g) (fun z => (M z).ginv) y k j i := by
  filter_upwards with y k i j
  exact Bianchi.christoffel_symm (fun z => (M z).g) (fun z => (M z).ginv)
    (x := y) (by
      filter_upwards with z i j
      exact ((M z).symm.apply i j).symm) k i j

/-- Differentiability of the coordinate Christoffel symbols from `C²` metric
components and differentiable inverse components. -/
lemma differentiableAt_christoffel_of_contDiffAt_two {n : ℕ}
    {g ginv : (Fin n → ℝ) → Tensor2 n} {x : Fin n → ℝ}
    (hgC2 : ∀ i j, ContDiffAt ℝ 2 (fun y => g y i j) x)
    (hginvD : ∀ i j, DifferentiableAt ℝ (fun y => ginv y i j) x)
    (k i j : Fin n) :
    DifferentiableAt ℝ (fun y => CoordinateCurvature.christoffel g ginv y k i j) x := by
  have hpdD : ∀ (μ a b : Fin n),
      DifferentiableAt ℝ (fun y => CoordinateCurvature.coordDeriv μ (fun z => g z a b) y) x :=
    fun μ a b => CoordinateCurvature.coordDeriv_differentiableAt μ (hgC2 a b)
  have hterm : ∀ l : Fin n,
      DifferentiableAt ℝ (fun y => ginv y k l *
        (CoordinateCurvature.coordDeriv i (fun z => g z j l) y
          + CoordinateCurvature.coordDeriv j (fun z => g z i l) y
          - CoordinateCurvature.coordDeriv l (fun z => g z i j) y)) x := by
    intro l
    exact (hginvD k l).mul (((hpdD i j l).add (hpdD j i l)).sub (hpdD l i j))
  unfold CoordinateCurvature.christoffel
  exact DifferentiableAt.const_mul (DifferentiableAt.fun_sum fun l _ => hterm l) _

/-- Warped spatial metric `dx₀² + (1 + x₀²)(dx₁² + dx₂²)`. -/
noncomputable def warpedSpatialMetric (x : Fin 3 → ℝ) : Tensor2 3 :=
  fun i j => if i = j then (if i = 0 then 1 else 1 + (x 0) ^ 2) else 0

/-- Inverse of `warpedSpatialMetric`. -/
noncomputable def warpedSpatialMetricInv (x : Fin 3 → ℝ) : Tensor2 3 :=
  fun i j => if i = j then (if i = 0 then 1 else (1 + (x 0) ^ 2)⁻¹) else 0

/-- The derived Riemann tensor of the nonconstant warped metric. -/
noncomputable def warpedSpatialRiemann : RiemannTensor 3 := by
  have hsymmAll : ∀ (y : Fin 3 → ℝ) i j,
      warpedSpatialMetric y i j = warpedSpatialMetric y j i := by
    intro y i j
    by_cases hij : i = j
    · subst hij; rfl
    · have hji : j ≠ i := Ne.symm hij
      simp [warpedSpatialMetric, hij, hji]
  have hC2 : ∀ i j, ContDiffAt ℝ 2 (fun y => warpedSpatialMetric y i j) 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      by_cases hi : i = 0
      · have hfun : (fun y : Fin 3 → ℝ => warpedSpatialMetric y i i) =
            fun _ : Fin 3 → ℝ => (1 : ℝ) := by
          funext y
          simp [warpedSpatialMetric, hi]
        rw [hfun]
        exact contDiffAt_const
      · have hfun : (fun y : Fin 3 → ℝ => warpedSpatialMetric y i i) =
            fun y : Fin 3 → ℝ => 1 + (y 0) ^ 2 := by
          funext y
          simp [warpedSpatialMetric, hi]
        rw [hfun]
        fun_prop
    · have hfun : (fun y : Fin 3 → ℝ => warpedSpatialMetric y i j) =
          fun _ : Fin 3 → ℝ => (0 : ℝ) := by
        funext y
        simp [warpedSpatialMetric, hij]
      rw [hfun]
      exact contDiffAt_const
  have hinvD : ∀ i j, DifferentiableAt ℝ (fun y => warpedSpatialMetricInv y i j) 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      by_cases hi : i = 0
      · have hfun : (fun y : Fin 3 → ℝ => warpedSpatialMetricInv y i i) =
            fun _ : Fin 3 → ℝ => (1 : ℝ) := by
          funext y
          simp [warpedSpatialMetricInv, hi]
        rw [hfun]
        exact differentiableAt_const 1
      · have hfun : (fun y : Fin 3 → ℝ => warpedSpatialMetricInv y i i) =
            fun y : Fin 3 → ℝ => (1 + (y 0) ^ 2)⁻¹ := by
          funext y
          simp [warpedSpatialMetricInv, hi]
        rw [hfun]
        fun_prop (disch := positivity)
    · have hfun : (fun y : Fin 3 → ℝ => warpedSpatialMetricInv y i j) =
          fun _ : Fin 3 → ℝ => (0 : ℝ) := by
        funext y
        simp [warpedSpatialMetricInv, hij]
      rw [hfun]
      exact differentiableAt_const 0
  refine spatialRiemannTensorOf warpedSpatialMetric warpedSpatialMetricInv 0
    (Filter.Eventually.of_forall hsymmAll) ?_ hC2 ?_ ?_
  · filter_upwards with y m j
    have hf : 1 + (y 0) ^ 2 ≠ 0 := by nlinarith [sq_nonneg (y 0)]
    fin_cases m <;> fin_cases j <;>
      simp [warpedSpatialMetric, warpedSpatialMetricInv, hf]
  · intro k i j
    exact differentiableAt_christoffel_of_contDiffAt_two hC2 hinvD k i j
  · filter_upwards with y k i j
    exact Bianchi.christoffel_symm warpedSpatialMetric warpedSpatialMetricInv
      (Filter.Eventually.of_forall hsymmAll) k i j

lemma warpedChristoffel_011 (x : Fin 3 → ℝ) :
    CoordinateCurvature.christoffel warpedSpatialMetric warpedSpatialMetricInv x 0 1 1 = -x 0 := by
  have hderiv : CoordinateCurvature.coordDeriv 0 (fun y : Fin 3 → ℝ => 1 + (y 0) ^ 2) x = 2
    * x 0 := by
    apply CoordinateCurvature.coordDeriv_of_hasDerivAt
    have h : (fun s : ℝ => 1 + (Function.update x 0 s 0) ^ 2) =
        fun s : ℝ => 1 + s ^ 2 := by
      funext s
      simp
    rw [h]
    convert (hasDerivAt_const (x 0) (1 : ℝ)).add (hasDerivAt_pow 2 (x 0)) using 1
    ring
  simp only [CoordinateCurvature.christoffel, warpedSpatialMetric, warpedSpatialMetricInv]
  simp [hderiv, CoordinateCurvature.coordDeriv_const]

lemma warpedChristoffel_001 (x : Fin 3 → ℝ) :
    CoordinateCurvature.christoffel warpedSpatialMetric warpedSpatialMetricInv x 0 0 1 = 0 := by
  simp only [CoordinateCurvature.christoffel, warpedSpatialMetric, warpedSpatialMetricInv]
  simp [CoordinateCurvature.coordDeriv_const]

lemma warpedChristoffel_zero (x : Fin 3 → ℝ) (hx : x = 0) :
    ∀ k i j, CoordinateCurvature.christoffel warpedSpatialMetric warpedSpatialMetricInv x k i j
      = 0 := by
  subst hx
  have hderiv : CoordinateCurvature.coordDeriv 0 (fun y : Fin 3 → ℝ => 1 + (y 0) ^ 2) 0 = 0 := by
    apply CoordinateCurvature.coordDeriv_of_hasDerivAt
    have h : (fun s : ℝ => 1 + (Function.update (0 : Fin 3 → ℝ) 0 s 0) ^ 2) =
        fun s : ℝ => 1 + s ^ 2 := by
      funext s
      simp
    rw [h]
    convert (hasDerivAt_const (0 : ℝ) (1 : ℝ)).add (hasDerivAt_pow 2 (0 : ℝ)) using 1
    ring
  have hderiv1 : CoordinateCurvature.coordDeriv 1 (fun y : Fin 3 → ℝ => 1 + (y 0) ^ 2) 0 = 0 := by
    apply CoordinateCurvature.coordDeriv_const_slice 1 (c := 1 + ((0 : Fin 3 → ℝ) 0) ^ 2)
    intro s
    simp
  have hderiv2 : CoordinateCurvature.coordDeriv 2 (fun y : Fin 3 → ℝ => 1 + (y 0) ^ 2) 0 = 0 := by
    apply CoordinateCurvature.coordDeriv_const_slice 2 (c := 1 + ((0 : Fin 3 → ℝ) 0) ^ 2)
    intro s
    simp
  intro k i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [CoordinateCurvature.christoffel, warpedSpatialMetric, warpedSpatialMetricInv,
      hderiv, hderiv1, hderiv2, CoordinateCurvature.coordDeriv_const]

lemma warpedRiemann_0101 :
    CoordinateCurvature.riemann warpedSpatialMetric warpedSpatialMetricInv 0 0 1 0 1 = -1 := by
  have h1 : CoordinateCurvature.coordDeriv 0
      (fun y => CoordinateCurvature.christoffel warpedSpatialMetric warpedSpatialMetricInv y 0 1 1)
        0 = -1 := by
    rw [CoordinateCurvature.coordDeriv_congr 0 0 (fun y => warpedChristoffel_011 y)]
    simp [CoordinateCurvature.coordDeriv]
  have h2 : CoordinateCurvature.coordDeriv 1
      (fun y => CoordinateCurvature.christoffel warpedSpatialMetric warpedSpatialMetricInv y 0 0 1)
        0 = 0 := by
    rw [CoordinateCurvature.coordDeriv_congr 1 0 (fun y => warpedChristoffel_001 y)]
    exact CoordinateCurvature.coordDeriv_const 1 0 0
  have h3 : (∑ l : Fin 3,
      (CoordinateCurvature.christoffel warpedSpatialMetric warpedSpatialMetricInv 0 0 0 l *
        CoordinateCurvature.christoffel warpedSpatialMetric warpedSpatialMetricInv 0 l 1 1 -
      CoordinateCurvature.christoffel warpedSpatialMetric warpedSpatialMetricInv 0 0 1 l *
        CoordinateCurvature.christoffel warpedSpatialMetric warpedSpatialMetricInv 0 l 0 1))
          = 0 := by
    have hz := warpedChristoffel_zero 0 rfl
    simp [hz]
  simp only [CoordinateCurvature.riemann, h1, h2, h3]
  ring

/-- The nonconstant warped metric gives nonzero derived curvature: `R_{0101} = -1`. -/
lemma spatialRiemannTensorOf_warped_nonconstant :
    warpedSpatialRiemann.comp 0 1 0 1 = -1 := by
  rw [warpedSpatialRiemann]
  change (∑ e, warpedSpatialMetric 0 0 e *
    CoordinateCurvature.riemann warpedSpatialMetric warpedSpatialMetricInv 0 e 1 0 1) = -1
  rw [Fin.sum_univ_three]
  norm_num [warpedSpatialMetric, warpedRiemann_0101]

/-- Chart initial data from an arbitrary field of bundled 3-metrics.  The
inverse relation and Christoffel symmetry are derived from `MetricTensor` and
`Bianchi.christoffel_symm`; metric and inverse-metric regularity and the vacuum
proof remain explicit. -/
noncomputable def ChartInitialData.ofChartData
    (X : ChartSpacetime) (M : (Fin 3 → ℝ) → MetricTensor 3)
    (K : (Fin 3 → ℝ) → Tensor2 3) (x : Fin 3 → ℝ)
    (hgC2 : ∀ i j, ContDiffAt ℝ 2 (fun y => (M y).g i j) x)
    (hginvD : ∀ i j, DifferentiableAt ℝ (fun y => (M y).ginv i j) x)
    (Ksymm : IsSymm (K x))
    (vacuum : (InitialData.mk (M x)
      (spatialRiemannTensorOf (fun y => (M y).g) (fun y => (M y).ginv) x
        (metricField_symm M x) (metricField_inv M x) hgC2
        (fun k i j => differentiableAt_christoffel_of_contDiffAt_two hgC2 hginvD k i j)
        (metricField_christoffel_symm M x))
      (K x) Ksymm).IsVacuumData
      (fun k i j => CoordinateCurvature.christoffel (fun y => (M y).g)
        (fun y => (M y).ginv) x k i j)
      (extrinsicDerivativeOf K x)) :
    ChartInitialData X :=
  ChartInitialData.ofFields X (M x) (fun y => (M y).g) (fun y => (M y).ginv) K x
    (metricField_symm M x) (metricField_inv M x) hgC2
    (fun k i j => differentiableAt_christoffel_of_contDiffAt_two hgC2 hginvD k i j)
    (metricField_christoffel_symm M x) Ksymm vacuum

/-- Chart-level regularity of initial data: smooth metric components and smooth
momentum-constraint derivatives.  The ADM tensors themselves are pointwise
matrices, so their regularity is carried by these two fields. -/
structure ChartInitialData.Regular {X : ChartSpacetime} (D : ChartInitialData X) : Prop where
  /-- The chart metric components are smooth. -/
  metric_smooth : X.IsSmooth
  /-- The momentum-constraint derivative is smooth on the slice. -/
  dK_smooth : ∀ (i j k : Fin 3), ContDiff ℝ ∞ fun _ : Fin 3 → ℝ => D.dK i j k

/-- Every bundled chart initial data set satisfies the Hamiltonian constraint. -/
lemma ChartInitialData.ham_zero (D : ChartInitialData X) :
    D.data.hamiltonianConstraint = 0 :=
  D.vacuum.1

/-- Every bundled chart initial data set satisfies the momentum constraint. -/
lemma ChartInitialData.mom_zero (D : ChartInitialData X) (i : Fin 3) :
    D.data.momentumConstraint D.Γ D.dK i = 0 :=
  D.vacuum.2 i

/-- The bundled vacuum predicate is exactly `InitialData.IsVacuumData`. -/
lemma ChartInitialData.isVacuumData (D : ChartInitialData X) :
    D.data.IsVacuumData D.Γ D.dK :=
  D.vacuum

/-- The Hamiltonian and momentum constraint residuals of chart initial data. -/
structure ConstraintResidual where
  /-- The Hamiltonian constraint residual. -/
  ham : ℝ
  /-- The momentum constraint residual. -/
  mom : Fin 3 → ℝ

/-- The constraint residual packaged from chart initial data. -/
noncomputable def ChartInitialData.constraintResidual
    (D : ChartInitialData X) : ConstraintResidual where
  ham := D.data.hamiltonianConstraint
  mom := fun i => D.data.momentumConstraint D.Γ D.dK i

/-- The packaged Hamiltonian residual vanishes. -/
lemma ChartInitialData.constraintResidual_ham (D : ChartInitialData X) :
    D.constraintResidual.ham = 0 := by
  simpa [ChartInitialData.constraintResidual] using D.vacuum.1

/-- Every packaged momentum residual vanishes. -/
lemma ChartInitialData.constraintResidual_mom (D : ChartInitialData X) (i : Fin 3) :
    D.constraintResidual.mom i = 0 := by
  simpa [ChartInitialData.constraintResidual] using D.vacuum.2 i

/-- The whole constraint residual vanishes. -/
lemma ChartInitialData.constraintResidual_eq_zero (D : ChartInitialData X) :
    D.constraintResidual.ham = 0 ∧ ∀ i, D.constraintResidual.mom i = 0 :=
  ⟨D.constraintResidual_ham, D.constraintResidual_mom⟩

/-- Every chart initial data set with a smooth chart metric has regular data. -/
lemma ChartInitialData.regular (D : ChartInitialData X) (hX : X.IsSmooth) :
    D.Regular where
  metric_smooth := hX
  dK_smooth := fun _ _ _ => contDiff_const

/-- The Minkowski chart metric is smooth. -/
lemma minkowskiChart_isSmooth : minkowskiChart.IsSmooth := by
  intro i j
  have h : (fun x : SpacetimeChart => minkowskiChart.coordinateMetric x i j) =
      fun _ => minkowskiMetric4 i j := by
    funext x
    simp [ChartSpacetime.coordinateMetric, minkowskiChart, minkowski]
  rw [h]
  exact contDiff_const

/-- Flat Minkowski initial data on the Minkowski chart. -/
def minkowskiChartInitialData : ChartInitialData minkowskiChart where
  data := flatInitialData
  Γ := 0
  dK := 0
  vacuum := flatInitialData_isVacuum

/-- The induced spatial metric on the Minkowski slice is the metric carried by
the flat chart initial data. -/
lemma minkowskiChartInitialData_metric :
    minkowskiChart.spatialMetric = minkowskiChartInitialData.data.h.g := by
  rw [minkowskiChart_spatialMetric]
  rfl

/-- The flat instance has vanishing Hamiltonian constraint. -/
lemma minkowskiChartInitialData_ham_zero :
    minkowskiChartInitialData.data.hamiltonianConstraint = 0 :=
  flatInitialData_hamiltonianConstraint_zero

/-- The Minkowski chart initial data are regular. -/
lemma minkowskiChartInitialData_regular :
    minkowskiChartInitialData.Regular :=
  ChartInitialData.regular minkowskiChartInitialData minkowskiChart_isSmooth

/-- The Minkowski chart has vanishing constraint residual. -/
lemma minkowskiChartInitialData_constraintResidual_eq_zero :
    minkowskiChartInitialData.constraintResidual.ham = 0 ∧
      ∀ i, minkowskiChartInitialData.constraintResidual.mom i = 0 :=
  minkowskiChartInitialData.constraintResidual_eq_zero

/-- The Minkowski chart data are also obtained from the derived curvature and
momentum constructors: the constant Euclidean metric gives `R3 = flat 3`, and
zero extrinsic curvature gives `dK = 0`. -/
noncomputable def minkowskiChartInitialDataDerived : ChartInitialData minkowskiChart := by
  let h : (Fin 3 → ℝ) → Tensor2 3 := fun _ => euclideanMetric3.g
  let hinv : (Fin 3 → ℝ) → Tensor2 3 := fun _ => euclideanMetric3.ginv
  let K : (Fin 3 → ℝ) → Tensor2 3 := fun _ => 0
  let hgSymm : ∀ᶠ y in 𝓝 (0 : Fin 3 → ℝ), ∀ i j, h y i j = h y j i := by
    filter_upwards with y i j
    simp [h, euclideanMetric3, Matrix.one_apply, eq_comm]
  let hInv : ∀ᶠ y in 𝓝 (0 : Fin 3 → ℝ), ∀ m j,
      ∑ a, hinv y a m * h y a j = if m = j then 1 else 0 := by
    filter_upwards with y m j
    simp [h, hinv, euclideanMetric3, Matrix.one_apply, eq_comm]
  let hgC2 : ∀ i j, ContDiffAt ℝ 2 (fun y => h y i j) 0 := by
    intro i j
    exact contDiffAt_const
  let hΓD : ∀ k i j,
      DifferentiableAt ℝ (fun y => CoordinateCurvature.christoffel h hinv y k i j) 0 := by
    intro k i j
    have hc : (fun y : Fin 3 → ℝ => CoordinateCurvature.christoffel h hinv y k i j)
      = fun _ => 0 := by
      funext y
      exact CoordinateCurvature.christoffel_const h hinv euclideanMetric3.g (fun _ => rfl) y k i j
    rw [hc]
    exact differentiableAt_const 0
  let hΓ : ∀ᶠ y in 𝓝 (0 : Fin 3 → ℝ), ∀ k i j,
      CoordinateCurvature.christoffel h hinv y k i j
        = CoordinateCurvature.christoffel h hinv y k j i := by
    filter_upwards with y k i j
    rw [CoordinateCurvature.christoffel_const h hinv euclideanMetric3.g (fun _ => rfl) y k i j,
      CoordinateCurvature.christoffel_const h hinv euclideanMetric3.g (fun _ => rfl) y k j i]
  have hR3 : spatialRiemannTensorOf h hinv 0 hgSymm hInv hgC2 hΓD hΓ =
      RiemannTensor.flat 3 :=
    spatialRiemannTensorOf_const euclideanMetric3.g h hinv 0 (fun _ => rfl) hgSymm hInv hgC2 hΓD hΓ
  have hdK : extrinsicDerivativeOf K 0 = fun _ => 0 := by
    change extrinsicDerivativeOf (fun _ : Fin 3 → ℝ => (0 : Tensor2 3)) 0 = fun _ => 0
    funext μ
    exact extrinsicDerivativeOf_const 0 0 μ
  have hΓ0 : (fun k i j => CoordinateCurvature.christoffel h hinv 0 k i j) = 0 := by
    funext k i j
    exact CoordinateCurvature.christoffel_const h hinv euclideanMetric3.g (fun _ => rfl) 0 k i j
  refine ChartInitialData.ofFields minkowskiChart euclideanMetric3 h hinv K 0
    hgSymm hInv hgC2 hΓD hΓ
    Matrix.isSymm_zero ?_
  rw [hR3, hdK, hΓ0]
  simpa [h, K, flatInitialData] using flatInitialData_isVacuum

/-! ## D. Manifold-level packaging

This is a global-chart manifold interface: `ManifoldSpacetime` carries a
`SmoothChartSpacetime` and a smoothness certificate, and `ManifoldInitialData`
exposes the chart-derived curvature and momentum data at that level.  The
`ManifoldTransition` layer records isometric overlaps between two such global
charts and checks that the induced spatial metric and initial data agree there.
It does not claim arbitrary multi-chart gluing or a geometric 4D Lorentzian
manifold.
-/

/-- Chart-level ADM data of a spacetime read in a single global chart, together
with the smoothness certificate for that chart.  The `Manifold` in the name refers
to this global chart scope only: the type is not a smooth manifold, and no
gluing of charts is asserted. -/
structure ManifoldSpacetime where
  /-- The underlying smooth chart spacetime. -/
  smoothChart : SmoothChartSpacetime
  /-- The chart metric is smooth. -/
  metric_smooth : smoothChart.toChartSpacetime.IsSmooth

namespace ManifoldSpacetime

/-- The chart spacetime read by the manifold interface. -/
def chartSpacetime (X : ManifoldSpacetime) : ChartSpacetime :=
  X.smoothChart.toChartSpacetime

lemma chartSpacetime_def (X : ManifoldSpacetime) :
    X.chartSpacetime = X.smoothChart.toChartSpacetime := rfl

end ManifoldSpacetime

/-- An isometric transition between the global charts of two manifold
spacetimes.  It preserves the chart coordinate, the metric and the inverse
metric; it is the chart-overlap compatibility certificate for the wrapper. -/
abbrev ManifoldTransition (X Y : ManifoldSpacetime) :=
  ChartSpacetime.Isometry X.chartSpacetime Y.chartSpacetime

namespace ManifoldTransition

/-- The identity transition. -/
def refl (X : ManifoldSpacetime) : ManifoldTransition X X :=
  ChartSpacetime.Isometry.refl X.chartSpacetime

/-- The inverse of a chart transition. -/
def symm {X Y : ManifoldSpacetime} (e : ManifoldTransition X Y) :
    ManifoldTransition Y X :=
  ChartSpacetime.Isometry.symm e

/-- Composition of chart transitions. -/
def trans {X Y Z : ManifoldSpacetime} (e : ManifoldTransition X Y)
    (f : ManifoldTransition Y Z) : ManifoldTransition X Z :=
  ChartSpacetime.Isometry.trans e f

/-- A chart transition preserves the spatial metric induced at the coordinate
origin. -/
lemma spatialMetric_eq {X Y : ManifoldSpacetime} (e : ManifoldTransition X Y) :
    Y.chartSpacetime.spatialMetric = X.chartSpacetime.spatialMetric := by
  let p : X.chartSpacetime.carrier := X.chartSpacetime.chart.symm 0
  have hp : e.toEquiv p = Y.chartSpacetime.chart.symm 0 := by
    apply Y.chartSpacetime.chart.injective
    simp [p, e.chart_comm]
  ext i j
  simp only [ChartSpacetime.spatialMetric, ChartSpacetime.coordinateMetric]
  rw [← hp]
  exact congrFun (congrFun (e.metric_pullback p) (Fin.succ i)) (Fin.succ j)

/-- A chart transition preserves all covariant coordinate metric components. -/
lemma coordinateMetric_eq {X Y : ManifoldSpacetime} (e : ManifoldTransition X Y)
    (x : SpacetimeChart) :
    Y.chartSpacetime.coordinateMetric x = X.chartSpacetime.coordinateMetric x := by
  let p : X.chartSpacetime.carrier := X.chartSpacetime.chart.symm x
  have hp : e.toEquiv p = Y.chartSpacetime.chart.symm x := by
    apply Y.chartSpacetime.chart.injective
    simp [p, e.chart_comm]
  simp only [ChartSpacetime.coordinateMetric]
  rw [← hp]
  exact e.metric_pullback p

/-- A chart transition preserves all inverse coordinate metric components. -/
lemma coordinateInverseMetric_eq {X Y : ManifoldSpacetime}
    (e : ManifoldTransition X Y) (x : SpacetimeChart) :
    Y.chartSpacetime.coordinateInverseMetric x =
      X.chartSpacetime.coordinateInverseMetric x := by
  let p : X.chartSpacetime.carrier := X.chartSpacetime.chart.symm x
  have hp : e.toEquiv p = Y.chartSpacetime.chart.symm x := by
    apply Y.chartSpacetime.chart.injective
    simp [p, e.chart_comm]
  simp only [ChartSpacetime.coordinateInverseMetric]
  rw [← hp]
  exact e.inverse_pullback p

/-- A chart transition preserves the induced spatial metric at every point of
the `t = 0` slice. -/
lemma spatialMetricField_eq {X Y : ManifoldSpacetime} (e : ManifoldTransition X Y)
    (y : Fin 3 → ℝ) :
    Y.chartSpacetime.spatialMetricField y =
      X.chartSpacetime.spatialMetricField y := by
  let p : X.chartSpacetime.carrier :=
    X.chartSpacetime.chart.symm (spacetimeSlice y)
  have hp : e.toEquiv p = Y.chartSpacetime.chart.symm (spacetimeSlice y) := by
    apply Y.chartSpacetime.chart.injective
    simp [p, e.chart_comm]
  ext i j
  simp only [ChartSpacetime.spatialMetricField, ChartSpacetime.coordinateMetric]
  rw [← hp]
  exact congrFun (congrFun (e.metric_pullback p) (Fin.succ i)) (Fin.succ j)

end ManifoldTransition

/-- Chart-level ADM initial data: `ChartInitialData` packaged against a
`ManifoldSpacetime`, so the induced spatial metric, the derived curvature and the
constraint residual are those of the single global chart. -/
structure ManifoldInitialData (X : ManifoldSpacetime) where
  /-- The underlying chart initial data. -/
  data : ChartInitialData X.chartSpacetime

namespace ManifoldInitialData

/-- The ADM metric is the spatial metric induced by the chart metric.  This is
the geometric condition needed for a transition to compare data across charts. -/
def IsInduced {X : ManifoldSpacetime} (D : ManifoldInitialData X) : Prop :=
  D.data.data.h.g = X.chartSpacetime.spatialMetric

/-- Induced manifold initial data agree under a chart transition when their
derived spatial curvature, extrinsic curvature and momentum derivative agree.
The metric agreement is derived from the transition and `IsInduced`. -/
structure IsCompatible {X Y : ManifoldSpacetime} (e : ManifoldTransition X Y)
    (D : ManifoldInitialData X) (E : ManifoldInitialData Y) : Prop where
  /-- The first data set is induced by its chart metric. -/
  left_induced : D.IsInduced
  /-- The second data set is induced by its chart metric. -/
  right_induced : E.IsInduced
  /-- The derived spatial Riemann tensors agree. -/
  curvature_eq : D.data.data.R3 = E.data.data.R3
  /-- The extrinsic curvatures agree. -/
  extrinsic_eq : D.data.data.K = E.data.data.K
  /-- The momentum-constraint derivatives agree. -/
  derivative_eq : D.data.dK = E.data.dK

/-- Compatible data have the same induced ADM metric components. -/
lemma IsCompatible.metric_eq {X Y : ManifoldSpacetime} {e : ManifoldTransition X Y}
    {D : ManifoldInitialData X} {E : ManifoldInitialData Y}
    (h : IsCompatible e D E) :
    D.data.data.h.g = E.data.data.h.g := by
  calc
    D.data.data.h.g = X.chartSpacetime.spatialMetric := h.left_induced
    _ = Y.chartSpacetime.spatialMetric := (e.spatialMetric_eq).symm
    _ = E.data.data.h.g := h.right_induced.symm

/-- Transition compatibility is reflexive on induced data. -/
lemma IsCompatible.refl {X : ManifoldSpacetime} (D : ManifoldInitialData X)
    (hD : D.IsInduced) :
    IsCompatible (ManifoldTransition.refl X) D D where
  left_induced := hD
  right_induced := hD
  curvature_eq := rfl
  extrinsic_eq := rfl
  derivative_eq := rfl

/-- Transition compatibility is symmetric. -/
lemma IsCompatible.symm {X Y : ManifoldSpacetime} {e : ManifoldTransition X Y}
    {D : ManifoldInitialData X} {E : ManifoldInitialData Y}
    (h : IsCompatible e D E) :
    IsCompatible (ManifoldTransition.symm e) E D where
  left_induced := h.right_induced
  right_induced := h.left_induced
  curvature_eq := h.curvature_eq.symm
  extrinsic_eq := h.extrinsic_eq.symm
  derivative_eq := h.derivative_eq.symm

/-- Transition compatibility is transitive. -/
lemma IsCompatible.trans {X Y Z : ManifoldSpacetime}
    {e : ManifoldTransition X Y} {f : ManifoldTransition Y Z}
    {D : ManifoldInitialData X} {E : ManifoldInitialData Y}
    {F : ManifoldInitialData Z}
    (hDE : IsCompatible e D E) (hEF : IsCompatible f E F) :
    IsCompatible (ManifoldTransition.trans e f) D F where
  left_induced := hDE.left_induced
  right_induced := hEF.right_induced
  curvature_eq := hDE.curvature_eq.trans hEF.curvature_eq
  extrinsic_eq := hDE.extrinsic_eq.trans hEF.extrinsic_eq
  derivative_eq := hDE.derivative_eq.trans hEF.derivative_eq

/-- Construct manifold-level data whose `R3` and `dK` are derived from an
arbitrary field of bundled spatial metrics. -/
noncomputable def ofChartData
    (X : ManifoldSpacetime) (M : (Fin 3 → ℝ) → MetricTensor 3)
    (K : (Fin 3 → ℝ) → Tensor2 3) (x : Fin 3 → ℝ)
    (hgC2 : ∀ i j, ContDiffAt ℝ 2 (fun y => (M y).g i j) x)
    (hginvD : ∀ i j, DifferentiableAt ℝ (fun y => (M y).ginv i j) x)
    (Ksymm : IsSymm (K x))
    (vacuum : (InitialData.mk (M x)
      (spatialRiemannTensorOf (fun y => (M y).g) (fun y => (M y).ginv) x
        (metricField_symm M x) (metricField_inv M x) hgC2
        (fun k i j => differentiableAt_christoffel_of_contDiffAt_two hgC2 hginvD k i j)
        (metricField_christoffel_symm M x))
      (K x) Ksymm).IsVacuumData
      (fun k i j => CoordinateCurvature.christoffel (fun y => (M y).g)
        (fun y => (M y).ginv) x k i j)
      (extrinsicDerivativeOf K x)) :
    ManifoldInitialData X :=
  ⟨ChartInitialData.ofChartData X.chartSpacetime M K x hgC2 hginvD Ksymm vacuum⟩

/-- Manifold-level data inherit chart regularity from the smoothness
certificate. -/
lemma regular {X : ManifoldSpacetime} (D : ManifoldInitialData X) :
    D.data.Regular :=
  ChartInitialData.regular D.data X.metric_smooth

/-- Manifold-level data have vanishing Hamiltonian residual. -/
lemma ham_zero {X : ManifoldSpacetime} (D : ManifoldInitialData X) :
    D.data.data.hamiltonianConstraint = 0 :=
  D.data.ham_zero

/-- Manifold-level data have vanishing momentum residual. -/
lemma mom_zero {X : ManifoldSpacetime} (D : ManifoldInitialData X) (i : Fin 3) :
    D.data.data.momentumConstraint D.data.Γ D.data.dK i = 0 :=
  D.data.mom_zero i

/-- Manifold-level data satisfy the vacuum constraints. -/
lemma isVacuumData {X : ManifoldSpacetime} (D : ManifoldInitialData X) :
    D.data.data.IsVacuumData D.data.Γ D.data.dK :=
  D.data.isVacuumData

/-- Manifold-level data have zero constraint residual. -/
lemma constraintResidual_eq_zero {X : ManifoldSpacetime} (D : ManifoldInitialData X) :
    D.data.constraintResidual.ham = 0 ∧
      ∀ i, D.data.constraintResidual.mom i = 0 :=
  D.data.constraintResidual_eq_zero

end ManifoldInitialData

/-- Minkowski as a global-chart manifold interface. -/
def minkowskiManifold : ManifoldSpacetime where
  smoothChart := minkowskiSmoothChart
  metric_smooth := minkowskiChart_isSmooth

/-- The Minkowski manifold-level initial data, using the derived chart data. -/
noncomputable def minkowskiManifoldInitialData : ManifoldInitialData minkowskiManifold :=
  ⟨minkowskiChartInitialDataDerived⟩

/-- The Minkowski manifold data are induced by the Minkowski chart metric. -/
lemma minkowskiManifoldInitialData_isInduced :
    ManifoldInitialData.IsInduced minkowskiManifoldInitialData := by
  rw [ManifoldInitialData.IsInduced]
  change euclideanMetric3.g = minkowskiChart.spatialMetric
  exact minkowskiChart_spatialMetric.symm

/-- The Minkowski manifold data are compatible with themselves under the
identity chart transition. -/
lemma minkowskiManifoldInitialData_isCompatible :
    ManifoldInitialData.IsCompatible
      (ManifoldTransition.refl minkowskiManifold)
      minkowskiManifoldInitialData minkowskiManifoldInitialData :=
  ManifoldInitialData.IsCompatible.refl minkowskiManifoldInitialData
    minkowskiManifoldInitialData_isInduced

end GeneralRelativity
