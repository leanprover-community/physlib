/-
Copyright (c) 2026 Alex Vergara Gil.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/

module

public import PhyslibAlpha.Relativity.General.InitialData.ChartInitialData
public import PhyslibAlpha.Relativity.General.InitialData.CovariantDerivTensor2
public import PhyslibAlpha.Relativity.General.InitialData.SobolevInitialData

/-!

# Schwarzschild as a manifold-level initial-data instance

## i. Overview

This module packages an exterior Schwarzschild chart as a `ManifoldSpacetime`
and constructs the time-symmetric Schwarzschild initial data as a
`ManifoldInitialData` instance.

The chart is a genuine exterior patch.  The radial coordinate is
`r = 2M + exp x₁`, so `r > 2M` and the Schwarzschild lapse is positive, and the
angular coordinate is `θ = π/2 + arctan x₂`, so `sin θ > 0`.  The chart
therefore covers a regular region of the exterior Schwarzschild spacetime
without horizon or polar-axis singularities.  It is not a claim that the
standard Schwarzschild coordinates extend regularly across the horizon.

The spatial data are the curved time-symmetric slice with
`K = 0` and `³R = 0`, already proved in `SobolevInitialData`.  The construction
uses that slice's derived curvature and checks the vacuum constraints; it does
not claim a global development.

## ii. Key results

- `schwarzschildExteriorChart` : the smooth exterior Schwarzschild chart.
- `schwarzschildManifold` : its `ManifoldSpacetime` packaging.
- `schwarzschildManifoldInitialData` : the manifold-level Schwarzschild
  initial-data instance.
- `manifoldInitialData_isInduced` : the instance is induced by the chart
  metric.
- `manifoldInitialData_isCompatible` : the instance is compatible with itself
  under the identity chart transition.
- `exteriorPartialDomain`, `exteriorPartialDomain_isOpen` : the Schwarzschild
  exterior overlap set `r > 2M ∧ sin θ ≠ 0` and its openness.
- `exteriorPartialChart` : the exterior Schwarzschild metric as a smooth
  `PartialChartSpacetime`, the source chart of the EF overlap transition.

## iii. Table of contents

- A. The Schwarzschild chart as a chart spacetime

## iv. References

* R. M. Wald, *General Relativity*, University of Chicago Press, 1984, Ch. 6.
  [ref: wald_1984_general_relativity, Ch. 6]
-/
@[expose] public section

/-! ## A. The Schwarzschild chart as a chart spacetime -/

namespace GeneralRelativity

open Filter Topology
open scoped ContDiff

namespace Schwarzschild

/-- The regular exterior coordinate map used for the Schwarzschild manifold
chart: `r = 2M + exp x₁` and `θ = π/2 + arctan x₂`. -/
noncomputable def exteriorPoint (M : ℝ) (x : SpacetimeChart) : SpacetimeChart :=
  ![x 0, 2 * M + Real.exp (x 1), Real.pi / 2 + Real.arctan (x 2), x 3]

lemma exteriorPoint_radial_pos {M : ℝ} (hM : 0 < M) (x : SpacetimeChart) :
    0 < exteriorPoint M x 1 := by
  have he : 0 < Real.exp (x 1) := Real.exp_pos _
  simp [exteriorPoint]
  nlinarith

lemma exteriorPoint_lapse_pos {M : ℝ} (hM : 0 < M) (x : SpacetimeChart) :
    0 < (schwarzschildSpacetime M).metricFn (exteriorPoint M x 1) := by
  have hr : 0 < exteriorPoint M x 1 := exteriorPoint_radial_pos hM x
  have hlt : 2 * M < exteriorPoint M x 1 := by
    have he : 0 < Real.exp (x 1) := Real.exp_pos _
    simp [exteriorPoint]
    nlinarith
  have hdiv : 2 * M / exteriorPoint M x 1 < 1 :=
    (div_lt_one hr).2 hlt
  simp only [Schwarzschild.SchwarzschildSpacetime.metricFn]
  linarith

lemma exteriorPoint_sin_pos (x : SpacetimeChart) :
    0 < Real.sin (exteriorPoint M x 2) := by
  have h : exteriorPoint M x 2 = Real.arctan (x 2) + Real.pi / 2 := by
    simp [exteriorPoint]
    ring
  rw [h, Real.sin_add_pi_div_two]
  exact Real.cos_arctan_pos (x 2)

lemma contDiff_exteriorRadial (M : ℝ) :
    ContDiff ℝ ∞ fun x : SpacetimeChart => 2 * M + Real.exp (x 1) := by
  fun_prop

lemma contDiff_exteriorLapse (M : ℝ) (hM : 0 < M) :
    ContDiff ℝ ∞ fun x : SpacetimeChart =>
      (schwarzschildSpacetime M).metricFn (2 * M + Real.exp (x 1)) := by
  simp only [Schwarzschild.SchwarzschildSpacetime.metricFn]
  refine (contDiff_const.sub (contDiff_const.div (contDiff_exteriorRadial M) ?_))
  intro x
  exact ne_of_gt (by
    have he : 0 < Real.exp (x 1) := Real.exp_pos _
    nlinarith)

lemma contDiff_exteriorLapseInv (M : ℝ) (hM : 0 < M) :
    ContDiff ℝ ∞ fun x : SpacetimeChart =>
      ((schwarzschildSpacetime M).metricFn (2 * M + Real.exp (x 1)))⁻¹ := by
  exact (contDiff_exteriorLapse M hM).inv
    (fun x => ne_of_gt (exteriorPoint_lapse_pos hM x))

lemma contDiff_exteriorCosAtan :
    ContDiff ℝ ∞ fun x : SpacetimeChart => Real.cos (Real.arctan (x 2)) := by
  exact Real.contDiff_cos.comp
    (Real.contDiff_arctan.comp (contDiff_apply (𝕜 := ℝ) (n := ∞) (F' := fun _ : Fin 4 => ℝ) 2))

lemma contDiff_exteriorSin :
    ContDiff ℝ ∞ fun x : SpacetimeChart =>
      Real.sin (Real.pi / 2 + Real.arctan (x 2)) := by
  have h : (fun x : SpacetimeChart =>
      Real.sin (Real.pi / 2 + Real.arctan (x 2))) =
      fun x : SpacetimeChart => Real.cos (Real.arctan (x 2)) := by
    funext x
    rw [add_comm, Real.sin_add_pi_div_two]
  rw [h]
  exact contDiff_exteriorCosAtan

/-- The Schwarzschild metric on the regular exterior chart. -/
noncomputable def exteriorMetric (M : ℝ) (hM : 0 < M) (x : SpacetimeChart) :
    MetricTensor 4 :=
  (schwarzschildSpacetime M).toStaticSpherical.metricTensor
    (exteriorPoint M x)
    (ne_of_gt (exteriorPoint_radial_pos hM x))
    (ne_of_gt (exteriorPoint_lapse_pos hM x))
    (ne_of_gt (exteriorPoint_sin_pos (M := M) x))

/-- The exterior Schwarzschild chart as a `ChartSpacetime`. -/
noncomputable def exteriorChart (M : ℝ) (hM : 0 < M) : ChartSpacetime where
  carrier := SpacetimeChart
  topology := inferInstance
  chart := Equiv.refl SpacetimeChart
  metric := exteriorMetric M hM

lemma exteriorChart_coordinateMetric (M : ℝ) (hM : 0 < M) (x : SpacetimeChart) :
    (exteriorChart M hM).coordinateMetric x =
      (schwarzschildSpacetime M).toStaticSpherical.metric
        (exteriorPoint M x) := by
  rfl

/-- The exterior Schwarzschild metric components are smooth on the chart. -/
lemma exteriorChart_isSmooth (M : ℝ) (hM : 0 < M) :
    (exteriorChart M hM).IsSmooth := by
  intro i j
  rw [show (fun x : SpacetimeChart =>
      (exteriorChart M hM).coordinateMetric x i j) =
      fun x : SpacetimeChart =>
        (schwarzschildSpacetime M).toStaticSpherical.metric
          (exteriorPoint M x) i j from by
    funext x
    exact congrFun (congrFun (exteriorChart_coordinateMetric M hM x) i) j]
  fin_cases i <;> fin_cases j <;>
    simp [StaticSpherical.StaticSphericalMetric.metric, exteriorPoint]
  all_goals
    first
    | exact contDiff_const
    | exact (contDiff_exteriorLapse M hM).neg
    | exact contDiff_exteriorLapseInv M hM
    | exact (contDiff_exteriorRadial M).pow 2
    | exact ((contDiff_exteriorRadial M).pow 2).mul (contDiff_exteriorSin.pow 2)

/-- The exterior Schwarzschild domain in standard coordinates: `r > 2M` and
off the polar axis. -/
def exteriorPartialDomain (M : ℝ) : Set SpacetimeChart :=
  {x | 2 * M < x 1 ∧ Real.sin (x 2) ≠ 0}

/-- The exterior Schwarzschild domain is open. -/
lemma exteriorPartialDomain_isOpen (M : ℝ) : IsOpen (exteriorPartialDomain M) := by
  have hcont : Continuous (fun x : SpacetimeChart => x 1) := continuous_apply 1
  have h1 : IsOpen {x : SpacetimeChart | 2 * M < x 1} :=
    hcont.isOpen_preimage (Set.Ioi (2 * M)) isOpen_Ioi
  have hsin_cont : Continuous (fun x : SpacetimeChart => Real.sin (x 2)) :=
    Real.continuous_sin.comp (continuous_apply 2)
  have h2 : IsOpen {x : SpacetimeChart | Real.sin (x 2) ≠ 0} :=
    hsin_cont.isOpen_preimage ({0}ᶜ) isOpen_compl_singleton
  rw [exteriorPartialDomain, Set.ofPred_and]
  exact h1.inter h2

/-- The exterior Schwarzschild metric as a partial chart on `r > 2M`. -/
noncomputable def exteriorPartialChart (M : ℝ) (hM : 0 < M) : PartialChartSpacetime where
  domain := exteriorPartialDomain M
  domain_open := exteriorPartialDomain_isOpen M
  metric := fun x hx => by
    obtain ⟨hr, hsin⟩ := hx
    have hx1 : (0 : ℝ) < x 1 := by linarith
    exact (schwarzschildSpacetime M).toStaticSpherical.metricTensor x
      hx1.ne'
      (by
        have hfrm : (schwarzschildSpacetime M).toStaticSpherical.metricFn (x 1) =
            (x 1 - 2 * M) / x 1 := by
          simp only [schwarzschildSpacetime, Schwarzschild.SchwarzschildSpacetime.metricFn,
            Schwarzschild.SchwarzschildSpacetime.toStaticSpherical]
          field_simp [hx1.ne']
        rw [hfrm]
        exact div_ne_zero (by linarith) hx1.ne')
      hsin

/-- The exterior Schwarzschild chart with its smooth-chart homeomorphism. -/
noncomputable def exteriorSmoothChart (M : ℝ) (hM : 0 < M) :
    SmoothChartSpacetime where
  toChartSpacetime := exteriorChart M hM
  chartHomeo := Homeomorph.refl SpacetimeChart
  chart_eq := fun _ => rfl

/-- Schwarzschild as a manifold-level spacetime, on the regular exterior chart. -/
noncomputable def manifold (M : ℝ) (hM : 0 < M) : ManifoldSpacetime where
  smoothChart := exteriorSmoothChart M hM
  metric_smooth := exteriorChart_isSmooth M hM

/-- A regular point on the exterior `t = 0` slice: `r = 2M + 1`, `θ = π/2`. -/
noncomputable def exteriorSpatialPoint (M : ℝ) : SpaceChart :=
  ![2 * M + 1, Real.pi / 2, 0]

lemma exteriorSpatialPoint_radial_pos {M : ℝ} (hM : 0 < M) :
    0 < exteriorSpatialPoint M 0 := by
  simp [exteriorSpatialPoint]
  linarith

lemma exteriorSpatialPoint_lapse_pos {M : ℝ} (hM : 0 < M) :
    0 < (sdsSpacetime M 0).metricFn (exteriorSpatialPoint M 0) := by
  rw [SchwarzschildDeSitter.SchwarzschildDeSitterSpacetime.metricFn_zero_lambda]
  have hr : 0 < exteriorSpatialPoint M 0 := exteriorSpatialPoint_radial_pos hM
  have hlt : 2 * M < exteriorSpatialPoint M 0 := by
    simp [exteriorSpatialPoint]
  have hdiv : 2 * M / exteriorSpatialPoint M 0 < 1 := (div_lt_one hr).2 hlt
  simp only [Schwarzschild.SchwarzschildSpacetime.metricFn]
  linarith

lemma exteriorSpatialPoint_sin_pos {M : ℝ} :
    0 < Real.sin (exteriorSpatialPoint M 1) := by
  simp [exteriorSpatialPoint]

/-- The Schwarzschild spatial metric at a regular point as a bundled
`MetricTensor 3`. -/
noncomputable def spatialMetricTensor (M : ℝ) (x : SpaceChart)
    (hr : x 0 ≠ 0) (hf : (sdsSpacetime M 0).metricFn (x 0) ≠ 0)
    (hsin : Real.sin (x 1) ≠ 0) : MetricTensor 3 where
  g := sdsSpatialMetric M 0 x
  ginv := sdsSpatialMetricInv M 0 x
  symm := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sdsSpatialMetric, Matrix.transpose_apply, eq_comm]
  inv_left := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sdsSpatialMetric, sdsSpatialMetricInv, Matrix.mul_apply] <;>
      field_simp [hr, hf, hsin]
  inv_right := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sdsSpatialMetric, sdsSpatialMetricInv, Matrix.mul_apply] <;>
      field_simp [hr, hf, hsin]

/-- The scalar curvature of the derived Riemann tensor agrees with the pipeline
scalar curvature when the metric and inverse are those at the point. -/
lemma ricciScalar_spatialRiemannTensorOf
    (M : MetricTensor 3) (h hinv : SpaceChart → Tensor2 3) (x : SpaceChart)
    (hMinv : hinv x = M.ginv)
    (hgSymm : ∀ᶠ y in 𝓝 x, ∀ i j, h y i j = h y j i)
    (hInv : ∀ᶠ y in 𝓝 x, ∀ m j, ∑ a, hinv y a m * h y a j = if m = j then 1 else 0)
    (hgC2 : ∀ i j, ContDiffAt ℝ 2 (fun y => h y i j) x)
    (hΓD : ∀ k i j, DifferentiableAt ℝ (fun y => CoordinateCurvature.christoffel h hinv y k i j) x)
    (hΓ : ∀ᶠ y in 𝓝 x, ∀ k i j,
      CoordinateCurvature.christoffel h hinv y k i j
        = CoordinateCurvature.christoffel h hinv y k j i) :
    ricciScalar M (spatialRiemannTensorOf h hinv x hgSymm hInv hgC2 hΓD hΓ) =
      CoordinateCurvature.ricciScalar h hinv x := by
  simp only [ricciScalar, ricci, spatialRiemannTensorOf, CoordinateCurvature.ricciScalar,
    CoordinateCurvature.ricciTensor]
  rw [← hMinv]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have hrel := hInv.self_of_nhds
  calc
    (∑ k, ∑ l, hinv x k l * ∑ e, h x k e * CoordinateCurvature.riemann h hinv x e i l j)
        = ∑ l, ∑ k, hinv x k l * ∑ e, h x k e * CoordinateCurvature.riemann h hinv x e i l j := by
          rw [Finset.sum_comm]
    _ = ∑ l, ∑ e, (∑ k, hinv x k l * h x k e) * CoordinateCurvature.riemann h hinv x e i l j := by
          apply Finset.sum_congr rfl
          intro l _
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro e _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k _
          ring
    _ = ∑ l, CoordinateCurvature.riemann h hinv x l i l j := by
          apply Finset.sum_congr rfl
          intro l _
          rw [Finset.sum_eq_single l]
          · simp [hrel]
          · intro e _ hne
            simp [hrel, hne.symm]
          · intro hnot
            exact absurd (Finset.mem_univ l) hnot
    _ = ∑ ρ, CoordinateCurvature.riemann h hinv x ρ i ρ j := rfl

lemma sdsSpatialMetric_isSymm (M Λ : ℝ) (x : SpaceChart) :
    IsSymm (sdsSpatialMetric M Λ x) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sdsSpatialMetric, Matrix.transpose_apply, eq_comm]

lemma contDiffAt_sdsLapse_zero (M : ℝ) {r : ℝ} (hr : r ≠ 0) :
    ContDiffAt ℝ 2 (fun s : ℝ =>
      (sdsSpacetime M 0).metricFn s) r := by
  have h : (fun s : ℝ => (sdsSpacetime M 0).metricFn s) =
      fun s : ℝ => 1 - 2 * M / s := by
    funext s
    rw [SchwarzschildDeSitter.SchwarzschildDeSitterSpacetime.metricFn_zero_lambda]
    simp [Schwarzschild.SchwarzschildSpacetime.metricFn]
  rw [h]
  fun_prop (disch := exact hr)

lemma contDiffAt_sdsLapse_zero_comp (M : ℝ) (x : SpaceChart) (hr : x 0 ≠ 0) :
    ContDiffAt ℝ 2 (fun y : SpaceChart =>
      (sdsSpacetime M 0).metricFn (y 0)) x := by
  have h : (fun y : SpaceChart => (sdsSpacetime M 0).metricFn (y 0)) =
      fun y : SpaceChart => 1 - 2 * M / (y 0) := by
    funext y
    rw [SchwarzschildDeSitter.SchwarzschildDeSitterSpacetime.metricFn_zero_lambda]
    simp [Schwarzschild.SchwarzschildSpacetime.metricFn]
  rw [h]
  fun_prop (disch := exact hr)

lemma contDiffAt_sdsSpatialMetric (M : ℝ) (x : SpaceChart)
    (hr : x 0 ≠ 0) (hf : (sdsSpacetime M 0).metricFn (x 0) ≠ 0)
    (_hsin : Real.sin (x 1) ≠ 0) :
    ∀ i j, ContDiffAt ℝ 2 (fun y : SpaceChart => sdsSpatialMetric M 0 y i j) x := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sdsSpatialMetric]
  all_goals
    first
    | exact ContDiffAt.inv (contDiffAt_sdsLapse_zero_comp M x hr) hf
    | fun_prop

lemma contDiffAt_sdsSpatialMetricInv (M : ℝ) (x : SpaceChart)
    (hr : x 0 ≠ 0) (_hf : (sdsSpacetime M 0).metricFn (x 0) ≠ 0)
    (hsin : Real.sin (x 1) ≠ 0) :
    ∀ i j, ContDiffAt ℝ 2 (fun y : SpaceChart => sdsSpatialMetricInv M 0 y i j) x := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sdsSpatialMetricInv]
  all_goals
    first
    | exact contDiffAt_sdsLapse_zero_comp M x hr
    | exact ContDiffAt.inv (by fun_prop) (pow_ne_zero 2 hr)
    | fun_prop (disch := first | exact pow_ne_zero 2 hr |
        exact pow_ne_zero 2 hsin |
        exact mul_ne_zero (pow_ne_zero 2 hr) (pow_ne_zero 2 hsin))

/-- The bundled Schwarzschild spatial metric at the exterior slice point. -/
noncomputable def exteriorSpatialMetricTensor (M : ℝ) (hM : 0 < M) : MetricTensor 3 :=
  spatialMetricTensor M (exteriorSpatialPoint M)
    (ne_of_gt (exteriorSpatialPoint_radial_pos hM))
    (ne_of_gt (exteriorSpatialPoint_lapse_pos hM))
    (ne_of_gt (exteriorSpatialPoint_sin_pos (M := M)))

/-- The time-symmetric Schwarzschild chart initial data at the regular exterior
slice point. -/
noncomputable def chartInitialData (M : ℝ) (hM : 0 < M) :
    ChartInitialData (exteriorChart M hM) := by
  let x : SpaceChart := exteriorSpatialPoint M
  let h : SpaceChart → Tensor2 3 := fun y => sdsSpatialMetric M 0 y
  let hinv : SpaceChart → Tensor2 3 := fun y => sdsSpatialMetricInv M 0 y
  let K : SpaceChart → Tensor2 3 := fun _ => 0
  have hr : x 0 ≠ 0 := ne_of_gt (exteriorSpatialPoint_radial_pos hM)
  have hf : (sdsSpacetime M 0).metricFn (x 0) ≠ 0 :=
    ne_of_gt (exteriorSpatialPoint_lapse_pos hM)
  have hsin : Real.sin (x 1) ≠ 0 :=
    ne_of_gt (exteriorSpatialPoint_sin_pos (M := M))
  have hsymm : ∀ᶠ y in 𝓝 x, ∀ i j, h y i j = h y j i := by
    filter_upwards with y i j
    exact ((sdsSpatialMetric_isSymm M 0 y).apply i j).symm
  have hev : ∀ᶠ y in 𝓝 x,
      y 0 ≠ 0 ∧ (sdsSpacetime M 0).metricFn (y 0) ≠ 0 ∧
        Real.sin (y 1) ≠ 0 := by
    have h0 : ∀ᶠ y : SpaceChart in 𝓝 x, y 0 ≠ 0 :=
      (continuousAt_apply 0 x).eventually_ne hr
    have h1 : ∀ᶠ y : SpaceChart in 𝓝 x,
        (sdsSpacetime M 0).metricFn (y 0) ≠ 0 :=
      (continuousAt_apply 0 x).eventually
        ((contDiffAt_sdsLapse_zero M hr).continuousAt.eventually_ne hf)
    have h2 : ∀ᶠ y : SpaceChart in 𝓝 x, Real.sin (y 1) ≠ 0 :=
      (continuousAt_apply 1 x).eventually
        (Real.continuous_sin.continuousAt.eventually_ne hsin)
    exact h0.and (h1.and h2)
  have hInv : ∀ᶠ y in 𝓝 x, ∀ m j,
      ∑ a, hinv y a m * h y a j = if m = j then 1 else 0 := by
    filter_upwards [hev] with y hy m j
    fin_cases m <;> fin_cases j <;>
      simp [h, hinv, sdsSpatialMetric, sdsSpatialMetricInv] <;>
      field_simp [hy.1, hy.2.1, hy.2.2]
  have hC2 : ∀ i j, ContDiffAt ℝ 2 (fun y : SpaceChart => h y i j) x :=
    contDiffAt_sdsSpatialMetric M x hr hf hsin
  have hginvD : ∀ i j, DifferentiableAt ℝ (fun y : SpaceChart => hinv y i j) x :=
    fun i j => (contDiffAt_sdsSpatialMetricInv M x hr hf hsin i j).differentiableAt (by norm_num)
  have hΓD : ∀ k i j,
      DifferentiableAt ℝ (fun y => CoordinateCurvature.christoffel h hinv y k i j) x :=
    differentiableAt_christoffel_of_contDiffAt_two hC2 hginvD
  have hΓ : ∀ᶠ y in 𝓝 x, ∀ k i j,
      CoordinateCurvature.christoffel h hinv y k i j =
        CoordinateCurvature.christoffel h hinv y k j i := by
    filter_upwards with y k i j
    exact Bianchi.christoffel_symm h hinv
      (Filter.Eventually.of_forall fun z i j =>
        ((sdsSpatialMetric_isSymm M 0 z).apply i j).symm) k i j
  have hKsymm : IsSymm (K x) := Matrix.isSymm_zero
  let R3 := spatialRiemannTensorOf h hinv x hsymm hInv hC2 hΓD hΓ
  have hscalar : ricciScalar (exteriorSpatialMetricTensor M hM) R3 = 0 := by
    rw [show R3 = spatialRiemannTensorOf h hinv x hsymm hInv hC2 hΓD hΓ from rfl]
    rw [ricciScalar_spatialRiemannTensorOf (exteriorSpatialMetricTensor M hM)
      h hinv x (by rfl) hsymm hInv hC2 hΓD hΓ]
    have hfS : (schwarzschildSpacetime M).metricFn (x 0) ≠ 0 := by
      intro h
      apply hf
      rwa [SchwarzschildDeSitter.SchwarzschildDeSitterSpacetime.metricFn_zero_lambda]
    have hham := GeneralRelativity.schwarzschild_spatial_hamiltonian_zero M x hr hfS hsin
    change CoordinateCurvature.ricciScalar (sdsSpatialMetric M 0)
      (sdsSpatialMetricInv M 0) x = 0
    simpa [spatialScalarCurvOf, hamiltonianConstraintOf] using hham
  refine ChartInitialData.ofFields (exteriorChart M hM) (exteriorSpatialMetricTensor M hM)
    h hinv K x hsymm hInv hC2 hΓD hΓ hKsymm ?_
  constructor
  · rw [InitialData.hamiltonianConstraint_eq_ricciScalar_of_K_zero _ (by rfl)]
    exact hscalar
  · intro i
    apply InitialData.momentumConstraint_zero_of_covariantDeriv_zero
    intro μ i j
    simp [InitialData.covariantDerivTensor2, K, extrinsicDerivativeOf_const]

/-- The Schwarzschild manifold-level initial-data instance. -/
noncomputable def manifoldInitialData (M : ℝ) (hM : 0 < M) :
    ManifoldInitialData (manifold M hM) :=
  ⟨chartInitialData M hM⟩

/-- The Schwarzschild instance is induced by the exterior chart metric. -/
lemma manifoldInitialData_isInduced (M : ℝ) (hM : 0 < M) :
    ManifoldInitialData.IsInduced (manifoldInitialData M hM) := by
  change (sdsSpatialMetric M 0 (exteriorSpatialPoint M)) =
    (exteriorChart M hM).spatialMetric
  ext i j
  rw [ChartSpacetime.spatialMetric, exteriorChart_coordinateMetric M hM 0]
  fin_cases i <;> fin_cases j <;>
    simp [StaticSpherical.StaticSphericalMetric.metric, exteriorPoint,
      exteriorSpatialPoint, sdsSpatialMetric,
      Schwarzschild.SchwarzschildSpacetime.toStaticSpherical,
      Schwarzschild.SchwarzschildSpacetime.metricFn,
      SchwarzschildDeSitter.SchwarzschildDeSitterSpacetime.metricFn]

/-- The Schwarzschild instance is compatible with itself under the identity
chart transition. -/
lemma manifoldInitialData_isCompatible (M : ℝ) (hM : 0 < M) :
    ManifoldInitialData.IsCompatible
      (ManifoldTransition.refl (manifold M hM))
      (manifoldInitialData M hM) (manifoldInitialData M hM) :=
  ManifoldInitialData.IsCompatible.refl (manifoldInitialData M hM)
    (manifoldInitialData_isInduced M hM)

end Schwarzschild

end GeneralRelativity
