/-
Copyright (c) 2026 Alex Vergara Gil.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.General.BianchiContracted
public import PhyslibAlpha.Relativity.General.ManifoldInterface

/-!
# The Bianchi identities on a chart spacetime

The general second and contracted Bianchi identities of `General/Bianchi.lean`,
instantiated on any `ChartSpacetime`.

## i. Overview

`General/Bianchi.lean` proves the second Bianchi identity and the contracted
Bianchi identity for any smooth coordinate metric `(g, ginv)` in arbitrary
dimension.  A `ChartSpacetime` carries exactly such a coordinate metric and its
inverse, so the two identities hold there as soon as the metric and its
Christoffel symbols are `C²` at the point; in particular the Einstein tensor is
divergence free, `∇^μ G_{μl} = 0`.  The symmetry and inverse-identity hypotheses
of the general statements are read off the `MetricTensor` fields of the chart.

## ii. Key results

- `chartSpacetime_second_bianchi` : the second Bianchi identity for the
  Riemann tensor of any `ChartSpacetime` with `C²` Christoffel symbols.
- `chartSpacetime_covDiv_einstein_eq_zero` : `∇^μ G_{μl} = 0` for any
  `ChartSpacetime` with `C²` metric and Christoffel symbols.

## iii. Table of contents

- A. The identities on a chart spacetime

## iv. References

* S. M. Carroll, *Lecture Notes on General Relativity*, arXiv:gr-qc/9712019,
  §3.2, pp. 72–73. [ref: Carroll1997]

-/

@[expose] public section

namespace GeneralRelativity

namespace Bianchi

open CoordinateCurvature Topology Filter

/-! ## A. The identities on a chart spacetime -/

/-- Any `ChartSpacetime` with `C²` Christoffel symbols satisfies the second
Bianchi identity everywhere in the chart. -/
lemma chartSpacetime_second_bianchi (X : ChartSpacetime) {x : SpacetimeChart}
    (hΓC2 : ∀ k i j, ContDiffAt ℝ 2 (fun y => X.christoffel y k i j) x)
    (l ρ σ μ ν : Fin 4) :
    covDerivRiemann X.coordinateMetric X.coordinateInverseMetric x l ρ σ μ ν
      + covDerivRiemann X.coordinateMetric X.coordinateInverseMetric x μ ρ σ ν l
      + covDerivRiemann X.coordinateMetric X.coordinateInverseMetric x ν ρ σ l μ = 0 :=
  second_bianchi X.coordinateMetric X.coordinateInverseMetric
    (Filter.Eventually.of_forall fun y i j => (X.metric (X.chart.symm y)).symm.apply j i)
    hΓC2 l ρ σ μ ν

/-- Any `ChartSpacetime` with `C²` metric, differentiable inverse metric, and
`C²` Christoffel symbols satisfies the contracted Bianchi identity and Einstein
tensor conservation `∇^μ G_{μl} = 0`. -/
lemma chartSpacetime_covDiv_einstein_eq_zero (X : ChartSpacetime) {x : SpacetimeChart}
    (hgC2 : ∀ i j, ContDiffAt ℝ 2 (fun y => X.coordinateMetric y i j) x)
    (hginvD : ∀ i j, DifferentiableAt ℝ (fun y => X.coordinateInverseMetric y i j) x)
    (hΓC2 : ∀ k i j, ContDiffAt ℝ 2 (fun y => X.christoffel y k i j) x)
    (l : Fin 4) :
    covDiv2 X.coordinateMetric X.coordinateInverseMetric X.einstein x l = 0 := by
  have hInvL : ∀ y i j,
      ∑ k, X.coordinateInverseMetric y i k * X.coordinateMetric y k j =
        if i = j then 1 else 0 := by
    intro y i j
    have h := congrFun (congrFun (X.metric (X.chart.symm y)).inv_right i) j
    simpa [ChartSpacetime.coordinateMetric, ChartSpacetime.coordinateInverseMetric,
      Matrix.mul_apply, Matrix.one_apply] using h
  have hInvR : ∀ y i j,
      ∑ k, X.coordinateMetric y i k * X.coordinateInverseMetric y k j =
        if i = j then 1 else 0 := by
    intro y i j
    have h := congrFun (congrFun (X.metric (X.chart.symm y)).inv_left i) j
    simpa [ChartSpacetime.coordinateMetric, ChartSpacetime.coordinateInverseMetric,
      Matrix.mul_apply, Matrix.one_apply] using h
  exact covDiv_einstein_eq_zero X.coordinateMetric X.coordinateInverseMetric
    (Filter.Eventually.of_forall fun y i j => (X.metric (X.chart.symm y)).symm.apply j i)
    (Filter.Eventually.of_forall fun y i j => (X.metric (X.chart.symm y)).ginv_symm.apply j i)
    (Filter.Eventually.of_forall hInvL)
    (Filter.Eventually.of_forall hInvR)
    hgC2 hginvD hΓC2 l

end Bianchi
end GeneralRelativity
