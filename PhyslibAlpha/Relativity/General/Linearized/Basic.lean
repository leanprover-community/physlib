/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.Metrics.CoordinateMetric
public import PhyslibAlpha.Relativity.Metrics.MetricTrace

/-!

# Linearized metric perturbations

Linearized symmetric metric perturbations `h_{ij}(x)` around Minkowski spacetime `η_{ij}` with
pointwise symmetry and `C²` coordinate regularity predicates.

## i. Overview

In linearized general relativity, the spacetime metric is expanded around flat Minkowski
spacetime as `g_{ij}(x) = η_{ij} + h_{ij}(x)` with `|h_{ij}| ≪ 1`. The structure
`MetricPerturbation` bundles a symmetric `(0, 2)` tensor field `h : (Fin 4 → ℝ) → Tensor2 4`
with its pointwise symmetry proof, providing the shared geometric object across trace reversal,
linearized curvature, diffeomorphism gauge transformations, Lorenz gauge reduction, gravitational
waves, and the Newtonian limit.

## ii. Key results

- `MetricPerturbation` : symmetric spacetime metric perturbation `h_{ij}(x)`.
- `MetricPerturbation.symm_apply` : component symmetry `h_{ij}(x) = h_{ji}(x)`.
- `MetricPerturbation.IsC2At` : `C²` regularity of all metric perturbation components at `x`.
- `MetricPerturbation.add` : pointwise sum of two metric perturbations.

## iii. Table of contents

- A. The `MetricPerturbation` structure

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 4 (Sec. 4.4). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 18.
  [ref: mtw_1973_gravitation]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 6
  (https://arxiv.org/pdf/gr-qc/9712019#page=144). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

namespace Linearized

open Pipeline

/-!

## A. The `MetricPerturbation` structure

A small perturbation `h_{ij}(x)` of flat Minkowski spacetime carries pointwise index symmetry and
inherits addition and coordinate-wise `C²` differentiability.

-/

/-- A small symmetric `(0, 2)` metric perturbation `h_{ij}(x)` around Minkowski spacetime. -/
structure MetricPerturbation where
  /-- Covariant components `h_{ij}(x)` of the metric perturbation. -/
  h : (Fin 4 → ℝ) → Tensor2 4
  /-- Pointwise symmetry `h_{ij}(x) = h_{ji}(x)`. -/
  symm : ∀ x, IsSymm (h x)

/-- Componentwise symmetry `P.h x i j = P.h x j i` of a metric perturbation `P`. -/
lemma MetricPerturbation.symm_apply (P : MetricPerturbation) (x : Fin 4 → ℝ) (i j : Fin 4) :
    P.h x i j = P.h x j i :=
  (P.symm x).apply j i

/-- Pointwise `C²` regularity of every component of a metric perturbation `P` at `x`. -/
def MetricPerturbation.IsC2At (P : MetricPerturbation) (x : Fin 4 → ℝ) : Prop :=
  ∀ a b, ContDiffAt ℝ 2 (fun z => P.h z a b) x

/-- Pointwise `C²` regularity of a metric perturbation extends to an open neighborhood. -/
lemma MetricPerturbation.IsC2At.eventually {P : MetricPerturbation} {x : Fin 4 → ℝ}
    (hP : P.IsC2At x) : ∀ᶠ y in nhds x, P.IsC2At y := by
  dsimp only [IsC2At]
  rw [Filter.eventually_all]; intro a; rw [Filter.eventually_all]; intro b
  exact (hP a b).eventually (by simp)

/-- Pointwise sum `(P + Q)_{ij}(x) = P_{ij}(x) + Q_{ij}(x)` of two metric perturbations. -/
def MetricPerturbation.add (P Q : MetricPerturbation) : MetricPerturbation where
  h x := P.h x + Q.h x
  symm x := Matrix.IsSymm.ext fun i j => by
    dsimp
    rw [P.symm_apply x j i, Q.symm_apply x j i]

end Linearized

end GeneralRelativity
