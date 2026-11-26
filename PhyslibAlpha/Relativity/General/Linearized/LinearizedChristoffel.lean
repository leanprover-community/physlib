/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.General.Linearized.TraceReversed
import Mathlib.Tactic.Ring

/-!

# Linearized Christoffel symbols

First-order linearized Christoffel symbols for a `MetricPerturbation` around Minkowski spacetime.

## i. Overview

Perturbing flat Minkowski spacetime by `g = η + h` gives first-order Christoffel symbols
`linearizedChristoffel P x k i j = ½ η^{kk} (∂_j h_{ki} + ∂_i h_{kj} - ∂_k h_{ij})`. This module
establishes their lower-index symmetry (`linearizedChristoffel_symm`), pointwise differentiability
for `C²` perturbations, and local additivity around Minkowski spacetime.

## ii. Key results

- `linearizedChristoffel`, `linearizedChristoffel_symm` : linearized Christoffel symbols and lower
  index symmetry.
- `differentiableAt_linearizedChristoffel`, `linearizedChristoffel_add_eventuallyEq` : `C²`
  differentiability and local additivity helpers.

## iii. Table of contents

- A. Linearized Christoffel symbols and regularity

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

## A. Linearized Christoffel symbols and regularity

First-order connection coefficients `Γ^k_{ij}` depend linearly on first partial derivatives of the
symmetric metric perturbation `P.h`.

-/

/-- Linearized Christoffel symbols `Γ^k_{ij} = ½ η^{km} (∂_j h_{mi} + ∂_i h_{mj} - ∂_m h_{ij})`. -/
noncomputable def linearizedChristoffel (P : MetricPerturbation) (x : Fin 4 → ℝ)
    (k i j : Fin 4) : ℝ :=
  (1 / 2) * minkowskiMetric4 k k
    * (coordDeriv j (fun y => P.h y k i) x + coordDeriv i (fun y => P.h y k j) x
      - coordDeriv k (fun y => P.h y i j) x)

/-- Lower-index symmetry of linearized Christoffel symbols for a `MetricPerturbation`. -/
lemma linearizedChristoffel_symm (P : MetricPerturbation) (x : Fin 4 → ℝ) (k i j : Fin 4) :
    linearizedChristoffel P x k i j = linearizedChristoffel P x k j i := by
  have hij : (fun y => P.h y i j) = fun y => P.h y j i := funext fun y => P.symm_apply y i j
  simp only [linearizedChristoffel, hij]
  ring

/-- A `C²` metric perturbation `P` at `x` has differentiable linearized Christoffel symbols at
`x`. -/
lemma differentiableAt_linearizedChristoffel {P : MetricPerturbation} {x : Fin 4 → ℝ}
    (hP : P.IsC2At x) (k i j : Fin 4) :
    DifferentiableAt ℝ (fun y => linearizedChristoffel P y k i j) x := by
  simp only [linearizedChristoffel]
  exact (((coordDeriv_differentiableAt j (hP k i)).add
    (coordDeriv_differentiableAt i (hP k j))).sub
    (coordDeriv_differentiableAt k (hP i j))).const_mul _

/-- Local additivity of `linearizedChristoffel` on a neighborhood of `x` for `C²` perturbations. -/
lemma linearizedChristoffel_add_eventuallyEq {P Q : MetricPerturbation} {x : Fin 4 → ℝ}
    (hP : P.IsC2At x) (hQ : Q.IsC2At x) (k i j : Fin 4) :
    (fun y => linearizedChristoffel (P.add Q) y k i j) =ᶠ[nhds x]
      fun y => linearizedChristoffel P y k i j + linearizedChristoffel Q y k i j := by
  filter_upwards [hP.eventually, hQ.eventually] with y hy1 hy2
  have d1 : ∀ a b, DifferentiableAt ℝ (fun z => P.h z a b) y :=
    fun a b => (hy1 a b).differentiableAt (by norm_num)
  have d2 : ∀ a b, DifferentiableAt ℝ (fun z => Q.h z a b) y :=
    fun a b => (hy2 a b).differentiableAt (by norm_num)
  simp only [linearizedChristoffel, MetricPerturbation.add, Matrix.add_apply]
  rw [coordDeriv_add j y (slice_differentiableAt j (d1 k i)) (slice_differentiableAt j (d2 k i)),
    coordDeriv_add i y (slice_differentiableAt i (d1 k j)) (slice_differentiableAt i (d2 k j)),
    coordDeriv_add k y (slice_differentiableAt k (d1 i j)) (slice_differentiableAt k (d2 i j))]
  ring

end Linearized

end GeneralRelativity
