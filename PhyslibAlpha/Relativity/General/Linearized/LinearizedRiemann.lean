/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.General.Linearized.LinearizedChristoffel
import Mathlib.Tactic.Ring

/-!

# Linearized Riemann curvature tensor

First-order linearized Riemann curvature tensor for a `MetricPerturbation` around Minkowski
spacetime.

## i. Overview

Differentiating `linearizedChristoffel` yields the linearized Riemann curvature tensor
`linearizedRiemann P x r s m n = ∂_m Γ^r_{n s} - ∂_n Γ^r_{m s}`. This module defines
`linearizedRiemann` and proves antisymmetry in its last two indices together with additivity for
`C²` perturbations.

## ii. Key results

- `linearizedRiemann`, `linearizedRiemann_antisymm`, `linearizedRiemann_add` : linearized Riemann
  tensor, antisymmetry, and additivity.

## iii. Table of contents

- A. Linearized Riemann curvature tensor

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

## A. Linearized Riemann curvature tensor

To first order in the metric perturbation `h`, quadratic Christoffel products vanish, leaving the
linearized Riemann curvature `∂_m Γ^r_{ns} - ∂_n Γ^r_{ms}`.

-/

/-- Linearized Riemann curvature tensor `R^r_{s m n} = ∂_m Γ^r_{n s} - ∂_n Γ^r_{m s}`. -/
noncomputable def linearizedRiemann (P : MetricPerturbation) (x : Fin 4 → ℝ)
    (r s m n : Fin 4) : ℝ :=
  coordDeriv m (fun y => linearizedChristoffel P y r n s) x
    - coordDeriv n (fun y => linearizedChristoffel P y r m s) x

/-- Antisymmetry of `linearizedRiemann` in its last two indices. -/
lemma linearizedRiemann_antisymm (P : MetricPerturbation) (x : Fin 4 → ℝ) (r s m n : Fin 4) :
    linearizedRiemann P x r s m n = -linearizedRiemann P x r s n m := by
  simp only [linearizedRiemann]
  ring

/-- Additivity of `linearizedRiemann` for `C²` perturbations. -/
lemma linearizedRiemann_add (P Q : MetricPerturbation) (x : Fin 4 → ℝ)
    (hP : P.IsC2At x) (hQ : Q.IsC2At x) (r s m n : Fin 4) :
    linearizedRiemann (P.add Q) x r s m n =
      linearizedRiemann P x r s m n + linearizedRiemann Q x r s m n := by
  simp only [linearizedRiemann]
  rw [coordDeriv_congr_nhds m x (linearizedChristoffel_add_eventuallyEq hP hQ r n s),
    coordDeriv_congr_nhds n x (linearizedChristoffel_add_eventuallyEq hP hQ r m s),
    coordDeriv_add m x (slice_differentiableAt m (differentiableAt_linearizedChristoffel hP r n s))
      (slice_differentiableAt m (differentiableAt_linearizedChristoffel hQ r n s)),
    coordDeriv_add n x (slice_differentiableAt n (differentiableAt_linearizedChristoffel hP r m s))
      (slice_differentiableAt n (differentiableAt_linearizedChristoffel hQ r m s))]
  ring

end Linearized

end GeneralRelativity
