/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.General.Linearized.LinearizedRiemann

/-!

# Linearized Ricci tensor and scalar curvature

First-order linearized Ricci tensor and scalar curvature for a `MetricPerturbation` around
Minkowski spacetime.

## i. Overview

Contracting `linearizedRiemann P` on its first and third indices yields the linearized Ricci
tensor `linearizedRicci P`, whose Minkowski trace defines `linearizedRicciScalar P`.

## ii. Key results

- `linearizedRicci`, `linearizedRicciScalar` : linearized Ricci tensor and Ricci scalar.

## iii. Table of contents

- A. Linearized Ricci tensor and scalar curvature

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

/-!

## A. Linearized Ricci tensor and scalar curvature

Contracting the first and third indices of the linearized Riemann tensor and taking its Minkowski
trace produces the first-order Ricci tensor and scalar curvature.

-/

/-- Linearized Ricci tensor `R^{(1)}_{ij} = ∑ r, R^r_{i r j}`. -/
noncomputable def linearizedRicci (P : MetricPerturbation) (x : Fin 4 → ℝ) (i j : Fin 4) : ℝ :=
  ∑ r : Fin 4, linearizedRiemann P x r i r j

/-- Linearized Ricci scalar `S^{(1)} = η^{ij} R^{(1)}_{ij}`. -/
noncomputable def linearizedRicciScalar (P : MetricPerturbation) (x : Fin 4 → ℝ) : ℝ :=
  ∑ i : Fin 4, minkowskiMetric4 i i * linearizedRicci P x i i

end Linearized

end GeneralRelativity
