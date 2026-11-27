/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.General.Linearized.LinearizedRicci

/-!

# Linearized Einstein tensor

First-order linearized Einstein tensor for a `MetricPerturbation` around Minkowski spacetime.

## i. Overview

Forming the trace-reversed combination `G^{(1)}_{ij} = R^{(1)}_{ij} - ½ η_{ij} R^{(1)}` defines
the first-order Einstein tensor around Minkowski spacetime, supplying the gravitational field
operator for linearized gauge invariance, Lorenz-gauge wave equations, gravitational radiation, and
the Newtonian Poisson limit.

## ii. Key results

- `linearizedEinstein` : linearized Einstein tensor `G^{(1)}_{ij}`.

## iii. Table of contents

- A. Linearized Einstein tensor

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

## A. Linearized Einstein tensor

The weak-field Einstein tensor is the trace-reversed linearized Ricci tensor on Minkowski
background.

-/

/-- Linearized Einstein tensor `G^{(1)}_{ij} = R^{(1)}_{ij} - ½ η_{ij} R^{(1)}`. -/
noncomputable def linearizedEinstein (P : MetricPerturbation) (x : Fin 4 → ℝ)
    (i j : Fin 4) : ℝ :=
  linearizedRicci P x i j - (1 / 2) * minkowskiMetric4 i j * linearizedRicciScalar P x

end Linearized

end GeneralRelativity
