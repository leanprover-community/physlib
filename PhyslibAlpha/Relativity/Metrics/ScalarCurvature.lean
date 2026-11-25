/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.Metrics.MetricTrace
public import PhyslibAlpha.Relativity.Tensors.RicciTensor

/-!

# Scalar curvature

The Ricci scalar curvature `S = g^{ij} Ric_{ij}` obtained by contracting the Ricci tensor against
the inverse metric.

## i. Overview

This module defines the scalar curvature `ricciScalar M R` as the full contraction of `M.ginv` with
`ricci M R` and shows that it agrees definitionally with `metricTrace M (ricci M R)`.

## ii. Key results

- `ricciScalar` : scalar curvature `S = ∑ i j, g^{ij} Ric_{ij}`.
- `ricciScalar_eq_metricTrace` : `ricciScalar` is the metric trace of `ricci`.

## iii. Table of contents

- A. Scalar curvature

## iv. References

* R. M. Wald, *General Relativity* (1984). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973). [ref: mtw_1973_gravitation]

-/

@[expose] public section

namespace GeneralRelativity

/-!

## A. Scalar curvature

-/

/-- Scalar curvature `S = ∑ i j, g^{ij} Ric_{ij}`. -/
noncomputable def ricciScalar {n : ℕ} (M : MetricTensor n) (R : RiemannTensor n) : ℝ :=
  ∑ i, ∑ j, M.ginv i j * ricci M R i j

/-- Scalar curvature is the metric trace of the Ricci tensor. -/
lemma ricciScalar_eq_metricTrace {n : ℕ} (M : MetricTensor n) (R : RiemannTensor n) :
    ricciScalar M R = metricTrace M (ricci M R) := rfl

end GeneralRelativity
