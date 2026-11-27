/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.Tensors.RiemannTensor

/-!

# Four-dimensional frame Kretschmann scalar

Kretschmann scalar from orthonormal-frame components of a four-dimensional Riemann tensor.

## i. Overview

The sum of squared orthonormal-frame components `∑_{a,b,c,d} R_{abcd}²` agrees with the Lorentzian
Kretschmann scalar when odd-time-index components vanish or in a Riemannian frame.

## ii. Key results

- `RiemannTensor.frameKretschmannScalar` : sum of squared orthonormal-frame curvature components.

## iii. Table of contents

- A. Frame Kretschmann scalar

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 3 (Sec. 3.2). [ref: wald_1984_general_relativity]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 3 (Sec. 3.6)
  (https://arxiv.org/pdf/gr-qc/9712019#page=79). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

namespace RiemannTensor

/-!

## A. Frame Kretschmann scalar

The frame sum squares each covariant component without raising indices, so it matches the
Lorentzian invariant only when the gravitomagnetic components vanish.

-/

/-- Sum of squared orthonormal-frame curvature components `∑_{a,b,c,d} R_{abcd}²`. In a Lorentzian
orthonormal frame of signature `(-, +, +, +)`, `R_{abcd} R^{abcd}` weights components with an odd
number of temporal indices by `-1`, so this expression coincides with the Lorentzian Kretschmann
scalar whenever odd-time-index (gravitomagnetic) components vanish (such as purely electric static
curvature), as well as in any Riemannian orthonormal frame. -/
noncomputable def frameKretschmannScalar (R : RiemannTensor 4) : ℝ :=
  ∑ i, ∑ j, ∑ l, ∑ m, R.comp i j l m * R.comp i j l m

end RiemannTensor

end GeneralRelativity
