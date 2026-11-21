/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.General.Einstein

/-!

# Minkowski spacetime as a vacuum solution

The flat metric `η = diag(-1, 1, 1, 1)` with vanishing curvature solves `G = 0`.

## i. Overview

This module packages `eta4` as a `MetricTensor 4` (`minkowski`) and verifies that with the
flat curvature tensor `RiemannTensor.flat 4`, its Ricci tensor, scalar curvature, and Einstein
tensor all vanish.

## ii. Key results

- `minkowski` : four-dimensional Minkowski spacetime in inertial coordinates.
- `minkowski_ginv_offdiag` : the inverse Minkowski metric is diagonal.
- `minkowski_ricci_eq_zero`, `minkowski_scalarCurv_eq_zero`, `minkowski_einstein_eq_zero` :
  Minkowski spacetime is Ricci flat, scalar flat, and a vacuum solution of `G = 0`.

## iii. Table of contents

- A. The Minkowski spacetime metric
- B. Vacuum Einstein equations for Minkowski spacetime

## iv. References

* None.

-/

@[expose] public section

namespace GeneralRelativity

/-!

## A. The Minkowski spacetime metric

-/

/-- Four-dimensional Minkowski spacetime in inertial coordinates, with signature
`(-, +, +, +)`. -/
def minkowski : MetricTensor 4 where
  g := eta4
  ginv := eta4
  symm := eta4_symm
  inv_left := eta4_mul_self
  inv_right := eta4_mul_self

/-- Off-diagonal entries of the inverse Minkowski metric vanish. -/
lemma minkowski_ginv_offdiag {k l : Fin 4} (h : k ≠ l) : minkowski.ginv k l = 0 := by
  fin_cases k <;> fin_cases l <;> simp_all [minkowski, eta4]

/-!

## B. Vacuum Einstein equations for Minkowski spacetime

-/

/-- The flat curvature tensor on Minkowski spacetime is Ricci flat. -/
lemma minkowski_ricci_eq_zero : ricci minkowski (RiemannTensor.flat 4) = 0 :=
  ricci_flat 4 minkowski

/-- The flat curvature tensor on Minkowski spacetime has zero scalar curvature. -/
lemma minkowski_scalarCurv_eq_zero : scalarCurv minkowski (RiemannTensor.flat 4) = 0 := by
  simp [scalarCurv]

/-- Minkowski spacetime is a vacuum solution of the Einstein equations. -/
lemma minkowski_einstein_eq_zero : einstein minkowski (RiemannTensor.flat 4) = 0 := by
  ext i j
  simp [einstein, minkowski_scalarCurv_eq_zero]

/-- `G = 0` and `Ric = 0` agree on Minkowski spacetime. -/
lemma minkowski_vacuum_iff_ricci_flat :
    einstein minkowski (RiemannTensor.flat 4) = 0 ↔
      ricci minkowski (RiemannTensor.flat 4) = 0 :=
  vacuum_iff_ricci_flat minkowski (RiemannTensor.flat 4)

end GeneralRelativity
