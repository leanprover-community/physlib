/-
Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Jose Fernandez Morales
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.Local.FirstVariation.Criterion
/-!
# First variation and the Euler-Lagrange criterion

Public entry point: a field is critical iff its local Euler-Lagrange operator vanishes.

## i. Overview

This module is the public entry point for the local first-variation theory. The core linearized
density objects live in `FirstVariation.Basic`, the analytic derivation tools and packaged
hypotheses live in `FirstVariation.Density`, `FirstVariation.IntegrationByParts`,
`FirstVariation.Regularity`, and `FirstVariation.Criterion`, and this file exposes the cleanest
surface-level statements of the local Euler-Lagrange criterion.

## ii. Key results

- `ClassicalFieldTheory.Local.hasSmoothEulerLagrangeRegularity_of_smoothInCoordinates`
- `ClassicalFieldTheory.Local.isCritical_iff_eulerLagrange_zero_of_contDiff_and_smoothInCoordinates`
- `ClassicalFieldTheory.Local.
  isCritical_iff_eulerLagrange_zero_of_admissibleForAction_and_smoothInCoordinates`

## iii. Table of contents

- A. Smooth-coordinate regularity
- B. Final Euler-Lagrange criteria

## iv. References

* J. Cortés and A. Haupt, Lecture Notes on Mathematical Methods of Classical Physics, Chapter 5,
  Theorem 5.2. [ref: cortes_haupt_2016]
-/

@[expose] public section

open scoped ContDiff

namespace ClassicalFieldTheory
namespace Local

/-!
## A. Smooth-coordinate regularity

-/

theorem hasSmoothEulerLagrangeRegularity_of_smoothInCoordinates
    (L : Lagrangian d m k) (hL : Lagrangian.SmoothInCoordinates L) :
    HasSmoothEulerLagrangeRegularity L := by
  exact hasSmoothEulerLagrangeRegularity_of_contDiffCoordDerivInCoordinates L hL.2

/-!
## B. Final Euler-Lagrange criteria

-/

theorem isCritical_iff_eulerLagrange_zero_of_contDiff_and_smoothInCoordinates
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m)) (hf : ContDiff ℝ ∞ f)
    (hL : Lagrangian.SmoothInCoordinates L)
    (hbase : HasFiniteAction L f) :
    IsCritical L f ↔ eulerLagrangeOp L f = 0 := by
  exact
    isCritical_iff_eulerLagrange_zero_of_hasFiniteAction_and_continuousInCoordinates
      L f hf hL.2 hL.1 hbase

theorem isCritical_iff_eulerLagrange_zero_of_admissibleForAction_and_smoothInCoordinates
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m))
    (hLf : IsAdmissibleForAction L f)
    (hL : Lagrangian.SmoothInCoordinates L) :
    IsCritical L f ↔ eulerLagrangeOp L f = 0 := by
  rcases hLf with ⟨hf, hbase⟩
  exact isCritical_iff_eulerLagrange_zero_of_contDiff_and_smoothInCoordinates L f hf hL hbase

end Local
end ClassicalFieldTheory
