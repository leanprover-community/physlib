/-
Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Jose Fernandez Morales
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.Local.FirstVariation
/-!
# Local Euler-Lagrange equations

A named predicate for the local Euler-Lagrange equations and the criticality criteria using it.

## i. Overview

This module gives a named predicate for fields satisfying the local Euler-Lagrange equations.

The equation itself is still the existing local coordinate equation

`eulerLagrangeOp L f = 0`.

The purpose of this file is only to expose that condition as a reusable API point and to restate
the already-proved criticality criteria using this named predicate. It does not introduce a new
Euler-Lagrange operator or any new analytic hypotheses.

## ii. Key results

- `ClassicalFieldTheory.Local.SatisfiesEulerLagrange`
- `ClassicalFieldTheory.Local.
  isCritical_iff_satisfiesEulerLagrange_of_contDiff_and_smoothInCoordinates`
- `ClassicalFieldTheory.Local.
  isCritical_iff_satisfiesEulerLagrange_of_admissibleForAction_and_smoothInCoordinates`

## iii. Table of contents

- A. Euler-Lagrange equation predicate
- B. Criticality criteria

## iv. References

* J. Cortés and A. Haupt, Lecture Notes on Mathematical Methods of Classical Physics,
  arXiv:1612.03100v2, Chapter 5, Theorem 5.2. [ref: cortes_haupt_2016]
-/

@[expose] public section

open scoped ContDiff

namespace ClassicalFieldTheory
namespace Local

/-!
## A. Euler-Lagrange equation predicate

-/

/-- A field satisfies the local Euler-Lagrange equations for a local lagrangian when the
Euler-Lagrange operator vanishes along that field. -/
def SatisfiesEulerLagrange (L : Lagrangian d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m)) : Prop :=
  eulerLagrangeOp L f = 0

@[simp]
lemma satisfiesEulerLagrange_iff (L : Lagrangian d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m)) :
    SatisfiesEulerLagrange L f ↔ eulerLagrangeOp L f = 0 :=
  Iff.rfl

lemma SatisfiesEulerLagrange.eulerLagrangeOp_eq_zero
    {L : Lagrangian d m k} {f : Space d → EuclideanSpace ℝ (Fin m)}
    (h : SatisfiesEulerLagrange L f) :
    eulerLagrangeOp L f = 0 :=
  h

lemma SatisfiesEulerLagrange.of_eulerLagrangeOp_eq_zero
    {L : Lagrangian d m k} {f : Space d → EuclideanSpace ℝ (Fin m)}
    (h : eulerLagrangeOp L f = 0) :
    SatisfiesEulerLagrange L f :=
  h

/-!
## B. Criticality criteria

-/

theorem isCritical_iff_satisfiesEulerLagrange_of_contDiff_and_smoothInCoordinates
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m)) (hf : ContDiff ℝ ∞ f)
    (hL : Lagrangian.SmoothInCoordinates L)
    (hbase : HasFiniteAction L f) :
    IsCritical L f ↔ SatisfiesEulerLagrange L f := by
  exact isCritical_iff_eulerLagrange_zero_of_contDiff_and_smoothInCoordinates L f hf hL hbase

theorem isCritical_iff_satisfiesEulerLagrange_of_admissibleForAction_and_smoothInCoordinates
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m))
    (hLf : IsAdmissibleForAction L f)
    (hL : Lagrangian.SmoothInCoordinates L) :
    IsCritical L f ↔ SatisfiesEulerLagrange L f := by
  exact isCritical_iff_eulerLagrange_zero_of_admissibleForAction_and_smoothInCoordinates L f hLf hL

end Local
end ClassicalFieldTheory
