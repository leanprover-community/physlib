/-
Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Jose Fernandez Morales
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.Local.FirstVariation
/-!
# First-order local field theory

Aliases and projections specializing the local field theory API to first-order jets.

## i. Overview

This module provides a thin usability layer for first-order local field theory, i.e. the
specialization of the local CFT stack to `k = 1`.

The definitions here do not introduce a new theory. They are aliases and projections for the
existing coordinate-readout stack:

- first-order jet points are `JetPoint d m 1`,
- first-order lagrangians are `Lagrangian d m 1`,
- field values are still the zero-order jet coordinates,
- first derivatives are the coordinates indexed by `MultiIndex.increment 0 i`.

This keeps the general finite-order API as the source of truth while making the common first-order
case easier to state in examples and later mechanics bridges.

## ii. Key results

- `ClassicalFieldTheory.Local.FirstOrderJetPoint`
- `ClassicalFieldTheory.Local.FirstOrderLagrangian`
- `ClassicalFieldTheory.Local.firstDerivativeIndex`
- `ClassicalFieldTheory.Local.JetPoint.firstDerivCoord`
- `ClassicalFieldTheory.Local.firstOrderJetAt`

## iii. Table of contents

- A. First-order aliases
- B. First derivative indices
- C. First-order jet projections
- D. First-order evaluation and variational API

## iv. References

* J. Cortés and A. Haupt, Lecture Notes on Mathematical Methods of Classical Physics,
  arXiv:1612.03100v2, Chapter 5. [ref: cortes_haupt_2016]
-/

@[expose] public section

open Physlib

namespace ClassicalFieldTheory
namespace Local

/-!
## A. First-order aliases

-/

/-- Coordinate data for first-order local jet points. -/
abbrev FirstOrderJetCoordinates (d m : ℕ) := JetCoordinates d m 1

/-- Coordinate-level first-order jet points. -/
abbrev FirstOrderJetPoint (d m : ℕ) := JetPoint d m 1

/-- Fiber-direction data for first-order jet points. -/
abbrev FirstOrderJetFiberData (d m : ℕ) := JetFiberData d m 1

/-- First-order local lagrangians. -/
abbrev FirstOrderLagrangian (d m : ℕ) := Lagrangian d m 1

/-!
## B. First derivative indices

-/

/-- The first-derivative coordinate index in the source direction `i`. -/
def firstDerivativeIndex (d : ℕ) (i : Fin d) : DerivativeIndex d 1 :=
  ⟨Physlib.MultiIndex.increment 0 i, by simp⟩

@[simp]
lemma firstDerivativeIndex_coe (d : ℕ) (i : Fin d) :
    ((firstDerivativeIndex d i : DerivativeIndex d 1) : MultiIndex d) =
      Physlib.MultiIndex.increment 0 i := rfl

lemma firstDerivativeIndex_order (d : ℕ) (i : Fin d) :
    ((firstDerivativeIndex d i : DerivativeIndex d 1) : MultiIndex d).order = 1 := by
  simp [firstDerivativeIndex]

/-!
## C. First-order jet projections

-/

namespace JetPoint

variable {d m : ℕ}

/-- The first derivative coordinate `u^a_i` of a first-order jet point. -/
def firstDerivCoord (J : FirstOrderJetPoint d m) (i : Fin d) (a : Fin m) : ℝ :=
  J.coord (firstDerivativeIndex d i) a

/-- The bundled target vector of first derivative coordinates in the source direction `i`. -/
def firstDerivVector (J : FirstOrderJetPoint d m) (i : Fin d) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun a => J.firstDerivCoord i a

@[simp]
lemma firstDerivVector_apply (J : FirstOrderJetPoint d m) (i : Fin d) (a : Fin m) :
    J.firstDerivVector i a = J.firstDerivCoord i a := by
  simp [firstDerivVector]

@[simp]
lemma firstDerivCoord_ofBaseCoordinates (x : Space d) (u : FirstOrderJetCoordinates d m)
    (i : Fin d) (a : Fin m) :
    (JetPoint.ofBaseCoordinates x u).firstDerivCoord i a = u (firstDerivativeIndex d i) a := rfl

end JetPoint

/-!
## D. First-order evaluation and variational API

-/

/-- The first-order coordinate-level jet point of a field at a point. -/
noncomputable abbrev firstOrderJetAt (f : Space d → EuclideanSpace ℝ (Fin m)) (x : Space d) :
    FirstOrderJetPoint d m :=
  jetAt 1 f x

@[simp]
lemma firstOrderJetAt_base (f : Space d → EuclideanSpace ℝ (Fin m)) (x : Space d) :
    (firstOrderJetAt f x).base = x := rfl

lemma firstOrderJetAt_value (f : Space d → EuclideanSpace ℝ (Fin m)) (x : Space d) :
    (firstOrderJetAt f x).value = f x := by
  simp [firstOrderJetAt]

@[simp]
lemma firstOrderJetAt_firstDerivCoord (f : Space d → EuclideanSpace ℝ (Fin m))
    (x : Space d) (i : Fin d) (a : Fin m) :
    (firstOrderJetAt f x).firstDerivCoord i a =
      ∂^[Physlib.MultiIndex.increment 0 i] (fun y => (f y) a) x := rfl

/-- Evaluate a first-order local lagrangian along the first jets of a field. -/
noncomputable abbrev firstOrderActionDensity (L : FirstOrderLagrangian d m)
    (f : Space d → EuclideanSpace ℝ (Fin m)) : Space d → ℝ :=
  actionDensity L f

/-- The action of a first-order local lagrangian. -/
noncomputable abbrev firstOrderAction (L : FirstOrderLagrangian d m)
    (f : Space d → EuclideanSpace ℝ (Fin m)) : ℝ :=
  action L f

/-- The Euler-Lagrange operator of a first-order local lagrangian. -/
noncomputable abbrev firstOrderEulerLagrangeOp (L : FirstOrderLagrangian d m)
    (f : Space d → EuclideanSpace ℝ (Fin m)) : Space d → EuclideanSpace ℝ (Fin m) :=
  eulerLagrangeOp L f

theorem firstOrder_isCritical_iff_eulerLagrange_zero
    (L : FirstOrderLagrangian d m) (f : Space d → EuclideanSpace ℝ (Fin m))
    (hLf : IsAdmissibleForAction L f)
    (hL : Lagrangian.SmoothInCoordinates L) :
    IsCritical L f ↔ firstOrderEulerLagrangeOp L f = 0 := by
  exact isCritical_iff_eulerLagrange_zero_of_admissibleForAction_and_smoothInCoordinates L f hLf hL

end Local
end ClassicalFieldTheory
