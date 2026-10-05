/-
Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Jose Fernandez Morales
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.Local.Action
/-!
# Local Euler-Lagrange operators

The local Euler-Lagrange operator of a local Lagrangian, built componentwise.

## i. Overview

This module defines the local Euler-Lagrange operator associated with a local Lagrangian.

In the first implementation pass, the derivatives of the Lagrangian with respect to the jet
coordinates are packaged explicitly as part of the local Lagrangian data. This keeps the formula
close to the one in the book while avoiding a premature smooth structure on `JetPoint`.

## ii. Key results

- `ClassicalFieldTheory.Local.eulerLagrangeTerm` : a single summand in the local
  Euler-Lagrange formula.
- `ClassicalFieldTheory.Local.eulerLagrangeComponent` : one component `E_a(L)` of the operator.
- `ClassicalFieldTheory.Local.eulerLagrangeOp` : the full local Euler-Lagrange operator.

## iii. Table of contents

- A. Euler-Lagrange summands
- B. Components of the Euler-Lagrange operator
- C. The full operator

## iv. References

* J. Cortés and A. Haupt, Lecture Notes on Mathematical Methods of Classical Physics, Chapter 5.
  [ref: cortes_haupt_2016]
-/

@[expose] public section

open scoped BigOperators
open Physlib

namespace ClassicalFieldTheory
namespace Local

/-!
## A. Euler-Lagrange summands

-/

/-- The summand `(-1)^|I| D_I (∂L/∂u^a_I)` in the local Euler-Lagrange formula. -/
noncomputable def eulerLagrangeTerm (L : Lagrangian d m k) (I : DerivativeIndex d k) (a : Fin m)
    (f : Space d → EuclideanSpace ℝ (Fin m)) : Space d → ℝ :=
  fun x =>
    (-1 : ℝ) ^ I.1.order * iteratedTotalDerivative k I.1 (L.coordDeriv I a) f x

@[simp]
lemma eulerLagrangeTerm_apply (L : Lagrangian d m k) (I : DerivativeIndex d k) (a : Fin m)
    (f : Space d → EuclideanSpace ℝ (Fin m)) (x : Space d) :
    eulerLagrangeTerm L I a f x =
      (-1 : ℝ) ^ I.1.order * iteratedTotalDerivative k I.1 (L.coordDeriv I a) f x := rfl

/-!
## B. Components of the Euler-Lagrange operator

-/

/-- The `a`-th component of the local Euler-Lagrange operator. -/
noncomputable def eulerLagrangeComponent (L : Lagrangian d m k) (a : Fin m)
    (f : Space d → EuclideanSpace ℝ (Fin m)) : Space d → ℝ :=
  fun x => ∑ I : DerivativeIndex d k, eulerLagrangeTerm L I a f x

@[simp]
lemma eulerLagrangeComponent_apply (L : Lagrangian d m k) (a : Fin m)
    (f : Space d → EuclideanSpace ℝ (Fin m)) (x : Space d) :
    eulerLagrangeComponent L a f x = ∑ I : DerivativeIndex d k, eulerLagrangeTerm L I a f x := rfl

/-!
## C. The full operator

-/

/-- The local Euler-Lagrange operator attached to a local Lagrangian. -/
noncomputable def eulerLagrangeOp (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m)) :
    Space d → EuclideanSpace ℝ (Fin m) :=
  fun x => WithLp.toLp 2 fun a => eulerLagrangeComponent L a f x

lemma eulerLagrangeOp_apply (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m))
    (x : Space d) (a : Fin m) :
    eulerLagrangeOp L f x a = eulerLagrangeComponent L a f x := by
  simp [eulerLagrangeOp]

@[simp]
lemma eulerLagrangeOp_eq (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m)) :
    eulerLagrangeOp L f = fun x => WithLp.toLp 2 fun a => eulerLagrangeComponent L a f x := by
  rfl

end Local
end ClassicalFieldTheory
