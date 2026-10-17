/-
Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Jose Fernandez Morales
-/
module

public import Physlib.SpaceAndTime.Space.Derivatives.DerivativeIndex
public import Physlib.SpaceAndTime.Space.Derivatives.Iterated
/-!
# Coordinate-level jet points

Coordinate-level jet points of fields on `Space d` and the jets of a field at a point.

## i. Overview

This module introduces the coordinate-level point of the locally trivialized `k`-jet bundle for
fields on `Space d` with values in `EuclideanSpace ℝ (Fin m)`.

This module only formalizes the local coordinate model `Jet^k(Ω, ℝ^m) ≃ Ω × V`; it does not
attempt to define global jet bundles.

At this core stage, a jet point is represented by:

- its base point in `Space d`,
- and its jet coordinates indexed by derivative indices of order at most `k`.

In particular, the zero-th order field value is not stored separately: it is the zero derivative
coordinate.

## ii. Key results

- `ClassicalFieldTheory.Local.JetCoordinates`
- `ClassicalFieldTheory.Local.JetPoint`
- `ClassicalFieldTheory.Local.jetCoordinatesAt`
- `ClassicalFieldTheory.Local.jetAt`

## iii. Table of contents

- A. Jet coordinates
- B. Jet points
- C. Jet points of fields

## iv. References

* J. Cortés and A. Haupt, Lecture Notes on Mathematical Methods of Classical Physics,
  arXiv:1612.03100v2, Chapter 5, Section 5.1. [ref: cortes_haupt_2016]
-/

@[expose] public section

open Physlib

namespace ClassicalFieldTheory
namespace Local

/-!
## A. Jet coordinates

-/

/-- Coordinate data `u^a_I` for `k`-th order jet points.

For each derivative index `I`, these are the scalar components of the corresponding
`EuclideanSpace ℝ (Fin m)` fiber coordinate. We keep this componentwise form because the
local Euler-Lagrange formulas are indexed by both `I` and `a`. -/
abbrev JetCoordinates (d m k : ℕ) := DerivativeIndex d k → Fin m → ℝ

/-!
## B. Jet points

-/

/-- The coordinate-level points of the locally trivialized `k`-jet bundle for fields
`Space d → EuclideanSpace ℝ (Fin m)`. -/
structure JetPoint (d m k : ℕ) where
  /-- The base point of the jet point. -/
  base : Space d
  /-- The jet coordinates indexed by all derivative indices of order at most `k`. -/
  fiber : JetCoordinates d m k

namespace JetPoint

variable {d m k : ℕ}

/-- The coordinate `u^a_I` of a jet point. -/
def coord (J : JetPoint d m k) (I : DerivativeIndex d k) (a : Fin m) : ℝ := J.fiber I a

/-- The zero-th order value encoded by a jet point. -/
def value (J : JetPoint d m k) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun a => J.coord 0 a

@[simp]
lemma value_apply (J : JetPoint d m k) (a : Fin m) :
    J.value a = J.coord 0 a := by
  simp [value]

@[ext]
lemma ext (J K : JetPoint d m k) (hbase : J.base = K.base)
    (hcoord : ∀ I a, J.coord I a = K.coord I a) :
    J = K := by
  cases J with
  | mk x u =>
    cases K with
    | mk y v =>
      dsimp [coord] at hbase hcoord
      subst y
      congr
      funext I a
      exact hcoord I a

/-- Build a jet point from a base point and its jet coordinates. -/
def ofBaseCoordinates (x : Space d) (u : JetCoordinates d m k) : JetPoint d m k where
  base := x
  fiber := u

/-- The base point and jet coordinates of a jet point. -/
def toBaseCoordinates (J : JetPoint d m k) : Space d × JetCoordinates d m k := (J.base, J.fiber)

@[simp]
lemma ofBaseCoordinates_base (x : Space d) (u : JetCoordinates d m k) :
    (ofBaseCoordinates x u).base = x := rfl

@[simp]
lemma ofBaseCoordinates_fiber (x : Space d) (u : JetCoordinates d m k) :
    (ofBaseCoordinates x u).fiber = u := rfl

@[simp]
lemma ofBaseCoordinates_coord (x : Space d) (u : JetCoordinates d m k)
    (I : DerivativeIndex d k) (a : Fin m) :
    (ofBaseCoordinates x u).coord I a = u I a := rfl

@[simp]
lemma ofBaseCoordinates_base_fiber (J : JetPoint d m k) :
    ofBaseCoordinates J.base J.fiber = J := by
  apply JetPoint.ext
  · rfl
  · intro I a
    rfl

@[simp]
lemma toBaseCoordinates_ofBaseCoordinates (x : Space d) (u : JetCoordinates d m k) :
    (ofBaseCoordinates x u).toBaseCoordinates = (x, u) := rfl

end JetPoint

/-!
## C. Jet points of fields

-/

/-- The jet-coordinate function determined by a field `g`. -/
noncomputable def jetCoordinatesAt (k : ℕ) (g : Space d → EuclideanSpace ℝ (Fin m))
    (x : Space d) :
    JetCoordinates d m k :=
  fun I a => ∂^[I.1] (fun y => (g y) a) x

/-- The coordinate-level `k`-jet point of a field `f` at the point `x`. -/
noncomputable def jetAt (k : ℕ) (f : Space d → EuclideanSpace ℝ (Fin m)) (x : Space d) :
    JetPoint d m k where
  base := x
  fiber := jetCoordinatesAt k f x

@[simp]
lemma jetAt_base (k : ℕ) (f : Space d → EuclideanSpace ℝ (Fin m)) (x : Space d) :
    (jetAt k f x).base = x := rfl

@[simp]
lemma jetAt_value (k : ℕ) (f : Space d → EuclideanSpace ℝ (Fin m)) (x : Space d) :
    (jetAt k f x).value = f x := by
  ext a
  simp [JetPoint.value, JetPoint.coord, jetAt, jetCoordinatesAt, Space.iteratedDeriv_zero]

@[simp]
lemma jetAt_coord (k : ℕ) (f : Space d → EuclideanSpace ℝ (Fin m)) (x : Space d)
    (I : DerivativeIndex d k) (a : Fin m) :
    (jetAt k f x).coord I a = ∂^[I.1] (fun y => (f y) a) x := rfl

lemma jetAt_coord_zero (k : ℕ) (f : Space d → EuclideanSpace ℝ (Fin m)) (x : Space d)
    (a : Fin m) :
    (jetAt k f x).coord 0 a = (f x) a := by
  simp [jetAt_coord]

@[simp]
lemma jetCoordinatesAt_eq (k : ℕ) (g : Space d → EuclideanSpace ℝ (Fin m)) (x : Space d)
    (I : DerivativeIndex d k) (a : Fin m) :
    jetCoordinatesAt k g x I a = ∂^[I.1] (fun y => (g y) a) x := rfl

lemma jetCoordinatesAt_zero (k : ℕ) (g : Space d → EuclideanSpace ℝ (Fin m))
    (x : Space d) (a : Fin m) :
    jetCoordinatesAt k g x 0 a = (g x) a := by
  simp [jetCoordinatesAt]

lemma jetAt_eq_ofBaseCoordinates (k : ℕ) (f : Space d → EuclideanSpace ℝ (Fin m))
    (x : Space d) :
    jetAt k f x = JetPoint.ofBaseCoordinates x (jetCoordinatesAt k f x) := by
  apply JetPoint.ext
  · rfl
  · intro I a
    rfl

end Local
end ClassicalFieldTheory
