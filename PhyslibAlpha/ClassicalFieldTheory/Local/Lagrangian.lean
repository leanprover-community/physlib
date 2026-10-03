/-
Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Jose Fernandez Morales
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.Local.JetPointRegularity
public import PhyslibAlpha.ClassicalFieldTheory.Local.TotalDerivative
/-!
# Local Lagrangians

Local finite-order Lagrangians on jet points, their regularity, and evaluation along fields.

## i. Overview

This module defines local Lagrangians of finite order for fields on `Space d` with values in
`EuclideanSpace ℝ (Fin m)`.

In the first local stage of the Classical Field Theory development, a local `k`-th order
Lagrangian is treated as a function on `JetPoint d m k`. This matches the local book-level picture
`L : Jet^k(Ω, R^m) → R` while postponing any stronger smoothness packaging until the ambient
structure on local jet-point data has been made explicit enough to support it naturally.

## ii. Key results

- `ClassicalFieldTheory.Local.Lagrangian` : local `k`-th order Lagrangians.
- `ClassicalFieldTheory.Local.Lagrangian.coordDeriv` : coordinate derivatives with respect to the
  jet coordinates `u^a_I`.
- `ClassicalFieldTheory.Local.Lagrangian.SmoothInCoordinates` : the combined public regularity
  package for smooth local lagrangians in explicit jet coordinates.
- `ClassicalFieldTheory.Local.Lagrangian.alongField` : evaluate a local Lagrangian along the jets
  of a field.

## iii. Table of contents

- A. Local Lagrangians
- B. Regularity packages
- C. Evaluation along a field

## iv. References

* J. Cortés and A. Haupt, Lecture Notes on Mathematical Methods of Classical Physics, Chapter 5.
  [ref: cortes_haupt_2016]
-/

@[expose] public section

open Physlib
open scoped BigOperators ContDiff

namespace ClassicalFieldTheory
namespace Local

/-!
## A. Local Lagrangians

-/

/-- A local `k`-th order Lagrangian for fields `Space d → EuclideanSpace ℝ (Fin m)`. -/
structure Lagrangian (d m k : ℕ) where
  /-- The underlying jet-dependent function. -/
  toFun : JetPoint d m k → ℝ
  /-- The derivatives of the Lagrangian with respect to the jet coordinates `u^a_I`. -/
  coordDeriv : DerivativeIndex d k → Fin m → JetPoint d m k → ℝ
  /-- The first derivative of the Lagrangian along affine lines in the jet-fiber coordinates is
  given by the pairing with the coordinate derivatives. -/
  hasDerivAlongFiber :
    ∀ J : JetPoint d m k, ∀ V : JetFiberData d m k,
      HasDerivAt (fun s : ℝ => toFun (J.lineMap V s))
        (∑ I : DerivativeIndex d k, ∑ a : Fin m, coordDeriv I a J * V.coord I a) 0

namespace Lagrangian

variable {d m k : ℕ}

instance : CoeFun (Lagrangian d m k) (fun _ => JetPoint d m k → ℝ) where
  coe L := L.toFun

/-- The derivative of `L` along the fiber-jet direction `V` based at `J`. -/
noncomputable def fiberDerivative (L : Lagrangian d m k) (J : JetPoint d m k)
    (V : JetFiberData d m k) : ℝ :=
  ∑ I : DerivativeIndex d k, ∑ a : Fin m, L.coordDeriv I a J * V.coord I a

lemma hasDerivAt_lineMap (L : Lagrangian d m k) (J : JetPoint d m k) (V : JetFiberData d m k) :
    HasDerivAt (fun s : ℝ => L (J.lineMap V s)) (L.fiberDerivative J V) 0 := by
  simpa [fiberDerivative] using L.hasDerivAlongFiber J V

/-!
## B. Regularity packages

-/

/-- Continuity of a local lagrangian in the explicit local jet coordinates `(x, u^a_I)`. -/
def ContinuousInCoordinates (L : Lagrangian d m k) : Prop :=
  Continuous (fun p : Space d × JetCoordinates d m k =>
    L (JetPoint.ofBaseCoordinates p.1 p.2))

/-- Intrinsic smoothness of the jet-coordinate derivatives of a local Lagrangian in the explicit
local jet coordinates `(x, u^a_I)`. -/
def ContDiffCoordDerivInCoordinates (L : Lagrangian d m k) : Prop :=
  ∀ I : DerivativeIndex d k, ∀ a : Fin m,
    ContDiff ℝ ∞
      (fun p : Space d × JetCoordinates d m k =>
        L.coordDeriv I a (JetPoint.ofBaseCoordinates p.1 p.2))

/-- Public regularity package for a smooth local lagrangian in explicit local jet coordinates:
continuity of the lagrangian itself together with smoothness of all jet-coordinate derivatives. -/
def SmoothInCoordinates (L : Lagrangian d m k) : Prop :=
  L.ContinuousInCoordinates ∧ L.ContDiffCoordDerivInCoordinates

/-- Smoothness of all coefficient functions `x ↦ ∂L/∂u_I^a (j^k f(x))` along a field `f`. -/
def ContDiffCoordDerivAlongField (L : Lagrangian d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m)) : Prop :=
  ∀ I : DerivativeIndex d k, ∀ a : Fin m,
    ContDiff ℝ ∞ (fun x => L.coordDeriv I a (jetAt k f x))

/-- Continuity of the coefficient family `(s, x) ↦ ∂L/∂u_I^a (j^k(F s)(x))` along a
one-parameter family of fields `F : ℝ → Space d → EuclideanSpace ℝ (Fin m)`. -/
def ContinuousCoordDerivAlongFamily (L : Lagrangian d m k)
    (F : ℝ → Space d → EuclideanSpace ℝ (Fin m)) : Prop :=
  ∀ I : DerivativeIndex d k, ∀ a : Fin m,
    Continuous (fun p : ℝ × Space d => L.coordDeriv I a (jetAt k (F p.1) p.2))

lemma continuousAlongField_of_inCoordinates (L : Lagrangian d m k)
    (hcont : ContinuousInCoordinates L) (f : Space d → EuclideanSpace ℝ (Fin m))
    (hf : ContDiff ℝ ∞ f) :
    Continuous (fun x : Space d => L (jetAt k f x)) := by
  exact
    hcont.comp (jetBaseCoordinates_contDiff k f hf).continuous

lemma contDiffCoordDerivAlongField_of_inCoordinates (L : Lagrangian d m k)
    (hcoord : ContDiffCoordDerivInCoordinates L) (f : Space d → EuclideanSpace ℝ (Fin m))
    (hf : ContDiff ℝ ∞ f) :
    ContDiffCoordDerivAlongField L f := by
  intro I a
  have hjet : ContDiff ℝ ∞ (fun x : Space d => (x, jetCoordinatesAt k f x)) :=
    jetBaseCoordinates_contDiff k f hf
  have hcomp :=
    (hcoord I a).comp hjet
  exact hcomp

lemma continuousCoordDerivAlongFamily_of_inCoordinates (L : Lagrangian d m k)
    (hcoord : ContDiffCoordDerivInCoordinates L)
    (F : ℝ → Space d → EuclideanSpace ℝ (Fin m))
    (hjet : Continuous (fun p : ℝ × Space d => (p.2, jetCoordinatesAt k (F p.1) p.2))) :
    ContinuousCoordDerivAlongFamily L F := by
  intro I a
  have hbase :
      Continuous
        (fun p : ℝ × Space d =>
          L.coordDeriv I a (JetPoint.ofBaseCoordinates p.2 (jetCoordinatesAt k (F p.1) p.2))) := by
    exact (hcoord I a).continuous.comp hjet
  simpa only [jetAt_eq_ofBaseCoordinates] using hbase

/-!
## C. Evaluation along a field

-/

/-- Evaluate a local Lagrangian along the `k`-jets of a field. -/
noncomputable def alongField (L : Lagrangian d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m)) : Space d → ℝ :=
  evalOnJet k L f

@[simp]
lemma alongField_apply (L : Lagrangian d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m)) (x : Space d) :
    L.alongField f x = L (jetAt k f x) := rfl

end Lagrangian
end Local
end ClassicalFieldTheory
