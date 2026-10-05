/-
Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Jose Fernandez Morales
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.Local.FirstVariation.Support
/-!
# First variation regularity

Continuity of the Euler-Lagrange operator and smooth regularity from coordinate regularity.

## i. Overview

This module contains regularity consequences used in the local Euler-Lagrange criterion: continuity
of the Euler-Lagrange operator from coefficient regularity, and the bridge from coordinate
regularity of the local Lagrangian to the packaged smooth-regularity statement.

## ii. Key results

- `ClassicalFieldTheory.Local.continuous_eulerLagrangeOp_of_regular`
- `ClassicalFieldTheory.Local.hasSmoothEulerLagrangeRegularity_of_contDiffCoordDerivInCoordinates`

## iii. Table of contents

- A. Continuity of the Euler-Lagrange operator
- B. Smooth regularity in coordinates

## iv. References

* J. Cortés and A. Haupt, Lecture Notes on Mathematical Methods of Classical Physics, Chapter 5,
  Theorem 5.2. [ref: cortes_haupt_2016]
-/

@[expose] public section

open MeasureTheory
open InnerProductSpace
open Physlib
open scoped BigOperators ContDiff

namespace ClassicalFieldTheory
namespace Local

/-!
## A. Continuity of the Euler-Lagrange operator

-/

/-- The combined regularity package currently needed to derive the local Euler-Lagrange
criterion for a field `f`: smooth coefficient functions along `f`, and continuity of the
corresponding coefficient families along every admissible varied-field family based at `f`. -/
def HasEulerLagrangeRegularityAt (L : Lagrangian d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m)) : Prop :=
  Lagrangian.ContDiffCoordDerivAlongField L f ∧
    ∀ η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m)),
      Lagrangian.ContinuousCoordDerivAlongFamily L (fun s : ℝ => variedField f η s)

/-- A local Lagrangian has smooth Euler-Lagrange regularity if every smooth field satisfies the
regularity package currently needed by the local first-variation proof. -/
def HasSmoothEulerLagrangeRegularity (L : Lagrangian d m k) : Prop :=
  ∀ f : Space d → EuclideanSpace ℝ (Fin m),
    ContDiff ℝ ∞ f → HasEulerLagrangeRegularityAt L f

lemma continuous_eulerLagrangeTerm_of_regular
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m))
    (hcoeff : Lagrangian.ContDiffCoordDerivAlongField L f)
    (I : DerivativeIndex d k) (a : Fin m) :
    Continuous (eulerLagrangeTerm L I a f) := by
  have htd : ContDiff ℝ ∞
      (iteratedTotalDerivative k I.1 (L.coordDeriv I a) f) := by
    exact
      Space.iteratedDeriv_contDiff I.1 (hcoeff I a)
  have hsign : ContDiff ℝ ∞
      (fun _ : Space d => (-1 : ℝ) ^ I.1.order) := by
    fun_prop
  exact (hsign.mul htd).continuous

lemma continuous_eulerLagrangeComponent_of_regular
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m))
    (hcoeff : Lagrangian.ContDiffCoordDerivAlongField L f)
    (a : Fin m) :
    Continuous (eulerLagrangeComponent L a f) := by
  refine continuous_finsetSum Finset.univ ?_
  intro I _
  exact continuous_eulerLagrangeTerm_of_regular L f hcoeff I a

lemma continuous_eulerLagrangeOp_of_regular
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m))
    (hcoeff : Lagrangian.ContDiffCoordDerivAlongField L f) :
    Continuous (eulerLagrangeOp L f) := by
  let g : Space d → Fin m → ℝ := fun x a => eulerLagrangeComponent L a f x
  have hg : Continuous g := continuous_pi fun a =>
    continuous_eulerLagrangeComponent_of_regular L f hcoeff a
  change Continuous (fun x : Space d => (WithLp.toLp 2 (g x) : EuclideanSpace ℝ (Fin m)))
  fun_prop

/-!
## B. Smooth regularity in coordinates

-/

theorem hasSmoothEulerLagrangeRegularity_of_contDiffCoordDerivInCoordinates
    (L : Lagrangian d m k) (hcoord : Lagrangian.ContDiffCoordDerivInCoordinates L) :
    HasSmoothEulerLagrangeRegularity L := by
  intro f hf
  refine ⟨Lagrangian.contDiffCoordDerivAlongField_of_inCoordinates L hcoord f hf, ?_⟩
  intro η
  exact Lagrangian.continuousCoordDerivAlongFamily_of_inCoordinates L hcoord
    (fun s : ℝ => variedField f η s)
    (continuous_jetBaseCoordinates_variedField k f η hf)

end Local
end ClassicalFieldTheory
