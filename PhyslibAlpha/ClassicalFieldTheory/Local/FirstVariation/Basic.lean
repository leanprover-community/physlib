/-
Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Jose Fernandez Morales
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.Local.EulerLagrange
public import Physlib.Mathematics.VariationalCalculus.Basic
/-!
# First variation core objects

The linearized first-variation density and its Euler-Lagrange pairing.

## i. Overview

This module contains the basic objects used throughout the local first-variation theory:
the linearized density before integration by parts and its Euler-Lagrange pairing.

## ii. Key results

- `ClassicalFieldTheory.Local.firstVariationDensityTerm`
- `ClassicalFieldTheory.Local.firstVariationDensity`
- `ClassicalFieldTheory.Local.firstVariationValue`

## iii. Table of contents

- A. First-variation values

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
## A. First-variation values

-/

/-- A single term in the linearized first-variation density before integration by parts. -/
noncomputable def firstVariationDensityTerm (L : Lagrangian d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m))
    (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m))) (I : DerivativeIndex d k)
    (a : Fin m) :
    Space d → ℝ :=
  fun x => L.coordDeriv I a (jetAt k f x) * ∂^[I.1] (fun y => (η y) a) x

/-- The pointwise linearized first-variation density before integration by parts. -/
noncomputable def firstVariationDensity (L : Lagrangian d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m))
    (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m))) : Space d → ℝ :=
  fun x => ∑ I : DerivativeIndex d k, ∑ a : Fin m, firstVariationDensityTerm L f η I a x

/-- The value predicted by the first-variation formula for an admissible variation. -/
noncomputable def firstVariationValue (L : Lagrangian d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m))
    (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m))) : ℝ :=
  ∫ x, ⟪eulerLagrangeOp L f x, η x⟫_ℝ

@[simp]
lemma firstVariationDensityTerm_apply (L : Lagrangian d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m))
    (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m))) (I : DerivativeIndex d k)
    (a : Fin m) (x : Space d) :
    firstVariationDensityTerm L f η I a x =
      L.coordDeriv I a (jetAt k f x) * ∂^[I.1] (fun y => (η y) a) x := rfl

@[simp]
lemma firstVariationDensity_apply (L : Lagrangian d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m))
    (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m))) (x : Space d) :
    firstVariationDensity L f η x =
      ∑ I : DerivativeIndex d k, ∑ a : Fin m, firstVariationDensityTerm L f η I a x := rfl

@[simp]
lemma firstVariationValue_eq_integral (L : Lagrangian d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m))
    (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m))) :
    firstVariationValue L f η = ∫ x, ⟪eulerLagrangeOp L f x, η x⟫_ℝ := rfl

lemma firstVariationValue_eq_zero_of_eulerLagrange_zero
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m))
    (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m))) (hEuler : eulerLagrangeOp L f = 0) :
    firstVariationValue L f η = 0 := by
  unfold firstVariationValue
  rw [hEuler]
  simp

end Local
end ClassicalFieldTheory
