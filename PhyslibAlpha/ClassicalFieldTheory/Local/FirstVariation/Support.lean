/-
Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Jose Fernandez Morales
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.Local.FirstVariation.Basic
/-!
# First variation support lemmas

Support lemmas for the first variation: varied fields, test functions, varied jet coordinates.

## i. Overview

This module collects the reusable support lemmas used by the analytic part of the local
first-variation proof: basic identities for varied fields, iterated derivative regularity for
test functions, and continuity of the varied local-jet coordinate map.

## ii. Key results

- `ClassicalFieldTheory.Local.variedField_zero`
- `ClassicalFieldTheory.Local.variedField_variedField`

## iii. Table of contents

- A. Varied fields
- B. Iterated derivative support lemmas
- C. Varied local-jet coordinates

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
## A. Varied fields

-/

@[simp]
lemma variedField_zero (f : Space d → EuclideanSpace ℝ (Fin m))
    (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m))) :
    variedField f η 0 = f := by
  funext x
  simp [variedField]

@[simp]
lemma variedField_variedField (f : Space d → EuclideanSpace ℝ (Fin m))
    (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m)))
    (s t : ℝ) :
    variedField (variedField f η s) η t = variedField f η (s + t) := by
  funext x
  simp [variedField, add_assoc, add_smul]

/-!
## B. Iterated derivative support lemmas

-/

lemma contDiff_space_deriv {g : Space d → ℝ} (hg : ContDiff ℝ ∞ g)
    (i : Fin d) : ContDiff ℝ ∞ (∂[i] g) := by
  have hfamily : ContDiff ℝ ∞ (fun x : Space d => fun j : Fin d => ∂[j] g x) := by
    simpa using (Space.deriv_contDiff (n := ∞) hg)
  exact (contDiff_apply ℝ ℝ i).comp hfamily

lemma isTestFunction_space_deriv {g : Space d → ℝ} (hg : IsTestFunction g) (i : Fin d) :
    IsTestFunction (∂[i] g) := by
  simpa [Space.deriv_eq_fderiv_fun] using IsTestFunction.fderiv_apply hg (Space.basis i)

lemma iteratedDerivList_contDiff (L : List (Fin d)) {g : Space d → ℝ}
    (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (L.foldr (fun i h => ∂[i] h) g) := by
  induction L generalizing g with
  | nil =>
      simpa using hg
  | cons i L ih =>
      have htail : ContDiff ℝ ∞ (L.foldr (fun j h => ∂[j] h) g) := ih hg
      exact contDiff_space_deriv htail i

lemma iteratedDerivList_isTestFunction (L : List (Fin d)) {g : Space d → ℝ}
    (hg : IsTestFunction g) :
    IsTestFunction (L.foldr (fun i h => ∂[i] h) g) := by
  induction L generalizing g with
  | nil =>
      simpa using hg
  | cons i L ih =>
      simp only [List.foldr]
      exact isTestFunction_space_deriv (ih hg) i

lemma iteratedDerivList_commute_deriv (L : List (Fin d)) (i : Fin d)
    {g : Space d → ℝ} (hg : ContDiff ℝ ∞ g) :
    L.foldr (fun j h => ∂[j] h) (∂[i] g) = ∂[i] (L.foldr (fun j h => ∂[j] h) g) := by
  induction L generalizing g with
  | nil =>
      rfl
  | cons j L ih =>
      simp only [List.foldr]
      rw [ih hg]
      rw [Space.deriv_commute (u := j) (v := i)]
      have h2 : ContDiff ℝ (2 : ℕ∞) (L.foldr (fun j h => ∂[j] h) g) := by
        exact (iteratedDerivList_contDiff L hg).of_le (by
          exact WithTop.coe_le_coe.mpr le_top)
      exact h2

lemma iteratedDeriv_coord_isTestFunction (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m)))
    (I : DerivativeIndex d k) (a : Fin m) :
    IsTestFunction (fun x => ∂^[I.1] (fun y => (η y) a) x) := by
  simpa [Space.iteratedDeriv, Space.coord] using
    iteratedDerivList_isTestFunction I.1.toList (η.coord_euclidean a)

lemma firstVariationDensityTerm_integrable_of_continuous_coordDeriv
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m))
    (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m)))
    (I : DerivativeIndex d k) (a : Fin m)
    (hcont : Continuous (fun x : Space d =>
      L.coordDeriv I a (jetAt k f x))) :
    Integrable (firstVariationDensityTerm L f η I a) := by
  let ψ : Space d → ℝ := fun x => ∂^[I.1] (fun y => (η y) a) x
  have hψ : IsTestFunction ψ := iteratedDeriv_coord_isTestFunction η I a
  have hψcont : Continuous ψ := hψ.contDiff.continuous
  have htermCont : Continuous (fun x => L.coordDeriv I a (jetAt k f x) * ψ x) :=
    hcont.mul hψcont
  have hsupp : HasCompactSupport (fun x => L.coordDeriv I a (jetAt k f x) * ψ x) :=
    HasCompactSupport.mul_left hψ.supp
  exact
    htermCont.integrable_of_hasCompactSupport hsupp

/-!
## C. Varied local-jet coordinates

-/

lemma continuous_jetBaseCoordinates_variedField
    (k : ℕ) (f : Space d → EuclideanSpace ℝ (Fin m))
    (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m)))
    (hf : ContDiff ℝ ∞ f) :
    Continuous
      (fun p : ℝ × Space d => (p.2, jetCoordinatesAt k (variedField f η p.1) p.2)) := by
  have hfjet : Continuous (jetCoordinatesAt k f) :=
    (jetCoordinatesAt_contDiff k f hf).continuous
  have hηjet : Continuous (jetCoordinatesAt k η) :=
    (jetCoordinatesAt_contDiff k η η.isTestFunction.contDiff).continuous
  have hcoord :
      Continuous
        (fun p : ℝ × Space d =>
          jetCoordinatesAt k f p.2 + p.1 • jetCoordinatesAt k η p.2) := by
    exact (hfjet.comp continuous_snd).add (continuous_fst.smul (hηjet.comp continuous_snd))
  have hpair :
      Continuous
        (fun p : ℝ × Space d =>
          (p.2, jetCoordinatesAt k f p.2 + p.1 • jetCoordinatesAt k η p.2)) := by
    exact Continuous.prodMk continuous_snd hcoord
  have heq :
      (fun p : ℝ × Space d => (p.2, jetCoordinatesAt k (variedField f η p.1) p.2)) =
      (fun p : ℝ × Space d =>
        (p.2, jetCoordinatesAt k f p.2 + p.1 • jetCoordinatesAt k η p.2)) := by
    funext p
    congr 1
    exact
      (jetCoordinatesAt_add_smul k f η p.2 p.1 hf η.isTestFunction.contDiff)
  rw [heq]
  exact hpair

end Local
end ClassicalFieldTheory
