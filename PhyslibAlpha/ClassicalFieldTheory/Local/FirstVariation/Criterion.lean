/-
Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Jose Fernandez Morales
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.Local.FirstVariation.Density
public import PhyslibAlpha.ClassicalFieldTheory.Local.FirstVariation.IntegrationByParts
public import PhyslibAlpha.ClassicalFieldTheory.Local.FirstVariation.Regularity
/-!
# First variation criteria

Assembles the first-variation formula into Euler-Lagrange criteria for critical fields.

## i. Overview

This module assembles the analytic ingredients of the local first-variation proof into the
packaged first-variation formula and the internal Euler-Lagrange criteria used by the public
facade.

## ii. Key results

- `ClassicalFieldTheory.Local.
  isCritical_iff_eulerLagrange_zero_of_hasFiniteAction_and_continuousInCoordinates`

## iii. Table of contents

- A. First-variation assembly
- B. Intermediate Euler-Lagrange criteria

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
## A. First-variation assembly

-/

/-- Explicit global finiteness hypothesis for all admissible variations. -/
def AllVariationsHaveFiniteAction (L : Lagrangian d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m)) : Prop :=
  ∀ η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m)), HasFiniteActionVariation L f η

/-- The first-variation formula for the local action, packaged as a reusable hypothesis. -/
def HasFirstVariationFormula (L : Lagrangian d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m)) : Prop :=
  ∀ η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m)), HasFiniteActionVariation L f η →
    HasDerivAt (actionVariation L f η) (firstVariationValue L f η) 0

lemma isCritical_of_eulerLagrange_zero (L : Lagrangian d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m))
    (hfirst : HasFirstVariationFormula L f) (hEuler : eulerLagrangeOp L f = 0) :
    IsCritical L f := by
  intro η hη
  have hderiv := hfirst η hη
  have hzero : firstVariationValue L f η = 0 :=
    firstVariationValue_eq_zero_of_eulerLagrange_zero L f η hEuler
  rw [hzero] at hderiv
  exact hderiv

lemma eulerLagrange_zero_of_isCritical (L : Lagrangian d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m))
    (hfirst : HasFirstVariationFormula L f)
    (hfin : AllVariationsHaveFiniteAction L f)
    (hcont : Continuous (eulerLagrangeOp L f))
    (hcrit : IsCritical L f) :
    eulerLagrangeOp L f = 0 := by
  apply fundamental_theorem_of_variational_calculus' (@volume (Space d) _)
  · exact hcont
  · intro g hg
    let η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m)) := ⟨g, hg⟩
    have hηfin : HasFiniteActionVariation L f η := hfin η
    have hfirstη : HasDerivAt (actionVariation L f η) (firstVariationValue L f η) 0 :=
      hfirst η hηfin
    have hcritη : HasDerivAt (actionVariation L f η) 0 0 := hcrit η hηfin
    have hzero : firstVariationValue L f η = 0 := HasDerivAt.unique hfirstη hcritη
    simpa [firstVariationValue, η] using hzero

theorem isCritical_iff_eulerLagrange_zero (L : Lagrangian d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m))
    (hfirst : HasFirstVariationFormula L f)
    (hfin : AllVariationsHaveFiniteAction L f)
    (hcont : Continuous (eulerLagrangeOp L f)) :
    IsCritical L f ↔ eulerLagrangeOp L f = 0 := by
  constructor
  · exact eulerLagrange_zero_of_isCritical L f hfirst hfin hcont
  · exact isCritical_of_eulerLagrange_zero L f hfirst

private lemma hasFirstVariationFormula_of_underIntegral_linearized_and_parts
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m))
    (hint : HasActionVariationDerivativeUnderIntegral L f)
    (hpoint : HasPointwiseLinearizedDensityFormula L f)
    (hibp : HasIntegratedByPartsFormula L f) :
    HasFirstVariationFormula L f := by
  intro η hη
  have hderiv := hint η hη
  have hlinearized :
      (∫ x, deriv (fun s : ℝ => actionDensity L (variedField f η s) x) 0)
        = ∫ x, firstVariationDensity L f η x := by
    apply integral_congr_ae
    filter_upwards with x
    simpa using hpoint η x
  have hvalue :
      (∫ x, deriv (fun s : ℝ => actionDensity L (variedField f η s) x) 0)
        = firstVariationValue L f η := by
    rw [hlinearized, hibp η]
  rw [hvalue] at hderiv
  exact hderiv

private lemma hasFirstVariationFormula_of_contDiff_underIntegral_and_parts
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m)) (hf : ContDiff ℝ ∞ f)
    (hint : HasActionVariationDerivativeUnderIntegral L f)
    (hibp : HasIntegratedByPartsFormula L f) :
    HasFirstVariationFormula L f := by
  exact hasFirstVariationFormula_of_underIntegral_linearized_and_parts L f hint
    (hasPointwiseLinearizedDensityFormula_of_contDiff L f hf) hibp

private lemma hasFirstVariationFormula_of_underIntegral_linearized_and_termwise
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m))
    (hint : HasActionVariationDerivativeUnderIntegral L f)
    (hpoint : HasPointwiseLinearizedDensityFormula L f)
    (hterm : HasTermwiseIntegratedByPartsFormula L f) :
    HasFirstVariationFormula L f := by
  exact hasFirstVariationFormula_of_underIntegral_linearized_and_parts L f hint hpoint
    (hasIntegratedByPartsFormula_of_termwise L f hterm)

private lemma hasFirstVariationFormula_of_contDiff_underIntegral_and_termwise
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m)) (hf : ContDiff ℝ ∞ f)
    (hint : HasActionVariationDerivativeUnderIntegral L f)
    (hterm : HasTermwiseIntegratedByPartsFormula L f) :
    HasFirstVariationFormula L f := by
  exact hasFirstVariationFormula_of_contDiff_underIntegral_and_parts L f hf hint
    (hasIntegratedByPartsFormula_of_termwise L f hterm)

/-!
## B. Intermediate Euler-Lagrange criteria

-/

/-- The local Euler-Lagrange criterion obtained from the packaged analytic ingredients of the
first-variation formula. This is the current formalized form of Theorem 5.2. -/
private theorem isCritical_iff_eulerLagrange_zero_of_underIntegral_linearized_and_parts
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m))
    (hint : HasActionVariationDerivativeUnderIntegral L f)
    (hpoint : HasPointwiseLinearizedDensityFormula L f)
    (hibp : HasIntegratedByPartsFormula L f)
    (hfin : AllVariationsHaveFiniteAction L f)
    (hcont : Continuous (eulerLagrangeOp L f)) :
    IsCritical L f ↔ eulerLagrangeOp L f = 0 := by
  exact isCritical_iff_eulerLagrange_zero L f
    (hasFirstVariationFormula_of_underIntegral_linearized_and_parts L f hint hpoint hibp)
    hfin hcont

/-- Variant of the local Euler-Lagrange criterion where the integration-by-parts input is reduced
to a termwise hypothesis. -/
private theorem isCritical_iff_eulerLagrange_zero_of_underIntegral_linearized_and_termwise
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m))
    (hint : HasActionVariationDerivativeUnderIntegral L f)
    (hpoint : HasPointwiseLinearizedDensityFormula L f)
    (hterm : HasTermwiseIntegratedByPartsFormula L f)
    (hfin : AllVariationsHaveFiniteAction L f)
    (hcont : Continuous (eulerLagrangeOp L f)) :
    IsCritical L f ↔ eulerLagrangeOp L f = 0 := by
  exact isCritical_iff_eulerLagrange_zero_of_underIntegral_linearized_and_parts L f
    hint hpoint (hasIntegratedByPartsFormula_of_termwise L f hterm) hfin hcont

private theorem isCritical_iff_eulerLagrange_zero_of_contDiff_underIntegral_and_termwise
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m)) (hf : ContDiff ℝ ∞ f)
    (hint : HasActionVariationDerivativeUnderIntegral L f)
    (hterm : HasTermwiseIntegratedByPartsFormula L f)
    (hfin : AllVariationsHaveFiniteAction L f)
    (hcont : Continuous (eulerLagrangeOp L f)) :
    IsCritical L f ↔ eulerLagrangeOp L f = 0 := by
  exact isCritical_iff_eulerLagrange_zero L f
    (hasFirstVariationFormula_of_contDiff_underIntegral_and_termwise L f hf hint hterm)
    hfin hcont

private theorem isCritical_iff_eulerLagrange_zero_of_contDiff_continuous_coordDeriv_and_termwise
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m)) (hf : ContDiff ℝ ∞ f)
    (hcontVar : ∀ η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m)),
      ∀ I : DerivativeIndex d k, ∀ a : Fin m,
      Continuous (fun p : ℝ × Space d =>
        L.coordDeriv I a (jetAt k (variedField f η p.1) p.2)))
    (hterm : HasTermwiseIntegratedByPartsFormula L f)
    (hfin : AllVariationsHaveFiniteAction L f)
    (hcont : Continuous (eulerLagrangeOp L f)) :
    IsCritical L f ↔ eulerLagrangeOp L f = 0 := by
  exact isCritical_iff_eulerLagrange_zero_of_contDiff_underIntegral_and_termwise L f hf
    (hasActionVariationDerivativeUnderIntegral_of_contDiff_of_continuous_coordDeriv L f hf
      hcontVar)
    hterm hfin hcont

private theorem isCritical_iff_eulerLagrange_zero_of_contDiff_and_regular
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m)) (hf : ContDiff ℝ ∞ f)
    (hcontVar : ∀ η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m)),
      Lagrangian.ContinuousCoordDerivAlongFamily L (fun s : ℝ => variedField f η s))
    (hcoeff : Lagrangian.ContDiffCoordDerivAlongField L f)
    (hfin : AllVariationsHaveFiniteAction L f)
    (hcont : Continuous (eulerLagrangeOp L f)) :
    IsCritical L f ↔ eulerLagrangeOp L f = 0 := by
  exact isCritical_iff_eulerLagrange_zero_of_contDiff_underIntegral_and_termwise L f hf
    (hasActionVariationDerivativeUnderIntegral_of_contDiff_of_regular L f hf hcontVar)
    (hasTermwiseIntegratedByPartsFormula_of_regular L f hcoeff)
    hfin hcont

private theorem isCritical_iff_eulerLagrange_zero_of_contDiff_and_regularityAt
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m)) (hf : ContDiff ℝ ∞ f)
    (hreg : HasEulerLagrangeRegularityAt L f)
    (hfin : AllVariationsHaveFiniteAction L f)
    (hcont : Continuous (eulerLagrangeOp L f)) :
    IsCritical L f ↔ eulerLagrangeOp L f = 0 := by
  rcases hreg with ⟨hcoeff, hcontVar⟩
  exact isCritical_iff_eulerLagrange_zero_of_contDiff_and_regular L f hf hcontVar hcoeff
    hfin hcont

private theorem isCritical_iff_eulerLagrange_zero_of_contDiff_and_smoothRegularity
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m)) (hf : ContDiff ℝ ∞ f)
    (hreg : HasSmoothEulerLagrangeRegularity L)
    (hfin : AllVariationsHaveFiniteAction L f)
    (hcont : Continuous (eulerLagrangeOp L f)) :
    IsCritical L f ↔ eulerLagrangeOp L f = 0 := by
  exact isCritical_iff_eulerLagrange_zero_of_contDiff_and_regularityAt L f hf (hreg f hf)
    hfin hcont

private theorem isCritical_iff_eulerLagrange_zero_of_contDiff_and_coordinateRegularity
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m)) (hf : ContDiff ℝ ∞ f)
    (hcoord : Lagrangian.ContDiffCoordDerivInCoordinates L)
    (hfin : AllVariationsHaveFiniteAction L f)
    (hcont : Continuous (eulerLagrangeOp L f)) :
    IsCritical L f ↔ eulerLagrangeOp L f = 0 := by
  exact isCritical_iff_eulerLagrange_zero_of_contDiff_and_smoothRegularity L f hf
    (hasSmoothEulerLagrangeRegularity_of_contDiffCoordDerivInCoordinates L hcoord) hfin hcont

private theorem isCritical_iff_eulerLagrange_zero_of_contDiff_and_regularityAt'
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m)) (hf : ContDiff ℝ ∞ f)
    (hreg : HasEulerLagrangeRegularityAt L f)
    (hfin : AllVariationsHaveFiniteAction L f) :
    IsCritical L f ↔ eulerLagrangeOp L f = 0 := by
  rcases hreg with ⟨hcoeff, hcontVar⟩
  exact isCritical_iff_eulerLagrange_zero_of_contDiff_and_regular L f hf hcontVar hcoeff hfin
    (continuous_eulerLagrangeOp_of_regular L f hcoeff)

private theorem isCritical_iff_eulerLagrange_zero_of_contDiff_and_smoothRegularity'
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m)) (hf : ContDiff ℝ ∞ f)
    (hreg : HasSmoothEulerLagrangeRegularity L)
    (hfin : AllVariationsHaveFiniteAction L f) :
    IsCritical L f ↔ eulerLagrangeOp L f = 0 := by
  exact isCritical_iff_eulerLagrange_zero_of_contDiff_and_regularityAt' L f hf (hreg f hf) hfin

private theorem isCritical_iff_eulerLagrange_zero_of_contDiff_and_coordinateRegularity'
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m)) (hf : ContDiff ℝ ∞ f)
    (hcoord : Lagrangian.ContDiffCoordDerivInCoordinates L)
    (hfin : AllVariationsHaveFiniteAction L f) :
    IsCritical L f ↔ eulerLagrangeOp L f = 0 := by
  exact isCritical_iff_eulerLagrange_zero_of_contDiff_and_smoothRegularity' L f hf
    (hasSmoothEulerLagrangeRegularity_of_contDiffCoordDerivInCoordinates L hcoord) hfin

private theorem
    isCritical_iff_eulerLagrange_zero_of_contDiff_and_coordinateRegularity_of_hasFiniteAction
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m)) (hf : ContDiff ℝ ∞ f)
    (hcoord : Lagrangian.ContDiffCoordDerivInCoordinates L)
    (hbase : HasFiniteAction L f)
    (hlocal :
      ∀ η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m)),
        HasCompactlySupportedActionVariationDifference L f η) :
    IsCritical L f ↔ eulerLagrangeOp L f = 0 := by
  have hfin : AllVariationsHaveFiniteAction L f := by
    intro η
    exact hasFiniteActionVariation_of_hasFiniteAction_of_compactlySupportedDifference
      L f η hbase (hlocal η)
  exact isCritical_iff_eulerLagrange_zero_of_contDiff_and_coordinateRegularity' L f hf hcoord hfin

theorem isCritical_iff_eulerLagrange_zero_of_hasFiniteAction_and_continuousInCoordinates
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m)) (hf : ContDiff ℝ ∞ f)
    (hcoord : Lagrangian.ContDiffCoordDerivInCoordinates L)
    (hcontL : Lagrangian.ContinuousInCoordinates L)
    (hbase : HasFiniteAction L f) :
    IsCritical L f ↔ eulerLagrangeOp L f = 0 := by
  exact isCritical_iff_eulerLagrange_zero_of_contDiff_and_coordinateRegularity_of_hasFiniteAction
    L f hf hcoord hbase
    (fun η =>
      hasCompactlySupportedActionVariationDifference_of_continuousInCoordinates
        L hcontL f hf η)

end Local
end ClassicalFieldTheory
