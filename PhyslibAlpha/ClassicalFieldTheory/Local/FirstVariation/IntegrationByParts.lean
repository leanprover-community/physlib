/-
Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Jose Fernandez Morales
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.Local.FirstVariation.Support
/-!
# First variation integration by parts

Repeated integration by parts for the local first-variation formula.

## i. Overview

This module contains the repeated integration-by-parts step needed for the local first-variation
formula, together with the termwise and summed packaged versions used later in the
Euler-Lagrange criterion.

## ii. Key results

- `ClassicalFieldTheory.Local.integral_mul_iteratedDeriv_eq_sign`
- `ClassicalFieldTheory.Local.hasTermwiseIntegratedByPartsFormula_of_regular`
- `ClassicalFieldTheory.Local.hasIntegratedByPartsFormula_of_termwise`

## iii. Table of contents

- A. Repeated integration by parts
- B. Termwise formulas

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
## A. Repeated integration by parts

-/

/-- The integration-by-parts step sending the linearized density to the Euler-Lagrange pairing. -/
def HasIntegratedByPartsFormula (L : Lagrangian d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m)) : Prop :=
  ∀ η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m)),
    ∫ x, firstVariationDensity L f η x = firstVariationValue L f η

/-- Termwise integration-by-parts data for the linearized first-variation density. -/
def HasTermwiseIntegratedByPartsFormula (L : Lagrangian d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m)) : Prop :=
  ∀ η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m)),
    ∀ I : DerivativeIndex d k, ∀ a : Fin m,
    Integrable (firstVariationDensityTerm L f η I a) ∧
    Integrable (fun x => eulerLagrangeTerm L I a f x * (η x) a) ∧
    (∫ x, firstVariationDensityTerm L f η I a x)
      = ∫ x, eulerLagrangeTerm L I a f x * (η x) a

private lemma integral_mul_space_deriv_eq_neg_deriv_mul (i : Fin d) {g h : Space d → ℝ}
    (hg : ContDiff ℝ ∞ g) (hh : IsTestFunction h) :
    ∫ x, g x * ∂[i] h x = ∫ x, (-∂[i] g x) * h x := by
  rw [Space.deriv_eq_fderiv_fun, Space.deriv_eq_fderiv_fun]
  calc
    ∫ x, g x * fderiv ℝ h x (Space.basis i)
      = -∫ x, fderiv ℝ g x (Space.basis i) * h x := by
          rw [integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable]
          · simpa [Space.deriv_eq_fderiv_basis] using
              (IsTestFunction.integrable (μ := volume) <|
                IsTestFunction.mul_left (contDiff_space_deriv hg i) hh)
          · simpa [Space.deriv_eq_fderiv_basis] using
              (IsTestFunction.integrable (μ := volume) <|
                IsTestFunction.mul_left hg (isTestFunction_space_deriv hh i))
          · exact IsTestFunction.integrable (μ := volume) <| IsTestFunction.mul_left hg hh
          · intro x hx
            exact Differentiable.differentiableAt (hg.differentiable (by simp))
          · intro x hx
            exact Differentiable.differentiableAt hh.differentiable
    _ = ∫ x, (-fderiv ℝ g x (Space.basis i)) * h x := by
          rw [← integral_neg]
          congr with x
          ring

private lemma integral_mul_iteratedDerivList_eq_sign (L : List (Fin d)) {g h : Space d → ℝ}
    (hg : ContDiff ℝ ∞ g) (hh : IsTestFunction h) :
    ∫ x, g x * L.foldr (fun i f => ∂[i] f) h x =
      ∫ x, (((-1 : ℝ) ^ L.length) * L.foldr (fun i f => ∂[i] f) g x) * h x := by
  induction L generalizing g h with
  | nil =>
      simp
  | cons i L ih =>
      have hdg : ContDiff ℝ ∞ (∂[i] g) := by
        exact contDiff_space_deriv hg i
      have hhL : IsTestFunction (L.foldr (fun j f => ∂[j] f) h) := by
        exact iteratedDerivList_isTestFunction L hh
      calc
        ∫ x, g x * ∂[i] (L.foldr (fun j f => ∂[j] f) h) x
          = ∫ x, (-∂[i] g x) * L.foldr (fun j f => ∂[j] f) h x := by
              exact integral_mul_space_deriv_eq_neg_deriv_mul i hg hhL
        _ = -∫ x, ∂[i] g x * L.foldr (fun j f => ∂[j] f) h x := by
              rw [← integral_neg]
              congr with x
              ring
        _ = -∫ x, (((-1 : ℝ) ^ L.length) *
            L.foldr (fun j f => ∂[j] f) (∂[i] g) x) * h x := by
              rw [ih hdg hh]
        _ = ∫ x, (((-1 : ℝ) ^ (L.length + 1)) *
            ∂[i] (L.foldr (fun j f => ∂[j] f) g) x) * h x := by
              rw [← integral_neg]
              congr with x
              rw [iteratedDerivList_commute_deriv L i hg, pow_succ, mul_assoc]
              ring

/-- Repeated integration by parts for iterated coordinate derivatives against a test function. -/
lemma integral_mul_iteratedDeriv_eq_sign {g h : Space d → ℝ} (I : MultiIndex d)
    (hg : ContDiff ℝ ∞ g) (hh : IsTestFunction h) :
    ∫ x, g x * ∂^[I] h x =
      ∫ x, (((-1 : ℝ) ^ I.order) * ∂^[I] g x) * h x := by
  simpa [Space.iteratedDeriv, Physlib.MultiIndex.length_toList] using
    integral_mul_iteratedDerivList_eq_sign I.toList hg hh

/-!
## B. Termwise formulas

-/

/-- Concrete termwise integration by parts for the first-variation density, assuming the jet
coordinate coefficient functions are smooth along the field. -/
lemma hasTermwiseIntegratedByPartsFormula_of_contDiff_coordDeriv
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m))
    (hcoeff : ∀ I : DerivativeIndex d k, ∀ a : Fin m,
      ContDiff ℝ ∞ (fun x => L.coordDeriv I a (jetAt k f x))) :
    HasTermwiseIntegratedByPartsFormula L f := by
  intro η I a
  let g : Space d → ℝ := fun x => L.coordDeriv I a (jetAt k f x)
  let h : Space d → ℝ := fun x => (η.toFun x) a
  have hg : ContDiff ℝ ∞ g := hcoeff I a
  have hh : IsTestFunction h := by
    simpa [h] using η.coord_euclidean a
  constructor
  · simpa [g, h, firstVariationDensityTerm, Space.iteratedDeriv] using
      firstVariationDensityTerm_integrable_of_continuous_coordDeriv L f η I a hg.continuous
  constructor
  · have htd : ContDiff ℝ ∞ (∂^[I.1] g) :=
      Space.iteratedDeriv_contDiff I.1 hg
    have htdSign : ContDiff ℝ ∞
        (fun x => ((-1 : ℝ) ^ I.1.order) * ∂^[I.1] g x) := by
      apply ContDiff.mul
      · fun_prop
      · exact htd
    exact
      (IsTestFunction.integrable (μ := volume) <|
        IsTestFunction.mul_left htdSign hh)
  · exact
      integral_mul_iteratedDeriv_eq_sign I.1 hg hh

lemma hasTermwiseIntegratedByPartsFormula_of_regular
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m))
    (hcoeff : Lagrangian.ContDiffCoordDerivAlongField L f) :
    HasTermwiseIntegratedByPartsFormula L f := by
  exact hasTermwiseIntegratedByPartsFormula_of_contDiff_coordDeriv L f hcoeff

private lemma integral_firstVariationDensity_eq_termwise_sum
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m))
    (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m)))
    (hterm : HasTermwiseIntegratedByPartsFormula L f) :
    ∫ x, firstVariationDensity L f η x =
      ∑ I : DerivativeIndex d k, ∑ a : Fin m,
        ∫ x, firstVariationDensityTerm L f η I a x := by
  calc
    ∫ x, firstVariationDensity L f η x
      = ∫ x, ∑ I : DerivativeIndex d k, ∑ a : Fin m,
        firstVariationDensityTerm L f η I a x := by
          rfl
    _ = ∑ I : DerivativeIndex d k, ∑ a : Fin m,
        ∫ x, firstVariationDensityTerm L f η I a x := by
          rw [MeasureTheory.integral_finsetSum Finset.univ
            (fun I _ => integrable_finsetSum Finset.univ (fun a _ => (hterm η I a).1))]
          apply Finset.sum_congr rfl
          intro I _
          rw [MeasureTheory.integral_finsetSum Finset.univ (fun a _ => (hterm η I a).1)]

private lemma integral_eulerLagrange_termwise_sum_eq_pairing
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m))
    (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m)))
    (hterm : HasTermwiseIntegratedByPartsFormula L f) :
    ∑ I : DerivativeIndex d k, ∑ a : Fin m, ∫ x, eulerLagrangeTerm L I a f x * (η x) a
      = firstVariationValue L f η := by
  calc
    ∑ I : DerivativeIndex d k, ∑ a : Fin m, ∫ x, eulerLagrangeTerm L I a f x * (η x) a
      = ∫ x, ∑ I : DerivativeIndex d k, ∑ a : Fin m,
        eulerLagrangeTerm L I a f x * (η x) a := by
          calc
            ∑ I : DerivativeIndex d k, ∑ a : Fin m,
                ∫ x, eulerLagrangeTerm L I a f x * (η x) a
              =
                ∑ I : DerivativeIndex d k,
                  ∫ x, ∑ a : Fin m, eulerLagrangeTerm L I a f x * (η x) a := by
                  apply Finset.sum_congr rfl
                  intro I _
                  rw [← MeasureTheory.integral_finsetSum Finset.univ
                    (fun a _ => (hterm η I a).2.1)]
            _ =
                ∫ x, ∑ I : DerivativeIndex d k,
                  ∑ a : Fin m, eulerLagrangeTerm L I a f x * (η x) a := by
                  rw [← MeasureTheory.integral_finsetSum Finset.univ
                    (fun I _ => integrable_finsetSum Finset.univ (fun a _ => (hterm η I a).2.1))]
    _ = ∫ x, ⟪eulerLagrangeOp L f x, η x⟫_ℝ := by
          apply integral_congr_ae
          filter_upwards with x
          rw [PiLp.inner_apply]
          simp_rw [eulerLagrangeOp_apply, eulerLagrangeComponent_apply]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro a _
          rw [show ⟪∑ I : DerivativeIndex d k, eulerLagrangeTerm L I a f x,
              (η.toFun x).ofLp a⟫_ℝ =
              (∑ I : DerivativeIndex d k, eulerLagrangeTerm L I a f x) *
                (η.toFun x).ofLp a by
            norm_num [inner, Inner.inner]
            ring]
          rw [← Finset.sum_mul]
    _ = firstVariationValue L f η := by
          rfl

lemma hasIntegratedByPartsFormula_of_termwise (L : Lagrangian d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m))
    (hterm : HasTermwiseIntegratedByPartsFormula L f) :
    HasIntegratedByPartsFormula L f := by
  intro η
  calc
    ∫ x, firstVariationDensity L f η x
      = ∑ I : DerivativeIndex d k, ∑ a : Fin m,
        ∫ x, firstVariationDensityTerm L f η I a x := by
          exact integral_firstVariationDensity_eq_termwise_sum L f η hterm
    _ = ∑ I : DerivativeIndex d k, ∑ a : Fin m,
        ∫ x, eulerLagrangeTerm L I a f x * (η x) a := by
          apply Finset.sum_congr rfl
          intro I _
          apply Finset.sum_congr rfl
          intro a _
          exact (hterm η I a).2.2
    _ = firstVariationValue L f η := by
          exact integral_eulerLagrange_termwise_sum_eq_pairing L f η hterm

end Local
end ClassicalFieldTheory
