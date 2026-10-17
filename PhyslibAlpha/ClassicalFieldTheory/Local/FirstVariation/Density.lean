/-
Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Jose Fernandez Morales
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.Local.FirstVariation.Support
public import Mathlib.Analysis.Calculus.ParametricIntegral
/-!
# First variation density formulas

Differentiation of the varied action density, pointwise and under the integral sign.

## i. Overview

This module contains the pointwise and integral first-variation formulas before integration by
parts: differentiation of the varied action density, dominated differentiation under the integral,
and the corresponding packaged hypotheses.

## ii. Key results

- `ClassicalFieldTheory.Local.hasPointwiseLinearizedDensityFormula_of_contDiff`
- `ClassicalFieldTheory.Local.hasActionVariationDerivativeUnderIntegral_of_contDiff_of_regular`

## iii. Table of contents

- A. Differentiation under the integral sign
- B. Pointwise linearization

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
## A. Differentiation under the integral sign

-/

/-- Differentiation of the varied action under the integral sign, packaged as a hypothesis. -/
def HasActionVariationDerivativeUnderIntegral (L : Lagrangian d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m)) :
    Prop :=
  ∀ η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m)), HasFiniteActionVariation L f η →
    HasDerivAt (actionVariation L f η)
      (∫ x, deriv (fun s : ℝ => actionDensity L (variedField f η s) x) 0) 0

/-- Pointwise linearization of the action density before integration by parts. -/
def HasPointwiseLinearizedDensityFormula (L : Lagrangian d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m)) : Prop :=
  ∀ η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m)), ∀ x : Space d,
    deriv (fun s : ℝ => actionDensity L (variedField f η s) x) 0 =
      firstVariationDensity L f η x

/-- A direct bridge from Mathlib's dominated differentiation-under-the-integral theorem to the
local action variation. This isolates the measure-theoretic input needed to prove
`HasActionVariationDerivativeUnderIntegral`. -/
lemma actionVariation_hasDerivAt_of_dominated_loc_of_deriv_le
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m))
    (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m)))
    {F' : ℝ → Space d → ℝ} {bound : Space d → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hmeas :
      ∀ᶠ s in nhds (0 : ℝ),
        AEStronglyMeasurable (actionDensity L (variedField f η s)) volume)
    (hfinite0 : Integrable (actionDensity L (variedField f η 0)))
    (hF'_meas : AEStronglyMeasurable (F' 0) volume)
    (hbound :
      ∀ᵐ x ∂volume, ∀ s ∈ Metric.ball (0 : ℝ) ε, ‖F' s x‖ ≤ bound x)
    (hbound_int : Integrable bound volume)
    (hderiv :
      ∀ᵐ x ∂volume, ∀ s ∈ Metric.ball (0 : ℝ) ε,
        HasDerivAt (fun r : ℝ => actionDensity L (variedField f η r) x) (F' s x) s) :
    HasDerivAt (actionVariation L f η) (∫ x, F' 0 x) 0 := by
  have hs : Metric.ball (0 : ℝ) ε ∈ nhds (0 : ℝ) := Metric.ball_mem_nhds _ hε
  exact
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (F := fun s x => actionDensity L (variedField f η s) x)
      (x₀ := (0 : ℝ)) (s := Metric.ball (0 : ℝ) ε) hs
      hmeas hfinite0 hF'_meas hbound hbound_int hderiv).2

/-- A dominated bound for the pointwise first variation along the varied-field family near
`s = 0`. This packages the analytic domination needed to differentiate the action under the
integral sign. -/
def HasDominatedVariationDerivativeNear (L : Lagrangian d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m))
    (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m))) : Prop :=
  ∃ ε > 0, ∃ bound : Space d → ℝ,
    AEStronglyMeasurable (firstVariationDensity L f η) volume ∧
    Integrable bound volume ∧
    ∀ᵐ x ∂volume, ∀ s ∈ Metric.ball (0 : ℝ) ε,
      ‖firstVariationDensity L (variedField f η s) η x‖ ≤ bound x

private lemma continuous_coordDeriv_at_zero
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m))
    (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m)))
    (hcont : ∀ I : DerivativeIndex d k, ∀ a : Fin m,
      Continuous (fun p : ℝ × Space d =>
        L.coordDeriv I a (jetAt k (variedField f η p.1) p.2)))
    (I : DerivativeIndex d k) (a : Fin m) :
    Continuous (fun x : Space d => L.coordDeriv I a (jetAt k f x)) := by
  have hpair : Continuous (fun x : Space d => ((0 : ℝ), x)) := by
    fun_prop
  have hcoeff0 :
      Continuous (fun x : Space d => L.coordDeriv I a (jetAt k (variedField f η 0) x)) := by
    exact (hcont I a).comp hpair
  simpa [variedField_zero] using hcoeff0

private lemma firstVariationDensityTerm_norm_le_of_coeff_bound
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m))
    (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m)))
    (ψ : DerivativeIndex d k → Fin m → Space d → ℝ)
    (hψ : ∀ I : DerivativeIndex d k, ∀ a : Fin m, ∀ x : Space d,
      ψ I a x = ∂^[I.1] (fun y => (η y) a) x)
    (C : DerivativeIndex d k → Fin m → ℝ)
    (K : DerivativeIndex d k → Fin m → Set (Space d))
    (hKzero : ∀ I : DerivativeIndex d k, ∀ a : Fin m, ∀ x, x ∉ K I a → ψ I a x = 0)
    (hC : ∀ I : DerivativeIndex d k, ∀ a : Fin m,
      ∀ p ∈ Metric.closedBall (0 : ℝ) 1 ×ˢ K I a,
        ‖L.coordDeriv I a (jetAt k (variedField f η p.1) p.2)‖ ≤ C I a)
    {x : Space d} {s : ℝ} (hs : s ∈ Metric.ball (0 : ℝ) 1)
    (I : DerivativeIndex d k) (a : Fin m) :
    ‖firstVariationDensityTerm L (variedField f η s) η I a x‖ ≤ C I a * ‖ψ I a x‖ := by
  by_cases hx : x ∈ K I a
  · have hs' : s ∈ Metric.closedBall (0 : ℝ) 1 := Metric.ball_subset_closedBall hs
    have hcoeff := hC I a (s, x) ⟨hs', hx⟩
    calc
      ‖firstVariationDensityTerm L (variedField f η s) η I a x‖
        = ‖L.coordDeriv I a (jetAt k (variedField f η s) x) * ψ I a x‖ := by
            rw [hψ I a x]
            simp [firstVariationDensityTerm]
      _ = ‖L.coordDeriv I a (jetAt k (variedField f η s) x)‖ * ‖ψ I a x‖ := by
            rw [norm_mul]
      _ ≤ C I a * ‖ψ I a x‖ := by
            exact mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)
  · have hψzero : ψ I a x = 0 := hKzero I a x hx
    rw [hψ I a x] at hψzero
    rw [hψ I a x]
    simp [firstVariationDensityTerm, hψzero]

private lemma norm_firstVariationDensity_le_bound
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m))
    (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m)))
    (ψ : DerivativeIndex d k → Fin m → Space d → ℝ)
    (hψ : ∀ I : DerivativeIndex d k, ∀ a : Fin m, ∀ x : Space d,
      ψ I a x = ∂^[I.1] (fun y => (η y) a) x)
    (C : DerivativeIndex d k → Fin m → ℝ)
    (K : DerivativeIndex d k → Fin m → Set (Space d))
    (hKzero : ∀ I : DerivativeIndex d k, ∀ a : Fin m, ∀ x, x ∉ K I a → ψ I a x = 0)
    (hC : ∀ I : DerivativeIndex d k, ∀ a : Fin m,
      ∀ p ∈ Metric.closedBall (0 : ℝ) 1 ×ˢ K I a,
        ‖L.coordDeriv I a (jetAt k (variedField f η p.1) p.2)‖ ≤ C I a)
    {x : Space d} {s : ℝ} (hs : s ∈ Metric.ball (0 : ℝ) 1) :
    ‖firstVariationDensity L (variedField f η s) η x‖
      ≤ ∑ I : DerivativeIndex d k, ∑ a : Fin m, C I a * ‖ψ I a x‖ := by
  have houter :
      ‖∑ I : DerivativeIndex d k, ∑ a : Fin m,
          firstVariationDensityTerm L (variedField f η s) η I a x‖
        ≤ ∑ I : DerivativeIndex d k, ‖∑ a : Fin m,
            firstVariationDensityTerm L (variedField f η s) η I a x‖ := by
    exact norm_sum_le _ _
  calc
    ‖firstVariationDensity L (variedField f η s) η x‖
      = ‖∑ I : DerivativeIndex d k, ∑ a : Fin m,
          firstVariationDensityTerm L (variedField f η s) η I a x‖ := by
            simp [firstVariationDensity]
    _ ≤ ∑ I : DerivativeIndex d k, ‖∑ a : Fin m,
          firstVariationDensityTerm L (variedField f η s) η I a x‖ := houter
    _ ≤ ∑ I : DerivativeIndex d k, ∑ a : Fin m,
          ‖firstVariationDensityTerm L (variedField f η s) η I a x‖ := by
            refine Finset.sum_le_sum ?_
            intro I _
            exact norm_sum_le _ _
    _ ≤ ∑ I : DerivativeIndex d k, ∑ a : Fin m, C I a * ‖ψ I a x‖ := by
            refine Finset.sum_le_sum ?_
            intro I _
            refine Finset.sum_le_sum ?_
            intro a _
            exact firstVariationDensityTerm_norm_le_of_coeff_bound
              L f η ψ hψ C K hKzero hC hs I a

/-- A concrete dominated bound for the varied first-variation density, obtained from continuity of
the jet-coordinate coefficient family in `(s, x)`. The compact support of the iterated derivatives
of the admissible variation supplies the integrable majorant. -/
lemma hasDominatedVariationDerivativeNear_of_continuous_coordDeriv
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m))
    (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m)))
    (hcont : ∀ I : DerivativeIndex d k, ∀ a : Fin m,
      Continuous (fun p : ℝ × Space d =>
        L.coordDeriv I a (jetAt k (variedField f η p.1) p.2))) :
    HasDominatedVariationDerivativeNear L f η := by
  classical
  let ψ : DerivativeIndex d k → Fin m → Space d → ℝ :=
    fun I a x => ∂^[I.1] (fun y => (η y) a) x
  have hψ : ∀ I : DerivativeIndex d k, ∀ a : Fin m, IsTestFunction (ψ I a) := by
    intro I a
    simpa [ψ] using iteratedDeriv_coord_isTestFunction η I a
  have hψ_eval : ∀ I : DerivativeIndex d k, ∀ a : Fin m, ∀ x : Space d,
      ψ I a x = ∂^[I.1] (fun y => (η y) a) x := by
    intro I a x
    rfl
  choose K hKcompact hKzero using fun I : DerivativeIndex d k => fun a : Fin m =>
    exists_compact_iff_hasCompactSupport.mpr (hψ I a).supp
  let C : DerivativeIndex d k → Fin m → ℝ := fun I a =>
    Classical.choose <|
      ((isCompact_closedBall (0 : ℝ) 1).prod (hKcompact I a)).exists_bound_of_continuousOn
        ((hcont I a).continuousOn)
  have hC : ∀ I : DerivativeIndex d k, ∀ a : Fin m,
      ∀ p ∈ Metric.closedBall (0 : ℝ) 1 ×ˢ K I a,
        ‖L.coordDeriv I a (jetAt k (variedField f η p.1) p.2)‖ ≤ C I a := by
    intro I a
    simpa [C] using Classical.choose_spec
      (((isCompact_closedBall (0 : ℝ) 1).prod (hKcompact I a)).exists_bound_of_continuousOn
        ((hcont I a).continuousOn))
  let bound : Space d → ℝ :=
    fun x => ∑ I : DerivativeIndex d k, ∑ a : Fin m, C I a * ‖ψ I a x‖
  have hbound_int : Integrable bound volume := by
    refine integrable_finsetSum Finset.univ ?_
    intro I _
    refine integrable_finsetSum Finset.univ ?_
    intro a _
    exact ((hψ I a).integrable (μ := volume)).norm.const_mul (C I a)
  have hfirst_int :
      Integrable (firstVariationDensity L f η) volume := by
    refine integrable_finsetSum Finset.univ ?_
    intro I _
    refine integrable_finsetSum Finset.univ ?_
    intro a _
    have hcoeff0 :
        Continuous (fun x : Space d => L.coordDeriv I a (jetAt k f x)) :=
      continuous_coordDeriv_at_zero L f η hcont I a
    exact firstVariationDensityTerm_integrable_of_continuous_coordDeriv L f η I a hcoeff0
  have hbound :
      ∀ x : Space d, ∀ s ∈ Metric.ball (0 : ℝ) 1,
        ‖firstVariationDensity L (variedField f η s) η x‖ ≤ bound x := by
    intro x s hs
    simpa [bound] using norm_firstVariationDensity_le_bound
      L f η ψ hψ_eval C K hKzero hC hs
  refine ⟨1, zero_lt_one, bound, hfirst_int.aestronglyMeasurable, hbound_int, ?_⟩
  exact Filter.Eventually.of_forall hbound

/-!
## B. Pointwise linearization

-/

lemma hasDerivAt_actionDensity_variedField_zero_of_contDiff
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m)) (hf : ContDiff ℝ ∞ f) :
    ∀ η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m)), ∀ x : Space d,
      HasDerivAt (fun s : ℝ => actionDensity L (variedField f η s) x)
        (firstVariationDensity L f η x) 0 := by
  intro η x
  have hjet :
      ∀ s : ℝ, jetAt k (variedField f η s) x =
        (jetAt k f x).lineMap (jetDirectionAt k η x) s := by
    intro s
    exact jetAt_add_smul k f η x s hf η.isTestFunction.contDiff
  have hfun :
      (fun s : ℝ => actionDensity L (variedField f η s) x) =
        fun s : ℝ => L ((jetAt k f x).lineMap (jetDirectionAt k η x) s) := by
    funext s
    rw [actionDensity_apply]
    simp [hjet s]
  rw [hfun]
  simpa [Lagrangian.fiberDerivative, firstVariationDensity, firstVariationDensityTerm,
    jetDirectionAt_coord] using
    (L.hasDerivAt_lineMap (jetAt k f x) (jetDirectionAt k η x))

lemma hasDerivAt_actionDensity_variedField_of_contDiff
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m)) (hf : ContDiff ℝ ∞ f)
    (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m))) (x : Space d) (s : ℝ) :
    HasDerivAt (fun r : ℝ => actionDensity L (variedField f η r) x)
      (firstVariationDensity L (variedField f η s) η x) s := by
  have hzero :
      HasDerivAt (fun t : ℝ => actionDensity L (variedField (variedField f η s) η t) x)
        (firstVariationDensity L (variedField f η s) η x) 0 := by
    exact hasDerivAt_actionDensity_variedField_zero_of_contDiff L (variedField f η s)
      (variedField_contDiff f η s hf) η x
  have hshift :
      HasDerivAt (fun t : ℝ => actionDensity L (variedField f η (t + s)) x)
        (firstVariationDensity L (variedField f η s) η x) 0 := by
    simpa [variedField_variedField, add_comm] using hzero
  let k : ℝ → ℝ := fun t => actionDensity L (variedField f η (t + s)) x
  have hk : HasDerivAt k (firstVariationDensity L (variedField f η s) η x) (s - s) := by
    simpa [k] using hshift
  simpa [k, sub_eq_add_neg, add_assoc] using
    (HasDerivAt.comp_sub_const (f := k) (x := s) (a := s) hk)

lemma hasPointwiseLinearizedDensityFormula_of_contDiff
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m)) (hf : ContDiff ℝ ∞ f) :
    HasPointwiseLinearizedDensityFormula L f := by
  intro η x
  exact (hasDerivAt_actionDensity_variedField_zero_of_contDiff L f hf η x).deriv

lemma hasActionVariationDerivativeUnderIntegral_of_contDiff_of_dominatedVariation
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m)) (hf : ContDiff ℝ ∞ f)
    (hdom : ∀ η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m)),
      HasFiniteActionVariation L f η →
      HasDominatedVariationDerivativeNear L f η) :
    HasActionVariationDerivativeUnderIntegral L f := by
  intro η hη
  rcases hdom η hη with ⟨ε, hε, bound, hF'_meas, hbound_int, hbound⟩
  let F' : ℝ → Space d → ℝ := fun s => firstVariationDensity L (variedField f η s) η
  have hmeas :
      ∀ᶠ s in nhds (0 : ℝ),
        AEStronglyMeasurable (actionDensity L (variedField f η s)) volume := by
    exact Filter.Eventually.of_forall fun s => (hη s).aestronglyMeasurable
  have hderiv :
      ∀ᵐ x ∂volume, ∀ s ∈ Metric.ball (0 : ℝ) ε,
        HasDerivAt (fun r : ℝ => actionDensity L (variedField f η r) x) (F' s x) s := by
    filter_upwards with x
    intro s hs
    simpa [F'] using hasDerivAt_actionDensity_variedField_of_contDiff L f hf η x s
  have hfinite0 : Integrable (actionDensity L (variedField f η 0)) := hη 0
  have hF0_meas : AEStronglyMeasurable (F' 0) volume := by
    simpa [F', firstVariationDensity, firstVariationDensityTerm, variedField] using hF'_meas
  have hresult :=
    actionVariation_hasDerivAt_of_dominated_loc_of_deriv_le L f η hε hmeas hfinite0
      hF0_meas hbound hbound_int hderiv
  have hvalue :
      (∫ x, F' 0 x)
        = ∫ x, deriv (fun s : ℝ => actionDensity L (variedField f η s) x) 0 := by
    apply integral_congr_ae
    filter_upwards with x
    simpa [F', firstVariationDensity, firstVariationDensityTerm, variedField] using
      (hasPointwiseLinearizedDensityFormula_of_contDiff L f hf η x).symm
  rw [hvalue] at hresult
  exact hresult

lemma hasActionVariationDerivativeUnderIntegral_of_contDiff_of_continuous_coordDeriv
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m)) (hf : ContDiff ℝ ∞ f)
    (hcontVar : ∀ η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m)),
      ∀ I : DerivativeIndex d k, ∀ a : Fin m,
      Continuous (fun p : ℝ × Space d =>
        L.coordDeriv I a (jetAt k (variedField f η p.1) p.2))) :
    HasActionVariationDerivativeUnderIntegral L f := by
  refine hasActionVariationDerivativeUnderIntegral_of_contDiff_of_dominatedVariation L f hf ?_
  intro η _hη
  exact hasDominatedVariationDerivativeNear_of_continuous_coordDeriv L f η (hcontVar η)

lemma hasActionVariationDerivativeUnderIntegral_of_contDiff_of_regular
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m)) (hf : ContDiff ℝ ∞ f)
    (hcontVar : ∀ η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m)),
      Lagrangian.ContinuousCoordDerivAlongFamily L (fun s : ℝ => variedField f η s)) :
    HasActionVariationDerivativeUnderIntegral L f := by
  apply hasActionVariationDerivativeUnderIntegral_of_contDiff_of_continuous_coordDeriv L f hf
  intro η I a
  exact hcontVar η I a

end Local
end ClassicalFieldTheory
