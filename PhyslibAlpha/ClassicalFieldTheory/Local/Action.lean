/-
Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Jose Fernandez Morales
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.Local.Lagrangian
public import PhyslibAlpha.ClassicalFieldTheory.Local.Variation
/-!
# Local action functionals

The local action of a field, its value under admissible variations, and critical fields.

## i. Overview

This module defines the local action functional associated with a local Lagrangian, together with
the first notions needed to talk about variational criticality.

For the first implementation pass, the action is defined directly as the integral of a local
Lagrangian evaluated along jets of a field. The integrability conditions needed for this action and
for its variations are kept explicit in the API.

## ii. Key results

- `ClassicalFieldTheory.Local.actionDensity` : the density associated with a field.
- `ClassicalFieldTheory.Local.action` : the action of a field.
- `ClassicalFieldTheory.Local.HasFiniteAction` : finiteness of the action integral.
- `ClassicalFieldTheory.Local.IsAdmissibleForAction` : symmetric admissibility of a lagrangian and
  field pair for the action functional.
- `ClassicalFieldTheory.Local.actionVariation` : the action under an admissible variation.
- `ClassicalFieldTheory.Local.IsCritical` : vanishing first derivative of the varied action.

## iii. Table of contents

- A. Action densities and action
- B. Action under variation
- C. Critical fields

## iv. References

* J. Cortés and A. Haupt, Lecture Notes on Mathematical Methods of Classical Physics, Chapter 5.
  [ref: cortes_haupt_2016]
-/

@[expose] public section

open MeasureTheory
open Physlib

namespace ClassicalFieldTheory
namespace Local

open scoped ContDiff Topology

/-!
## A. Action densities and action

-/

/-- The action density determined by a local Lagrangian and a field. -/
noncomputable def actionDensity (L : Lagrangian d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m)) : Space d → ℝ :=
  L.alongField f

/-- The integrability condition for the action density of a field. -/
def HasFiniteAction (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m)) : Prop :=
  Integrable (actionDensity L f)

/-- Symmetric admissibility predicate for the action functional: the pair `(L, f)` is admissible
when the field is smooth and the corresponding action density is integrable. -/
def IsAdmissibleForAction (L : Lagrangian d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m)) : Prop :=
  ContDiff ℝ ∞ f ∧ HasFiniteAction L f

/-- The action associated with a local Lagrangian. -/
noncomputable def action (L : Lagrangian d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m)) : ℝ :=
  ∫ x, actionDensity L f x

@[simp]
lemma actionDensity_apply (L : Lagrangian d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m)) (x : Space d) :
    actionDensity L f x = L (jetAt k f x) := rfl

@[simp]
lemma action_eq_integral (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m)) :
    action L f = ∫ x, actionDensity L f x := rfl

/-!
## B. Action under variation

-/

/-- The field obtained by varying `f` in the direction `η` with parameter `s`. -/
noncomputable def variedField (f : Space d → EuclideanSpace ℝ (Fin m))
    (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m)))
    (s : ℝ) :
    Space d → EuclideanSpace ℝ (Fin m) :=
  fun x => f x + s • η x

/-- Smoothness of the varied field for smooth `f` and admissible `η`. -/
lemma variedField_contDiff (f : Space d → EuclideanSpace ℝ (Fin m))
    (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m)))
    (s : ℝ)
    (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (variedField f η s) := by
  exact hf.add (η.isTestFunction.contDiff.const_smul s)

/-- The action of a field under an admissible variation. -/
noncomputable def actionVariation (L : Lagrangian d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m))
    (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m))) : ℝ → ℝ :=
  fun s => action L (variedField f η s)

/-- Explicit integrability condition for the family of varied action densities. -/
def HasFiniteActionVariation (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m))
    (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m))) : Prop :=
  ∀ s : ℝ, Integrable (actionDensity L (variedField f η s))

/-- Locality package for the action density under compactly supported variations: for every
variation parameter `s`, the change in the action density is a continuous compactly supported
function. Combined with finiteness of the base action, this implies finiteness of the varied
action. -/
def HasCompactlySupportedActionVariationDifference (L : Lagrangian d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m))
    (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m))) : Prop :=
  ∀ s : ℝ,
    Continuous (fun x => actionDensity L (variedField f η s) x - actionDensity L f x) ∧
      HasCompactSupport (fun x => actionDensity L (variedField f η s) x - actionDensity L f x)

/-- If the base action is finite and every varied action density differs from the base density by
a continuous compactly supported function, then the whole varied family has finite action. -/
lemma hasFiniteActionVariation_of_hasFiniteAction_of_compactlySupportedDifference
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m))
    (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m)))
    (hbase : HasFiniteAction L f)
    (hdiff : HasCompactlySupportedActionVariationDifference L f η) :
    HasFiniteActionVariation L f η := by
  intro s
  rcases hdiff s with ⟨hcont, hsupp⟩
  have hsub :
      Integrable (fun x => actionDensity L (variedField f η s) x - actionDensity L f x) := by
    exact hcont.integrable_of_hasCompactSupport hsupp
  have hadd :
      Integrable
        (fun x =>
          (actionDensity L (variedField f η s) x - actionDensity L f x)
            + actionDensity L f x) := by
    exact hsub.add hbase
  simp_all [sub_eq_add_neg, add_assoc]
  exact hadd

@[simp]
lemma variedField_apply (f : Space d → EuclideanSpace ℝ (Fin m))
    (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m))) (s : ℝ)
    (x : Space d) :
    variedField f η s x = f x + s • η x := rfl

@[simp]
lemma actionVariation_apply (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m))
    (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m))) (s : ℝ) :
    actionVariation L f η s = action L (variedField f η s) := rfl

lemma jetAt_variedField_eq_of_notMem_tsupport
    (k : ℕ) (f : Space d → EuclideanSpace ℝ (Fin m))
    (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m))) (s : ℝ)
    {x : Space d}
    (hf : ContDiff ℝ ∞ f) (hx : x ∉ tsupport η.toFun) :
    jetAt k (variedField f η s) x = jetAt k f x := by
  have hcoords :
      jetCoordinatesAt k (variedField f η s) x = jetCoordinatesAt k f x := by
    have h1 := jetCoordinatesAt_add_smul k f η.toFun x s hf η.isTestFunction.contDiff
    simp_all [jetCoordinatesAt_eq_zero_of_notMem_tsupport k η.toFun hx]
    exact h1
  rw [jetAt_eq_ofBaseCoordinates, jetAt_eq_ofBaseCoordinates]
  exact congrArg (JetPoint.ofBaseCoordinates x) hcoords

lemma actionDensity_variedField_eq_of_notMem_tsupport
    (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m))
    (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m)))
    (s : ℝ)
    {x : Space d} (hf : ContDiff ℝ ∞ f) (hx : x ∉ tsupport η.toFun) :
    actionDensity L (variedField f η s) x = actionDensity L f x := by
  simp [actionDensity_apply, jetAt_variedField_eq_of_notMem_tsupport k f η s hf hx]

lemma hasCompactlySupportedActionVariationDifference_of_continuousInCoordinates
    (L : Lagrangian d m k) (hcontL : Lagrangian.ContinuousInCoordinates L)
    (f : Space d → EuclideanSpace ℝ (Fin m)) (hf : ContDiff ℝ ∞ f)
    (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m))) :
    HasCompactlySupportedActionVariationDifference L f η := by
  intro s
  have hbaseCont : Continuous (actionDensity L f) := by
    exact Lagrangian.continuousAlongField_of_inCoordinates L hcontL f hf
  have hvarCont : Continuous (actionDensity L (variedField f η s)) := by
    exact Lagrangian.continuousAlongField_of_inCoordinates L hcontL (variedField f η s)
        (variedField_contDiff f η s hf)
  refine ⟨hvarCont.sub hbaseCont, ?_⟩
  refine η.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _) ?_
  have hsupp :
      Function.support (fun x => actionDensity L (variedField f η s) x - actionDensity L f x)
        ⊆ tsupport η.toFun := by
    intro x hx
    by_contra hxt
    rw [Function.mem_support] at hx
    have heq := actionDensity_variedField_eq_of_notMem_tsupport L f η s hf hxt
    rw [heq] at hx
    exact hx (sub_self _)
  simpa [tsupport] using closure_minimal hsupp (isClosed_tsupport _)

/-!
## C. Critical fields

-/

/-- A field is critical for a local action if every admissible compactly supported variation has
vanishing first derivative at `s = 0`, under the explicit finite-action hypothesis for the varied
family. -/
def IsCritical (L : Lagrangian d m k) (f : Space d → EuclideanSpace ℝ (Fin m)) : Prop :=
  ∀ η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m)), HasFiniteActionVariation L f η →
    HasDerivAt (actionVariation L f η) 0 0

end Local
end ClassicalFieldTheory
