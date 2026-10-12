/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import PhyslibAlpha.Mathematics.TauCeti.Analysis.CStarAlgebra.UnitaryCharacter
public import PhyslibAlpha.Mathematics.TauCeti.RepresentationTheory.Continuous.Integrated.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# Group characters detected by integrated operators

Let `π` be a strongly continuous unitary representation of an abelian group and let `A` be a
complete star subalgebra containing its integrated operators.

## i. Overview

Let `π` be a strongly continuous unitary representation of an abelian group and let `A` be a
complete star subalgebra containing its integrated operators. Each character of `A` that is
nonzero on some integrated operator determines a unique continuous group character `χ`, with

`ω (π(g) π(f)) = χ(g) ω (π(f))`.

The nonvanishing assumption is necessary: adjoining an identity to a nonunital algebra can
introduce a character that annihilates all the integrated operators. On the other characters,
the displayed equation identifies the spectral parameter as an element of the Pontryagin dual.
It applies to all integrable weights, independently of the weight witnessing nonvanishing.
The hypothesis on `A` is simply containment of the integrated form's range; translation
invariance and norm continuity follow from the integrated form's existing translation API.

## ii. Key results

This file proves the statement described in the overview.

## iii. Table of contents

- A. Development

## iv. References

* G. B. Folland, *A Course in Abstract Harmonic Analysis*, second edition, §§3.2 and 4.4.
-/

public section

/-! ## A. Development -/

open MeasureTheory WeakDual

namespace TauCeti

variable {G H : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {μ : Measure G} [μ.IsAddLeftInvariant] [μ.InnerRegularCompactLTTop]
  [IsLocallyFiniteMeasure μ]

/-- A nonvanishing character of an algebra containing the integrated form of a strongly
continuous unitary representation detects a unique continuous group character. Its value is
the multiplier on every integrated operator, independently of the witnessing weight. -/
lemma _root_.ContRepresentation.existsUnique_pontryaginDual_of_integratedOperatorL1
    (π : ContRepresentation ℂ (Multiplicative G) H)
    {hcont : ∀ v, Continuous fun g : G => π (.ofAdd g) v}
    (hbdd : ∃ C, ∀ g, ‖π g‖ ≤ C)
    (hπ : ContRepresentation.IsUnitary π)
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) [CompleteSpace A] :
    ∀ (hA : ∀ f : G →₁[μ] ℂ, π.integratedOperatorL1 hcont hbdd μ f ∈ A)
    (ω : characterSpace ℂ A),
    (∃ f : G →₁[μ] ℂ, ω ⟨π.integratedOperatorL1 hcont hbdd μ f, hA f⟩ ≠ 0) →
    ∃! χ : PontryaginDual (Multiplicative G), ∀ (g : G) (f : G →₁[μ] ℂ),
      ω ⟨π.integratedOperatorL1 hcont hbdd μ
          (Lp.compMeasurePreserving (fun t => -g + t)
            (measurePreserving_add_left μ (-g)) f), hA _⟩ =
        (χ (.ofAdd g) : ℂ) * ω ⟨π.integratedOperatorL1 hcont hbdd μ f, hA f⟩ := by
  intro hA ω hω
  have hmem (g : G) (f : G →₁[μ] ℂ) :
      π (.ofAdd g) * π.integratedOperatorL1 hcont hbdd μ f ∈ A := by
    rw [ContinuousLinearMap.mul_def, π.comp_integratedOperatorL1]
    exact hA _
  have htranslate (g : G) (f : G →₁[μ] ℂ) :
      (⟨π.integratedOperatorL1 hcont hbdd μ
          (Lp.compMeasurePreserving (fun t => -g + t)
            (measurePreserving_add_left μ (-g)) f), hA _⟩ : A) =
        ⟨π (.ofAdd g) * π.integratedOperatorL1 hcont hbdd μ f, hmem g f⟩ := by
    apply Subtype.ext
    simp only [ContinuousLinearMap.mul_def, π.comp_integratedOperatorL1]
  obtain ⟨f₀, hf₀⟩ := hω
  let a : A := ⟨π.integratedOperatorL1 hcont hbdd μ f₀, hA f₀⟩
  have hcomm (g : Multiplicative G) : Commute (π g) (a : H →L[ℂ] H) :=
    π.commute_integratedOperatorL1 g f₀
  have htrans : Continuous fun g : Multiplicative G => π g * (a : H →L[ℂ] H) := by
    simpa only [ContinuousLinearMap.mul_def, Function.comp_def, ofAdd_toAdd, a] using
      (π.continuous_comp_integratedOperatorL1 f₀).comp continuous_toAdd
  obtain ⟨χ, hχ, -⟩ := π.toMonoidHom.existsUnique_pontryaginDual_of_unitary_translate
    hπ.mem_unitary A a hcomm (fun g => hmem g.toAdd f₀) htrans ω hf₀
  have hχ' (g : G) (f : G →₁[μ] ℂ) :
      ω ⟨π.integratedOperatorL1 hcont hbdd μ
          (Lp.compMeasurePreserving (fun t => -g + t)
            (measurePreserving_add_left μ (-g)) f), hA _⟩ =
        (χ (.ofAdd g) : ℂ) * ω ⟨π.integratedOperatorL1 hcont hbdd μ f, hA f⟩ := by
    rw [htranslate]
    exact hχ (.ofAdd g) ⟨_, hA f⟩ (hmem g f)
  refine ⟨χ, hχ', fun ψ hψ => ?_⟩
  apply PontryaginDual.ext
  intro g
  apply Circle.ext
  exact mul_right_cancel₀ hf₀ ((hψ g.toAdd f₀).symm.trans (hχ' g.toAdd f₀))

end TauCeti
