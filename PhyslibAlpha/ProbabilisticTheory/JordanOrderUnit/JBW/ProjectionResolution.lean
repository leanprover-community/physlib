/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.JordanOrderUnit.JBW.Basic
public import PhyslibAlpha.ProbabilisticTheory.JordanOrderUnit.ProjectionResolution
public import PhyslibAlpha.ProbabilisticTheory.Measurement.BornRule
public import PhyslibAlpha.ProbabilisticTheory.Measurement.BoundedScalarization

/-!
# Projection resolutions in JBW-algebras

## i. Overview

A projection resolution is defined at the Jordan order-unit level. In a JBW-algebra two further
things hold. A normal state turns a projection resolution into an ordinary probability law, and
its bounded Borel calculus into ordinary integration against that law. And normal states
separate projection resolutions, so a projection resolution is determined by its probability laws.

## ii. Key results

- `MeasurableProjectionResolution.probabilityLaw` : the probability law in a normal state.
- `MeasurableProjectionResolution.scalarBoundedBorel_eq_integral` : a normal state applied to the
  bounded Borel calculus is the integral against the scalarized measure.
- `MeasurableProjectionResolution.eq_of_forall_normal_probabilityLaw_eq` : normal-state
  probability laws determine the projection resolution.

## iii. Table of contents

- A. Probability laws
- B. Separation by normal states

-/

@[expose] public section

namespace ProbabilisticTheory

open MeasureTheory

namespace MeasurableProjectionResolution

variable {Ω E : Type*} [MeasurableSpace Ω] [IsJBOrderUnit E]

/-! ## A. Probability laws -/

/-- The probability law of a projection resolution in a normal state. -/
noncomputable def probabilityLaw (P : MeasurableProjectionResolution Ω E)
    (ω : 𝓢[ℝ, E]) (hω : ω.IsNormal) : ProbabilityMeasure Ω :=
  P.toEffectValuedMeasure.probabilityLaw ω hω

/-- The probability of an event is the state evaluated at its projection. -/
lemma probabilityLaw_apply (P : MeasurableProjectionResolution Ω E)
    (ω : 𝓢[ℝ, E]) (hω : ω.IsNormal) (s : Set Ω) (hs : MeasurableSet s) :
    (P.probabilityLaw ω hω : Measure Ω) s = ENNReal.ofReal (ω (P s hs : E)) :=
  EffectValuedMeasure.probabilityLaw_apply P.toEffectValuedMeasure ω hω s hs

/-- A normal state applied to the bounded Borel calculus is the bounded integral against the
scalarized measure. -/
lemma scalarBoundedBorel_eq_integral (P : MeasurableProjectionResolution Ω E)
    (ω : 𝓢[ℝ, E]) (hω : ω.IsNormal) {f : Ω → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ x, |f x| ≤ M) :
    ω (P.boundedBorel f hf hM) =
      EffectValuedMeasure.integral hf hM (P.toEffectValuedMeasure.scalarize ω hω) :=
  EffectValuedMeasure.map_integral hf hM P.toEffectValuedMeasure ω hω

/-! ## B. Separation by normal states -/

/-- Normal states separate projection resolutions pointwise. -/
lemma eq_of_forall_normal_state_eq {P Q : MeasurableProjectionResolution Ω E} [JBWAlgebra E]
    (h : ∀ ω : 𝓢[ℝ, E], ω.IsNormal → ∀ s hs, ω (P s hs : E) = ω (Q s hs : E)) : P = Q :=
  ext fun s hs => JBWAlgebra.eq_of_forall_normal_state_eq fun ω hω => h ω hω s hs

/-- A projection resolution in a JBW-algebra is determined by its probability laws in all normal
states. -/
lemma eq_of_forall_normal_probabilityLaw_eq {P Q : MeasurableProjectionResolution Ω E}
    [JBWAlgebra E]
    (h : ∀ ω : 𝓢[ℝ, E], ∀ hω : ω.IsNormal, P.probabilityLaw ω hω = Q.probabilityLaw ω hω) :
    P = Q := by
  refine eq_of_forall_normal_state_eq fun ω hω s hs => ?_
  have hmeasure : (P.probabilityLaw ω hω : Measure Ω) s = (Q.probabilityLaw ω hω : Measure Ω) s :=
    by rw [h ω hω]
  rw [P.probabilityLaw_apply ω hω s hs, Q.probabilityLaw_apply ω hω s hs] at hmeasure
  exact (ENNReal.ofReal_eq_ofReal_iff (ω.map_nonneg (P s hs).2.1)
    (ω.map_nonneg (Q s hs).2.1)).mp hmeasure

end MeasurableProjectionResolution

end ProbabilisticTheory
