/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.OperatorAlgebra.Observables.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic

/-!
# Positive observables

Positive observables form the positive cone in the real vector space of observables. Every
observable has a canonical decomposition as the difference of two orthogonal positive parts.
-/

@[expose] public section
namespace OperatorAlgebra

variable {A : Type*} [OperatorAlgebra A]

/-- A positive observable. -/
abbrev PositiveObservable (A : Type*) [OperatorAlgebra A] :=
  _root_.PositiveObservable A

namespace Observable

/-! ## A. Positive observables -/

/-- An observable is positive exactly when it is the square of an observable. -/
lemma nonneg_iff_exists_observable_sq (a : Observable A) :
    0 ≤ (a : A) ↔ ∃ b : Observable A, (a : A) = (b : A) * b := by
  constructor
  · intro ha
    obtain ⟨b, hb, hab⟩ :=
      CStarAlgebra.nonneg_iff_exists_isSelfAdjoint_and_eq_mul_self.mp ha
    exact ⟨⟨b, hb⟩, hab⟩
  · rintro ⟨b, hab⟩
    exact CStarAlgebra.nonneg_iff_exists_isSelfAdjoint_and_eq_mul_self.mpr
      ⟨b, b.property, hab⟩

/-! ## B. Positive and negative parts -/

/-- The positive part of an observable. -/
noncomputable def posPart (a : Observable A) : PositiveObservable A :=
  ⟨⟨(a : A)⁺, CFC.posPart_nonneg (a : A) |>.isSelfAdjoint⟩, CFC.posPart_nonneg (a : A)⟩

/-- The negative part of an observable. -/
noncomputable def negPart (a : Observable A) : PositiveObservable A :=
  ⟨⟨(a : A)⁻, CFC.negPart_nonneg (a : A) |>.isSelfAdjoint⟩, CFC.negPart_nonneg (a : A)⟩

/-- Every observable is the difference of its positive and negative parts. -/
lemma posPart_sub_negPart (a : Observable A) :
    (posPart a).1 - (negPart a).1 = a := by
  apply Subtype.ext
  exact CFC.posPart_sub_negPart (a : A) a.property

/-- The positive and negative parts of an observable are orthogonal. -/
lemma posPart_mul_negPart (a : Observable A) :
    ((posPart a).1 : A) * (negPart a).1 = 0 := by
  exact CFC.posPart_mul_negPart (a : A)

/-- The negative and positive parts are orthogonal in the opposite order as well. -/
lemma negPart_mul_posPart (a : Observable A) :
    ((negPart a).1 : A) * (posPart a).1 = 0 := by
  exact CFC.negPart_mul_posPart (a : A)

/-- The positive/negative decomposition is the unique decomposition into orthogonal positive
observables. -/
lemma posPart_negPart_unique (a : Observable A) (b c : PositiveObservable A)
    (hsub : (a : A) = (b.1 : A) - c.1)
    (horth : (b.1 : A) * c.1 = 0) :
    posPart a = b ∧ negPart a = c := by
  obtain ⟨hb, hc⟩ := CFC.posPart_negPart_unique hsub horth b.property c.property
  exact ⟨Subtype.ext (Subtype.ext hb), Subtype.ext (Subtype.ext hc)⟩

end Observable

end OperatorAlgebra
