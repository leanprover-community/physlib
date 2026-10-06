/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.StarAlgebra.Observable
public import PhyslibAlpha.ProbabilisticTheory.CStarAlgebra.OrderUnit
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!

# Positive and negative parts of observables

Every observable of a C⋆-algebra splits uniquely into orthogonal positive and negative parts.

## i. Overview

Every observable `a` of a C⋆-algebra splits uniquely as `a = a⁺ - a⁻` with `a⁺`, `a⁻` positive and
orthogonal, `a⁺ a⁻ = 0`. This is the Jordan decomposition, the analogue of splitting a function or a
signed measure into its positive and negative parts. Mathlib builds `a⁺` and `a⁻` by the continuous
functional calculus; here they are positive observables.

## ii. Key results

- `Observable.posPart`, `Observable.negPart` : the positive and negative parts.
- `Observable.posPart_sub_negPart` : `a⁺ - a⁻ = a`.
- `Observable.posPart_mul_negPart` : the parts are orthogonal.
- `Observable.posPart_negPart_unique` : the decomposition is unique.

## iii. Table of contents

- A. Positive observables
- B. Positive and negative parts

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

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
    ((posPart a).1 : A) * (negPart a).1 = 0 :=
  CFC.posPart_mul_negPart (a : A)

/-- The negative and positive parts are orthogonal in the opposite order as well. -/
lemma negPart_mul_posPart (a : Observable A) :
    ((negPart a).1 : A) * (posPart a).1 = 0 :=
  CFC.negPart_mul_posPart (a : A)

/-- The positive/negative decomposition is the unique decomposition into orthogonal positive
observables: this is the Jordan decomposition theorem. -/
lemma posPart_negPart_unique (a : Observable A) (b c : PositiveObservable A)
    (hsub : (a : A) = (b.1 : A) - c.1)
    (horth : (b.1 : A) * c.1 = 0) :
    posPart a = b ∧ negPart a = c := by
  obtain ⟨hb, hc⟩ := CFC.posPart_negPart_unique hsub horth b.property c.property
  exact ⟨Subtype.ext (Subtype.ext hb), Subtype.ext (Subtype.ext hc)⟩

end Observable

end ProbabilisticTheory
