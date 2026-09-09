/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.StarAlgebra.Observable
public import PhyslibAlpha.AlgebraicFramework.CStarAlgebra.OrderUnit
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!

# The Jordan decomposition of a self-adjoint element

Every self-adjoint element `a` of a C⋆-algebra splits canonically as `a = a⁺ - a⁻`, a difference of
two *orthogonal* positive elements (`a⁺ * a⁻ = 0`) — the noncommutative analogue of splitting a
real-valued function into its positive and negative parts, or a signed measure into its positive
and negative variation (Camille Jordan's decomposition theorem, 1881/1892). This is not the same
"Jordan" as `StarAlgebra/Jordan.lean`'s Jordan *product* `a ∘ b := a * b + b * a` — that one is
named for Pascual Jordan, no relation, and the shared name is an unfortunate but standard clash in
the operator-algebra literature.

Mathlib already builds `a⁺`, `a⁻` from the continuous functional calculus (`cfcₙ` applied to the
functions `t ↦ max t 0` and `t ↦ max (-t) 0`) and proves the decomposition, orthogonality, and
uniqueness facts at the level of a bare C⋆-algebra element. This file packages exactly those facts
one level up, at the level of `Observable A := selfAdjoint A` and `PositiveObservable A`, so that
"take the positive/negative part" is available as an operation *on observables*, landing in
`PositiveObservable A` rather than requiring the caller to separately track self-adjointness and
nonnegativity of a bare element of `A` after the fact.

Genuinely needing a full C⋆-algebra here (rather than a bare order-unit space) is not a corner that
was cut: the continuous functional calculus behind `a⁺`, `a⁻` needs completeness and the
C⋆-identity to exist at all, so `[CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]` is the
correct, load-bearing hypothesis, not one to weaken.

## Main definitions

- `Observable.posPart`, `Observable.negPart` : the positive and negative parts of an observable, as
  `PositiveObservable A`.
- `Observable.posPart_sub_negPart` : `a⁺ - a⁻ = a`.
- `Observable.posPart_mul_negPart`, `Observable.negPart_mul_posPart` : the two parts are orthogonal.
- `Observable.posPart_negPart_unique` : this is the *only* decomposition of `a` into a difference of
  orthogonal positive observables.

-/

@[expose] public section

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
