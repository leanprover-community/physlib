/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Basic.StarAlgebra.Observable
public import PhyslibAlpha.QuantumMechanics.Basic.CStarAlgebra.OrderUnit
public import PhyslibAlpha.QuantumMechanics.Basic.OrderUnit.Composite
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

## Why this matters beyond this file

`OrderUnit/Composite.lean`'s "Future work" section identifies the missing ingredient for proving
`MaxCone E₁ E₂` (the maximal-cone tensor product of two order-unit spaces) is itself an order-unit
space: an arbitrary element of `E₁ ⊗[ℝ] E₂` is *some* finite sum `∑ xᵢ ⊗ₜ yᵢ` with no control over
the sign of the individual `xᵢ`, `yᵢ`, and — in a bare order-unit space — "there is no Jordan-type
decomposition of `t` into a difference of two elements of `MaxCone E₁ E₂` to fall back on, unlike
the C*-algebra/matrix setting". This file is exactly that C⋆-algebra-level fallback, for the
specific case `E = Observable A = selfAdjoint A`. It does **not** resolve `Composite.lean`'s gap in
general — that gap is about an arbitrary order-unit space `E` with no further structure, and no
amount of C⋆-algebra machinery reaches that generality. What it does provide, as a genuinely short
consequence proved below (`exists_sub_mem_maxConeSet`), is that every element of
`Observable A ⊗[ℝ] Observable B` (for `A`, `B` both C⋆-algebras) *is* such a difference of two
elements of `MaxCone (Observable A) (Observable B)` — the one piece of `Composite.lean`'s "Future
work" that the Jordan decomposition alone settles. Boundedness by a multiple of `1 ⊗ₜ 1` (the rest
of `IsOrderUnit`) is a separate, harder fact — the docstring there is explicit that it "genuinely
needs more than the order-unit axioms this file assumes" — and is not attempted here.

## Main definitions

- `Observable.posPart`, `Observable.negPart` : the positive and negative parts of an observable, as
  `PositiveObservable A`.
- `Observable.posPart_sub_negPart` : `a⁺ - a⁻ = a`.
- `Observable.posPart_mul_negPart`, `Observable.negPart_mul_posPart` : the two parts are orthogonal.
- `Observable.posPart_negPart_unique` : this is the *only* decomposition of `a` into a difference of
  orthogonal positive observables.
- `exists_sub_mem_maxConeSet` : every element of `Observable A ⊗[ℝ] Observable B` is a difference of
  two elements of the maximal cone `MaxCone (Observable A) (Observable B)` (see above).

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

/-! ## C. A partial step towards `Composite.lean`'s order unit

This section is a bonus, not the main deliverable of this file (see the module doc above for the
precise scope of what it does and does not establish). It uses the Jordan decomposition to settle,
for `E₁ = Observable A`, `E₂ = Observable B` with `A`, `B` C⋆-algebras, exactly the one gap
`OrderUnit/Composite.lean`'s "Future work" section names by that name: every element of
`Observable A ⊗[ℝ] Observable B` is a difference of two elements of `MaxCone (Observable A)
(Observable B)`. The remaining, harder half of `IsOrderUnit` — bounding every such element by a
multiple of `1 ⊗ₜ 1` — is not attempted; `Composite.lean` itself is explicit that this needs
genuinely more (a Cauchy–Schwarz-type argument using the C⋆-norm), not just this decomposition. -/

open scoped TensorProduct

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- Every element of `Observable A ⊗[ℝ] Observable B` is a difference of two elements of the
maximal cone `MaxCone (Observable A) (Observable B)`: expand a simple tensor `x ⊗ₜ y` using the
Jordan decomposition `x = x⁺ - x⁻`, `y = y⁺ - y⁻` on each factor,
`x ⊗ₜ y = (x⁺ ⊗ₜ y⁺ + x⁻ ⊗ₜ y⁻) - (x⁺ ⊗ₜ y⁻ + x⁻ ⊗ₜ y⁺)`, a difference of two sums of simple tensors
of positive elements, and extend additively over `TensorProduct.induction_on`. -/
theorem exists_sub_mem_maxConeSet (t : Observable A ⊗[ℝ] Observable B) :
    ∃ t₁ t₂ : MaxCone (Observable A) (Observable B),
      (t₁ : Observable A ⊗[ℝ] Observable B) - (t₂ : Observable A ⊗[ℝ] Observable B) = t := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul x y =>
      set xp := (Observable.posPart x).1
      set xn := (Observable.negPart x).1
      set yp := (Observable.posPart y).1
      set yn := (Observable.negPart y).1
      have hx : xp - xn = x := Observable.posPart_sub_negPart x
      have hy : yp - yn = y := Observable.posPart_sub_negPart y
      have hxp : (0 : Observable A) ≤ xp := (Observable.posPart x).2
      have hxn : (0 : Observable A) ≤ xn := (Observable.negPart x).2
      have hyp : (0 : Observable B) ≤ yp := (Observable.posPart y).2
      have hyn : (0 : Observable B) ≤ yn := (Observable.negPart y).2
      refine ⟨⟨xp ⊗ₜ[ℝ] yp, tmul_mem_maxConeSet hxp hyp⟩ +
        ⟨xn ⊗ₜ[ℝ] yn, tmul_mem_maxConeSet hxn hyn⟩,
        ⟨xp ⊗ₜ[ℝ] yn, tmul_mem_maxConeSet hxp hyn⟩ +
        ⟨xn ⊗ₜ[ℝ] yp, tmul_mem_maxConeSet hxn hyp⟩, ?_⟩
      show xp ⊗ₜ[ℝ] yp + xn ⊗ₜ[ℝ] yn - (xp ⊗ₜ[ℝ] yn + xn ⊗ₜ[ℝ] yp) = x ⊗ₜ[ℝ] y
      rw [← hx, ← hy]
      simp only [TensorProduct.sub_tmul, TensorProduct.tmul_sub]
      abel
  | add t₁ t₂ h₁ h₂ =>
      obtain ⟨a1, a2, ha⟩ := h₁
      obtain ⟨b1, b2, hb⟩ := h₂
      refine ⟨a1 + b1, a2 + b2, ?_⟩
      show ((a1 : _) + (b1 : _)) - ((a2 : _) + (b2 : _)) = t₁ + t₂
      rw [show ((a1 : Observable A ⊗[ℝ] Observable B) + (b1 : _)) - ((a2 : _) + (b2 : _)) =
        ((a1 : _) - (a2 : _)) + ((b1 : _) - (b2 : _)) from by abel, ha, hb]
