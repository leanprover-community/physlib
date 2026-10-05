/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.JordanOrderUnit.CStarAlgebra.Basic
public import PhyslibAlpha.ProbabilisticTheory.CStarAlgebra.JordanDecomposition
public import PhyslibAlpha.ProbabilisticTheory.JordanOrderUnit.Conditioning

/-!

# Jordan positivity in a C⋆-algebra

In a C⋆-algebra, nonnegative observables are Jordan squares and `a₊ ∘ a₋ = 0`.

## i. Overview

In a C⋆-algebra an observable is nonnegative iff it is a Jordan square, and its positive and
negative parts are Jordan orthogonal.

## ii. Key results

- `JB.nonneg_iff_exists_jpow_two` : the positive observables are the Jordan squares.
- `JB.jordanOrthogonal_posPart_negPart` : positive and negative parts are Jordan orthogonal.
- `JB.quadRep_nonneg` : the quadratic representation `U_a` preserves positivity.
- `JB.JordanAlgebra.IsJordanProjection.conditionCStar` : conditioning a state on a projection.

## iii. Table of contents

- A. Positivity via the Jordan square
- B. Orthogonality of the Jordan decomposition

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory

namespace JB

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open scoped selfAdjoint
open scoped JB

/-! ## A. Positivity via the Jordan square -/

/-- An observable is positive exactly when it is the Jordan square of an observable — the Jordan
form of `Observable.nonneg_iff_exists_observable_sq`, via `mul_self_eq` identifying the Jordan
square of a single element with its ordinary square. -/
lemma nonneg_iff_exists_jpow_two (a : selfAdjoint A) :
    0 ≤ (a : A) ↔
      ∃ b : selfAdjoint A, (a : A) = ((JordanAlgebra.jpow b 2 : selfAdjoint A) : A) := by
  rw [Observable.nonneg_iff_exists_observable_sq]
  refine exists_congr fun b => ?_
  rw [JordanAlgebra.jpow_two, mul_self_eq]

/-- The quadratic representation of a C⋆-algebra preserves positivity, since `U_a b = a b a`. -/
lemma quadRep_nonneg (a : selfAdjoint A) {b : selfAdjoint A} (hb : 0 ≤ b) :
    0 ≤ JordanAlgebra.quadRep a b := by
  show (0 : A) ≤ ((JordanAlgebra.quadRep a b : selfAdjoint A) : A)
  rw [quadRep_eq_conj]
  simpa only [a.2.star_eq] using
    star_left_conjugate_nonneg (show (0 : A) ≤ (b : A) from hb) (a : A)

/-- The canonical self-adjoint Cstar realization supplies the abstract quadratic-order
capability.  Thus generic Jordan measurement code can use `U_a` as a positive operation without
depending on this realization; this instance is only the concrete discharge of that capability. -/
instance : JordanAlgebra.IsQuadraticallyPositive (selfAdjoint A) where
  quadRep_nonneg := quadRep_nonneg

/-- Projection conditioning in the canonical Cstar Jordan realization.  In contrast to the
abstract constructor, no separate quadratic-positivity argument is required: it is supplied by
the shared `IsQuadraticallyPositive` instance. -/
noncomputable def JordanAlgebra.IsJordanProjection.conditionCStar {p : selfAdjoint A}
    (hp : JordanAlgebra.IsJordanProjection p) (ω : 𝓢[ℝ, selfAdjoint A]) (hmass : 0 < ω p) :
    𝓢[ℝ, selfAdjoint A] :=
  hp.conditionOfQuadraticPositive ω hmass

/-! ## B. Orthogonality of the Jordan decomposition -/

/-- The positive and negative parts of an observable are Jordan-orthogonal, `a₊ ∘ a₋ = 0`: the
Jordan form of `Observable.posPart_mul_negPart`/`.negPart_mul_posPart`. -/
lemma jordanOrthogonal_posPart_negPart (a : selfAdjoint A) :
    JordanAlgebra.JordanOrthogonal (Observable.posPart a).1 (Observable.negPart a).1 := by
  unfold JordanAlgebra.JordanOrthogonal
  apply Subtype.ext
  rw [selfAdjoint.mul_def, selfAdjoint.val_jordanMul, Observable.posPart_mul_negPart,
    Observable.negPart_mul_posPart]
  simp

end JB

end ProbabilisticTheory
