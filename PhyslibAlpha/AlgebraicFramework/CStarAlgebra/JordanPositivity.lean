/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.CStarAlgebra.Jordan
public import PhyslibAlpha.AlgebraicFramework.CStarAlgebra.JordanDecomposition
public import PhyslibAlpha.AlgebraicFramework.JordanOrderUnit.Conditioning

/-!

# Jordan positivity and decomposition in a Cstar algebra

## i. Overview

The exact cone theorem `a ≥ 0 ⟺ ∃ b, a = b²` and the decomposition
`a = a₊ - a₋` with `a₊ ∘ a₋ = 0` are already available for the canonical realization:
`CStarAlgebra/JordanDecomposition.lean` has `Observable.nonneg_iff_exists_observable_sq`,
`Observable.posPart`/`Observable.negPart`, `Observable.posPart_sub_negPart`, and
`Observable.posPart_mul_negPart`/`.negPart_mul_posPart` — using the *ordinary* associative square
and product, since it predates the Jordan layer. This file is the two-line connection to
the Jordan-native statements, using `mul_self_eq` from `CStarAlgebra/Jordan.lean` (the Jordan
square of a single element is the ordinary square) and ordinary two-sided vanishing to obtain
Jordan orthogonality.

Square roots, `|a|`, and the CFC-based characterization `a ≥ 0 ⟺ σ(a) ⊆ [0,∞)` are not
duplicated here: their abstract versions already live on the single-observable JB functional
calculus path, `JordanOrderUnit/JB/GeneratedByOne/CFC.lean` (`jordanAbs`,
`jordanPosPart`/`jordanNegPart`, `jordanCfc_nonneg_iff`), which applies uniformly to this
realization's `selfAdjoint A` once it is known to be a `JBAlgebra` — no realization-specific
restatement is needed.

## ii. Key definitions and results

- `JB.nonneg_iff_exists_jpow_two`
- `JB.jordanOrthogonal_posPart_negPart`

## iii. Table of contents

- A. Positivity via the Jordan square
- B. Orthogonality of the Jordan decomposition

-/

@[expose] public section

namespace JB

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open scoped selfAdjoint
open scoped JB

/-! ## A. Positivity via the Jordan square -/

/-- An observable is positive exactly when it is the Jordan square of an observable — the Jordan
form of `Observable.nonneg_iff_exists_observable_sq`, via `mul_self_eq` identifying the Jordan
square of a single element with its ordinary square. -/
theorem nonneg_iff_exists_jpow_two (a : selfAdjoint A) :
    0 ≤ (a : A) ↔
      ∃ b : selfAdjoint A, (a : A) = ((JordanAlgebra.jpow b 2 : selfAdjoint A) : A) := by
  rw [Observable.nonneg_iff_exists_observable_sq]
  refine exists_congr fun b => ?_
  rw [JordanAlgebra.jpow_two, mul_self_eq]

/-- Quadratic representation preserves positivity in the canonical Cstar Jordan realization.
This is the concrete source of the positivity hypothesis used by abstract projection
conditioning: `U_a(b) = aba = a* b a` because `a` is self-adjoint, and positive cones are closed
under star-conjugation. -/
theorem quadRep_nonneg (a : selfAdjoint A) {b : selfAdjoint A} (hb : 0 ≤ b) :
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
theorem jordanOrthogonal_posPart_negPart (a : selfAdjoint A) :
    JordanAlgebra.JordanOrthogonal (Observable.posPart a).1 (Observable.negPart a).1 := by
  unfold JordanAlgebra.JordanOrthogonal
  apply Subtype.ext
  rw [selfAdjoint.mul_def, selfAdjoint.val_jordanMul, Observable.posPart_mul_negPart,
    Observable.negPart_mul_posPart]
  simp

end JB
