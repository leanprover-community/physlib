/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.CStarAlgebra.lpSpace
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range

/-!
# The pointwise star order on bounded functions

Bounded complex functions are ordered pointwise, and this order is their star order.

## i. Overview

The bounded complex functions `lp (fun _ : X ↦ ℂ) ∞` on a type `X` form a commutative
C⋆-algebra. Ordering them pointwise makes them a star-ordered ring: a bounded function is
positive exactly when it is the square of the square root of its real part. Every closed
star subalgebra is then a commutative C⋆-algebra with the same star order.

## ii. Key results

- `lp.instStarOrderedRing` : the pointwise order on bounded complex functions is the star order.
- `lp.instStarOrderedSubalgebra` : a closed star subalgebra carries the pointwise star order.

## iii. Table of contents

- A. The pointwise order
- B. Closed subalgebras

## iv. References

-/

@[expose] public section

open scoped ENNReal ComplexOrder

namespace lp

variable {X : Type*} {S : StarSubalgebra ℂ (lp (fun _ : X ↦ ℂ) ∞)}
  [IsClosed (S : Set (lp (fun _ : X ↦ ℂ) ∞))]

/-! ## A. The pointwise order -/

/-- Bounded functions are ordered pointwise. -/
noncomputable instance instPartialOrder : PartialOrder (lp (fun _ : X ↦ ℂ) ∞) :=
  PartialOrder.lift (⇑) Subtype.val_injective

/-- Adding a bounded function preserves the pointwise order. -/
instance : IsOrderedAddMonoid (lp (fun _ : X ↦ ℂ) ∞) where
  add_le_add_left _ _ h z x := add_le_add_left (h x) (z x)

/-- The pointwise square root of the real part of a bounded function. -/
noncomputable def sqrtRe (f : lp (fun _ : X ↦ ℂ) ∞) : lp (fun _ : X ↦ ℂ) ∞ :=
  ⟨Complex.ofReal ∘ Real.sqrt ∘ Complex.re ∘ ⇑f, memℓp_infty ⟨√‖f‖, by
    rintro _ ⟨x, rfl⟩
    simpa [abs_of_nonneg] using Real.sqrt_le_sqrt
      ((Complex.re_le_norm (f x)).trans (lp.norm_apply_le_norm ENNReal.top_ne_zero f x))⟩⟩

/-- A positive bounded function is the square of its square root. -/
lemma star_sqrtRe_mul_self {f : lp (fun _ : X ↦ ℂ) ∞} (hf : 0 ≤ f) :
    star (sqrtRe f) * sqrtRe f = f := by
  refine lp.ext (funext fun x ↦ ?_)
  rw [lp.infty_coeFn_mul, Pi.mul_apply, lp.coeFn_star, Pi.star_apply]
  change star (√(f x).re : ℂ) * √(f x).re = f x
  rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (Complex.nonneg_iff.mp (hf x)).1]
  exact (Complex.eq_re_of_ofReal_le (hf x)).symm

/-- The pointwise order is the star order: positive bounded functions are squares. -/
noncomputable instance instStarOrderedRing : StarOrderedRing (lp (fun _ : X ↦ ℂ) ∞) :=
  StarOrderedRing.of_nonneg_iff' add_le_add_right fun f ↦
    ⟨fun hf ↦ ⟨sqrtRe f, (star_sqrtRe_mul_self hf).symm⟩,
      by rintro ⟨g, rfl⟩ x; exact star_mul_self_nonneg (g x)⟩

/-! ## B. Closed subalgebras -/

/-- A closed algebra of bounded functions is a commutative C⋆-algebra. -/
noncomputable instance instCommCStarSubalgebra : CommCStarAlgebra S :=
  StarSubalgebra.commCStarAlgebra S

/-- A closed algebra of bounded functions carries the pointwise star order. -/
noncomputable instance instStarOrderedSubalgebra : StarOrderedRing S := by
  let : NonnegSpectrumClass ℝ (lp (fun _ : X ↦ ℂ) ∞) := CStarAlgebra.instNonnegSpectrumClass
  let : NonUnitalIsometricContinuousFunctionalCalculus ℝ (lp (fun _ : X ↦ ℂ) ∞) IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalIsometricContinuousFunctionalCalculus
  exact Subtype.starOrderedRing (𝕜 := ℂ) S

end lp
