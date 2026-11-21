/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.CStarAlgebra.lpSpace
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
public import Physlib.ProbabilisticTheory.CStarAlgebra.Basic

/-!
# Classical observables

Classical observables are represented by real-valued functions on a configuration space. The
admissible bounded observables form the self-adjoint part of a commutative C⋆-algebra.

## i. Overview

A classical system is described by a configuration space `X`. An observable assigns a real value
to each configuration. Observables are ordered pointwise. The choice of admissible functions
depends on the structure of the system: for a measurable space one may consider bounded
measurable functions, for a topological space bounded continuous functions.

Mathlib's commutative C⋆-algebra `lp (fun _ : X ↦ ℂ) ∞` provides the ambient algebra of bounded
complex functions on `X`, equipped with pointwise operations and the supremum norm. A
closed unital star subalgebra `S` specifies the admissible functions of a classical system.

Through `ofCStarAlgebra`, the self-adjoint part of `S` defines a probabilistic theory with its
associated states, effects and channels. Classical and quantum theories thus share the same
C⋆-algebraic foundation, with classical theories distinguished by commutativity.

## ii. Key results

- `ProbabilisticTheory.Classical.instStarOrderedRing` : the pointwise order of bounded functions
  is the order of the C⋆-algebra.
- `ProbabilisticTheory.Classical.toFun` : the real function of a classical observable.
- `ProbabilisticTheory.Classical.toFun_mul` : observables multiply pointwise.
- `ProbabilisticTheory.Classical.toFun_le_toFun_iff` : one classical observable is below another
  exactly when its value is smaller at every configuration.

## iii. Table of contents

- A. The pointwise order of bounded functions
- B. Closed function algebras
- C. Classical observables as real functions

## iv. References

-/

@[expose] public section

open scoped ENNReal ComplexOrder

namespace ProbabilisticTheory.Classical

variable {X : Type*} {S : StarSubalgebra ℂ (lp (fun _ : X ↦ ℂ) ∞)}
  [IsClosed (S : Set (lp (fun _ : X ↦ ℂ) ∞))]

/-! ## A. The pointwise order of bounded functions -/

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

/-! ## B. Closed function algebras -/

/-- A closed algebra of bounded functions is a commutative C⋆-algebra. -/
noncomputable instance instCommCStarSubalgebra : CommCStarAlgebra S :=
  StarSubalgebra.commCStarAlgebra S

/-- A closed algebra of bounded functions carries the pointwise star order. -/
noncomputable instance instStarOrderedSubalgebra : StarOrderedRing S := by
  let : NonnegSpectrumClass ℝ (lp (fun _ : X ↦ ℂ) ∞) := CStarAlgebra.instNonnegSpectrumClass
  let : NonUnitalIsometricContinuousFunctionalCalculus ℝ (lp (fun _ : X ↦ ℂ) ∞) IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalIsometricContinuousFunctionalCalculus
  exact Subtype.starOrderedRing (𝕜 := ℂ) S

/-! ## C. Classical observables as real functions -/

/-- The real function of a classical observable: its value at each configuration. -/
noncomputable def toFun : selfAdjoint S →ₗ[ℝ] X → ℝ where
  toFun f x := ((f : S) : lp (fun _ : X ↦ ℂ) ∞) x |>.re
  map_add' _ _ := rfl
  map_smul' _ _ := funext fun _ ↦ Complex.re_ofReal_mul _ _

/-- A classical observable takes real values. -/
lemma ofReal_toFun (f : selfAdjoint S) (x : X) :
    (toFun f x : ℂ) = ((f : S) : lp (fun _ : X ↦ ℂ) ∞) x :=
  Complex.conj_eq_iff_re.mp (congrFun (congrArg (⇑) (congrArg Subtype.val f.2)) x)

@[simp]
lemma toFun_one : toFun (1 : selfAdjoint S) = 1 := rfl

/-- The product of classical observables is the pointwise product of their values. -/
@[simp]
lemma toFun_mul (f g : selfAdjoint S) : toFun (f * g) = toFun f * toFun g :=
  funext fun x ↦ Complex.ofReal_injective <| by
    rw [Pi.mul_apply, Complex.ofReal_mul, ofReal_toFun, ofReal_toFun, ofReal_toFun]; rfl

/-- One classical observable is below another exactly when its value is smaller at every
configuration. -/
lemma toFun_le_toFun_iff {f g : selfAdjoint S} : toFun f ≤ toFun g ↔ f ≤ g :=
  forall_congr' fun x ↦ by rw [← Complex.real_le_real, ofReal_toFun, ofReal_toFun]

/-- A classical observable is determined by its values. -/
lemma toFun_injective : Function.Injective (toFun : selfAdjoint S →ₗ[ℝ] X → ℝ) :=
  fun _ _ h ↦ le_antisymm (toFun_le_toFun_iff.mp h.le) (toFun_le_toFun_iff.mp h.ge)

/-- Squares of classical observables are positive. -/
lemma selfAdjoint_sq_nonneg (f : selfAdjoint S) : 0 ≤ f ^ 2 :=
  toFun_le_toFun_iff.mp fun x ↦ show (0 : ℝ) ≤ toFun (f ^ 2) x by
    rw [sq, toFun_mul]; exact mul_self_nonneg _

end ProbabilisticTheory.Classical
