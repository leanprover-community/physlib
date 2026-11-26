/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.Mathematics.ForMathlib.LpStarOrder
public import Physlib.ProbabilisticTheory.CStarAlgebra.Basic

/-!
# Classical probabilistic theories

In a classical system every observable has a definite value in each configuration.

## i. Overview

An observable of a classical system with configurations `X` is a bounded real function on `X`.
A closed algebra `S` of bounded functions fixes which functions count as observables. On a
measurable space these are the bounded measurable functions.

The observables in `S` form the probabilistic theory `classical S`. Observables add, multiply and
compare value by value. Their algebra is commutative, which is characteristic of classical
systems.

## ii. Key results

- `ProbabilisticTheory.classical` : the classical theory of a closed algebra of bounded functions.
- `ProbabilisticTheory.Classical.instFunLike` : the value of an observable in a configuration.
- `ProbabilisticTheory.Classical.le_def` : observables are ordered by their values.

## iii. Table of contents

- A. The classical theory
- B. Values of observables

## iv. References

-/

@[expose] public section

open scoped ENNReal ComplexOrder

namespace ProbabilisticTheory

/-! ## A. The classical theory -/

/-- The classical theory whose observables are the real functions in a closed algebra `S` of
bounded functions. -/
noncomputable def classical {X : Type*} (S : StarSubalgebra ℂ (lp (fun _ : X ↦ ℂ) ∞))
    [IsClosed (S : Set (lp (fun _ : X ↦ ℂ) ∞))] : ProbabilisticTheory :=
  ofCStarAlgebra S

end ProbabilisticTheory

namespace ProbabilisticTheory.Classical

variable {X : Type*} {S : StarSubalgebra ℂ (lp (fun _ : X ↦ ℂ) ∞)}
  [IsClosed (S : Set (lp (fun _ : X ↦ ℂ) ∞))]

/-! ## B. Values of observables -/

/-- An observable as a real function in `S`. -/
def toSelfAdjoint : Observables (classical S) ≃ selfAdjoint S :=
  Equiv.refl _

/-- Observables multiply value by value. -/
noncomputable instance : CommRing (Observables (classical S)) :=
  let R : CommRing (selfAdjoint S) := inferInstance
  { R with
    toAddCommGroup := (classical S).addCommGroup
    toOne := (classical S).one }

/-- The value of an observable in a configuration. -/
noncomputable instance instFunLike : FunLike (Observables (classical S)) X ℝ where
  coe f x := (((toSelfAdjoint f).1 : lp (fun _ : X ↦ ℂ) ∞) x).re
  coe_injective f g h := toSelfAdjoint.injective <| Subtype.ext <| Subtype.ext <| lp.ext <|
    funext fun x ↦ by
      have re (f : Observables (classical S)) := Complex.conj_eq_iff_re.mp
        (congrFun (congrArg (⇑) (congrArg Subtype.val (toSelfAdjoint f).2)) x)
      rw [← re f, ← re g]; exact congrArg Complex.ofReal (congrFun h x)

/-- The function of an observable takes real values. -/
lemma ofReal_apply (f : Observables (classical S)) (x : X) :
    (f x : ℂ) = ((toSelfAdjoint f).1 : lp (fun _ : X ↦ ℂ) ∞) x :=
  Complex.conj_eq_iff_re.mp (congrFun (congrArg (⇑) (congrArg Subtype.val (toSelfAdjoint f).2)) x)

@[simp] lemma zero_apply (x : X) : (0 : Observables (classical S)) x = 0 := rfl

@[simp] lemma one_apply (x : X) : (1 : Observables (classical S)) x = 1 := rfl

@[simp] lemma add_apply (f g : Observables (classical S)) (x : X) : (f + g) x = f x + g x := rfl

@[simp] lemma sub_apply (f g : Observables (classical S)) (x : X) : (f - g) x = f x - g x := rfl

@[simp] lemma smul_apply (c : ℝ) (f : Observables (classical S)) (x : X) :
    (c • f) x = c * f x :=
  Complex.re_ofReal_mul _ _

/-- The product of two observables multiplies their values. -/
@[simp] lemma mul_apply (f g : Observables (classical S)) (x : X) : (f * g) x = f x * g x :=
  Complex.ofReal_injective <| by
    rw [Complex.ofReal_mul, ofReal_apply, ofReal_apply, ofReal_apply]; rfl

@[simp] lemma pow_apply (f : Observables (classical S)) (n : ℕ) (x : X) :
    (f ^ n) x = f x ^ n := by
  induction n <;> simp [pow_succ, *]

/-- Observables are ordered by their values. -/
lemma le_def {f g : Observables (classical S)} : f ≤ g ↔ ∀ x, f x ≤ g x :=
  forall_congr' fun x ↦ by rw [← Complex.real_le_real, ofReal_apply, ofReal_apply]; rfl

/-- The square of an observable is positive. -/
lemma sq_nonneg' (f : Observables (classical S)) : 0 ≤ f ^ 2 :=
  le_def.mpr fun x ↦ by simpa using sq_nonneg (f x)

end ProbabilisticTheory.Classical
