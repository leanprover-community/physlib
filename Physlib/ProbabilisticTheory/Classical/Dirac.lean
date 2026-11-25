/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.Classical.Basic
public import Physlib.Meta.TODO.Basic
public import Physlib.ProbabilisticTheory.CStarAlgebra.Channel
public import Physlib.ProbabilisticTheory.State.Convex

/-!
# Dirac states

A classical system in a definite configuration is in a pure state.

## i. Overview

The Dirac state at a configuration `x` assigns to each observable its value at `x`. It describes
a classical system whose configuration is known exactly, so every observable has vanishing
variance. Conversely, a state in which every observable has vanishing variance around its value
at `x` is the Dirac state at `x`. Dirac states are therefore pure.

## ii. Key results

- `ProbabilisticTheory.Classical.dirac` : the Dirac state at a configuration.
- `ProbabilisticTheory.Classical.eq_dirac_iff` : the Dirac state is the state in which every
  observable has a sharp value.
- `ProbabilisticTheory.Classical.isPure_dirac` : Dirac states are pure.

## iii. Table of contents

- A. Dirac states
- B. Sharp values
- C. Purity

## iv. References

-/

@[expose] public section

open scoped ENNReal ComplexOrder

namespace ProbabilisticTheory.Classical

variable {X : Type*} {S : StarSubalgebra ℂ (lp (fun _ : X ↦ ℂ) ∞)}
  [IsClosed (S : Set (lp (fun _ : X ↦ ℂ) ∞))]

/-! ## A. Dirac states -/

variable (S) in
/-- Reading off the value of each quantity in the configuration `x`. -/
noncomputable def eval (x : X) : S →ₚ[ℂ] ℂ where
  toFun f := (f : lp (fun _ : X ↦ ℂ) ∞) x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  monotone' _ _ h := h x

variable (S) in
/-- The Dirac state at a configuration `x` evaluates observables at `x`. -/
noncomputable def dirac (x : X) : State (classical S) :=
  realEquivComplex.symm.toChannel.comp (Channel.ofComplex (eval S x) rfl)

/-- The Dirac state at `x` assigns each observable its value at `x`. -/
@[simp]
lemma dirac_apply (x : X) (f : Observables (classical S)) : dirac S x f = f x := rfl

/-! ## B. Sharp values -/

TODO "Move `sq_apply_le_apply_sq` to the uncertainty relations of states."

/-- The square of the mean is at most the mean of the square. -/
lemma sq_apply_le_apply_sq (ω : State (classical S)) (f : Observables (classical S)) :
    ω f ^ 2 ≤ ω (f ^ 2) := by
  have hsq : (f - ω f • 1) ^ 2 = f ^ 2 - (2 * ω f) • f + (ω f ^ 2) • 1 :=
    DFunLike.ext _ _ fun x ↦ by simp; ring
  have h := map_nonneg ω (sq_nonneg' (f - ω f • 1))
  simp [hsq] at h
  nlinarith

/-- The Dirac state at `x` is the state in which every observable has the sharp value it takes
at `x`. -/
lemma eq_dirac_iff {ω : State (classical S)} {x : X} :
    ω = dirac S x ↔ ∀ f, ω ((f - f x • 1) ^ 2) = 0 := by
  refine ⟨fun h f ↦ ?_, fun h ↦ Channel.ext fun f ↦ ?_⟩
  · simp [h]
  · simpa [h, sub_eq_zero] using sq_apply_le_apply_sq ω (f - f x • 1)

/-! ## C. Purity -/

/-- A classical system in a definite configuration is in a pure state. -/
lemma isPure_dirac (x : X) : (dirac S x).IsPure := by
  refine State.isPure_iff_forall_mix_eq.mpr fun φ ψ t ht0 ht1 hmix ↦ ?_
  have h f := State.apply_eq_zero_of_mix_eq ht0 ht1 hmix
    (sq_nonneg' _) (eq_dirac_iff.mp rfl f)
  exact ⟨eq_dirac_iff.mpr (h · |>.1), eq_dirac_iff.mpr (h · |>.2)⟩

end ProbabilisticTheory.Classical
