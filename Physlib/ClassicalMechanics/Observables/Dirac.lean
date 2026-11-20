/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ClassicalMechanics.Observables.Basic
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

/-- Evaluation at a configuration, a positive functional on the function algebra. -/
noncomputable def eval (x : X) : S →ₚ[ℂ] ℂ where
  toFun f := (f : lp (fun _ : X ↦ ℂ) ∞) x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  monotone' _ _ h := h x

/-- The Dirac state at a configuration `x` evaluates observables at `x`. -/
noncomputable def dirac (x : X) : (ofCStarAlgebra S).State :=
  realEquivComplex.symm.toChannel.comp (Channel.ofComplex (eval x) rfl)

/-- The Dirac state at `x` assigns each observable its value at `x`. -/
@[simp]
lemma dirac_apply (x : X) (f : selfAdjoint S) : dirac x f = toFun f x := rfl

/-! ## B. Sharp values -/

/-- The square of the mean is at most the mean of the square. -/
lemma sq_apply_le_apply_sq (ω : (ofCStarAlgebra S).State) (f : selfAdjoint S) :
    ω f ^ 2 ≤ ω (f ^ 2) := by
  have hsq : (f - ω f • 1) ^ 2 = f ^ 2 - (2 * ω f) • f + (ω f ^ 2) • 1 :=
    toFun_injective (funext fun x ↦ by simp [sq]; ring)
  have h := map_nonneg ω (selfAdjoint_sq_nonneg (f - ω f • 1))
  simp only [hsq, map_add, map_sub, map_smul, map_one, smul_eq_mul] at h
  nlinarith

/-- The Dirac state at `x` is the state in which every observable has the sharp value it takes
at `x`. -/
lemma eq_dirac_iff {ω : (ofCStarAlgebra S).State} {x : X} :
    ω = dirac x ↔ ∀ f, ω ((f - toFun f x • 1) ^ 2) = 0 := by
  refine ⟨fun h f ↦ by rw [h, dirac_apply]; simp [sq], fun h ↦ Channel.ext fun f ↦ ?_⟩
  have hsq := sq_apply_le_apply_sq ω (f - toFun f x • 1)
  rw [h, map_sub, map_smul, map_one, smul_eq_mul, mul_one] at hsq
  exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm hsq (sq_nonneg _)))

/-! ## C. Purity -/

/-- A classical system in a definite configuration is in a pure state. -/
lemma isPure_dirac (x : X) : (dirac x : (ofCStarAlgebra S).State).IsPure := by
  refine State.isPure_iff_forall_mix_eq.mpr fun φ ψ t ht0 ht1 hmix ↦ ?_
  have h f := State.apply_eq_zero_of_mix_eq ht0 ht1 hmix
    (selfAdjoint_sq_nonneg _) (eq_dirac_iff.mp rfl f)
  exact ⟨eq_dirac_iff.mpr (h · |>.1), eq_dirac_iff.mpr (h · |>.2)⟩

end ProbabilisticTheory.Classical
