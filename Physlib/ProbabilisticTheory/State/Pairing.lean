/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.State.Separation
public import Physlib.ProbabilisticTheory.Effect.Convex

/-!
# The state–effect pairing

State–effect evaluation gives probabilities and distinguishes states.

## i. Overview

Evaluating an effect in a state gives a probability. Evaluation is affine in the effect, and
a state is determined by its values on all effects. This identifies states with their
probability-valued functions on effects. The converse separation result and the recovery of
effect distance from states are developed in `Effect/Pairing.lean`.

## ii. Key results

- `ProbabilisticTheory.State.apply_mem_Icc` : state–effect evaluation takes values in `[0, 1]`.
- `ProbabilisticTheory.State.apply_mix` : evaluation is affine in the effect argument.
- `ProbabilisticTheory.State.ext_of_effect_eq` : effects separate states.
- `ProbabilisticTheory.State.injective_apply_effect` : states embed into functions on effects.

## iii. Table of contents

- A. State–effect evaluation
- B. Effects separate states

## iv. References

-/

@[expose] public section

open ProbabilisticTheory

open scoped Effect

namespace ProbabilisticTheory.State

variable {P : ProbabilisticTheory}

/-!

## A. State–effect evaluation

-/

/-- State–effect evaluation takes values in `[0, 1]`. -/
lemma apply_mem_Icc (ω : P.State) (e : P.Effect) : ω e ∈ Set.Icc 0 1 :=
  ⟨map_nonneg ω e.2.1, ω.apply_le_one e.2.2⟩

/-- Evaluation is affine in the effect argument. -/
lemma apply_mix (ω : P.State) (e f : P.Effect) (t : unitInterval) :
    ω (Effect.mix e f t) = (t : ℝ) * ω e + (1 - (t : ℝ)) * ω f := by
  simp [Effect.coe_mix]

/-!

## B. Effects separate states

-/

/-- Two states that agree on all effects agree on every nonnegative element. -/
lemma ext_of_effect_eq_of_nonneg {ω φ : P.State}
    (h : ∀ e : P.Effect, ω e = φ e) {B : P.Observables} (hB : 0 ≤ B) : ω B = φ B := by
  obtain ⟨r, hr, hrB⟩ := Effect.exists_pos_smul_mem hB
  exact mul_left_cancel₀ hr.ne' (by simpa using h ⟨r • B, hrB⟩)

/-- A state is determined by its values on effects. -/
lemma ext_of_effect_eq {ω φ : P.State}
    (h : ∀ e : P.Effect, ω e = φ e) : ω = φ := by
  refine DFunLike.ext _ _ fun A => ?_
  obtain ⟨Ap, An, hAp, hAn, rfl⟩ := ProbabilisticTheory.exists_eq_sub_nonneg A
  rw [map_sub, map_sub, ext_of_effect_eq_of_nonneg h hAp, ext_of_effect_eq_of_nonneg h hAn]

/-- Evaluation on effects is injective on states. -/
lemma injective_apply_effect :
    Function.Injective (fun (ω : P.State) (e : P.Effect) => ω e) :=
  fun _ _ h => ext_of_effect_eq (congrFun h)

end ProbabilisticTheory.State
