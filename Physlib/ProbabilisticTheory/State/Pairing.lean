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

State–effect evaluation gives probabilities that distinguish states and effects alike.

## i. Overview

Evaluating an effect in a state gives a probability, and evaluation is affine in the effect.
A state is determined by its probabilities on all effects. Conversely, an effect is determined
by its probabilities in all states. The pairing therefore separates both sides.

## ii. Key results

- `ProbabilisticTheory.State.apply_mem_Icc` : state–effect evaluation takes values in `[0, 1]`.
- `ProbabilisticTheory.State.apply_mix` : evaluation is affine in the effect argument.
- `ProbabilisticTheory.State.ext_of_effect_eq` : effects separate states.
- `ProbabilisticTheory.Effect.ext_of_forall_apply_eq` : states separate effects.

## iii. Table of contents

- A. State–effect evaluation
- B. Effects separate states
- C. States separate effects

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

/-- A state is determined by its values on effects. -/
lemma ext_of_effect_eq {ω φ : P.State} (h : ∀ e : P.Effect, ω e = φ e) : ω = φ := by
  have hpos (p : PosCone P) : ω p = φ p := by
    obtain ⟨r, hr, hrp⟩ := Effect.exists_pos_smul_mem p.2
    exact mul_left_cancel₀ hr.ne' (by simpa using h ⟨r • p, hrp⟩)
  apply DFunLike.ext
  intro A
  obtain ⟨p, q, rfl⟩ := PosCone.exists_sub A
  rw [map_sub, map_sub, hpos p, hpos q]

end ProbabilisticTheory.State

/-!

## C. States separate effects

-/

namespace ProbabilisticTheory.Effect

variable {P : ProbabilisticTheory}

/-- An effect is determined by its values under all states. -/
lemma ext_of_forall_apply_eq {e f : P.Effect}
    (h : ∀ ω : P.State, ω e = ω f) : e = f :=
  Subtype.ext (State.ext_of_forall_apply_eq h)

end ProbabilisticTheory.Effect
