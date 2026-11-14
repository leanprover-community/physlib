/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Tactic.Positivity
public import Physlib.ProbabilisticTheory.OrderUnit.Cone

/-!
# Effects

## i. Overview

An effect models a yes/no measurement outcome, ranging continuously between the impossible
outcome `0` and the certain outcome `1`. Formally, it is a point of the order interval `[0, 1]`
inside `P.Observables`. For self-adjoint matrices, effects are exactly the operators
`0 ≤ M ≤ 1` — the elements of a POVM.

## ii. Key results

- `ProbabilisticTheory.Effect` : a bounded measurement outcome, the
  order interval `[0, 1]` of its observables.
- `Effect.mem_iff_mem_posCone_and_one_sub_mem_posCone` : an effect is exactly a positive element
  whose complement from the order unit is also positive.
- `Effect.exists_pos_smul_mem` : every positive observable becomes an effect after scaling it down
  enough.

## iii. Table of contents

- A. Effects

## iv. References

- G. Ludwig, *Foundations of Quantum Mechanics I*, Springer, 1983.
  <https://link.springer.com/book/10.1007/978-3-642-86751-4>

-/

@[expose] public section

open ProbabilisticTheory

/-!

## A. Effects

-/

/-- A bounded measurement outcome. -/
abbrev ProbabilisticTheory.Effect (P : ProbabilisticTheory) := Set.Icc (0 : P.Observables) 1

namespace ProbabilisticTheory.Effect

variable {P : ProbabilisticTheory}

/-- An effect is a positive element whose complement from the order unit is positive. -/
lemma mem_iff_mem_posCone_and_one_sub_mem_posCone {A : P.Observables} :
    A ∈ P.Effect ↔ A ∈ PosCone P ∧ 1 - A ∈ PosCone P := by
  simp only [Set.mem_Icc, PointedCone.mem_positive, sub_nonneg]

instance instZero : Zero P.Effect := ⟨0, le_refl 0, one_nonneg⟩

instance instOne : One P.Effect := ⟨1, one_nonneg, le_refl 1⟩

instance instNonempty : Nonempty P.Effect := ⟨0⟩

@[simp] lemma coe_zero : ((0 : P.Effect) : P.Observables) = 0 := rfl

@[simp] lemma coe_one : ((1 : P.Effect) : P.Observables) = 1 := rfl

/-- Every nonnegative observable becomes an effect after scaling it down by a large enough
positive real: the effect interval reaches in every direction the positive cone does. -/
lemma exists_pos_smul_mem {B : P.Observables} (hB : 0 ≤ B) :
    ∃ r : ℝ, 0 < r ∧ r • B ∈ P.Effect := by
  obtain ⟨n, hn⟩ := exists_nsmul_one_le B
  rw [← Nat.cast_smul_eq_nsmul ℝ] at hn
  refine ⟨((n : ℝ) + 1)⁻¹, by positivity, smul_nonneg (by positivity) hB, ?_⟩
  rw [inv_smul_le_iff_of_pos (by positivity)]
  exact hn.trans (smul_le_smul_of_nonneg_right (by linarith) one_nonneg)

end ProbabilisticTheory.Effect
