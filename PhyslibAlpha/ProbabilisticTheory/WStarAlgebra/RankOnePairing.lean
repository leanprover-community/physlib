/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.WStarAlgebra.TracePairingSurjectivity

/-!

# Rank-one operators in the trace pairing

The trace pairing of a rank-one operator `|x⟩⟨y|` with a trace-class `T` is `⟪y, T x⟫`.

## i. Overview

For a bounded operator `A` and a trace-class operator `T`, the trace pairing of `A |x⟩⟨y|` with `T`
is a matrix coefficient. This recovers a predual element from its values on rank-one operators.

## ii. Key results

- `trace_rankOne_formula` : the trace of a rank-one operator times a trace-class operator.
- `TraceClass.tracePairing_rankOne_left` : the trace pairing with a rank-one operator.

## iii. Table of contents

- A. The trace of a rank-one operator
- B. The trace pairing with a rank-one operator

## iv. References

* None.

-/

@[expose] public section

noncomputable section

namespace ProbabilisticTheory

open scoped ComplexOrder InnerProductSpace

namespace TraceClass

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-!

## A. The trace of a rank-one operator

-/

lemma trace_rankOne_formula (x y : H) :
    trace (InnerProductSpace.rankOne ℂ x y) (isTraceClass_rankOne x y) =
      ⟪y, x⟫_ℂ := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  rw [trace_eq_of_hilbertBasis (isTraceClass_rankOne x y) b]
  have hsum := b.hasSum_inner_mul_inner y x
  have hterm : (fun i : w =>
      ⟪b i, (InnerProductSpace.rankOne ℂ x y) (b i)⟫_ℂ) =
      (fun i : w => ⟪y, b i⟫_ℂ * ⟪b i, x⟫_ℂ) := by
    funext i
    simp only [InnerProductSpace.rankOne_apply, inner_smul_right]
  rw [hterm]
  exact hsum.tsum_eq

/-!

## B. The trace pairing with a rank-one operator

-/

lemma tracePairing_rankOne_left (T : TraceClass H) (x y : H) :
    tracePairing (InnerProductSpace.rankOne ℂ x y) T =
      ⟪y, T.1 x⟫_ℂ := by
  rw [tracePairing_apply]
  have hcycle := trace_mul_cycle (A := InnerProductSpace.rankOne ℂ x y)
    (T := T.1) (isTraceClass_coe T)
  calc
    trace (InnerProductSpace.rankOne ℂ x y * T.1) _ =
        trace (T.1 * InnerProductSpace.rankOne ℂ x y) _ := hcycle
    _ = trace (InnerProductSpace.rankOne ℂ (T.1 x) y) _ := by
      congr 1
      change T.1 ∘L InnerProductSpace.rankOne ℂ x y = _
      exact InnerProductSpace.comp_rankOne x y T.1
    _ = ⟪y, T.1 x⟫_ℂ := trace_rankOne_formula (T.1 x) y

end TraceClass

end ProbabilisticTheory
