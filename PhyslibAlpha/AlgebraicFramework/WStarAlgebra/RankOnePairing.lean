/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.WStarAlgebra.TracePairingSurjectivity

/-!
# Rank-one tests for the concrete predual pairing

Ported from `unbounded-alpha-public`'s `WStarAlgebra/RankOnePairing.lean`. The surjectivity proof
needs rank-one operators as test observables. This module exposes the corresponding formula with an
arbitrary trace-class second argument; it is the matrix-coefficient identity used to recover
positivity of a predual representative of a normal state.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace TraceClass

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem trace_rankOne_formula (x y : H) :
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

theorem tracePairing_rankOne_left (T : TraceClass H) (x y : H) :
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
