/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.State.Metric
public import Mathlib.Analysis.Convex.Cone.Dual
public import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Separation by states

States determine positivity, the order-unit norm, and equality of observables.

## i. Overview

In an Archimedean order-unit space, states determine the entire ordered normed structure. An
element is positive exactly when every state assigns it a nonnegative value, and its order-unit
norm is `‖A‖₁ = sup { |ω A| : ω a state }`. Consequently, states separate points: two elements are
equal whenever every state assigns them the same value.

The main ingredient is Hahn–Banach separation of a point from the positive cone. Applied to an
element `A ≱ 0`, it produces a state `ω` with `ω A < 0`. Everything else follows from this one
separation fact.

## ii. Key results

- `UnitalPositiveLinearMap.exists_apply_neg_of_not_nonneg` : every element outside the positive
  cone is separated from it by a state.
- `UnitalPositiveLinearMap.nonneg_iff_forall_state_nonneg` : states determine the positive cone.
- `UnitalPositiveLinearMap.sSup_abs_apply_eq_orderUnitNorm` : states determine the order-unit norm.
- `UnitalPositiveLinearMap.ext_of_forall_apply_eq` : states separate points.

## iii. Table of contents

- A. Separating points from the cone
- B. The positive cone
- C. The order-unit norm
- D. Separation of points

## iv. References

-/

@[expose] public section

open ProbabilisticTheory
open ArchimedeanOrderUnitSpace
open OrderUnitSpace

variable {E : Type*}

namespace UnitalPositiveLinearMap

/-!

## A. Separating points from the cone

-/

/-- A positive functional vanishing at the order unit vanishes everywhere. -/
lemma apply_eq_zero_of_apply_one_eq_zero [OrderUnitSpace E] {p : E →ₚ[ℝ] ℝ}
    (h1 : p (1 : E) = 0) (A : E) : p A = 0 := by
  obtain ⟨n, hl, hu⟩ := exists_two_sided_bound A
  exact le_antisymm (by simpa [h1] using p.monotone' hu)
    (by simpa [h1] using p.monotone' hl)

variable [ArchimedeanOrderUnitSpace E]

/-- Every element outside the positive cone is strictly separated from it by a state. -/
lemma exists_apply_neg_of_not_nonneg {A : E} (hA : ¬ 0 ≤ A) : ∃ ω : 𝓢[ℝ, E], ω A < 0 := by
  obtain ⟨f, hf_nonneg, hfA⟩ := ProperCone.hyperplane_separation_point
    ⟨PointedCone.positive ℝ E, isClosed_Ici_zero⟩ hA
  have hf_one_pos : 0 < f (1 : E) := (hf_nonneg 1 one_nonneg).lt_of_ne fun h1 =>
    hfA.ne (apply_eq_zero_of_apply_one_eq_zero (p := .mk₀ _ hf_nonneg) h1.symm A)
  exact ⟨ofLinearMap ((f (1 : E))⁻¹ • f.toLinearMap)
    (fun B hB => mul_nonneg (inv_nonneg.mpr hf_one_pos.le) (hf_nonneg B hB))
    (by simp [hf_one_pos.ne']), mul_neg_of_pos_of_neg (inv_pos.mpr hf_one_pos) hfA⟩

/-!

## B. The positive cone

-/

/-- An element is positive iff every state assigns it a nonnegative value. -/
lemma nonneg_iff_forall_state_nonneg (A : E) : 0 ≤ A ↔ ∀ ω : 𝓢[ℝ, E], 0 ≤ ω A := by
  constructor
  · exact fun hA ω => map_nonneg ω hA
  · contrapose!
    exact exists_apply_neg_of_not_nonneg

/-!

## C. The order-unit norm

-/

/-- Every nontrivial Archimedean order-unit space has a state. -/
instance instNonemptyState [Nontrivial E] : Nonempty (𝓢[ℝ, E]) := by
  obtain ⟨A, hA⟩ := exists_ne (0 : E)
  by_cases h : 0 ≤ A
  · exact (exists_apply_neg_of_not_nonneg (A := -A)
      (fun hn => hA (le_antisymm (neg_nonneg.mp hn) h))).nonempty
  · exact (exists_apply_neg_of_not_nonneg h).nonempty

/-- The order-unit norm is at most `r` iff every state predicts an absolute value at most `r`. -/
lemma orderUnitNorm_le_iff_forall_abs_apply_le [Nontrivial E] (A : E) (r : ℝ) :
    orderUnitNorm A ≤ r ↔ ∀ ω : 𝓢[ℝ, E], |ω A| ≤ r := by
  refine ⟨fun h ω => (abs_apply_le_orderUnitNorm ω A).trans h, fun h => ?_⟩
  refine orderUnitNorm_le ⟨(abs_nonneg _).trans (h Classical.ofNonempty), ?_, ?_⟩
  · rw [neg_le_iff_add_nonneg', nonneg_iff_forall_state_nonneg]
    exact fun ω => by simpa [neg_le_iff_add_nonneg'] using (abs_le.mp (h ω)).1
  · rw [← sub_nonneg, nonneg_iff_forall_state_nonneg]
    exact fun ω => by simpa [sub_nonneg] using (abs_le.mp (h ω)).2

/-- The order-unit norm is the supremum of `|ω A|` over all states `ω`. -/
lemma sSup_abs_apply_eq_orderUnitNorm [Nontrivial E] (A : E) :
    sSup (Set.range fun ω : 𝓢[ℝ, E] => |ω A|) = orderUnitNorm A := by
  exact eq_of_forall_ge_iff fun r => (ciSup_le_iff ⟨orderUnitNorm A,
    Set.forall_mem_range.mpr (fun ω => abs_apply_le_orderUnitNorm ω A)⟩).trans
    (orderUnitNorm_le_iff_forall_abs_apply_le A r).symm

/-- The order unit has norm exactly `1`. -/
@[simp]
lemma orderUnitNorm_one [Nontrivial E] : orderUnitNorm (1 : E) = 1 := by
  simpa using (sSup_abs_apply_eq_orderUnitNorm (1 : E)).symm

/-!

## D. Separation of points

-/

/-- States separate points: if `ω A = ω B` for every state `ω`, then `A = B`. -/
lemma ext_of_forall_apply_eq {A B : E} (h : ∀ ω : 𝓢[ℝ, E], ω A = ω B) : A = B := by
  apply le_antisymm <;> rw [← sub_nonneg, nonneg_iff_forall_state_nonneg] <;>
    intro ω <;> rw [map_sub, h ω, sub_self]

end UnitalPositiveLinearMap
