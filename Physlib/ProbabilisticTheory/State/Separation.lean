/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.State.Metric
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Separation by states

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

-/

@[expose] public section

open ArchimedeanOrderUnitSpace

variable {E : Type*} [ArchimedeanOrderUnitSpace E]

namespace UnitalPositiveLinearMap

/-!

## A. Separating points from the cone

-/

/-- A positive functional vanishing at the order unit vanishes everywhere. -/
lemma apply_eq_zero_of_apply_one_eq_zero {p : E →ₚ[ℝ] ℝ}
    (h1 : p (1 : E) = 0) (A : E) :
    p A = 0 := by
  obtain ⟨n, hn⟩ := OrderUnitSpace.exists_nsmul_one_le A
  obtain ⟨m, hm⟩ := OrderUnitSpace.exists_nsmul_one_le (-A)
  exact le_antisymm (by simpa [h1] using p.monotone' hn) (by simpa [h1] using p.monotone' hm)

/-- Every element outside the positive cone is strictly separated from it by a state. -/
lemma exists_apply_neg_of_not_nonneg {A : E} (hA : ¬ 0 ≤ A) : ∃ ω : 𝓢[ℝ, E], ω A < 0 := by
  obtain ⟨f, u, hfA, hcone⟩ := geometric_hahn_banach_point_closed
    (convex_Ici (0 : E)) isClosed_Ici_zero hA
  have hu : u < 0 := by simpa using hcone 0 le_rfl
  have hf_nonneg : ∀ B : E, 0 ≤ B → 0 ≤ f B := fun B hB => by
    by_contra! hfB
    have hsep := hcone (((u - 1) / f B) • B)
      (smul_nonneg (div_nonneg_of_nonpos (by linarith) hfB.le) hB)
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hfB.ne] at hsep
    linarith
  have hf_one_pos : 0 < f (1 : E) := (hf_nonneg 1 OrderUnitSpace.one_nonneg).lt_of_ne fun h1 => by
    have : f A = 0 := apply_eq_zero_of_apply_one_eq_zero (p := .mk₀ _ hf_nonneg) h1.symm A
    linarith [hfA.trans hu]
  exact ⟨ofLinearMap ((f (1 : E))⁻¹ • f.toLinearMap)
    (fun B hB => mul_nonneg (inv_nonneg.mpr hf_one_pos.le) (hf_nonneg B hB))
    (by simp [hf_one_pos.ne']), mul_neg_of_pos_of_neg (inv_pos.mpr hf_one_pos) (hfA.trans hu)⟩

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
  refine (exists_apply_neg_of_not_nonneg (A := -1) fun h => ?_).nonempty
  have h1 : (1 : E) = 0 := le_antisymm (neg_nonneg.mp h) OrderUnitSpace.one_nonneg
  have hz (B : E) : B = 0 := by
    obtain ⟨n, hl, hu⟩ := OrderUnitSpace.exists_two_sided_bound B
    exact le_antisymm (by simpa [h1] using hu) (by simpa [h1] using hl)
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  exact hab ((hz a).trans (hz b).symm)

/-- If `A ≤ r • 1` fails, some state predicts more than `r` for `A`. -/
lemma exists_state_apply_gt_of_not_le {A : E} {r : ℝ} (h : ¬ A ≤ r • (1 : E)) :
    ∃ ω : 𝓢[ℝ, E], r < ω A := by
  obtain ⟨ω, hω⟩ := exists_apply_neg_of_not_nonneg (A := r • 1 - A) (by rwa [sub_nonneg])
  exact ⟨ω, by simpa [map_sub] using hω⟩

/-- Any scalar below the order-unit norm of `A` is exceeded by `|ω A|` for some state `ω`. -/
lemma exists_state_abs_apply_gt_of_lt_orderUnitNorm [Nontrivial E] (A : E) {r : ℝ}
    (hr : r < orderUnitNorm A) : ∃ ω : 𝓢[ℝ, E], r < |ω A| := by
  rcases lt_or_ge r 0 with hr0 | hr0
  · obtain ⟨ω⟩ := (inferInstance : Nonempty (𝓢[ℝ, E]))
    exact ⟨ω, hr0.trans_le (abs_nonneg _)⟩
  rcases not_and_or.1 fun h : -(r • (1 : E)) ≤ A ∧ A ≤ r • 1 =>
    (orderUnitNorm_le ⟨hr0, h.1, h.2⟩).not_gt hr with h | h
  · obtain ⟨ω, hω⟩ := exists_state_apply_gt_of_not_le (A := -A) (by rwa [neg_le] at h)
    exact ⟨ω, hω.trans_le (by simpa using neg_le_abs (ω A))⟩
  · obtain ⟨ω, hω⟩ := exists_state_apply_gt_of_not_le h
    exact ⟨ω, hω.trans_le (le_abs_self _)⟩

/-- The order-unit norm is the supremum of `|ω A|` over all states `ω`. -/
lemma sSup_abs_apply_eq_orderUnitNorm [Nontrivial E] (A : E) :
    sSup (Set.range fun ω : 𝓢[ℝ, E] => |ω A|) = orderUnitNorm A := by
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt (Set.range_nonempty _)
    (by rintro _ ⟨ω, rfl⟩; exact abs_apply_le_orderUnitNorm ω A) fun r hr => ?_
  obtain ⟨ω, hω⟩ := exists_state_abs_apply_gt_of_lt_orderUnitNorm A hr
  exact ⟨_, ⟨ω, rfl⟩, hω⟩

/-- The order unit has norm exactly `1`. -/
@[simp]
lemma orderUnitNorm_one [Nontrivial E] : orderUnitNorm (1 : E) = 1 := by
  rw [← sSup_abs_apply_eq_orderUnitNorm]
  simp

/-!

## D. Separation of points

-/

/-- States separate points: if `ω A = ω B` for every state `ω`, then `A = B`. -/
lemma ext_of_forall_apply_eq {A B : E} (h : ∀ ω : 𝓢[ℝ, E], ω A = ω B) : A = B := by
  apply le_antisymm <;> rw [← sub_nonneg, nonneg_iff_forall_state_nonneg] <;>
    intro ω <;> rw [map_sub, h ω, sub_self]

end UnitalPositiveLinearMap
