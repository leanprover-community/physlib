/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import PhyslibAlpha.AlgebraicFramework.OrderUnit.Basic

/-!

# The order-unit norm

## i. Overview

`IsOrderUnit` only lets us compare outcomes to `1`; `IsArchimedeanOrderUnit` is what turns that
into an actual distance. `orderUnitNorm x` is the least `r` with `-r • 1 ≤ x ≤ r • 1` — how many
copies of the certain outcome it takes to sandwich `x` on both sides. This is a genuine norm, not
just a seminorm, exactly because nothing is infinitesimally close to `0` without being `0`.

## ii. Key definitions and results

- `IsArchimedeanOrderUnit.orderUnitNorm`
- `IsArchimedeanOrderUnit.orderUnitNormedAddCommGroup`

## iii. Table of contents

- A. Order-unit bounds
- B. Norm laws
- C. Positive definiteness
- D. The induced normed group

-/

@[expose] public section

namespace IsArchimedeanOrderUnit

variable {E : Type*} [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module ℝ E]
  [PosSMulMono ℝ E] [One E] [IsArchimedeanOrderUnit E]

/-! ## A. Order-unit bounds -/

/-- The nonnegative real bounds of `x` by the order unit. -/
def orderUnitBounds (x : E) : Set ℝ :=
  {r | 0 ≤ r ∧ -(r • (1 : E)) ≤ x ∧ x ≤ r • (1 : E)}

/-- The order-unit norm of `x`: the least nonnegative real `r` such that
`-r • 1 ≤ x ≤ r • 1`. -/
noncomputable def orderUnitNorm (x : E) : ℝ := sInf (orderUnitBounds x)

/-- Every element has an order-unit bound. -/
lemma orderUnitBounds_nonempty (x : E) : (orderUnitBounds x).Nonempty := by
  obtain ⟨n, hn⟩ := IsOrderUnit.exists_nsmul_one_le x
  obtain ⟨m, hm⟩ := IsOrderUnit.exists_nsmul_one_le (-x)
  have hn' : x ≤ (n : ℝ) • (1 : E) := by
    simpa only [Nat.cast_smul_eq_nsmul] using hn
  have hm' : -x ≤ (m : ℝ) • (1 : E) := by
    simpa only [Nat.cast_smul_eq_nsmul] using hm
  let r : ℝ := max (n : ℝ) m
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    exact le_trans (Nat.cast_nonneg n) (le_max_left _ _)
  refine ⟨r, hr_nonneg, ?_, ?_⟩
  · have hmr : (m : ℝ) ≤ r := by
      dsimp [r]
      exact le_max_right _ _
    have hnonneg : 0 ≤ (r - m) • (1 : E) :=
      smul_nonneg (sub_nonneg.mpr hmr) IsOrderUnit.one_nonneg
    have hle : (m : ℝ) • (1 : E) ≤ r • (1 : E) := by
      calc
        (m : ℝ) • (1 : E) = r • (1 : E) - (r - m) • (1 : E) := by
          rw [← sub_smul, sub_sub_cancel]
        _ ≤ r • (1 : E) := sub_le_self _ hnonneg
    simpa only [neg_smul, neg_neg] using (neg_le_neg hle).trans (neg_le_neg hm')
  · have hnr : (n : ℝ) ≤ r := by
      dsimp [r]
      exact le_max_left _ _
    have hnonneg : 0 ≤ (r - n) • (1 : E) :=
      smul_nonneg (sub_nonneg.mpr hnr) IsOrderUnit.one_nonneg
    calc
      x ≤ (n : ℝ) • (1 : E) := hn'
      _ = r • (1 : E) - (r - n) • (1 : E) := by
        rw [← sub_smul, sub_sub_cancel]
      _ ≤ r • (1 : E) := sub_le_self _ hnonneg

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] [IsArchimedeanOrderUnit E] in
/-- The order-unit bounds are bounded below by zero. -/
lemma orderUnitBounds_bddBelow (x : E) : BddBelow (orderUnitBounds x) :=
  ⟨0, fun _ hr ↦ hr.1⟩

/-- The order-unit norm is nonnegative. -/
lemma orderUnitNorm_nonneg (x : E) : 0 ≤ orderUnitNorm x :=
  le_csInf (orderUnitBounds_nonempty x) fun _ hr ↦ hr.1

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] [IsArchimedeanOrderUnit E] in
/-- Any order-unit bound is an upper bound for the order-unit norm. -/
lemma orderUnitNorm_le {x : E} {r : ℝ} (hr : r ∈ orderUnitBounds x) : orderUnitNorm x ≤ r :=
  csInf_le (orderUnitBounds_bddBelow x) hr

/-! ## B. Norm laws -/

/-- The order-unit norm of zero is zero. -/
@[simp]
lemma orderUnitNorm_zero : orderUnitNorm (0 : E) = 0 := by
  apply le_antisymm
  · exact orderUnitNorm_le ⟨le_rfl, by simp, by simp⟩
  · exact orderUnitNorm_nonneg 0

omit [PosSMulMono ℝ E] [IsArchimedeanOrderUnit E] in
/-- Negating an element preserves its order-unit bounds. -/
lemma orderUnitBounds_neg (x : E) : orderUnitBounds (-x) = orderUnitBounds x := by
  ext r
  constructor
  · rintro ⟨hr, hlow, hupp⟩
    exact ⟨hr, by simpa only [neg_neg] using neg_le_neg hupp,
      by simpa only [neg_smul, neg_neg] using neg_le_neg hlow⟩
  · rintro ⟨hr, hlow, hupp⟩
    exact ⟨hr, by simpa only [neg_neg] using neg_le_neg hupp,
      by simpa only [neg_smul, neg_neg] using neg_le_neg hlow⟩

omit [PosSMulMono ℝ E] [IsArchimedeanOrderUnit E] in
/-- Negating an element preserves its order-unit norm. -/
lemma orderUnitNorm_neg (x : E) : orderUnitNorm (-x) = orderUnitNorm x := by
  unfold orderUnitNorm
  rw [orderUnitBounds_neg]

omit [PosSMulMono ℝ E] [IsArchimedeanOrderUnit E] in
/-- The sum of two order-unit bounds is an order-unit bound of the sum. -/
lemma add_mem_orderUnitBounds {x y : E} {r s : ℝ} (hr : r ∈ orderUnitBounds x)
    (hs : s ∈ orderUnitBounds y) : r + s ∈ orderUnitBounds (x + y) := by
  refine ⟨add_nonneg hr.1 hs.1, ?_, ?_⟩
  · rw [add_smul, neg_add]
    exact add_le_add hr.2.1 hs.2.1
  · rw [add_smul]
    exact add_le_add hr.2.2 hs.2.2

/-- Order-unit bounds approximate the order-unit norm arbitrarily closely from above. -/
lemma exists_orderUnitBound_lt_orderUnitNorm_add (x : E) {ε : ℝ} (hε : 0 < ε) :
    ∃ r ∈ orderUnitBounds x, r < orderUnitNorm x + ε := by
  apply exists_lt_of_csInf_lt (orderUnitBounds_nonempty x)
  change sInf (orderUnitBounds x) < sInf (orderUnitBounds x) + ε
  exact lt_add_of_pos_right _ hε

/-- The order-unit norm satisfies the triangle inequality. -/
lemma orderUnitNorm_add_le (x y : E) :
    orderUnitNorm (x + y) ≤ orderUnitNorm x + orderUnitNorm y := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨r, hr, hr_lt⟩ := exists_orderUnitBound_lt_orderUnitNorm_add x (half_pos hε)
  obtain ⟨s, hs, hs_lt⟩ := exists_orderUnitBound_lt_orderUnitNorm_add y (half_pos hε)
  calc
    orderUnitNorm (x + y) ≤ r + s := orderUnitNorm_le (add_mem_orderUnitBounds hr hs)
    _ ≤ (orderUnitNorm x + ε / 2) + (orderUnitNorm y + ε / 2) :=
      add_le_add hr_lt.le hs_lt.le
    _ = orderUnitNorm x + orderUnitNorm y + ε := by
      rw [show (orderUnitNorm x + ε / 2) + (orderUnitNorm y + ε / 2) =
        (orderUnitNorm x + orderUnitNorm y) + (ε / 2 + ε / 2) by ac_rfl, add_halves]

/-! ## C. Positive definiteness -/

/-- If the order-unit norm of `x` vanishes, `x` lies below every positive multiple of the unit. -/
lemma le_pos_smul_one_of_orderUnitNorm_eq_zero {x : E} (hx : orderUnitNorm x = 0)
    {ε : ℝ} (hε : 0 < ε) : x ≤ ε • (1 : E) := by
  have hlt : orderUnitNorm x < ε := hx ▸ hε
  change sInf (orderUnitBounds x) < ε at hlt
  obtain ⟨r, hr, hrε⟩ := exists_lt_of_csInf_lt (orderUnitBounds_nonempty x) hlt
  have hnonneg : 0 ≤ (ε - r) • (1 : E) :=
    smul_nonneg (sub_nonneg.mpr hrε.le) IsOrderUnit.one_nonneg
  have hbound : r • (1 : E) ≤ ε • (1 : E) := by
    calc
      r • (1 : E) = ε • (1 : E) - (ε - r) • (1 : E) := by
        rw [← sub_smul, sub_sub_cancel]
      _ ≤ ε • (1 : E) := sub_le_self _ hnonneg
  exact hr.2.2.trans hbound

/-- The order-unit norm is positive-definite precisely because the order unit is Archimedean:
this is what tells apart two outcomes with `orderUnitNorm (x - y) = 0` as actually the same
outcome, not two indistinguishable-but-different ones. -/
lemma orderUnitNorm_eq_zero_iff {x : E} : orderUnitNorm x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    have hle_zero : x ≤ 0 := IsArchimedeanOrderUnit.le_zero_of_forall_pos_smul_one_le x
      fun _ hε ↦ le_pos_smul_one_of_orderUnitNorm_eq_zero hx hε
    have hneg : orderUnitNorm (-x) = 0 := by simpa only [orderUnitNorm_neg] using hx
    have hnonneg : 0 ≤ x := neg_nonpos.mp <|
      IsArchimedeanOrderUnit.le_zero_of_forall_pos_smul_one_le (-x)
        fun _ hε ↦ le_pos_smul_one_of_orderUnitNorm_eq_zero hneg hε
    exact le_antisymm hle_zero hnonneg
  · rintro rfl
    exact orderUnitNorm_zero

/-! ## D. The induced normed group -/

/-- The order-unit norm packaged as an additive-group norm. -/
noncomputable def orderUnitAddGroupNorm : AddGroupNorm E where
  toFun := orderUnitNorm
  map_zero' := orderUnitNorm_zero
  add_le' := orderUnitNorm_add_le
  neg' := orderUnitNorm_neg
  eq_zero_of_map_eq_zero' _x hx := orderUnitNorm_eq_zero_iff.mp hx

/-- The additive normed-group structure induced by the order-unit norm: `E` is now a genuine
metric space, with `orderUnitNorm (x - y)` the distance between two outcomes. -/
@[instance_reducible]
noncomputable def orderUnitNormedAddCommGroup : NormedAddCommGroup E :=
  orderUnitAddGroupNorm.toNormedAddCommGroup

end IsArchimedeanOrderUnit
