/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Topology.Sequences
public import PhyslibAlpha.AlgebraicFramework.OrderUnit.Basic
public import PhyslibAlpha.AlgebraicFramework.OrderUnit.Channel.Basic

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
- `IsArchimedeanOrderUnit.isClosed_nonneg_orderUnitNorm`

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

private lemma orderUnitNorm_smul_le_of_nonneg {c : ℝ} (hc : 0 ≤ c) (x : E) :
    orderUnitNorm (c • x) ≤ c * orderUnitNorm x := by
  apply le_of_forall_pos_le_add
  intro ε hε
  rcases hc.eq_or_lt with rfl | hc
  · simpa using hε.le
  · obtain ⟨r, hr, hrlt⟩ := exists_orderUnitBound_lt_orderUnitNorm_add x (div_pos hε hc)
    have hmem : c * r ∈ orderUnitBounds (c • x) := by
      refine ⟨mul_nonneg hc.le hr.1, ?_, ?_⟩
      · calc -((c * r) • (1 : E)) = c • (-(r • (1 : E))) := by module
          _ ≤ c • x := smul_le_smul_of_nonneg_left hr.2.1 hc.le
      · calc c • x ≤ c • (r • (1 : E)) := smul_le_smul_of_nonneg_left hr.2.2 hc.le
          _ = (c * r) • (1 : E) := by module
    calc
      orderUnitNorm (c • x) ≤ c * r := orderUnitNorm_le hmem
      _ ≤ c * (orderUnitNorm x + ε / c) := (mul_lt_mul_of_pos_left hrlt hc).le
      _ = c * orderUnitNorm x + ε := by field_simp

/-- The order-unit norm is bounded by the usual product under real scalar multiplication. -/
lemma orderUnitNorm_smul_le (c : ℝ) (x : E) :
    orderUnitNorm (c • x) ≤ |c| * orderUnitNorm x := by
  rcases le_total 0 c with hc | hc
  · rw [abs_of_nonneg hc]
    exact orderUnitNorm_smul_le_of_nonneg hc x
  · rw [abs_of_nonpos hc, show c • x = -((-c) • x) by rw [neg_smul, neg_neg],
      orderUnitNorm_neg]
    exact orderUnitNorm_smul_le_of_nonneg (neg_nonneg.mpr hc) x

/-- The order-unit norm is absolutely homogeneous under real scalar multiplication. -/
lemma orderUnitNorm_smul (c : ℝ) (x : E) :
    orderUnitNorm (c • x) = |c| * orderUnitNorm x := by
  apply le_antisymm (orderUnitNorm_smul_le c x)
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · have hback := orderUnitNorm_smul_le c⁻¹ (c • x)
    rw [inv_smul_smul₀ hc, abs_inv] at hback
    calc
      |c| * orderUnitNorm x ≤ |c| * (|c|⁻¹ * orderUnitNorm (c • x)) :=
        mul_le_mul_of_nonneg_left hback (abs_nonneg c)
      _ = orderUnitNorm (c • x) := by field_simp

private lemma smul_one_mono {r s : ℝ} (hrs : r ≤ s) :
    r • (1 : E) ≤ s • (1 : E) := by
  have hnonneg : 0 ≤ (s - r) • (1 : E) :=
    smul_nonneg (sub_nonneg.mpr hrs) IsOrderUnit.one_nonneg
  calc
    r • (1 : E) = s • (1 : E) - (s - r) • (1 : E) := by
      rw [← sub_smul, sub_sub_cancel]
    _ ≤ s • (1 : E) := sub_le_self _ hnonneg

/-- The order-unit norm itself is an upper order-unit bound, rather than merely the infimum of
strictly larger bounds. This is exactly where Archimedeanity closes the positive cone. -/
lemma le_orderUnitNorm_smul_one (x : E) : x ≤ orderUnitNorm x • (1 : E) := by
  apply sub_nonpos.mp
  apply IsArchimedeanOrderUnit.le_zero_of_forall_pos_smul_one_le
  intro ε hε
  obtain ⟨r, hr, hrlt⟩ := exists_orderUnitBound_lt_orderUnitNorm_add x hε
  calc
    x - orderUnitNorm x • (1 : E) ≤ r • (1 : E) - orderUnitNorm x • (1 : E) :=
      sub_le_sub_right hr.2.2 _
    _ = (r - orderUnitNorm x) • (1 : E) := by rw [sub_smul]
    _ ≤ ε • (1 : E) := smul_one_mono (by linarith)

/-- The order-unit norm itself is also a lower order-unit bound. -/
lemma neg_orderUnitNorm_smul_one_le (x : E) : -(orderUnitNorm x • (1 : E)) ≤ x := by
  have h := le_orderUnitNorm_smul_one (-x)
  rw [orderUnitNorm_neg] at h
  simpa only [neg_smul, neg_neg] using neg_le_neg h

/-- The infimum defining the order-unit norm is attained. -/
lemma orderUnitNorm_mem_orderUnitBounds (x : E) : orderUnitNorm x ∈ orderUnitBounds x :=
  ⟨orderUnitNorm_nonneg x, neg_orderUnitNorm_smul_one_le x, le_orderUnitNorm_smul_one x⟩

/-- A nonnegative scalar bounds `x` by the order unit exactly when it is at least the
order-unit norm. -/
lemma mem_orderUnitBounds_iff {x : E} {r : ℝ} :
    r ∈ orderUnitBounds x ↔ orderUnitNorm x ≤ r := by
  constructor
  · exact orderUnitNorm_le
  · intro h
    exact ⟨orderUnitNorm_nonneg x |>.trans h,
      (neg_le_neg (smul_one_mono h)).trans (neg_orderUnitNorm_smul_one_le x),
      (le_orderUnitNorm_smul_one x).trans (smul_one_mono h)⟩

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

/-- The real normed-space structure induced by the order-unit norm. This is a reducible
definition rather than an instance because `E` may already carry a different normed-space
structure whose norm must first be proved equal to the order-unit norm. -/
@[instance_reducible]
noncomputable def orderUnitNormedSpace :
    @NormedSpace ℝ E _
      (orderUnitNormedAddCommGroup (E := E)).toSeminormedAddCommGroup := by
  letI := orderUnitNormedAddCommGroup (E := E)
  refine ⟨?_⟩
  intro c x
  change orderUnitNorm (c • x) ≤ |c| * orderUnitNorm x
  exact orderUnitNorm_smul_le c x

/-! ## E. Closedness of the positive cone -/

/-- The positive cone is closed in the topology induced by the order-unit norm. -/
lemma isClosed_nonneg_orderUnitNorm :
    let _ := orderUnitNormedAddCommGroup (E := E)
    IsClosed {x : E | 0 ≤ x} := by
  let _ := orderUnitNormedAddCommGroup (E := E)
  apply IsSeqClosed.isClosed
  intro x p hx hp
  apply neg_nonpos.mp
  apply IsArchimedeanOrderUnit.le_zero_of_forall_pos_smul_one_le
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hp ε hε
  have hdist := hN N le_rfl
  have hnorm : orderUnitNorm (p - x N) < ε := by
    rw [dist_eq_norm] at hdist
    change orderUnitNorm (x N - p) < ε at hdist
    calc
      orderUnitNorm (p - x N) = orderUnitNorm (-(p - x N)) :=
        (orderUnitNorm_neg (p - x N)).symm
      _ = orderUnitNorm (x N - p) := by rw [neg_sub]
      _ < ε := hdist
  have hdiff : -(ε • (1 : E)) ≤ p - x N := by
    exact (neg_le_neg (smul_one_mono hnorm.le)).trans
      (neg_orderUnitNorm_smul_one_le (p - x N))
  have hnegp : -p ≤ ε • (1 : E) - x N := by
    have hshift := add_le_add_right (neg_le_neg hdiff) (-x N)
    convert hshift using 1 <;> abel
  calc
    -p ≤ ε • (1 : E) - x N := hnegp
    _ ≤ ε • (1 : E) := sub_le_self _ (hx N)

end IsArchimedeanOrderUnit

namespace IsArchimedeanOrderUnit

/-- For the classical order unit `1 : ℝ`, the order-unit norm is the ordinary absolute value.
This is the scalar coherence fact needed when a construction based on the order-unit norm is
compared with ordinary real analysis. -/
theorem orderUnitNorm_real (x : ℝ) : orderUnitNorm x = |x| := by
  apply le_antisymm
  · apply orderUnitNorm_le
    refine ⟨abs_nonneg x, ?_, ?_⟩
    · simpa [smul_eq_mul] using neg_abs_le x
    · simpa [smul_eq_mul] using le_abs_self x
  · apply abs_le.mpr
    constructor
    · simpa [smul_eq_mul] using neg_orderUnitNorm_smul_one_le x
    · simpa [smul_eq_mul] using le_orderUnitNorm_smul_one x

end IsArchimedeanOrderUnit

/-! ## F. A first-class copy carrying the order-unit norm -/

/-- A type synonym of `E` equipped canonically with its order-unit norm.  The original type is
left untouched, so this construction remains usable even when `E` already carries a different
norm intended for another purpose. -/
def WithOrderUnitNorm (E : Type*) := E

namespace WithOrderUnitNorm

variable {E : Type*} [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module ℝ E]
  [PosSMulMono ℝ E] [One E] [IsArchimedeanOrderUnit E]

instance : AddCommGroup (WithOrderUnitNorm E) := inferInstanceAs (AddCommGroup E)
instance : Module ℝ (WithOrderUnitNorm E) := inferInstanceAs (Module ℝ E)
instance : PartialOrder (WithOrderUnitNorm E) := inferInstanceAs (PartialOrder E)
instance : IsOrderedAddMonoid (WithOrderUnitNorm E) := inferInstanceAs (IsOrderedAddMonoid E)
instance : PosSMulMono ℝ (WithOrderUnitNorm E) := inferInstanceAs (PosSMulMono ℝ E)
instance : One (WithOrderUnitNorm E) := inferInstanceAs (One E)
instance : IsOrderUnit (WithOrderUnitNorm E) := inferInstanceAs (IsOrderUnit E)
instance : IsArchimedeanOrderUnit (WithOrderUnitNorm E) :=
  inferInstanceAs (IsArchimedeanOrderUnit E)

/-- The canonical normed additive group on the order-unit-norm copy. -/
noncomputable instance : NormedAddCommGroup (WithOrderUnitNorm E) :=
  IsArchimedeanOrderUnit.orderUnitNormedAddCommGroup (E := E)

/-- The canonical real normed-space structure on the order-unit-norm copy. -/
noncomputable instance : NormedSpace ℝ (WithOrderUnitNorm E) :=
  IsArchimedeanOrderUnit.orderUnitNormedSpace (E := E)

/-- The identity linear equivalence from `E` to its order-unit-norm copy. -/
def linearEquiv : E ≃ₗ[ℝ] WithOrderUnitNorm E := LinearEquiv.refl ℝ E

omit [PartialOrder E] [IsOrderedAddMonoid E] [PosSMulMono ℝ E] [One E]
  [IsArchimedeanOrderUnit E] in
@[simp]
lemma linearEquiv_apply (x : E) : linearEquiv x = x := rfl

@[simp]
lemma norm_eq_orderUnitNorm (x : WithOrderUnitNorm E) : ‖x‖ =
    IsArchimedeanOrderUnit.orderUnitNorm (show E from x) := rfl

/-- The order-unit-norm copy of the classical scalar order-unit space is linearly isometric to
ordinary `ℝ`.  This is the explicit topology bridge required when an order-unit-norm completion
is compared with a scalar-valued construction. -/
noncomputable def realLinearIsometryEquiv : WithOrderUnitNorm ℝ ≃ₗᵢ[ℝ] ℝ where
  __ := (linearEquiv (E := ℝ)).symm
  norm_map' x := by
    change |(show ℝ from x)| =
      IsArchimedeanOrderUnit.orderUnitNorm (show ℝ from x)
    exact (IsArchimedeanOrderUnit.orderUnitNorm_real _).symm

@[simp]
lemma realLinearIsometryEquiv_apply (x : WithOrderUnitNorm ℝ) :
    realLinearIsometryEquiv x = (show ℝ from x) :=
  rfl

/-- The scalar order-unit-norm copy is complete, transported explicitly from the standard
complete normed real line through `realLinearIsometryEquiv`. -/
noncomputable instance : CompleteSpace (WithOrderUnitNorm ℝ) :=
  (completeSpace_congr (e := realLinearIsometryEquiv.toLinearEquiv.toEquiv)
    realLinearIsometryEquiv.isometry.isUniformEmbedding).mpr inferInstance

end WithOrderUnitNorm

/-! ## G. Contractivity of unital positive maps -/

namespace UnitalPositiveLinearMap

variable {E F : Type*}
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module ℝ E]
  [PosSMulMono ℝ E] [One E] [IsArchimedeanOrderUnit E]
  [AddCommGroup F] [PartialOrder F] [IsOrderedAddMonoid F] [Module ℝ F]
  [PosSMulMono ℝ F] [One F] [IsArchimedeanOrderUnit F]

omit [IsOrderedAddMonoid F] [PosSMulMono ℝ F] [IsArchimedeanOrderUnit F] in
/-- A unital positive map is contractive for the order-unit norm.  This belongs to the ordered
linear interface, independently of any Jordan multiplication or completeness hypothesis. -/
lemma orderUnitNorm_map_le (φ : E →ₚ₁[ℝ] F) (x : E) :
    IsArchimedeanOrderUnit.orderUnitNorm (φ x) ≤ IsArchimedeanOrderUnit.orderUnitNorm x := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨r, hr, hrlt⟩ :=
    IsArchimedeanOrderUnit.exists_orderUnitBound_lt_orderUnitNorm_add x hε
  have hbound : r ∈ IsArchimedeanOrderUnit.orderUnitBounds (φ x) := by
    refine ⟨hr.1, ?_, ?_⟩
    · have h := φ.monotone' hr.2.1
      calc
        -(r • (1 : F)) = φ (-(r • (1 : E))) := by rw [map_neg, map_smul, map_one]
        _ ≤ φ x := h
    · have h := φ.monotone' hr.2.2
      calc
        φ x ≤ φ (r • (1 : E)) := h
        _ = r • (1 : F) := by rw [map_smul, map_one]
  exact (IsArchimedeanOrderUnit.orderUnitNorm_le hbound).trans hrlt.le

end UnitalPositiveLinearMap
