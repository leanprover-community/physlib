/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Physlib.ProbabilisticTheory.OrderUnit.Basic

/-!

# Archimedean order-unit spaces

## i. Overview

The Archimedean condition is a regularity assumption on an order-unit space that rules out
infinitesimal elements. With it, the order and the distinguished unit `1` determine a natural
norm,

`‖A‖₁ = inf {r ≥ 0 | -r • 1 ≤ A ≤ r • 1}`.

Thus the unit interval sets the scale for the observables: `[-1, 1]` is exactly the closed unit
ball. For self-adjoint matrices, this recovers the usual operator norm. Concretely, this is the
Minkowski functional of the order interval `[-1, 1]`: convexity of that interval gives the triangle
inequality, and its symmetry gives homogeneity, for free. The Archimedean condition is only needed
afterwards, to upgrade this from a seminorm to a genuine norm.

## ii. Key results

- `ProbabilisticTheory.orderUnitNorm_eq_zero_iff` : the order-unit norm separates points.
- `ProbabilisticTheory.closedIciTopology` : the positive cone is closed in the order-unit-norm
  topology.

## iii. Table of contents

- A. Archimedean order units
- B. The order-unit bounds and norm
- C. Norm axioms
- D. The induced normed space
- E. Order-closedness of the topology

## iv. References

-/

@[expose] public section

namespace ProbabilisticTheory

/-!

## A. Archimedean order units

-/

variable {P : ProbabilisticTheory}

/-- An observable below every positive multiple of the certain outcome is nonpositive. -/
lemma le_zero_of_forall_pos_smul_one_le (A : P.Observables)
    (h : ∀ ε : ℝ, 0 < ε → A ≤ ε • (1 : P.Observables)) : A ≤ 0 :=
  P.le_zero_of_forall_pos_smul_one_le' A h

/-!

## B. The order-unit bounds and norm

-/

/-- The nonnegative scalars that bound an element on both sides by the order unit. -/
def orderUnitBounds (A : P.Observables) : Set ℝ :=
  {r | 0 ≤ r ∧ -(r • (1 : P.Observables)) ≤ A ∧ A ≤ r • (1 : P.Observables)}

/-- The order-unit norm is the infimum of the order-unit bounds. -/
noncomputable def orderUnitNorm (A : P.Observables) : ℝ :=
  sInf (orderUnitBounds A)

/-- The order-unit bounds are bounded below by `0`. -/
lemma orderUnitBounds_bddBelow (A : P.Observables) : BddBelow (orderUnitBounds A) :=
  ⟨0, fun _ hr ↦ hr.1⟩

/-- Any order-unit bound on `A` is an upper bound for `A`'s order-unit norm. -/
lemma orderUnitNorm_le {A : P.Observables} {r : ℝ} (hr : r ∈ orderUnitBounds A) :
    orderUnitNorm A ≤ r :=
  csInf_le (orderUnitBounds_bddBelow A) hr

/-- Every element has some order-unit bound. -/
lemma orderUnitBounds_nonempty (A : P.Observables) : (orderUnitBounds A).Nonempty := by
  obtain ⟨n, hl, hu⟩ := exists_two_sided_bound A
  refine ⟨n, Nat.cast_nonneg n, ?_, ?_⟩
  · simpa only [Nat.cast_smul_eq_nsmul] using hl
  · simpa only [Nat.cast_smul_eq_nsmul] using hu

/-- The order-unit norm is an infimum of nonnegative reals, hence itself nonnegative. -/
lemma orderUnitNorm_nonneg (A : P.Observables) : 0 ≤ orderUnitNorm A :=
  le_csInf (orderUnitBounds_nonempty A) fun _ hr ↦ hr.1

@[simp]
lemma orderUnitNorm_zero : orderUnitNorm (0 : P.Observables) = 0 := by
  apply le_antisymm
  · exact orderUnitNorm_le ⟨le_rfl, by simp, by simp⟩
  · exact orderUnitNorm_nonneg 0

/-- Negation preserves the set of order-unit bounds: a symmetric interval bounding `A` bounds
`-A` too. -/
lemma orderUnitBounds_neg (A : P.Observables) : orderUnitBounds (-A) = orderUnitBounds A := by
  ext r
  constructor <;> rintro ⟨hr, hl, hu⟩ <;>
    exact ⟨hr, by simpa only [neg_neg] using neg_le_neg hu,
      by simpa only [neg_smul, neg_neg] using neg_le_neg hl⟩

@[simp]
lemma orderUnitNorm_neg (A : P.Observables) : orderUnitNorm (-A) = orderUnitNorm A := by
  unfold orderUnitNorm
  rw [orderUnitBounds_neg]

/-- A bound for `A` and a bound for `B` add up to a bound for `A + B`. -/
lemma add_mem_orderUnitBounds {A B : P.Observables} {r s : ℝ} (hr : r ∈ orderUnitBounds A)
    (hs : s ∈ orderUnitBounds B) : r + s ∈ orderUnitBounds (A + B) := by
  refine ⟨add_nonneg hr.1 hs.1, ?_, ?_⟩
  · rw [add_smul, neg_add]
    exact add_le_add hr.2.1 hs.2.1
  · rw [add_smul]
    exact add_le_add hr.2.2 hs.2.2

/-- There is an order-unit bound on `A` within `ε` of its norm. -/
lemma exists_orderUnitBound_lt (A : P.Observables) {ε : ℝ} (hε : 0 < ε) :
    ∃ r ∈ orderUnitBounds A, r < orderUnitNorm A + ε :=
  exists_lt_of_csInf_lt (orderUnitBounds_nonempty A) (lt_add_of_pos_right _ hε)

lemma orderUnitNorm_add_le (A B : P.Observables) :
    orderUnitNorm (A + B) ≤ orderUnitNorm A + orderUnitNorm B := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨r, hr, hrlt⟩ := exists_orderUnitBound_lt A (half_pos hε)
  obtain ⟨s, hs, hslt⟩ := exists_orderUnitBound_lt B (half_pos hε)
  calc
    orderUnitNorm (A + B) ≤ r + s := orderUnitNorm_le (add_mem_orderUnitBounds hr hs)
    _ ≤ (orderUnitNorm A + ε / 2) + (orderUnitNorm B + ε / 2) :=
      add_le_add hrlt.le hslt.le
    _ = orderUnitNorm A + orderUnitNorm B + ε := by ring

/-!

## C. Norm axioms

-/

/-- Scaling the unit by a larger nonnegative real gives a larger multiple: `r ↦ r • 1` is
monotone. -/
lemma smul_one_mono {r s : ℝ} (hrs : r ≤ s) :
    r • (1 : P.Observables) ≤ s • (1 : P.Observables) :=
  smul_le_smul_of_nonneg_right hrs one_nonneg

/-- Every element is bounded above by its order-unit norm times `1`. -/
lemma le_orderUnitNorm_smul_one (A : P.Observables) :
    A ≤ orderUnitNorm A • (1 : P.Observables) := by
  apply sub_nonpos.mp
  apply le_zero_of_forall_pos_smul_one_le
  intro ε hε
  obtain ⟨r, hr, hrlt⟩ := exists_orderUnitBound_lt A hε
  calc
    A - orderUnitNorm A • (1 : P.Observables) ≤
      r • (1 : P.Observables) - orderUnitNorm A • (1 : P.Observables) :=
      sub_le_sub_right hr.2.2 _
    _ = (r - orderUnitNorm A) • (1 : P.Observables) := by rw [sub_smul]
    _ ≤ ε • (1 : P.Observables) := smul_one_mono (by linarith)

/-- `A` is also bounded below by `-(orderUnitNorm A • 1)`. -/
lemma neg_orderUnitNorm_smul_one_le (A : P.Observables) :
    -(orderUnitNorm A • (1 : P.Observables)) ≤ A := by
  have h := le_orderUnitNorm_smul_one (-A)
  rw [orderUnitNorm_neg] at h
  simpa only [neg_smul, neg_neg] using neg_le_neg h

/-- The norm itself is an order-unit bound, i.e. the infimum defining `orderUnitNorm` is a
minimum. -/
lemma orderUnitNorm_mem_orderUnitBounds (A : P.Observables) : orderUnitNorm A ∈ orderUnitBounds A :=
  ⟨orderUnitNorm_nonneg A, neg_orderUnitNorm_smul_one_le A, le_orderUnitNorm_smul_one A⟩

/-- An element with order-unit norm strictly below `ε` is itself bounded above by `ε • 1`. -/
lemma le_smul_one_of_orderUnitNorm_lt {A : P.Observables} {ε : ℝ} (h : orderUnitNorm A < ε) :
    A ≤ ε • (1 : P.Observables) :=
  (le_orderUnitNorm_smul_one A).trans (smul_one_mono h.le)

/-- The mirror image of `le_smul_one_of_orderUnitNorm_lt`. -/
lemma neg_smul_one_le_of_orderUnitNorm_lt {A : P.Observables} {ε : ℝ} (h : orderUnitNorm A < ε) :
    -(ε • (1 : P.Observables)) ≤ A := by
  have h' : -A ≤ ε • (1 : P.Observables) :=
    le_smul_one_of_orderUnitNorm_lt (by rwa [orderUnitNorm_neg])
  simpa using neg_le_neg h'

/-- The order-unit norm is characterized exactly by its symmetric order interval. -/
lemma orderUnitNorm_le_iff {A : P.Observables} {r : ℝ} :
    orderUnitNorm A ≤ r ↔ 0 ≤ r ∧ -(r • (1 : P.Observables)) ≤ A ∧ A ≤ r • (1 : P.Observables) := by
  refine ⟨fun h ↦ ?_, orderUnitNorm_le⟩
  refine ⟨(orderUnitNorm_nonneg A).trans h, ?_, ?_⟩
  · exact (neg_le_neg (smul_one_mono h)).trans (neg_orderUnitNorm_smul_one_le A)
  · exact (le_orderUnitNorm_smul_one A).trans (smul_one_mono h)

/-- The order-unit norm is definite: `‖A‖₁ = 0` forces `A = 0`. -/
lemma orderUnitNorm_eq_zero_iff {A : P.Observables} : orderUnitNorm A = 0 ↔ A = 0 := by
  refine ⟨fun hA ↦ ?_, fun h ↦ h ▸ orderUnitNorm_zero⟩
  apply le_antisymm
  · simpa [hA] using (orderUnitNorm_mem_orderUnitBounds A).2.2
  · simpa [hA] using (orderUnitNorm_mem_orderUnitBounds A).2.1

/-- Nonnegative scalar multiplication scales the order-unit norm from above. -/
lemma orderUnitNorm_smul_le {r : ℝ} (hr : 0 ≤ r) (A : P.Observables) :
    orderUnitNorm (r • A) ≤ r * orderUnitNorm A := by
  apply orderUnitNorm_le_iff.mpr
  refine ⟨mul_nonneg hr (orderUnitNorm_nonneg A), ?_, ?_⟩
  · rw [← smul_smul, ← smul_neg]
    exact smul_le_smul_of_nonneg_left (neg_orderUnitNorm_smul_one_le A) hr
  · rw [← smul_smul]
    exact smul_le_smul_of_nonneg_left (le_orderUnitNorm_smul_one A) hr

/-- Positive scalar multiplication scales the order-unit norm. -/
lemma orderUnitNorm_smul_of_pos {r : ℝ} (hr : 0 < r) (A : P.Observables) :
    orderUnitNorm (r • A) = r * orderUnitNorm A := by
  refine le_antisymm (orderUnitNorm_smul_le hr.le A) ?_
  have h := orderUnitNorm_smul_le (inv_nonneg.mpr hr.le) (r • A)
  rwa [inv_smul_smul₀ hr.ne', le_inv_mul_iff₀ hr] at h

/-- The order-unit norm is absolutely homogeneous. -/
lemma orderUnitNorm_smul (r : ℝ) (A : P.Observables) :
    orderUnitNorm (r • A) = |r| * orderUnitNorm A := by
  rcases lt_trichotomy r 0 with hr | rfl | hr
  · rw [← orderUnitNorm_neg, ← neg_smul, orderUnitNorm_smul_of_pos (neg_pos.mpr hr),
      abs_of_neg hr]
  · simp
  · rw [orderUnitNorm_smul_of_pos hr, abs_of_pos hr]

/-- Rescaling any nonzero element down to the unit ball: `(orderUnitNorm A)⁻¹ • A` has norm at
most `1`, and scaling it back up by `orderUnitNorm A` recovers `A`. -/
lemma exists_orderUnitNorm_le_one_smul_eq {A : P.Observables} (hA : orderUnitNorm A ≠ 0) :
    ∃ B : P.Observables, orderUnitNorm B ≤ 1 ∧ orderUnitNorm A • B = A := by
  refine ⟨(orderUnitNorm A)⁻¹ • A, ?_, ?_⟩
  · rw [orderUnitNorm_smul, abs_of_nonneg (inv_nonneg.mpr (orderUnitNorm_nonneg A)),
      inv_mul_cancel₀ hA]
  · rw [smul_smul, mul_inv_cancel₀ hA, one_smul]

/-!

## D. The induced normed space

-/

/-- The order-unit norm packaged as an additive-group norm. -/
noncomputable def orderUnitAddGroupNorm : AddGroupNorm P.Observables where
  toFun := orderUnitNorm
  map_zero' := orderUnitNorm_zero
  add_le' := orderUnitNorm_add_le
  neg' := orderUnitNorm_neg
  eq_zero_of_map_eq_zero' _ hA := orderUnitNorm_eq_zero_iff.mp hA

/-- The normed additive group given by the order-unit norm. -/
noncomputable scoped instance orderUnitNormedAddCommGroup : NormedAddCommGroup P.Observables :=
  orderUnitAddGroupNorm.toNormedAddCommGroup

/-- The real normed space given by the order-unit norm. -/
noncomputable scoped instance orderUnitNormedSpace : NormedSpace ℝ P.Observables where
  norm_smul_le r A := le_of_eq (orderUnitNorm_smul r A)

/-!

## E. Order-closedness of the topology

-/

/-- The positive cone is closed in the order-unit-norm topology. -/
lemma isClosed_Ici_zero : IsClosed (Set.Ici (0 : P.Observables)) := by
  apply IsSeqClosed.isClosed
  intro x p hx hp
  apply neg_nonpos.mp
  apply le_zero_of_forall_pos_smul_one_le
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hp ε hε
  specialize hN N (le_refl N)
  rw [dist_eq_norm] at hN
  apply le_trans _ (le_smul_one_of_orderUnitNorm_lt hN)
  simpa using hx N

/-- Every upper set `[a, ∞)` is closed in the order-unit-norm topology. -/
scoped instance closedIciTopology : ClosedIciTopology P.Observables where
  isClosed_Ici a := by
    rw [← zero_add a, ← Set.preimage_sub_const_Ici]
    exact isClosed_Ici_zero.preimage (continuous_sub_right a)

end ProbabilisticTheory
