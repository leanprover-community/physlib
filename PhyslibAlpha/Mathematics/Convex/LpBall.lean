/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convex.Strict.Extreme
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Extreme points of `ℓq` balls

The extreme points of the `ℓq` ball are its unit sphere, those of the `ℓ1` ball its vertices.

## i. Overview

The closed `ℓq` ball `{a | ∑ |a i| ^ q ≤ 1}` in `ℝⁿ` is strictly convex for `1 < q < ∞`: its
extreme points are its whole unit sphere. The `ℓ1` ball is instead a polytope, the convex hull of
its `2n` vertices `± eᵢ`, and these vertices are its only extreme points.

## ii. Key results

- `LpBall.extremePoints_lpBall` : the extreme points of the `ℓq` ball are its unit sphere.
- `LpBall.l1Ball_eq_convexHull` : the `ℓ1` ball is the convex hull of its vertices.
- `LpBall.vertex_isExtreme`, `LpBall.eq_vertex_of_isExtreme` : the extreme points of the `ℓ1` ball
  are its vertices.

## iii. Table of contents

- A. Extreme points of the `ℓq` ball
- B. Extreme points of the `ℓ1` ball

## iv. References

* None.

-/

@[expose] public section

namespace LpBall

variable {n m : ℕ} {p q : ℝ}

/-! ## A. Extreme points of the `ℓq` ball -/

/-- An extreme point of a sublevel set `{g ≤ 1}` of a continuous function lies on `{g = 1}`. -/
lemma eq_one_of_mem_extremePoints {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nontrivial E] {g : E → ℝ} (hg : Continuous g) {a : E}
    (ha : a ∈ Set.extremePoints ℝ {b | g b ≤ 1}) : g a = 1 := by
  by_contra hne
  refine Set.disjoint_left.mp (disjoint_interior_extremePoints _) ?_ ha
  exact (isOpen_lt hg continuous_const).subset_interior_iff.mpr (fun _ hb => le_of_lt hb)
    (lt_of_le_of_ne ha.1 hne)

/-- `x ↦ |x| ^ p` is strictly convex for `p > 1`. -/
lemma abs_rpow_combo_lt (hp : 1 < p) {x y : ℝ} (hxy : x ≠ y) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) : |t * x + (1 - t) * y| ^ p < t * |x| ^ p + (1 - t) * |y| ^ p := by
  have h1t : 0 < 1 - t := by linarith
  rcases eq_or_ne |x| |y| with he | hne
  · obtain rfl : x = -y := (abs_eq_abs.mp he).resolve_left hxy
    have hy : 0 < |y| := abs_pos.2 fun h => hxy (by simp [h])
    have hlt : |t * -y + (1 - t) * y| < |y| := by
      rw [show t * -y + (1 - t) * y = (1 - 2 * t) * y by ring, abs_mul]
      exact mul_lt_of_lt_one_left hy (abs_lt.2 ⟨by linarith, by linarith⟩)
    calc _ < |y| ^ p := Real.rpow_lt_rpow (abs_nonneg _) hlt (by linarith)
      _ = _ := by rw [abs_neg]; ring
  · refine (Real.rpow_le_rpow (abs_nonneg _) ?_ (by linarith)).trans_lt
      ((strictConvexOn_rpow hp).2 (abs_nonneg x) (abs_nonneg y) hne ht0 h1t (by ring))
    simpa [abs_mul, abs_of_pos ht0, abs_of_pos h1t] using abs_add_le (t * x) ((1 - t) * y)

lemma abs_rpow_combo_le (hp : 1 < p) (x y t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |t * x + (1 - t) * y| ^ p ≤ t * |x| ^ p + (1 - t) * |y| ^ p := by
  rcases eq_or_ne x y with rfl | hxy
  · rw [show t * x + (1 - t) * x = x by ring]
    linarith
  rcases ht0.eq_or_lt with rfl | ht0'
  · simp
  rcases ht1.eq_or_lt with rfl | ht1'
  · simp
  exact (abs_rpow_combo_lt hp hxy ht0' ht1').le

lemma sum_abs_rpow_combo_lt (hp : 1 < p) {x y : Fin n → ℝ} (hxy : x ≠ y) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) : ∑ i, |t * x i + (1 - t) * y i| ^ p <
      t * ∑ i, |x i| ^ p + (1 - t) * ∑ i, |y i| ^ p := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_lt_sum (fun j _ => abs_rpow_combo_le hp _ _ _ ht0.le ht1.le)
    ⟨i, Finset.mem_univ i, abs_rpow_combo_lt hp hi ht0 ht1⟩

/-- The extreme points of the closed `ℓq` ball are its unit sphere. -/
lemma extremePoints_lpBall (hpq : p.HolderConjugate q) [NeZero n] :
    Set.extremePoints ℝ {a : Fin n → ℝ | ∑ i, |a i| ^ q ≤ 1} = {a | ∑ i, |a i| ^ q = 1} := by
  have hq1 : 1 < q := hpq.symm.lt
  ext a
  refine ⟨eq_one_of_mem_extremePoints (continuous_finsetSum _ fun i _ =>
    (Real.continuous_rpow_const (zero_le_one.trans hq1.le)).comp
      (continuous_abs.comp (continuous_apply i))), fun ha => mem_extremePoints_iff_left.2
    ⟨ha.le, fun x hx y hy ⟨t, s, ht, hs, hts, hcombo⟩ => ?_⟩⟩
  obtain rfl : s = 1 - t := by linarith
  by_contra hxa
  subst hcombo
  have hxy : x ≠ y := fun h => hxa (by subst h; module)
  have hlt := sum_abs_rpow_combo_lt hq1 hxy ht (by linarith)
  simp only [Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ha hx hy
  nlinarith [mul_le_mul_of_nonneg_left hx ht.le, mul_le_mul_of_nonneg_left hy hs.le]

/-! ## B. Extreme points of the `ℓ1` ball -/

/-- The vertex of the `ℓ1` ball with coordinate `s` at `i` and `0` elsewhere. -/
def vertex (i : Fin m) (s : ℝ) : Fin m → ℝ := fun j => if j = i then s else 0

lemma vertex_mem_l1Ball (i : Fin m) {s : ℝ} (hs : |s| ≤ 1) : ∑ k, |vertex i s k| ≤ 1 := by
  simpa [vertex, apply_ite abs] using hs

/-- A point of the `ℓ1` ball with `s * x i = 1`, `s = ±1`, is the vertex `vertex i s`. -/
lemma eq_vertex_of_mul_eq_one {x : Fin m → ℝ} (hx : ∑ k, |x k| ≤ 1) {i : Fin m} {s : ℝ}
    (hs : s = 1 ∨ s = -1) (h : s * x i = 1) : x = vertex i s := by
  have hxi : x i = s := by rcases hs with rfl | rfl <;> linarith
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hxi,
    show |s| = 1 by rcases hs with rfl | rfl <;> simp, add_le_iff_nonpos_right] at hx
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => abs_nonneg (x k)).1
    (le_antisymm hx (Finset.sum_nonneg fun k _ => abs_nonneg _))
  funext k
  rcases eq_or_ne k i with rfl | hk
  · simp [vertex, hxi]
  · simpa [vertex, hk] using h0 k (Finset.mem_erase.2 ⟨hk, Finset.mem_univ k⟩)

lemma mul_apply_le_one {x : Fin m → ℝ} (hx : ∑ k, |x k| ≤ 1) (i : Fin m) {s : ℝ}
    (hs : |s| = 1) : s * x i ≤ 1 :=
  (le_abs_self _).trans (by
    rw [abs_mul, hs, one_mul]
    exact (Finset.single_le_sum (fun k _ => abs_nonneg (x k)) (Finset.mem_univ i)).trans hx)

/-- Every vertex of the `ℓ1` ball is extreme. -/
lemma vertex_isExtreme (i : Fin m) {s : ℝ} (hs : s = 1 ∨ s = -1) :
    vertex i s ∈ Set.extremePoints ℝ {a : Fin m → ℝ | ∑ k, |a k| ≤ 1} := by
  have hs1 : |s| = 1 := by rcases hs with rfl | rfl <;> simp
  refine mem_extremePoints_iff_left.2 ⟨vertex_mem_l1Ball i hs1.le, fun x hx y hy
    ⟨t, u, ht, hu, htu, h⟩ => eq_vertex_of_mul_eq_one hx hs ?_⟩
  have hi : t * x i + u * y i = s := by simpa [vertex] using congrFun h i
  have hss : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  have h1 : t * (s * x i) + u * (s * y i) = 1 := by linear_combination s * hi + hss
  have hx1 := mul_apply_le_one hx i hs1
  have hy1 := mul_apply_le_one hy i hs1
  nlinarith [mul_nonneg ht.le (sub_nonneg.2 hx1), mul_nonneg hu.le (sub_nonneg.2 hy1)]

/-- The vertex `vertex i s` with `s = 1` or `s = -1` according to `b`. -/
abbrev signedVertex (j : Fin m × Bool) : Fin m → ℝ := vertex j.1 (if j.2 then 1 else -1)

lemma signedVertex_mem_l1Ball (j : Fin m × Bool) : ∑ k, |signedVertex j k| ≤ 1 :=
  vertex_mem_l1Ball _ (by cases j.2 <;> simp)

lemma signedVertex_isExtreme (j : Fin m × Bool) :
    signedVertex j ∈ Set.extremePoints ℝ {a : Fin m → ℝ | ∑ k, |a k| ≤ 1} :=
  vertex_isExtreme j.1 (by cases j.2 <;> simp)

lemma signedVertex_injective : Function.Injective (signedVertex (m := m)) := by
  rintro ⟨i, b⟩ ⟨i', b'⟩ h
  have h1 := congrFun h i
  rcases eq_or_ne i i' with rfl | hii
  · cases b <;> cases b' <;> norm_num [signedVertex, vertex] at h1 <;> rfl
  · cases b <;> norm_num [signedVertex, vertex, hii] at h1

/-- Convex weights on the signed vertices recovering a point of the `ℓ1` ball: the positive and
negative parts of each coordinate, with the missing mass spread evenly. -/
noncomputable def l1Weight (a : Fin m → ℝ) (j : Fin m × Bool) : ℝ :=
  (if j.2 then max (a j.1) 0 else max (-a j.1) 0) + (1 - ∑ k, |a k|) / (2 * m)

lemma l1Weight_nonneg {a : Fin m → ℝ} (ha : ∑ k, |a k| ≤ 1) (j : Fin m × Bool) :
    0 ≤ l1Weight a j :=
  add_nonneg (by split_ifs <;> positivity) (div_nonneg (by linarith) (by positivity))

lemma sum_l1Weight [NeZero m] (a : Fin m → ℝ) : ∑ j, l1Weight a j = 1 := by
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne m)
  simp only [l1Weight, Fintype.sum_prod_type, Fintype.sum_bool, ite_true, Bool.false_eq_true,
    ite_false, max_zero_add_max_neg_zero_eq_abs_self, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul]
  field_simp
  push_cast
  ring

lemma sum_l1Weight_smul (a : Fin m → ℝ) : ∑ j, l1Weight a j • signedVertex j = a := by
  ext k
  simp [l1Weight, Fintype.sum_prod_type, vertex, Finset.sum_apply]
  rw [← sub_eq_add_neg, max_zero_sub_max_neg_zero_eq_self]

/-- The `ℓ1` ball lies in the convex hull of its vertices. -/
lemma mem_convexHull_signedVertex [NeZero m] {a : Fin m → ℝ} (ha : ∑ k, |a k| ≤ 1) :
    a ∈ convexHull ℝ (Set.range signedVertex) :=
  sum_l1Weight_smul a ▸ (convex_convexHull ℝ _).sum_mem (fun j _ => l1Weight_nonneg ha j)
    (sum_l1Weight a) fun j _ => subset_convexHull ℝ _ ⟨j, rfl⟩

lemma convex_l1Ball : Convex ℝ {a : Fin m → ℝ | ∑ k, |a k| ≤ 1} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hy ⊢
  calc ∑ k, |a * x k + b * y k| ≤ ∑ k, (a * |x k| + b * |y k|) :=
        Finset.sum_le_sum fun k _ => (abs_add_le _ _).trans_eq
          (by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb])
    _ = a * ∑ k, |x k| + b * ∑ k, |y k| := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ 1 := by nlinarith

/-- The `ℓ1` ball is the convex hull of its vertices. -/
lemma l1Ball_eq_convexHull [NeZero m] :
    {a : Fin m → ℝ | ∑ k, |a k| ≤ 1} = convexHull ℝ (Set.range signedVertex) :=
  subset_antisymm (fun _ => mem_convexHull_signedVertex) <| convexHull_min
    (Set.range_subset_iff.2 signedVertex_mem_l1Ball) convex_l1Ball

/-- Every extreme point of the `ℓ1` ball is a vertex. -/
lemma eq_vertex_of_isExtreme [NeZero m] {a : Fin m → ℝ}
    (ha : a ∈ Set.extremePoints ℝ {a : Fin m → ℝ | ∑ k, |a k| ≤ 1}) :
    ∃ i s, (s = 1 ∨ s = -1) ∧ a = vertex i s := by
  rw [l1Ball_eq_convexHull] at ha
  obtain ⟨⟨i, b⟩, rfl⟩ := extremePoints_convexHull_subset ha
  exact ⟨i, _, by cases b <;> simp, rfl⟩

end LpBall
