/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Algebra.Order.Group.Lattice
public import Mathlib.Algebra.Order.Group.PosPart
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.GCongr

/-!
# Vector lattices

Elementary arithmetic of infima in real vector lattices: Riesz decomposition and disjointness.

## i. Overview

A real vector lattice is an ordered real vector space in which any two elements have a least upper
bound. Two nonnegative elements are disjoint when their infimum is `0`. This file collects the
elementary arithmetic of infima: the Riesz decomposition, the behaviour of infima under positive
scalars, and how disjointness interacts with sums and with least upper bounds of sequences.

## ii. Key results

- `VectorLattice.riesz_decomposition` : an element below a sum of two nonnegative elements splits
  into two pieces, one below each summand.
- `VectorLattice.smul_inf` : positive scalars distribute over infima.
- `VectorLattice.inf_sum_of_pairwise` : infima distribute over sums of pairwise disjoint nonnegative
  elements.
- `VectorLattice.isLUB_inf` : infima distribute over least upper bounds of sequences.

## iii. Table of contents

- A. Riesz decomposition and disjointness
- B. Positive scalars

## iv. References

* None.

-/

@[expose] public section

namespace VectorLattice

variable {G : Type*} [AddCommGroup G] [Lattice G]

/-- The positive part of an element below a nonnegative element is below it. -/
lemma posPart_le_of_le {y z : G} (h : y ≤ z) (hz : 0 ≤ z) : y⁺ ≤ z :=
  sup_le h hz

variable [IsOrderedAddMonoid G]

/-! ## A. Riesz decomposition and disjointness -/

/-- **Riesz decomposition**: if `0 ≤ g ≤ f₁ + f₂` with `0 ≤ f₁, f₂`, then `g ⊓ f₁` and
`g - g ⊓ f₁` split `g` into pieces between `0` and `f₁`, resp. `f₂`. -/
lemma riesz_decomposition {f₁ f₂ g : G} (h₁ : 0 ≤ f₁) (h₂ : 0 ≤ f₂) (hg0 : 0 ≤ g)
    (hg : g ≤ f₁ + f₂) :
    0 ≤ g ⊓ f₁ ∧ g ⊓ f₁ ≤ f₁ ∧ 0 ≤ g - g ⊓ f₁ ∧ g - g ⊓ f₁ ≤ f₂ := by
  refine ⟨le_inf hg0 h₁, inf_le_right, sub_nonneg.2 inf_le_left, ?_⟩
  rw [sub_le_iff_le_add, add_inf]
  exact le_inf (le_add_of_nonneg_left h₂) (by rwa [add_comm])

/-- The infimum of a sum of nonnegative elements with a nonnegative element is at most the sum of
the infima. -/
lemma add_inf_le {h₁ h₂ c : G} (h₁0 : 0 ≤ h₁) (h₂0 : 0 ≤ h₂) (hc : 0 ≤ c) :
    (h₁ + h₂) ⊓ c ≤ h₁ ⊓ c + h₂ ⊓ c := by
  set g := (h₁ + h₂) ⊓ c
  obtain ⟨hg₁, -, -, hg₂'⟩ := riesz_decomposition h₁0 h₂0 (le_inf (add_nonneg h₁0 h₂0) hc)
    (inf_le_left : g ≤ h₁ + h₂)
  calc g = g ⊓ h₁ + (g - g ⊓ h₁) := by abel
    _ ≤ h₁ ⊓ c + h₂ ⊓ c := add_le_add (le_inf inf_le_right (inf_le_left.trans inf_le_right))
        (le_inf hg₂' ((sub_le_self _ hg₁).trans inf_le_right))

/-- Disjoint nonnegative elements split every nonnegative element additively. -/
lemma inf_add_of_inf_eq_zero {x u v : G} (hx : 0 ≤ x) (hu : 0 ≤ u) (hv : 0 ≤ v) (h : u ⊓ v = 0) :
    x ⊓ (u + v) = x ⊓ u + x ⊓ v := by
  refine le_antisymm (by rw [inf_comm, inf_comm x u, inf_comm x v]; exact add_inf_le hu hv hx) ?_
  have hd : (x ⊓ u) ⊓ (x ⊓ v) = 0 :=
    le_antisymm (h ▸ inf_le_inf inf_le_right inf_le_right) (le_inf (le_inf hx hu) (le_inf hx hv))
  refine le_inf ?_ (add_le_add inf_le_right inf_le_right)
  rw [← inf_add_sup (x ⊓ u) (x ⊓ v), hd, zero_add]
  exact sup_le inf_le_left inf_le_left

/-- An element disjoint from two nonnegative elements is disjoint from their sum. -/
lemma inf_add_eq_zero {x u v : G} (hx : 0 ≤ x) (hu : 0 ≤ u) (hv : 0 ≤ v) (hxu : x ⊓ u = 0)
    (hxv : x ⊓ v = 0) : x ⊓ (u + v) = 0 := by
  refine le_antisymm ?_ (le_inf hx (add_nonneg hu hv))
  rw [inf_comm, ← zero_add (0 : G)]
  exact (add_inf_le hu hv hx).trans (by rw [inf_comm u, inf_comm v, hxu, hxv])

/-- An element disjoint from every member of a finite family of nonnegative elements is disjoint
from their sum. -/
lemma inf_sum_eq_zero {ι : Type*} (s : Finset ι) {x : G} (hx : 0 ≤ x) (u : ι → G)
    (hu : ∀ i ∈ s, 0 ≤ u i) (h : ∀ i ∈ s, x ⊓ u i = 0) : x ⊓ ∑ i ∈ s, u i = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using inf_of_le_right hx
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact inf_add_eq_zero hx (hu i (Finset.mem_insert_self i s))
      (Finset.sum_nonneg fun j hj => hu j (Finset.mem_insert_of_mem hj))
      (h i (Finset.mem_insert_self i s))
      (ih (fun j hj => hu j (Finset.mem_insert_of_mem hj)) fun j hj =>
        h j (Finset.mem_insert_of_mem hj))

/-- A nonnegative element below `x + w`, where `w` is disjoint from `s`, meets `s` at most where
`x` does. -/
lemma add_inf_le_of_inf_eq_zero {x w s : G} (hx : 0 ≤ x) (hw : 0 ≤ w) (hs : 0 ≤ s)
    (h : w ⊓ s = 0) : (x + w) ⊓ s ≤ x ⊓ s := by
  have := add_inf_le hx hw hs
  rwa [h, add_zero] at this

/-- A nonnegative element splits along a finite family of pairwise disjoint nonnegative
elements. -/
lemma inf_sum_of_pairwise {κ : Type*} (t : Finset κ) {x : G} (hx : 0 ≤ x) (u : κ → G)
    (hu : ∀ i ∈ t, 0 ≤ u i) (hd : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → u i ⊓ u j = 0) :
    x ⊓ ∑ i ∈ t, u i = ∑ i ∈ t, x ⊓ u i := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using inf_of_le_right hx
  | insert i t hi ih =>
    have hu' : ∀ j ∈ t, 0 ≤ u j := fun j hj => hu j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, Finset.sum_insert hi, inf_add_of_inf_eq_zero hx
      (hu i (Finset.mem_insert_self i t)) (Finset.sum_nonneg hu')
      (inf_sum_eq_zero t (hu i (Finset.mem_insert_self i t)) u hu' fun j hj =>
        hd i (Finset.mem_insert_self i t) j (Finset.mem_insert_of_mem hj)
          (fun h => hi (h ▸ hj))),
      ih hu' fun j hj k hk => hd j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk)]

/-- Infima distribute over least upper bounds of sequences. -/
lemma isLUB_inf {a : ℕ → G} {c : G} (ha : IsLUB (Set.range a) c) (b : G) :
    IsLUB (Set.range fun n => a n ⊓ b) (c ⊓ b) := by
  refine ⟨Set.forall_mem_range.2 fun n => inf_le_inf_right b (ha.1 ⟨n, rfl⟩), fun t ht => ?_⟩
  have hc : c ≤ t + c ⊔ b - b := ha.2 <| Set.forall_mem_range.2 fun n => by
    have h₁ := inf_add_sup (a n) b
    have h₂ : a n ⊓ b ≤ t := ht ⟨n, rfl⟩
    have h₃ : a n ⊔ b ≤ c ⊔ b := sup_le_sup_right (ha.1 ⟨n, rfl⟩) b
    calc a n = a n ⊓ b + a n ⊔ b - b := by rw [h₁]; abel
      _ ≤ t + c ⊔ b - b := by gcongr
  have h := inf_add_sup c b
  calc c ⊓ b = c + b - c ⊔ b := by rw [← h]; abel
    _ ≤ t := by rw [sub_le_iff_le_add]; calc c + b ≤ t + c ⊔ b - b + b := by gcongr
      _ = t + c ⊔ b := by abel

/-! ## B. Positive scalars -/

variable [Module ℝ G] [PosSMulMono ℝ G]

omit [IsOrderedAddMonoid G] in
/-- Positive scalars distribute over infima. -/
lemma smul_inf {c : ℝ} (hc : 0 ≤ c) (x y : G) : c • (x ⊓ y) = c • x ⊓ c • y := by
  rcases hc.eq_or_lt with rfl | hc
  · simp
  refine le_antisymm (le_inf (smul_le_smul_of_nonneg_left inf_le_left hc.le)
    (smul_le_smul_of_nonneg_left inf_le_right hc.le)) ?_
  rw [← inv_smul_le_iff_of_pos hc]
  exact le_inf ((inv_smul_le_iff_of_pos hc).2 inf_le_left)
    ((inv_smul_le_iff_of_pos hc).2 inf_le_right)

/-- Disjoint nonnegative elements stay disjoint after scaling one of them. -/
lemma inf_smul_eq_zero {g u : G} (hg : 0 ≤ g) (hu : 0 ≤ u) (h : g ⊓ u = 0) {a : ℝ} (ha : 0 ≤ a) :
    g ⊓ a • u = 0 := by
  set m := max 1 a
  refine le_antisymm ?_ (le_inf hg (smul_nonneg ha hu))
  calc g ⊓ a • u ≤ m • g ⊓ m • u := inf_le_inf (le_smul_of_one_le_left hg (le_max_left _ _))
        (smul_le_smul_of_nonneg_right (le_max_right _ _) hu)
    _ = 0 := by rw [← smul_inf (zero_le_one.trans (le_max_left _ _)), h, smul_zero]

/-- Disjoint nonnegative elements stay disjoint after scaling both. -/
lemma smul_inf_smul_eq_zero {u v : G} (hu : 0 ≤ u) (hv : 0 ≤ v) (h : u ⊓ v = 0) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) : a • u ⊓ b • v = 0 := by
  have h₁ := inf_smul_eq_zero hu hv h hb
  rw [inf_comm] at h₁ ⊢
  exact inf_smul_eq_zero (smul_nonneg hb hv) hu h₁ ha

omit [IsOrderedAddMonoid G] in
/-- Positive scalars preserve least upper bounds of sequences. -/
lemma isLUB_smul {a : ℕ → G} {c : G} (ha : IsLUB (Set.range a) c) {r : ℝ} (hr : 0 < r) :
    IsLUB (Set.range fun n => r • a n) (r • c) :=
  ⟨Set.forall_mem_range.2 fun n => smul_le_smul_of_nonneg_left (ha.1 ⟨n, rfl⟩) hr.le,
    fun t ht => by
      rw [← le_inv_smul_iff_of_pos hr]
      exact ha.2 <| Set.forall_mem_range.2 fun n => by
        rw [le_inv_smul_iff_of_pos hr]; exact ht ⟨n, rfl⟩⟩

end VectorLattice
