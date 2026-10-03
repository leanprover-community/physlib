/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Order.Directed
public import Mathlib.Algebra.Order.Group.OrderIso
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Basic.Real.Basic

/-!
# Strong units

Strong units and order units of ordered abelian groups, and the directed order they induce.

## i. Overview

A strong unit of an ordered abelian group is an element `u` such that every element lies below some
natural multiple of `u`; an order unit is a nonnegative strong unit. A group with a nonnegative
strong unit is directed: any two elements lie below a common multiple of `u`. In a nontrivial
group a strong unit is nonzero.

## ii. Key results

- `IsStrongUnit` : every element lies below a natural multiple of `u`.
- `IsStrongUnit.exists_two_sided` : every element lies between opposite multiples of `u`.
- `IsStrongUnit.isDirectedOrder` : a nonnegative strong unit makes the order directed.
- `IsStrongUnit.ne_zero` : a strong unit of a nontrivial group is nonzero.
- `IsOrderUnit` : a nonnegative strong unit.

## iii. Table of contents

- A. Strong units
- B. Order units

## iv. References

* None.

-/

@[expose] public section

variable {G : Type*} [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G] {u : G}

/-! ## A. Strong units -/

variable (u) in
/-- A strong unit: every element lies below some natural multiple of `u`. -/
def IsStrongUnit : Prop := ∀ x : G, ∃ n : ℕ, x ≤ n • u

namespace IsStrongUnit

/-- Every element lies between two opposite multiples of a nonnegative strong unit. -/
lemma exists_two_sided (hunit : IsStrongUnit u) (hu : 0 ≤ u) (x : G) :
    ∃ n : ℕ, -(n • u) ≤ x ∧ x ≤ n • u := by
  obtain ⟨n₁, h₁⟩ := hunit x
  obtain ⟨n₂, h₂⟩ := hunit (-x)
  refine ⟨max n₁ n₂, ?_, h₁.trans (nsmul_le_nsmul_left hu (le_max_left _ _))⟩
  apply neg_le_of_neg_le
  exact h₂.trans (nsmul_le_nsmul_left hu (le_max_right _ _))

/-- A nonnegative strong unit makes the order directed. -/
lemma isDirectedOrder (hunit : IsStrongUnit u) (hu : 0 ≤ u) : IsDirectedOrder G :=
  ⟨fun x y => by
    obtain ⟨m, hm⟩ := hunit x
    obtain ⟨n, hn⟩ := hunit y
    exact ⟨(m + n) • u, hm.trans (nsmul_le_nsmul_left hu (Nat.le_add_right m n)),
      hn.trans (nsmul_le_nsmul_left hu (Nat.le_add_left n m))⟩⟩

/-- A strong unit of a nontrivial group is nonzero. -/
lemma ne_zero [Nontrivial G] (hunit : IsStrongUnit u) : u ≠ 0 := by
  rintro rfl
  obtain ⟨x, hx⟩ := exists_ne (0 : G)
  obtain ⟨m, hm⟩ := hunit x
  obtain ⟨n, hn⟩ := hunit (-x)
  simp only [nsmul_zero, neg_nonpos] at hm hn
  exact hx (le_antisymm hm hn)

end IsStrongUnit

/-! ## B. Order units -/

/-- An order unit: a nonnegative strong unit. -/
structure IsOrderUnit (u : G) : Prop where
  /-- An order unit is nonnegative. -/
  nonneg : 0 ≤ u
  /-- Every element lies below a natural multiple of an order unit. -/
  isStrongUnit : IsStrongUnit u

namespace IsOrderUnit

variable (hu : IsOrderUnit u)
include hu

/-- Every element lies between two opposite multiples of an order unit. -/
lemma exists_two_sided (x : G) : ∃ n : ℕ, -(n • u) ≤ x ∧ x ≤ n • u :=
  hu.isStrongUnit.exists_two_sided hu.nonneg x

lemma isDirectedOrder : IsDirectedOrder G := hu.isStrongUnit.isDirectedOrder hu.nonneg

section Module

variable [Module ℝ G] [PosSMulMono ℝ G]

/-- Finitely many elements lie below a common nonnegative multiple of an order unit. -/
lemma exists_forall_le_smul {ι : Type*} [Fintype ι] (x : ι → G) :
    ∃ μ : ℝ, 0 ≤ μ ∧ ∀ i, x i ≤ μ • u := by
  choose n hn using fun i => hu.isStrongUnit (x i)
  refine ⟨∑ i, (n i : ℝ), Finset.sum_nonneg fun i _ => (n i).cast_nonneg,
    fun i => (hn i).trans ?_⟩
  rw [← Nat.cast_smul_eq_nsmul ℝ]
  exact smul_le_smul_of_nonneg_right
    (Finset.single_le_sum (fun j _ => (n j).cast_nonneg) (Finset.mem_univ i)) hu.nonneg

/-- A multiple of an order unit of a nontrivial space is nonnegative only for a nonnegative
factor. -/
lemma nonneg_of_smul_nonneg [Nontrivial G] {c : ℝ} (h : 0 ≤ c • u) : 0 ≤ c := by
  by_contra hc
  push Not at hc
  have := le_antisymm (smul_nonpos_of_nonpos_of_nonneg hc.le hu.nonneg) h
  exact hu.isStrongUnit.ne_zero ((smul_eq_zero.1 this).resolve_left hc.ne)

end Module

end IsOrderUnit
