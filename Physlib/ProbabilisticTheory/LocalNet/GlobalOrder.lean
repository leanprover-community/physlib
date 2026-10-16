/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.LocalNet.Basic
public import Physlib.ProbabilisticTheory.OrderUnit.Archimedean
public import Mathlib.Algebra.Order.Group.Cone

/-!
# Order-unit structure on global observables

Positivity and the order unit on the space of global observables.

## i. Overview

Each `A X` already has an order and an order unit. But `N.Global` was constructed as a direct
limit of vector spaces, which gives it no order. The set `Pos N` supplies the missing positive
cone: a global observable belongs to it when some local representative is positive.

For a nonempty directed net, this cone defines an order on the global space. A global observable
cannot be both positive and negative unless it is zero: equality with zero in the direct limit
already holds in some larger subsystem. The additional assumption `N.IsOrderEmbedding` ensures
that the global order agrees with the existing order of each subsystem.

Every inclusion channel preserves `1`, so the order units of all subsystems give the same global
observable. Together with the order, this makes `N.Global` an order-unit space, and each
subsystem maps to it by a channel. If the subsystem spaces are Archimedean, the global space is
Archimedean as well.

## ii. Key results

- `LocalNet.Global.of_nonneg_iff`: with order-embedding inclusions, a local observable is positive
  globally exactly when it is positive in its subsystem.
- `LocalNet.Global.instOrderUnitSpace`: the global observables form an order-unit space.
- `LocalNet.Global.ofChannel`: each subsystem maps into the global space by a channel.
- `LocalNet.Global.instArchimedeanOrderUnitSpace`: the Archimedean property passes to the global
  space.

## iii. Table of contents

- A. Positivity
- B. The common order unit
- C. The order
- D. The global order-unit space and local channels
- E. The Archimedean property

## iv. References

-/

@[expose] public section

namespace ProbabilisticTheory

open ArchimedeanOrderUnitSpace UnitalPositiveLinearMap

variable {R : Type*} [Preorder R] [DecidableEq R] {A : R → Type*}

namespace LocalNet.Global

section Pos

variable [∀ X, OrderUnitSpace (A X)] {N : LocalNet R A}

/-!

## A. Positivity

The vector-space direct limit does not supply a positive cone. The set below collects the global
observables represented by positive local observables. For a directed family, positive
representatives from different subsystems can be included in a common larger one and added there.

-/

variable (N) in
/-- The candidate positive cone on the direct limit, formed from positive local representatives. -/
def Pos : Set N.Global :=
  {x | ∃ (i : R) (a : A i), 0 ≤ a ∧ of N i a = x}

/-- A nonnegative local observable represents an element of the global positive cone. -/
lemma of_mem_pos {i : R} {a : A i} (ha : 0 ≤ a) : of N i a ∈ Pos N := ⟨i, a, ha, rfl⟩

/-- The global positive cone is closed under nonnegative scalar multiplication. -/
lemma smul_mem_pos {c : ℝ} (hc : 0 ≤ c) {x : N.Global} (hx : x ∈ Pos N) : c • x ∈ Pos N := by
  obtain ⟨i, a, ha, rfl⟩ := hx
  exact ⟨i, c • a, smul_nonneg hc ha, map_smul _ _ _⟩

variable [IsDirectedOrder R]

/-- The global positive cone is closed under addition for a directed net. -/
lemma add_mem_pos {x y : N.Global} (hx : x ∈ Pos N) (hy : y ∈ Pos N) :
    x + y ∈ Pos N := by
  obtain ⟨i, a, ha, rfl⟩ := hx
  obtain ⟨j, b, hb, rfl⟩ := hy
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  refine ⟨k, N.incl hik a + N.incl hjk b, add_nonneg (map_nonneg _ ha) (map_nonneg _ hb), ?_⟩
  rw [map_add, of_incl, of_incl]

/-!

## B. The common order unit

The inclusion channels preserve `1`. Consequently, the order unit of every subsystem represents
the same global observable.

-/

variable [Nonempty R]

/-- The global order unit: the image of the order unit of a subsystem. By `of_one`, it does not
matter which one. -/
@[no_expose] noncomputable instance : One N.Global := ⟨of N (Classical.arbitrary R) 1⟩

/-- The order unit of each subsystem represents the global order unit. -/
lemma of_one (i : R) : of N i 1 = (1 : N.Global) := by
  rw [show (1 : N.Global) = of N (Classical.arbitrary R) 1 from rfl, of_eq_iff]
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i (Classical.arbitrary R)
  exact ⟨k, hik, hjk, (map_one _).trans (map_one _).symm⟩

end Pos

section Order

variable [∀ X, OrderUnitSpace (A X)] {N : LocalNet R A} [IsDirectedOrder R]

/-!

## C. The order

The global positive cone is pointed because an equality in the direct limit holds in some later
subsystem. Order-embedding inclusions additionally make the resulting order agree with each
subsystem's original order.

-/

/-- An observable in both the global positive cone and its negative is zero. -/
lemma eq_zero_of_mem_pos_of_neg_mem_pos {x : N.Global} (hx : x ∈ Pos N) (hx' : -x ∈ Pos N) :
    x = 0 := by
  obtain ⟨i, a, ha, rfl⟩ := hx
  obtain ⟨j, b, hb, hb'⟩ := hx'
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  have hsum : of N k (N.incl hik a + N.incl hjk b) = 0 := by
    rw [map_add, of_incl, of_incl, hb', add_neg_cancel]
  obtain ⟨l, hkl, hl⟩ := Module.DirectLimit.of.zero_exact (f := N.inclLin) hsum
  have h0 : N.incl hkl (N.incl hik a) = 0 := by
    rw [map_add] at hl
    exact ((add_eq_zero_iff_of_nonneg
      (map_nonneg (N.incl hkl) (map_nonneg (N.incl hik) ha))
      (map_nonneg (N.incl hkl) (map_nonneg (N.incl hjk) hb))).1 hl).1
  rw [← of_incl hik, ← of_incl hkl, h0, map_zero]

variable [Nonempty R]

/-- The global positive cone as an additive group cone. -/
@[no_expose] noncomputable def posCone : AddGroupCone N.Global where
  carrier := Pos N
  zero_mem' := ⟨Classical.arbitrary R, 0, le_rfl, map_zero _⟩
  add_mem' := add_mem_pos
  eq_zero_of_mem_of_neg_mem' := eq_zero_of_mem_pos_of_neg_mem_pos

/-- A global observable is below another when their difference is positive in some subsystem. -/
@[no_expose] noncomputable instance : PartialOrder N.Global := PartialOrder.mkOfAddGroupCone posCone

/-- `x ≤ y` exactly when `y - x` is nonnegative. -/
lemma le_def {x y : N.Global} : x ≤ y ↔ y - x ∈ Pos N := Iff.rfl

/-- Global nonnegativity is membership in the positive cone. -/
lemma nonneg_iff {x : N.Global} : 0 ≤ x ↔ x ∈ Pos N := by
  rw [le_def, sub_zero]

variable [N.IsOrderEmbedding] in
/-- A local observable is nonnegative globally exactly when it is nonnegative locally. -/
lemma of_nonneg_iff (i : R) (a : A i) : 0 ≤ of N i a ↔ 0 ≤ a := by
  refine ⟨fun ha => ?_, fun ha => nonneg_iff.2 (of_mem_pos ha)⟩
  obtain ⟨j, b, hb, heq⟩ := nonneg_iff.1 ha
  obtain ⟨k, hik, hjk, h⟩ := (of_eq_iff a b).1 heq.symm
  exact IsOrderEmbedding.nonneg_of_incl_nonneg hik (h ▸ map_nonneg (N.incl hjk) hb)

/-- Adding a global observable preserves the order. -/
instance : IsOrderedAddMonoid N.Global := IsOrderedAddMonoid.mkOfCone posCone

/-- Scaling by a nonnegative real preserves the order of global observables. -/
instance : PosSMulMono ℝ N.Global where
  smul_le_smul_of_nonneg_left c hc x y h := by
    rw [le_def] at h ⊢
    simpa [smul_sub] using smul_mem_pos hc h

/-- The global observables form an ordered real vector space. -/
noncomputable instance : OrderedVectorSpace N.Global where

variable [N.IsOrderEmbedding] in
/-- Two local observables have the same order relation locally and globally. -/
lemma of_le_iff (i : R) (a b : A i) : of N i a ≤ of N i b ↔ a ≤ b := by
  rw [← sub_nonneg, ← map_sub, of_nonneg_iff, sub_nonneg]

/-!

## D. The global order-unit space and local channels

The common image of `1` is an order unit for the global space. The canonical map from each
subsystem preserves positivity and this order unit, so it is a channel.

-/

/-- The global observables form an order-unit space. -/
noncomputable instance : OrderUnitSpace N.Global where
  one_nonneg := by
    rw [← of_one (Classical.arbitrary R)]
    exact nonneg_iff.2 (of_mem_pos OrderUnitSpace.one_nonneg)
  exists_nsmul_one_le x := by
    obtain ⟨i, a, rfl⟩ := exists_local x
    obtain ⟨n, hn⟩ := OrderUnitSpace.exists_nsmul_one_le a
    refine ⟨n, ?_⟩
    rw [← of_one i, ← map_nsmul, le_def, ← map_sub]
    exact of_mem_pos (sub_nonneg.mpr hn)

variable (N) in
/-- The canonical channel from a subsystem to the global observable space. -/
noncomputable def ofChannel (i : R) : A i →ₚ₁[ℝ] N.Global :=
  ofLinearMap (of N i) (fun _ ha => nonneg_iff.2 (of_mem_pos ha))
    (of_one i)

@[simp] lemma ofChannel_apply (i : R) (a : A i) : ofChannel N i a = of N i a := rfl

end Order

/-!

## E. The Archimedean property

The Archimedean condition can be checked in a subsystem representing the global observable.

-/

section Archimedean

variable [∀ X, ArchimedeanOrderUnitSpace (A X)] {N : LocalNet R A} [IsDirectedOrder R]
  [Nonempty R] [N.IsOrderEmbedding]

/-- The global order-unit space is Archimedean when every subsystem is Archimedean. -/
noncomputable instance : ArchimedeanOrderUnitSpace N.Global where
  le_zero_of_forall_pos_smul_one_le x hx := by
    obtain ⟨i, a, rfl⟩ := exists_local x
    rw [← map_zero (of N i), of_le_iff]
    refine le_zero_of_forall_pos_smul_one_le a fun ε hε => ?_
    have h := hx ε hε
    rwa [← of_one i, ← map_smul, of_le_iff] at h

end Archimedean

end LocalNet.Global

end ProbabilisticTheory
