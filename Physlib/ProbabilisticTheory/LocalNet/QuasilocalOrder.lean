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
# Order-unit structure on quasilocal observables

Positivity and a common unit for observables assembled from a local net.

## i. Overview

The quasilocal construction treats observables from different subsystems as observables of one
global system. A quantity measured locally can also be described in a larger subsystem; these
descriptions must refer to the same physical quantity. For the global description to work, it must
preserve more than identity: whether an observable is positive, how it compares with other
observables, and what represents the certain outcome.

This file shows how those properties carry over from the local systems. Positive local observables
give the quasilocal space its notion of positivity, and the local copies of `1` give it one certain
observable. Local observables thereby retain their interpretation as observables of the whole
system. The resulting order-unit structure lets a state of the global system assign positive,
normalized expectations to them.

## ii. Key results

- `LocalNet.Quasilocal.positive`: the global observables with a positive local representative.
- `LocalNet.Quasilocal.toQuasilocal_nonneg_iff`: local and global positivity agree when inclusions
  reflect order.
- `LocalNet.Quasilocal.instOrderUnitSpace`: the global observables inherit an order unit.
- `LocalNet.Quasilocal.toQuasilocalChannel`: each subsystem maps to the global observable space
  by a channel.
- `LocalNet.Quasilocal.instArchimedeanOrderUnitSpace`: the global space is Archimedean when the
  local spaces are.

## iii. Table of contents

- A. Positivity
- B. The common order unit
- C. The order
- D. The quasilocal order-unit space and local channels
- E. The Archimedean property

## iv. References

-/

@[expose] public section

namespace ProbabilisticTheory

open ArchimedeanOrderUnitSpace UnitalPositiveLinearMap

variable {R : Type*} [Preorder R] {A : R → Type*}

namespace LocalNet.Quasilocal

section OrderUnit

variable [∀ X, OrderUnitSpace (A X)] {N : LocalNet R A}

/-!

## A. Positivity

An observable assembled from local pieces is positive when it has a positive local description.
Positive observables from different subsystems can be brought into a common larger subsystem and
added there. Nonnegative scaling preserves positivity within any one subsystem.

-/

variable (N) in
/-- Global observables with a positive local representative. -/
def positive : Set N.Quasilocal :=
  {x | ∃ (i : R) (a : A i), 0 ≤ a ∧ toQuasilocal N i a = x}

/-- A positive local observable is positive globally. -/
lemma toQuasilocal_mem_pos {i : R} {a : A i} (ha : 0 ≤ a) :
    toQuasilocal N i a ∈ positive N :=
  ⟨i, a, ha, rfl⟩

/-- Nonnegative scaling preserves global positivity. -/
lemma smul_mem_pos {c : ℝ} (hc : 0 ≤ c) {x : N.Quasilocal}
    (hx : x ∈ positive N) : c • x ∈ positive N := by
  obtain ⟨i, a, ha, rfl⟩ := hx
  exact ⟨i, c • a, smul_nonneg hc ha, map_smul _ _ _⟩

variable [IsDirectedOrder R]

/-- The sum of positive global observables is positive. -/
lemma add_mem_pos {x y : N.Quasilocal} (hx : x ∈ positive N) (hy : y ∈ positive N) :
    x + y ∈ positive N := by
  obtain ⟨i, a, ha, rfl⟩ := hx
  obtain ⟨j, b, hb, rfl⟩ := hy
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  refine ⟨k, N.incl hik a + N.incl hjk b, add_nonneg (map_nonneg _ ha) (map_nonneg _ hb), ?_⟩
  rw [map_add, toQuasilocal_incl, toQuasilocal_incl]

/-- A global observable that is both positive and negative is zero. -/
lemma eq_zero_of_mem_pos_of_neg_mem_pos {x : N.Quasilocal}
    (hx : x ∈ positive N) (hx' : -x ∈ positive N) : x = 0 := by
  classical
  obtain ⟨i, a, ha, rfl⟩ := hx
  obtain ⟨j, b, hb, hb'⟩ := hx'
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  have hsum : toQuasilocal N k (N.incl hik a + N.incl hjk b) = 0 := by
    rw [map_add, toQuasilocal_incl, toQuasilocal_incl, hb', add_neg_cancel]
  obtain ⟨l, hkl, hl⟩ := Module.DirectLimit.of.zero_exact (f := N.inclLin) hsum
  have h0 : N.incl hkl (N.incl hik a) = 0 := by
    rw [map_add] at hl
    exact ((add_eq_zero_iff_of_nonneg
      (map_nonneg (N.incl hkl) (map_nonneg (N.incl hik) ha))
      (map_nonneg (N.incl hkl) (map_nonneg (N.incl hjk) hb))).1 hl).1
  rw [← toQuasilocal_incl hik, ← toQuasilocal_incl hkl, h0, map_zero]

/-!

## B. The common order unit

The certain observable must not depend on which subsystem describes it. Every inclusion preserves
`1`, so the local units all represent one global observable.

-/

variable [Nonempty R]

/-- The common global image of the local units. -/
noncomputable instance : One N.Quasilocal := ⟨toQuasilocal N (Classical.arbitrary R) 1⟩

omit [IsDirectedOrder R] in
/-- The global unit is represented by the unit of the chosen subsystem. -/
lemma one_eq_toQuasilocal :
    (1 : N.Quasilocal) = toQuasilocal N (Classical.arbitrary R) 1 := rfl

/-- Every local unit represents the global unit. -/
lemma toQuasilocal_one (i : R) : toQuasilocal N i 1 = (1 : N.Quasilocal) := by
  rw [one_eq_toQuasilocal, toQuasilocal_eq_iff]
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i (Classical.arbitrary R)
  exact ⟨k, hik, hjk, (map_one _).trans (map_one _).symm⟩

/-!

## C. The order

A comparison `x ≤ y` means that `y - x` has a positive local description. This is a partial order:
an observable cannot be both positive and negative unless it is zero. When inclusions reflect
order, comparisons made within a subsystem agree with comparisons in the global system.

-/

/-- The cone of positive global observables. -/
noncomputable def posCone : AddGroupCone N.Quasilocal where
  carrier := positive N
  zero_mem' := ⟨Classical.arbitrary R, 0, le_rfl, map_zero _⟩
  add_mem' := add_mem_pos
  eq_zero_of_mem_of_neg_mem' := eq_zero_of_mem_pos_of_neg_mem_pos

/-- The order on global observables induced by local positivity. -/
noncomputable instance : PartialOrder N.Quasilocal :=
  PartialOrder.mkOfAddGroupCone posCone

/-- `x ≤ y` exactly when `y - x` has a positive local representative. -/
lemma le_iff {x y : N.Quasilocal} : x ≤ y ↔ y - x ∈ positive N := Iff.rfl

/-- A global observable is nonnegative exactly when it belongs to `positive N`. -/
lemma nonneg_iff {x : N.Quasilocal} : 0 ≤ x ↔ x ∈ positive N := by
  rw [le_iff, sub_zero]

variable [N.IsOrderEmbedding] in
/-- A local observable is positive globally exactly when it is positive locally. -/
lemma toQuasilocal_nonneg_iff (i : R) (a : A i) : 0 ≤ toQuasilocal N i a ↔ 0 ≤ a := by
  constructor
  · intro ha
    obtain ⟨j, b, hb, heq⟩ := nonneg_iff.1 ha
    obtain ⟨k, hik, hjk, h⟩ := (toQuasilocal_eq_iff a b).1 heq.symm
    exact IsOrderEmbedding.nonneg_of_incl_nonneg hik (h ▸ map_nonneg (N.incl hjk) hb)
  · intro ha
    exact nonneg_iff.2 (toQuasilocal_mem_pos ha)

/-- Adding the same global observable preserves a comparison. -/
instance : IsOrderedAddMonoid N.Quasilocal := IsOrderedAddMonoid.mkOfCone posCone

/-- Nonnegative scaling preserves comparisons between global observables. -/
instance : PosSMulMono ℝ N.Quasilocal where
  smul_le_smul_of_nonneg_left c hc x y h := by
    rw [le_iff] at h ⊢
    simpa [smul_sub] using smul_mem_pos hc h

/-- Global observables form an ordered real vector space. -/
noncomputable instance : OrderedVectorSpace N.Quasilocal where

variable [N.IsOrderEmbedding] in
/-- A comparison of local observables has the same meaning globally. -/
lemma toQuasilocal_le_iff (i : R) (a b : A i) :
    toQuasilocal N i a ≤ toQuasilocal N i b ↔ a ≤ b := by
  rw [← sub_nonneg, ← map_sub, toQuasilocal_nonneg_iff, sub_nonneg]

/-!

## D. The quasilocal order-unit space and local channels

Every global observable has a local representative bounded by a multiple of the local unit. The
same bound holds for the global unit, making it an order unit. The map from each subsystem to the
global space preserves positivity and `1`, so it is a channel.

-/

/-- The global observable space inherits an order unit from its subsystems. -/
noncomputable instance : OrderUnitSpace N.Quasilocal where
  one_nonneg := by
    rw [← toQuasilocal_one (Classical.arbitrary R)]
    exact nonneg_iff.2 (toQuasilocal_mem_pos OrderUnitSpace.one_nonneg)
  exists_nsmul_one_le x := by
    obtain ⟨i, a, rfl⟩ := exists_toQuasilocal_eq x
    obtain ⟨n, hn⟩ := OrderUnitSpace.exists_nsmul_one_le a
    refine ⟨n, ?_⟩
    rw [← toQuasilocal_one i, ← map_nsmul, le_iff, ← map_sub]
    exact toQuasilocal_mem_pos (sub_nonneg.mpr hn)

variable (N) in
/-- Regard a subsystem observable as a global observable by a channel. -/
noncomputable def toQuasilocalChannel (i : R) : A i →ₚ₁[ℝ] N.Quasilocal := by
  refine ofLinearMap (toQuasilocal N i) ?_ (toQuasilocal_one i)
  intro _ ha
  exact nonneg_iff.2 (toQuasilocal_mem_pos ha)

@[simp] lemma toQuasilocalChannel_apply (i : R) (a : A i) :
    toQuasilocalChannel N i a = toQuasilocal N i a := rfl

end OrderUnit

/-!

## E. The Archimedean property

The global description should not introduce infinitesimal observables absent from every local
system. This property can be checked on a local representative, so it passes to the quasilocal
space.

-/

section Archimedean

variable [∀ X, ArchimedeanOrderUnitSpace (A X)] {N : LocalNet R A} [IsDirectedOrder R]
  [Nonempty R] [N.IsOrderEmbedding]

/-- The global observable space is Archimedean when every subsystem is Archimedean. -/
noncomputable instance : ArchimedeanOrderUnitSpace N.Quasilocal where
  le_zero_of_forall_pos_smul_one_le x hx := by
    obtain ⟨i, a, rfl⟩ := exists_toQuasilocal_eq x
    rw [← map_zero (toQuasilocal N i), toQuasilocal_le_iff]
    refine le_zero_of_forall_pos_smul_one_le a ?_
    intro ε hε
    have h := hx ε hε
    rwa [← toQuasilocal_one i, ← map_smul, toQuasilocal_le_iff] at h

end Archimedean

end LocalNet.Quasilocal

end ProbabilisticTheory
