/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Algebra.Alternative
public import Mathlib.Algebra.Star.Basic

/-!

# Nuclear involutions

## i. Overview

An element of an algebra is in the nucleus when it associates with all elements. A nuclear
involution is an involution whose symmetric elements are in the nucleus, as for the octonions.
Nuclear elements pass through associators, and the associator changes sign under the involution.

## ii. Key results

- `IsInNucleus`, `IsNuclearInvolution` : nuclear elements and nuclear involutions.
- `nuclear_comm_associator` : nuclear elements commute with associators.

-/

@[expose] public section

namespace ProbabilisticTheory

open IsAlternative

variable {D : Type*} [NonUnitalNonAssocRing D] [IsAlternative D]

/-- An element associating trivially in every slot. -/
def IsInNucleus (x : D) : Prop :=
  ∀ y z : D, associator x y z = 0 ∧ associator y x z = 0 ∧ associator y z x = 0

omit [IsAlternative D] in
lemma nuclear_slip_left {n : D} (hn : IsInNucleus n) (x y z : D) :
    associator (n * x) y z = n * associator x y z := by
  have h := teichmuller n x y z
  rw [(hn (x * y) z).1, (hn x (y * z)).1, (hn x y).1, zero_mul] at h
  linear_combination (norm := abel) h

lemma nuclear_slip_mid {n : D} (hn : IsInNucleus n) (x y z : D) :
    associator x (n * y) z = n * associator x y z := by
  rw [associator_swap_first x (n * y) z, nuclear_slip_left hn y x z,
    associator_swap_first y x z, mul_neg, neg_neg]

lemma nuclear_slip_last {n : D} (hn : IsInNucleus n) (x y z : D) :
    associator x y (n * z) = n * associator x y z := by
  rw [associator_swap_last x y (n * z), nuclear_slip_mid hn x z y,
    associator_swap_last x z y, mul_neg, neg_neg]

omit [IsAlternative D] in
lemma nuclear_slip_last_right {n : D} (hn : IsInNucleus n) (x y z : D) :
    associator x y (z * n) = associator x y z * n := by
  have h := teichmuller x y z n
  rw [(hn (x * y) z).2.2, (hn x (y * z)).2.2, (hn y z).2.2, mul_zero] at h
  linear_combination (norm := abel) h

variable [StarAddMonoid D]

/-- A star involution whose symmetric elements are nuclear. -/
class IsNuclearInvolution (D : Type*) [NonUnitalNonAssocRing D] [IsAlternative D]
    [StarAddMonoid D] : Prop where
  isNuclear_of_star_eq : ∀ x : D, star x = x → IsInNucleus x
  isNuclear_comm : ∀ n x : D, IsInNucleus n → IsInNucleus (n * x - x * n)

variable [IsNuclearInvolution D]

lemma isNuclear_add_star (x : D) : IsInNucleus (x + star x) := by
  apply IsNuclearInvolution.isNuclear_of_star_eq
  rw [star_add, star_star, add_comm]

lemma assoc_star_first (x y z : D) : associator (star x) y z = -associator x y z := by
  have h : associator (star x) y z + associator x y z = 0 := by
    rw [← associator_add_left, add_comm (star x) x]
    exact (isNuclear_add_star x y z).1
  linear_combination (norm := abel) h

lemma assoc_star_mid (x y z : D) : associator x (star y) z = -associator x y z := by
  have h : associator x (star y) z + associator x y z = 0 := by
    rw [← associator_add_mid, add_comm (star y) y]
    exact (isNuclear_add_star y x z).2.1
  linear_combination (norm := abel) h

lemma assoc_star_last (x y z : D) : associator x y (star z) = -associator x y z := by
  have h : associator x y (star z) + associator x y z = 0 := by
    rw [← associator_add_right, add_comm (star z) z]
    exact (isNuclear_add_star z x y).2.2
  linear_combination (norm := abel) h

lemma nuclear_comm_associator {n : D} (hn : IsInNucleus n) (x y z : D) :
    n * associator x y z = associator x y z * n := by
  have h4 := nuclear_slip_last hn x y z
  have h5 := nuclear_slip_last_right hn x y z
  have hz : associator x y (n * z - z * n) = 0 :=
    (IsNuclearInvolution.isNuclear_comm n z hn x y).2.2
  have hs : associator x y (n * z) - associator x y (z * n) = associator x y (n * z - z * n) := by
    unfold associator; simp only [mul_sub]; abel
  rw [hz] at hs
  linear_combination (norm := abel) -h4 + h5 + hs

end ProbabilisticTheory
