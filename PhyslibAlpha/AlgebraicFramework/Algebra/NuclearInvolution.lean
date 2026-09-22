/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.Algebra.Alternative
public import Mathlib.Algebra.Star.Basic

/-!
# Nuclear involutions

A star involution on an alternative algebra whose symmetric elements are nuclear (associate
trivially with everything) — the coordinate-algebra interface a `*`-alternative division algebra
like the octonions needs to support an exceptional Albert Jordan algebra of Hermitian matrices
over it. Independent of Jordan order, norms, CFC, and JBW normality.

## Key definitions and results

- `IsNuclear`, `IsNuclearInvolution`
- `nuclear_slip_left`/`_mid`/`_last`/`_last_right` : a nuclear element slips through the
  associator.
- `assoc_star_first`/`_mid`/`_last` : the associator is alternating in sign under `star`.
- `nuclear_comm_associator` : a nuclear element commutes with any associator.
-/

@[expose] public section

open IsAlternative

variable {D : Type*} [NonUnitalNonAssocRing D] [IsAlternative D]

/-- An element associating trivially in every slot. -/
def IsNuclear (x : D) : Prop :=
  ∀ y z : D, associator x y z = 0 ∧ associator y x z = 0 ∧ associator y z x = 0

omit [IsAlternative D] in
theorem nuclear_slip_left {n : D} (hn : IsNuclear n) (x y z : D) :
    associator (n * x) y z = n * associator x y z := by
  have h := teichmuller n x y z
  rw [(hn (x * y) z).1, (hn x (y * z)).1, (hn x y).1, zero_mul] at h
  linear_combination (norm := abel) h

theorem nuclear_slip_mid {n : D} (hn : IsNuclear n) (x y z : D) :
    associator x (n * y) z = n * associator x y z := by
  rw [associator_swap_first x (n * y) z, nuclear_slip_left hn y x z,
    associator_swap_first y x z, mul_neg, neg_neg]

theorem nuclear_slip_last {n : D} (hn : IsNuclear n) (x y z : D) :
    associator x y (n * z) = n * associator x y z := by
  rw [associator_swap_last x y (n * z), nuclear_slip_mid hn x z y,
    associator_swap_last x z y, mul_neg, neg_neg]

omit [IsAlternative D] in
theorem nuclear_slip_last_right {n : D} (hn : IsNuclear n) (x y z : D) :
    associator x y (z * n) = associator x y z * n := by
  have h := teichmuller x y z n
  rw [(hn (x * y) z).2.2, (hn x (y * z)).2.2, (hn y z).2.2, mul_zero] at h
  linear_combination (norm := abel) h

variable [StarAddMonoid D]

/-- A star involution whose symmetric elements are nuclear. -/
class IsNuclearInvolution (D : Type*) [NonUnitalNonAssocRing D] [IsAlternative D]
    [StarAddMonoid D] : Prop where
  isNuclear_of_star_eq : ∀ x : D, star x = x → IsNuclear x
  isNuclear_comm : ∀ n x : D, IsNuclear n → IsNuclear (n * x - x * n)

variable [IsNuclearInvolution D]

theorem isNuclear_add_star (x : D) : IsNuclear (x + star x) := by
  apply IsNuclearInvolution.isNuclear_of_star_eq
  rw [star_add, star_star, add_comm]

theorem assoc_star_first (x y z : D) : associator (star x) y z = -associator x y z := by
  have h : associator (star x) y z + associator x y z = 0 := by
    rw [← associator_add_left, add_comm (star x) x]
    exact (isNuclear_add_star x y z).1
  linear_combination (norm := abel) h

theorem assoc_star_mid (x y z : D) : associator x (star y) z = -associator x y z := by
  have h : associator x (star y) z + associator x y z = 0 := by
    rw [← associator_add_mid, add_comm (star y) y]
    exact (isNuclear_add_star y x z).2.1
  linear_combination (norm := abel) h

theorem assoc_star_last (x y z : D) : associator x y (star z) = -associator x y z := by
  have h : associator x y (star z) + associator x y z = 0 := by
    rw [← associator_add_right, add_comm (star z) z]
    exact (isNuclear_add_star z x y).2.2
  linear_combination (norm := abel) h

theorem nuclear_comm_associator {n : D} (hn : IsNuclear n) (x y z : D) :
    n * associator x y z = associator x y z * n := by
  have h4 := nuclear_slip_last hn x y z
  have h5 := nuclear_slip_last_right hn x y z
  have hz : associator x y (n * z - z * n) = 0 :=
    (IsNuclearInvolution.isNuclear_comm n z hn x y).2.2
  have hs : associator x y (n * z) - associator x y (z * n) = associator x y (n * z - z * n) := by
    unfold associator; simp only [mul_sub]; abel
  rw [hz] at hs
  linear_combination (norm := abel) -h4 + h5 + hs
