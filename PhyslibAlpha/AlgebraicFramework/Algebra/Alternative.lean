/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.LinearCombination

/-!
# Alternative algebras

The coordinate algebra of the exceptional Albert Jordan algebra is octonionic: alternative, not
associative.  This file isolates the general associator calculus needed for that eventual model.
It is independent of Jordan order, norms, CFC, and JBW normality.
-/

@[expose] public section

/-- An alternative multiplication has associative repeated factors on either side. -/
class IsAlternative (A : Type*) [Mul A] : Prop where
  /-- Left alternativity. -/
  mul_alternative_left : ∀ x y : A, x * (x * y) = (x * x) * y
  /-- Right alternativity. -/
  mul_alternative_right : ∀ x y : A, (y * x) * x = y * (x * x)

/-- Associative algebras are alternative. -/
instance (priority := 100) {A : Type*} [Semigroup A] : IsAlternative A where
  mul_alternative_left x y := (mul_assoc x x y).symm
  mul_alternative_right x y := mul_assoc y x x

namespace IsAlternative

variable {A : Type*} [NonUnitalNonAssocRing A]

/-- The failure of associativity. -/
def associator (x y z : A) : A := (x * y) * z - x * (y * z)

theorem associator_add_left (x y z w : A) :
    associator (x + y) z w = associator x z w + associator y z w := by
  unfold associator
  simp only [add_mul]
  abel

theorem associator_add_mid (x y z w : A) :
    associator x (y + z) w = associator x y w + associator x z w := by
  unfold associator
  simp only [add_mul, mul_add]
  abel

theorem associator_add_right (x y z w : A) :
    associator x y (z + w) = associator x y z + associator x y w := by
  unfold associator
  simp only [mul_add]
  abel

/-- Teichmüller's identity holds before alternativity is assumed. -/
theorem teichmuller (x y z w : A) :
    associator (x * y) z w - associator x (y * z) w + associator x y (z * w) =
      associator x y z * w + x * associator y z w := by
  unfold associator
  simp only [sub_mul, mul_sub]
  abel

variable [IsAlternative A]

theorem associator_self_left (x y : A) : associator x x y = 0 := by
  unfold associator
  rw [mul_alternative_left]
  abel

theorem associator_right_self (x y : A) : associator y x x = 0 := by
  unfold associator
  rw [mul_alternative_right]
  abel

/-- The associator is skew under an adjacent swap. -/
theorem associator_swap_first (x y z : A) : associator x y z = -associator y x z := by
  have h : associator (x + y) (x + y) z = 0 := associator_self_left (x + y) z
  rw [associator_add_left, associator_add_mid, associator_add_mid,
    associator_self_left x z, associator_self_left y z] at h
  have h' : associator x y z + associator y x z = 0 := by
    abel_nf
    rwa [zero_add, add_zero] at h
  exact eq_neg_iff_add_eq_zero.mpr h'

theorem associator_swap_last (x y z : A) : associator x y z = -associator x z y := by
  have h : associator x (y + z) (y + z) = 0 := associator_right_self (y + z) x
  rw [associator_add_mid, associator_add_right, associator_add_right,
    associator_right_self y x, associator_right_self z x] at h
  have h' : associator x y z + associator x z y = 0 := by
    rwa [add_zero, zero_add] at h
  rw [add_comm] at h'
  exact (neg_eq_iff_add_eq_zero.mpr h').symm

theorem associator_cyclic (x y z : A) : associator x y z = associator y z x := by
  rw [associator_swap_first x y z, associator_swap_last y x z, neg_neg]

theorem associator_outer_self (x y : A) : associator x y x = 0 := by
  rw [associator_swap_last x y x, associator_self_left, neg_zero]

/-- The flexible law is forced by alternativity. -/
theorem mul_flexible (x y : A) : x * (y * x) = (x * y) * x := by
  have h := associator_outer_self x y
  unfold associator at h
  exact sub_eq_zero.mp h |>.symm

/-- The left Moufang identity. -/
theorem moufang_left (x y z : A) : (x * (z * x)) * y = x * (z * (x * y)) := by
  rw [← sub_eq_zero]
  have hstart : (x * (z * x)) * y - x * (z * (x * y)) =
      associator (x * z) x y + associator x z (x * y) := by
    rw [mul_flexible x z]
    unfold associator
    abel
  rw [hstart, associator_swap_first (x * z) x y, associator_swap_last x z (x * y)]
  have e1 : associator x (x * z) y = (x * x * z) * y - x * ((x * z) * y) := by
    unfold associator
    rw [mul_alternative_left]
  have e2 : associator x (x * y) z = (x * x * y) * z - x * ((x * y) * z) := by
    unfold associator
    rw [mul_alternative_left]
  rw [e1, e2]
  have hA : associator (x * x) z y + associator (x * x) y z = 0 := by
    rw [associator_swap_last (x * x) z y, neg_add_cancel]
  have hB : associator x z y + associator x y z = 0 := by
    rw [associator_swap_last x z y, neg_add_cancel]
  have e3 : (x * x * z) * y = associator (x * x) z y + (x * x) * (z * y) := by
    unfold associator; abel
  have e4 : (x * x * y) * z = associator (x * x) y z + (x * x) * (y * z) := by
    unfold associator; abel
  rw [e3, e4, ← mul_alternative_left x (z * y), ← mul_alternative_left x (y * z)]
  have key : -(x * (x * (z * y))) + x * ((x * z) * y) +
      (-(x * (x * (y * z))) + x * ((x * y) * z)) =
      x * (associator x z y + associator x y z) := by
    unfold associator
    simp only [mul_add, mul_sub]
    abel
  rw [hB, mul_zero] at key
  linear_combination (norm := abel) -hA + key

/-- McCrimmon's left bumping formula, the key alternative-algebra identity for Albert matrices. -/
theorem left_bumping (x y z : A) : associator x y (z * x) = x * associator y z x := by
  rw [← sub_eq_zero, associator_swap_last x y (z * x)]
  have e1 : associator x (z * x) y = x * (z * (x * y)) - x * ((z * x) * y) := by
    unfold associator
    rw [moufang_left]
  rw [e1]
  have cyc : associator y z x = associator z x y := associator_cyclic y z x
  have key : -(x * (z * (x * y)) - x * ((z * x) * y)) - x * associator y z x =
      x * (associator z x y - associator y z x) := by
    unfold associator
    simp only [mul_sub]
    abel
  rw [key, cyc, sub_self, mul_zero]

end IsAlternative
