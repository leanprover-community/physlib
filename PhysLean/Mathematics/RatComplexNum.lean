/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Complex.Basic
/-!
# Rational complex numbers

-/

@[expose] public section

namespace PhysLean

/-- Rational complex numbers. This type is mainly used when decidability is needed. -/
structure RatComplexNum where
  /-- The real part of a `RatComplexNum`. -/
  fst : ℚ
  /-- The imaginary part of a `RatComplexNum`. -/
  snd : ℚ

namespace RatComplexNum

@[ext]
lemma ext {x y : RatComplexNum} (h1 : x.1 = y.1) (h2 : x.2 = y.2) : x = y := by
  cases x
  cases y
  simp only at h1 h2
  subst h1 h2
  rfl

/-- The equivalence as a type of `RatComplexNum` with `ℚ × ℚ`. -/
def equivToProd : RatComplexNum ≃ ℚ × ℚ where
  toFun := fun x => (x.1, x.2)
  invFun := fun x => ⟨x.1, x.2⟩
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro x
    cases x
    rfl

instance : DecidableEq RatComplexNum := Equiv.decidableEq equivToProd

instance : Add RatComplexNum where
  add := fun x y => ⟨x.fst + y.fst, x.snd + y.snd⟩

@[simp]
lemma add_fst (x y : RatComplexNum) : (x + y).fst = x.fst + y.fst := rfl

@[simp]
lemma add_snd (x y : RatComplexNum) : (x + y).snd = x.snd + y.snd := rfl

instance : AddCommGroup RatComplexNum where
  add_assoc := by
    intro a b c
    ext
    · simp only [add_fst]
      ring
    · simp only [add_snd]
      ring
  zero := ⟨0, 0⟩
  zero_add := by
    intro a
    match a with
    | ⟨a1, a2⟩ =>
      ext
      · change 0 + a1 = a1
        simp
      · change 0 + a2 = a2
        simp
  add_zero := by
    intro a
    match a with
    | ⟨a1, a2⟩ =>
      ext
      · change a1 + 0 = a1
        simp
      · change a2 + 0 = a2
        simp
  nsmul := fun n x => ⟨n • x.fst, n • x.snd⟩
  neg := fun x => ⟨-x.fst, -x.snd⟩
  zsmul := fun n x => ⟨n • x.1, n • x.2⟩
  neg_add_cancel := by
    intro a
    match a with
    | ⟨a1, a2⟩ =>
      ext
      · change -a1 + a1 = 0
        simp
      · change -a2 + a2 = 0
        simp
  add_comm := by
    intro x y
    ext
    · simp only [add_fst]
      ring
    · simp only [add_snd]
      ring
  nsmul_zero := by
    intro x
    simp only [zero_nsmul]
    rfl
  nsmul_succ := by
    intro x y
    ext
    · simp only [add_fst]
      ring
    · simp only [add_snd]
      ring
  zsmul_zero' := by
    intro a
    ext
    · simp only [zero_smul]
      rfl
    · simp only [zero_smul]
      rfl
  zsmul_succ' := by
    intro a n
    ext
    · simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, zsmul_eq_mul, Int.cast_add,
      Int.cast_natCast, Int.cast_one, add_fst]
      ring
    · simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, zsmul_eq_mul, Int.cast_add,
      Int.cast_natCast, Int.cast_one, add_snd]
      ring
  zsmul_neg' := by
    intro a n
    ext
    · simp only [zsmul_eq_mul, Int.cast_negSucc, Nat.cast_add, Nat.cast_one, neg_add_rev,
      Nat.succ_eq_add_one, Int.cast_add, Int.cast_natCast, Int.cast_one]
      ring
    · simp only [zsmul_eq_mul, Int.cast_negSucc, Nat.cast_add, Nat.cast_one, neg_add_rev,
      Nat.succ_eq_add_one, Int.cast_add, Int.cast_natCast, Int.cast_one]
      ring

instance : Mul RatComplexNum where
  mul := fun x y => ⟨x.fst * y.fst - x.snd * y.snd, x.fst * y.snd + x.snd * y.fst⟩

@[simp]
lemma mul_fst (x y : RatComplexNum) : (x * y).fst = x.fst * y.fst - x.snd * y.snd := rfl

@[simp]
lemma mul_snd (x y : RatComplexNum) : (x * y).snd = x.fst * y.snd + x.snd * y.fst := rfl

instance : Ring RatComplexNum where
  one := ⟨1, 0⟩
  mul_assoc := by
    intro x y z
    ext
    · simp only [mul_fst, mul_snd]
      ring
    · simp only [mul_fst, mul_snd]
      ring
  one_mul := by
    intro x
    match x with
    | ⟨x1, x2⟩ =>
      ext
      · change 1 * x1 - 0 * x2 = x1
        simp
      · change 1 * x2 + 0 * x1 = x2
        simp
  mul_one := by
    intro x
    match x with
    | ⟨x1, x2⟩ =>
      ext
      · change x1 * 1 - x2 * 0 = x1
        simp
      · change x1 * 0 + x2 * 1 = x2
        simp
  left_distrib := by
    intro a b c
    match a, b, c with
    | ⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩ =>
      ext
      · change a1 * (b1 + c1) - a2 * (b2 + c2) =
          (a1 * b1 - a2 * b2) + (a1 * c1 - a2 * c2)
        ring
      · change a1 * (b2 + c2) + a2 * (b1 + c1) =
          (a1 * b2 + a2 * b1) + (a1 * c2 + a2 * c1)
        ring
  right_distrib := by
    intro a b c
    match a, b, c with
    | ⟨b1, b2⟩, ⟨c1, c2⟩, ⟨a1, a2⟩ =>
      ext
      · change (b1 + c1) * a1 - (b2 + c2) * a2 =
          (b1 * a1 - b2 * a2) + (c1 * a1 - c2 * a2)
        ring
      · change (b1 + c1) * a2 + (b2 + c2) * a1 =
          (b1 * a2 + b2 * a1) + (c1 * a2 + c2 * a1)
        ring
  zero_mul := by
    intro a
    match a with
    | ⟨a1, a2⟩ =>
      ext
      · change 0 * a1 - 0 * a2 = 0
        simp
      · change 0 * a2 + 0 * a1 = 0
        simp
  mul_zero := by
    intro a
    match a with
    | ⟨a1, a2⟩ =>
      ext
      · change a1 * 0 - a2 * 0 = 0
        simp
      · change a1 * 0 + a2 * 0 = 0
        simp
  neg_add_cancel := by
    intro a
    match a with
    | ⟨a1, a2⟩ =>
      ext
      · change -a1 + a1 = 0
        simp
      · change -a2 + a2 = 0
        simp

@[simp]
lemma one_fst : (1 : RatComplexNum).fst = 1 := rfl

@[simp]
lemma one_snd : (1 : RatComplexNum).snd = 0 := rfl

@[simp]
lemma zero_fst : (0 : RatComplexNum).fst = 0 := rfl

@[simp]
lemma zero_snd : (0 : RatComplexNum).snd = 0 := rfl

open Complex

/-- The inclusion of `RatComplexNum` into the complex numbers. -/
noncomputable def toComplexNum : RatComplexNum →+* ℂ where
  toFun := fun x => x.fst + x.snd * I
  map_one' := by
    simp
  map_add' a b := by
    simp only [add_fst, Rat.cast_add, add_snd]
    ring
  map_mul' a b := by
    simp only [mul_fst, Rat.cast_sub, Rat.cast_mul, mul_snd, Rat.cast_add]
    ring_nf
    simp only [I_sq, mul_neg, mul_one]
    ring
  map_zero' := by
    simp

@[simp]
lemma I_mul_toComplexNum (a : RatComplexNum) : I * toComplexNum a = toComplexNum (⟨0, 1⟩ * a) := by
  simp only [toComplexNum, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, mul_fst, zero_mul,
    one_mul, zero_sub, Rat.cast_neg, mul_snd, zero_add]
  ring_nf
  simp only [I_sq, neg_mul, one_mul]
  ring

lemma ofNat_mul_toComplexNum (n : ℕ) (a : RatComplexNum) :
    n * toComplexNum a = toComplexNum (n * a) := by
  simp only [map_mul, map_natCast]

lemma toComplexNum_injective : Function.Injective toComplexNum := by
  intro a b ha
  simp only [toComplexNum, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk] at ha
  rw [Complex.ext_iff] at ha
  simp only [add_re, ratCast_re, mul_re, I_re, mul_zero, ratCast_im, I_im, mul_one, sub_self,
    add_zero, Rat.cast_inj, add_im, mul_im, zero_add] at ha
  ext
  · exact ha.1
  · exact ha.2

end RatComplexNum
end PhysLean
