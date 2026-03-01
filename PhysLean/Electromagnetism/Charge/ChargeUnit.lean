/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.RCLike.Basic
import PhysLean.Meta.TODO.Basic
/-!

# The units of charge

A unit of charge corresponding to a choice of translationally-invariant
metric on the charge manifold (to be defined diffeomorphic to `ℝ`).
Such a choice is (non-canonically) equivalent to a
choice of positive real number. We define the type `ChargeUnit` to be equivalent to the
positive reals.

We assume that the charge manifold is already defined with an orientation, with the
electron being in the negative direction.

On `ChargeUnit` there is an instance of division giving a real number, corresponding to the
ratio of the two scales of temperature unit.

To define specific charge units, we first state the existence of a
a given charge unit, and then construct all other charge units from it.
We choose to state the
existence of the charge unit of the coulomb, and construct all other charge units from that.

-/

open NNReal

/-- The choices of translationally-invariant metrics on the charge-manifold.
  Such a choice corresponds to a choice of units for charge.
  This assumes that an orientation has already being picked on the charge manifold. -/
structure ChargeUnit where
  /-- The underlying scale of the unit. -/
  val : ℝ
  property : 0 < val

namespace ChargeUnit

@[simp]
lemma val_ne_zero (x : ChargeUnit) : x.val ≠ 0 := by
  exact Ne.symm (ne_of_lt x.property)

lemma val_pos (x : ChargeUnit) : 0 < x.val := x.property

instance : Inhabited ChargeUnit where
  default := ⟨1, by norm_num⟩

/-!

## Division of ChargeUnit

-/

noncomputable instance : HDiv ChargeUnit ChargeUnit ℝ≥0 where
  hDiv x t := ⟨x.val / t.val, div_nonneg (le_of_lt x.val_pos) (le_of_lt t.val_pos)⟩

lemma div_eq_val (x y : ChargeUnit) :
    x / y = (⟨x.val / y.val, div_nonneg (le_of_lt x.val_pos) (le_of_lt y.val_pos)⟩ : ℝ≥0) := rfl

@[simp]
lemma div_ne_zero (x y : ChargeUnit) : ¬ x / y = (0 : ℝ≥0) := by
  rw [div_eq_val]
  refine coe_ne_zero.mp ?_
  simp

@[simp]
lemma div_pos (x y : ChargeUnit) : (0 : ℝ≥0) < x/ y := by
  apply lt_of_le_of_ne
  · exact zero_le (x / y)
  · exact Ne.symm (div_ne_zero x y)

@[simp]
lemma div_self (x : ChargeUnit) :
    x / x = (1 : ℝ≥0) := by
  simp [div_eq_val, x.val_ne_zero]

lemma div_symm (x y : ChargeUnit) :
    x / y = (y / x)⁻¹ := NNReal.eq <| by
  rw [div_eq_val, inv_eq_one_div, div_eq_val]
  simp

@[simp]
lemma div_mul_div_coe (x y z : ChargeUnit) :
    (x / y : ℝ) * (y /z : ℝ) = x /z := by
  simp [div_eq_val]
  field_simp

/-!

## The scaling of a charge unit

-/

/-- The scaling of a charge unit by a positive real. -/
def scale (r : ℝ) (x : ChargeUnit) (hr : 0 < r := by norm_num) : ChargeUnit :=
  ⟨r * x.val, mul_pos hr x.val_pos⟩

@[simp]
lemma scale_div_self (x : ChargeUnit) (r : ℝ) (hr : 0 < r) :
    scale r x hr / x = (⟨r, le_of_lt hr⟩ : ℝ≥0) := by
  simp [scale, div_eq_val]

@[simp]
lemma self_div_scale (x : ChargeUnit) (r : ℝ) (hr : 0 < r) :
    x / scale r x hr = (⟨1/r, _root_.div_nonneg (by simp) (le_of_lt hr)⟩ : ℝ≥0) := by
  simp [scale, div_eq_val]
  ext
  simp only [coe_mk]
  field_simp

@[simp]
lemma scale_one (x : ChargeUnit) : scale 1 x = x := by
  simp [scale]

@[simp]
lemma scale_div_scale (x1 x2 : ChargeUnit) {r1 r2 : ℝ} (hr1 : 0 < r1) (hr2 : 0 < r2) :
    scale r1 x1 hr1 / scale r2 x2 hr2 = (⟨r1, le_of_lt hr1⟩ / ⟨r2, le_of_lt hr2⟩) * (x1 / x2) := by
  refine NNReal.eq ?_
  simp [scale, div_eq_val]
  field_simp

@[simp]
lemma scale_scale (x : ChargeUnit) (r1 r2 : ℝ) (hr1 : 0 < r1) (hr2 : 0 < r2) :
    scale r1 (scale r2 x hr2) hr1 = scale (r1 * r2) x (mul_pos hr1 hr2) := by
  simp [scale]
  ring

/-!

## Specific choices of charge units

We define specific choices of charge units.
We first define the notion of a columb to correspond to the charge unit with underlying value
equal to `1`. This is really down to a choice in the isomorphism between the set of metrics
on the charge manifold and the positive reals.

-/

/-- The definition of a charge unit of coulomb. -/
def coulombs : ChargeUnit := ⟨1, by norm_num⟩

/-- The charge unit of a elementryCharge (1.602176634×10−19 coulomb). -/
noncomputable def elementaryCharge : ChargeUnit := scale (1.602176634e-19) coulombs

end ChargeUnit
