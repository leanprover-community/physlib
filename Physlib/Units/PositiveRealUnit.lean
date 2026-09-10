/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Copyright (c) 2026 Hirotaka Monya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Hirotaka Monya
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# A. Shared arithmetic for positive-real unit types

`PositiveRealUnitCore` records a unit magnitude and its inverse construction.
Each concrete unit declares this instance explicitly and keeps its own structure.
The inhabited and same-type division instances, rescaling operation, and arithmetic
laws are provided generically. No command or type-specific lemma wrappers are needed.

The arithmetic is adapted from the existing unit modules by Joseph Tooby-Smith.
This interface describes an individual unit type, independently of the selection
and combination of units by `UnitMagnitudeCatalog` and `UnitSystem`.
-/

@[expose] public section

open NNReal

/-!
## A.1. Representation and instances
-/

/-- Common representation API for unit types whose magnitude is a positive real. -/
class PositiveRealUnitCore (U : Type) where
  /-- The underlying real magnitude of a unit. -/
  val : U → ℝ
  /-- Every unit has a strictly positive magnitude. -/
  pos : ∀ x, 0 < val x
  /-- Construct a unit from a positive real magnitude. -/
  ofVal : (r : ℝ) → 0 < r → U
  /-- Construction preserves the supplied magnitude. -/
  val_ofVal : ∀ r hr, val (ofVal r hr) = r
  /-- Reconstructing a unit from its magnitude returns that unit. -/
  ofVal_val : ∀ x, ofVal (val x) (pos x) = x

namespace PositiveRealUnitCore

variable {U : Type} [PositiveRealUnitCore U]

/-- The unit of magnitude one supplies a default unit. -/
instance (priority := 100) instInhabited : Inhabited U where
  default := ofVal 1 (by norm_num)

@[simp]
lemma val_ne_zero (x : U) : val x ≠ 0 :=
  ne_of_gt (pos x)

/-- The ratio of the magnitudes of two units of the same type. -/
noncomputable def ratio (x y : U) : NNReal :=
  ⟨val x / val y, _root_.div_nonneg (pos x).le (pos y).le⟩

/-- Division of two units of the same type is their nonnegative real ratio. -/
noncomputable instance (priority := 100) instHDiv : HDiv U U NNReal where
  hDiv := ratio

/-!
## A.2. Unit ratios
-/

/-- Unit division agrees with the ratio of the two magnitudes. -/
lemma div_eq_val (x y : U) :
    x / y = (⟨val x / val y, _root_.div_nonneg (pos x).le (pos y).le⟩ : NNReal) := rfl

@[simp]
lemma div_pos (x y : U) : (0 : NNReal) < x / y := by
  apply NNReal.coe_pos.mp
  change 0 < val x / val y
  exact _root_.div_pos (pos x) (pos y)

@[simp]
lemma div_ne_zero (x y : U) : x / y ≠ (0 : NNReal) :=
  ne_of_gt (div_pos x y)

@[simp]
lemma div_self (x : U) : x / x = (1 : NNReal) := by
  apply NNReal.eq
  change val x / val x = 1
  exact _root_.div_self (val_ne_zero x)

lemma div_symm (x y : U) : x / y = (y / x : NNReal)⁻¹ := by
  apply NNReal.eq
  change val x / val y = (val y / val x)⁻¹
  rw [inv_div]

/-- Unit ratios compose along an intermediate choice of unit. -/
lemma div_mul_div (x y z : U) : (x / y : NNReal) * (y / z) = x / z := by
  apply NNReal.eq
  change val x / val y * (val y / val z) = val x / val z
  rw [div_mul_div_comm, mul_comm (val x) (val y),
    mul_div_mul_left _ _ (val_ne_zero y)]

@[simp]
lemma div_mul_div_coe (x y z : U) :
    (x / y : ℝ) * (y / z : ℝ) = x / z := by
  change val x / val y * (val y / val z) = val x / val z
  field_simp [val_ne_zero]

/-!
## A.3. Positive rescaling
-/

/-- Rescale a unit by a strictly positive real factor. -/
def scale (r : ℝ) (x : U) (hr : 0 < r := by norm_num) : U :=
  ofVal (r * val x) (mul_pos hr (pos x))

@[simp]
lemma scale_val (r : ℝ) (x : U) (hr : 0 < r) :
    val (scale r x hr) = r * val x :=
  val_ofVal _ _

/-- Units with equal magnitudes are equal. -/
lemma ext {x y : U} (h : val x = val y) : x = y := by
  rw [← ofVal_val x, ← ofVal_val y]
  congr

/-- The ratio of a rescaled unit to the original is the scaling factor. -/
@[simp]
lemma scale_div_self (x : U) (r : ℝ) (hr : 0 < r) :
    scale r x hr / x = (⟨r, le_of_lt hr⟩ : NNReal) := by
  apply NNReal.eq
  change val (scale r x hr) / val x = r
  rw [scale_val]
  field_simp [val_ne_zero]

/-- The reverse ratio is the reciprocal of the scaling factor. -/
@[simp]
lemma self_div_scale (x : U) (r : ℝ) (hr : 0 < r) :
    x / scale r x hr =
      (⟨1 / r, _root_.div_nonneg (by simp) (le_of_lt hr)⟩ : NNReal) := by
  apply NNReal.eq
  change val x / val (scale r x hr) = 1 / r
  rw [scale_val]
  field_simp [val_ne_zero, ne_of_gt hr]

@[simp]
lemma scale_one (x : U) : scale 1 x = x := by
  apply ext
  simp only [scale_val, one_mul]

/-- Rescaling two units multiplies their ratio by the ratio of the factors. -/
@[simp]
lemma scale_div_scale (x1 x2 : U) {r1 r2 : ℝ} (hr1 : 0 < r1) (hr2 : 0 < r2) :
    scale r1 x1 hr1 / scale r2 x2 hr2 =
      (⟨r1, le_of_lt hr1⟩ / ⟨r2, le_of_lt hr2⟩ : NNReal) * (x1 / x2) := by
  apply NNReal.eq
  change val (scale r1 x1 hr1) / val (scale r2 x2 hr2) =
    (r1 / r2) * (val x1 / val x2)
  rw [scale_val, scale_val]
  rw [div_mul_div_comm]

/-- Successive rescalings compose by multiplication of their factors. -/
@[simp]
lemma scale_scale (x : U) (r1 r2 : ℝ) (hr1 : 0 < r1) (hr2 : 0 < r2) :
    scale r1 (scale r2 x hr2) hr1 =
      scale (r1 * r2) x (mul_pos hr1 hr2) := by
  apply ext
  simp only [scale_val, mul_assoc]

/-- Rescaling a unit by the ratio to a target unit produces that target. -/
@[simp]
lemma scale_div (x y : U) (hr : 0 < (y / x : ℝ)) :
    scale (y / x) x hr = y := by
  apply ext
  rw [scale_val]
  change (val y / val x) * val x = val y
  field_simp [val_ne_zero]

end PositiveRealUnitCore
