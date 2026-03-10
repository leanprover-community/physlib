/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trong-Nghia Be, Matteo Cipollina, Tan-Phuoc-Hung Le, Joseph Tooby-Smith
-/
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Basic
import PhysLean.StatisticalMechanics.BoltzmannConstant
open NNReal
open Constants

/-!
# Temperature

In this module we define the type `Temperature` absolute thermodynamic temperature in kelvin.
This is the version of temperature most often used in undergraduate and non-mathematical physics.
-/

/-- The type `Temperature` represents absolute thermodynamic temperature in kelvin.
It wraps a nonnegative real number, which is the `val` field of the structure.
-/
structure Temperature where
  /-- The underlying nonnegative real number representing the temperature. -/
  val : ℝ≥0

/-!
## Type conversions from/to `Temperature`
-/
namespace Temperature

/-- Type coercion (implicit casting) from `Temperature` to `ℝ≥0`. -/
instance : Coe Temperature ℝ≥0 := ⟨fun (T : Temperature) => T.val⟩

/-- Convert a `Temperature` into a real number in `ℝ`. -/
def toReal (T : Temperature) : ℝ := NNReal.toReal T.val

/-- Type coercion (implicit casting) from `Temperature` to `ℝ`. -/
instance : Coe Temperature ℝ := ⟨fun (T : Temperature) => Temperature.toReal T⟩

/-- Build a `Temperature` from a nonnegative real number. -/
@[simp]
def ofNNReal (t : ℝ≥0) : Temperature := ⟨t⟩

/-- The `val` field of a temperature constructed from a nonnegative real number `t` is equal to `t`.
-/
@[simp]
lemma ofNNReal_val (t : ℝ≥0) : (ofNNReal t).val = t := rfl

/-- Coercing a temperature constructed from a nonnegative real number `t` back to `ℝ≥0` returns `t`.
-/
@[simp]
lemma coe_ofNNReal_coe (t : ℝ≥0) : ((ofNNReal t : Temperature) : ℝ≥0) = t := rfl

/-- Coercing a temperature constructed from a nonnegative real number `t` to `ℝ` returns `t`. -/
@[simp]
lemma coe_ofNNReal_real (t : ℝ≥0) : ((⟨t⟩ : Temperature) : ℝ) = t := rfl

/-- Build a temperature from a real number, given a proof that it is nonnegative. -/
@[simp]
noncomputable def ofRealNonneg (t : ℝ) (h_zero_le_t : 0 ≤ t) : Temperature :=
  ofNNReal ⟨t, h_zero_le_t⟩

/-- The `val` field of a temperature constructed from a nonnegative real number `t`
is equal to `⟨t, h_zero_le_t⟩`. -/
@[simp]
lemma ofRealNonneg_val {t : ℝ} (h_zero_le_t : 0 ≤ t) :
    (ofRealNonneg t h_zero_le_t).val = ⟨t, h_zero_le_t⟩ := rfl

/-!
## Extensionality for `Temperature`
-/

/-- Two `Temperature` instances are equal if their underlying `val` fields are equal. -/
@[ext]
lemma ext {T₁ T₂ : Temperature} (h_eq : T₁.val = T₂.val) : T₁ = T₂ := by
  cases T₁ with
  | mk T₁val
  cases T₂ with
  | mk T₂val
  cases h_eq
  rfl

/-!
## Topology on `Temperature`
-/

/-- Topology on `Temperature` induced from `ℝ≥0`. -/
instance : TopologicalSpace Temperature := TopologicalSpace.induced
  (fun (T : Temperature) => (T : ℝ≥0)) inferInstance

/-!
## Order structure on `Temperature` and related lemmas
-/

/-- The zero temperature (absolute zero) in kelvin. -/
instance : Zero Temperature := ⟨⟨0⟩⟩

/-- Zero is less than or equal to the real number representation of a `Temperature` in `ℝ≥0`. -/
@[simp]
lemma zero_le_nnreal (T : Temperature) : 0 ≤ (T : ℝ≥0) := T.val.property

/-- Zero is less than or equal to the real number representation of a `Temperature` in `ℝ`. -/
@[simp]
lemma zero_le_real (T : Temperature) : 0 ≤ (T : ℝ) := zero_le_nnreal T

/-- `Temperature` has a linear order inherited from `ℝ≥0` via the `val` field. -/
noncomputable instance : LinearOrder Temperature where
  le T₁ T₂ := T₁.val ≤ T₂.val
  lt T₁ T₂ := T₁.val < T₂.val
  le_refl T := le_refl T.val
  le_trans _ _ _ h₁ h₂ := le_trans h₁ h₂
  lt_iff_le_not_ge _ _ := lt_iff_le_not_ge
  le_antisymm _ _ h₁ h₂ := ext (le_antisymm h₁ h₂)
  le_total T₁ T₂ := le_total T₁.val T₂.val
  toDecidableLE T₁ T₂ := inferInstanceAs (Decidable (T₁.val ≤ T₂.val))

/-- `Temperature` has a bottom element (absolute zero). -/
noncomputable instance : OrderBot Temperature where
  bot := 0
  bot_le T := zero_le T.val

/-- `T₁ ≤ T₂` if and only if `T₁.val ≤ T₂.val` in `ℝ≥0`. -/
@[simp]
lemma le_def {T₁ T₂ : Temperature} : T₁ ≤ T₂ ↔ T₁.val ≤ T₂.val := Iff.rfl

/-- `T₁ < T₂` if and only if `T₁.val < T₂.val` in `ℝ≥0`. -/
@[simp]
lemma lt_def {T₁ T₂ : Temperature} : T₁ < T₂ ↔ T₁.val < T₂.val := Iff.rfl

/-- `⟨a⟩ ≤ ⟨b⟩` if and only if `a ≤ b` in `ℝ≥0`. -/
@[simp]
lemma mk_le_mk {a b : ℝ≥0} : Temperature.mk a ≤ Temperature.mk b ↔ a ≤ b := Iff.rfl

/-- `⟨a⟩ < ⟨b⟩` if and only if `a < b` in `ℝ≥0`. -/
@[simp]
lemma mk_lt_mk {a b : ℝ≥0} : Temperature.mk a < Temperature.mk b ↔ a < b := Iff.rfl

/-- Absolute zero is the minimum temperature. -/
@[simp]
lemma zero_le (T : Temperature) : (0 : Temperature) ≤ T := bot_le

/-- No temperature is strictly less than absolute zero. -/
@[simp]
lemma not_lt_zero (T : Temperature) : ¬ T < 0 := not_lt_bot

/-- The coercion to `ℝ` preserves `≤`. -/
lemma toReal_le_toReal {T₁ T₂ : Temperature} (h_le : T₁ ≤ T₂) : (T₁ : ℝ) ≤ (T₂ : ℝ) :=
  NNReal.coe_le_coe.mpr h_le

/-- The coercion to `ℝ` preserves `<`. -/
lemma toReal_lt_toReal {T₁ T₂ : Temperature} (h_lt : T₁ < T₂) : (T₁ : ℝ) < (T₂ : ℝ) :=
  NNReal.coe_lt_coe.mpr h_lt

/-- If the coercion to `ℝ` satisfies `≤`, then the temperatures satisfy `≤`. -/
lemma le_of_toReal_le {T₁ T₂ : Temperature} (h_le : (T₁ : ℝ) ≤ (T₂ : ℝ)) : T₁ ≤ T₂ :=
  NNReal.coe_le_coe.mp h_le

/-- If the coercion to `ℝ` satisfies `<`, then the temperatures satisfy `<`. -/
lemma lt_of_toReal_lt {T₁ T₂ : Temperature} (h_lt : (T₁ : ℝ) < (T₂ : ℝ)) : T₁ < T₂ :=
  NNReal.coe_lt_coe.mp h_lt

/-- `ofNNReal` preserves `≤`. -/
@[simp]
lemma ofNNReal_le_ofNNReal {a b : ℝ≥0} : ofNNReal a ≤ ofNNReal b ↔ a ≤ b := Iff.rfl

/-- `ofNNReal` preserves `<`. -/
@[simp]
lemma ofNNReal_lt_ofNNReal {a b : ℝ≥0} : ofNNReal a < ofNNReal b ↔ a < b := Iff.rfl

/-- The `val` of `min T₁ T₂` is `min T₁.val T₂.val`. -/
@[simp]
lemma val_min (T₁ T₂ : Temperature) : (min T₁ T₂).val = min T₁.val T₂.val := by
  simp only [min_def, le_def]
  split <;> rfl

/-- The `val` of `max T₁ T₂` is `max T₁.val T₂.val`. -/
@[simp]
lemma val_max (T₁ T₂ : Temperature) : (max T₁ T₂).val = max T₁.val T₂.val := by
  simp only [max_def, le_def]
  split <;> rfl

end Temperature
