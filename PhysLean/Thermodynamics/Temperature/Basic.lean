/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trong-Nghia Be, Matteo Cipollina, Tan-Phuoc-Hung Le, Joseph Tooby-Smith
-/
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Basic
import PhysLean.StatisticalMechanics.BoltzmannConstant
import PhysLean.Meta.Types.PosReal

/-!
# Temperature

In this module we define the types `Temperature` and `PositiveTemperature` to represent
absolute thermodynamic temperature in kelvin.
This is the version of temperature most often used in undergraduate and non-mathematical physics.

We also define the inverse temperature `β` (thermodynamic beta/coldness)
and its inverse function `ofβ`, which are commonly used in statistical mechanics and thermodynamics.
-/
open NNReal

/-- The type `Temperature` represents absolute thermodynamic temperature in kelvin.
It wraps a nonnegative real number, which is the `val` field of the structure.
-/
structure Temperature where
  val : ℝ≥0

/-- The type `PositiveTemperature` represents strictly positive absolute thermodynamic temperature
in kelvin.
It is defined as a subtype of `Temperature` where the `val` field is strictly positive.
-/
def PositiveTemperature := { T : Temperature // 0 < T.val }

/-!
## Type conversions from/to `Temperature`
-/
namespace Temperature
open Constants

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

end Temperature

/-!
## Extensionality for `Temperature`
-/
namespace Temperature

/-- Two `Temperature` instances are equal if their underlying `val` fields are equal. -/
@[ext]
lemma ext {T₁ T₂ : Temperature} (h_eq : T₁.val = T₂.val) : T₁ = T₂ := by
  cases T₁ with
  | mk T₁val
  cases T₂ with
  | mk T₂val
  cases h_eq
  rfl

end Temperature

/-!
## Topology on `Temperature`
-/
namespace Temperature

/-- Topology on `Temperature` induced from `ℝ≥0`. -/
instance : TopologicalSpace Temperature := TopologicalSpace.induced
  (fun (T : Temperature) => (T : ℝ≥0)) inferInstance

end Temperature

/-!
## Order structure on `Temperature` and related lemmas
-/
namespace Temperature

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

/-!
## Type conversion from/to `PositiveTemperature`
-/
namespace PositiveTemperature
open Constants

/-- Type coercion (implicit casting) from `PositiveTemperature` to `Temperature`. -/
instance : Coe PositiveTemperature Temperature := ⟨fun (T : PositiveTemperature) => T.1⟩

/-- Type coercion (implicit casting) from `PositiveTemperature` to `ℝ≥0`. -/
instance : Coe PositiveTemperature ℝ≥0 := ⟨fun (T : PositiveTemperature) => T.1.val⟩

/-- Type coercion (implicit casting) from `PositiveTemperature` to `ℝ>0`. -/
instance : Coe PositiveTemperature ℝ>0 := ⟨fun (T : PositiveTemperature) => ⟨T.1.val, T.2⟩⟩

/-- Convert a `PositiveTemperature` to a real number in `ℝ`. -/
def toReal (T : PositiveTemperature) : ℝ := Temperature.toReal T.1

/-- Type coercion (implicit casting) from `PositiveTemperature` to `ℝ`. -/
instance : Coe PositiveTemperature ℝ := ⟨fun (T : PositiveTemperature) => T.toReal⟩

/-- Build a `PositiveTemperature` from a strictly positive real number. -/
@[simp]
def ofPosReal (t : ℝ>0) : PositiveTemperature :=
  ⟨⟨t.1, le_of_lt t.2⟩, t.2⟩

/-- The `val` field of a positive temperature constructed from a positive real number `t`
is equal to `⟨t.1, le_of_lt t.2⟩`. -/
@[simp]
lemma ofPosReal_val (t : ℝ>0) : (ofPosReal t).1.val = ⟨t.1, le_of_lt t.2⟩ := rfl

/-- Coercing a positive temperature constructed from a positive real number `t`
back to `Temperature` returns `⟨⟨t.1, le_of_lt t.2⟩⟩`. -/
@[simp]
lemma coe_ofPosReal_temperature (t : ℝ>0) :
    ((ofPosReal t : PositiveTemperature) : Temperature) = ⟨⟨t.1, le_of_lt t.2⟩⟩ := rfl

/-- Coercing a positive temperature constructed from a positive real number `t` to `ℝ`
returns `t.1`. -/
@[simp]
lemma coe_ofPosReal_real (t : ℝ>0) : ((ofPosReal t : PositiveTemperature) : ℝ) = t.1 := rfl

end PositiveTemperature

/-!
## Extensionality for `PositiveTemperature`
-/
namespace PositiveTemperature

/-- Two `PositiveTemperature` instances are equal
if their underlying `Temperature` values are equal. -/
@[ext]
lemma ext {T₁ T₂ : PositiveTemperature} (h_eq : T₁.1 = T₂.1) : T₁ = T₂ := Subtype.ext h_eq

end PositiveTemperature

/-!
## Topology on `PositiveTemperature` and related lemmas
-/
namespace PositiveTemperature

/-- Topology on `PositiveTemperature` induced as a subtype of `Temperature`. -/
instance : TopologicalSpace PositiveTemperature := instTopologicalSpaceSubtype

end PositiveTemperature

/-!
## Order structure on `PositiveTemperature` and related lemmas
-/
namespace PositiveTemperature

/-- The `val` field (of type `ℝ≥0`) of the underlying `Temperature` is strictly positive. -/
@[simp]
lemma val_pos (T : PositiveTemperature) : 0 < T.1.val := T.2

/-- The real number representation of a `PositiveTemperature` is strictly positive. -/
@[simp]
lemma zero_lt_toReal (T : PositiveTemperature) : 0 < (T : ℝ) := T.2

/-- The `val` field of a `PositiveTemperature` is nonzero. -/
lemma val_ne_zero (T : PositiveTemperature) : T.1.val ≠ 0 := ne_of_gt (val_pos T)

/-- The real number representation of a `PositiveTemperature` is nonzero. -/
lemma toReal_ne_zero (T : PositiveTemperature) : (T : ℝ) ≠ 0 := ne_of_gt (zero_lt_toReal T)

/-- `PositiveTemperature` has a linear order inherited from `Temperature` via the subtype. -/
noncomputable instance : LinearOrder PositiveTemperature := Subtype.instLinearOrder _

/-- `T₁ ≤ T₂` if and only if `T₁.1.val ≤ T₂.1.val` in `ℝ≥0`. -/
@[simp]
lemma le_def {T₁ T₂ : PositiveTemperature} : T₁ ≤ T₂ ↔ T₁.1.val ≤ T₂.1.val := Iff.rfl

/-- `T₁ < T₂` if and only if `T₁.1.val < T₂.1.val` in `ℝ≥0`. -/
@[simp]
lemma lt_def {T₁ T₂ : PositiveTemperature} : T₁ < T₂ ↔ T₁.1.val < T₂.1.val := Iff.rfl

/-- `⟨a, ha⟩ ≤ ⟨b, hb⟩` if and only if `a ≤ b` in `Temperature`. -/
@[simp]
lemma mk_le_mk {a b : Temperature} {ha : 0 < a.val} {hb : 0 < b.val} :
  (⟨a, ha⟩ : PositiveTemperature) ≤ (⟨b, hb⟩ : PositiveTemperature) ↔ a ≤ b := Iff.rfl

/-- `⟨a, ha⟩ < ⟨b, hb⟩` if and only if `a < b` in `Temperature`. -/
@[simp]
lemma mk_lt_mk {a b : Temperature} {ha : 0 < a.val} {hb : 0 < b.val} :
  (⟨a, ha⟩ : PositiveTemperature) < (⟨b, hb⟩ : PositiveTemperature) ↔ a < b := Iff.rfl

/-- The coercion to `ℝ` preserves `≤`. -/
lemma toReal_le_toReal {T₁ T₂ : PositiveTemperature} (h_le : T₁ ≤ T₂) : (T₁ : ℝ) ≤ (T₂ : ℝ) :=
  Temperature.toReal_le_toReal h_le

/-- The coercion to `ℝ` preserves `<`. -/
lemma toReal_lt_toReal {T₁ T₂ : PositiveTemperature} (h_lt : T₁ < T₂) : (T₁ : ℝ) < (T₂ : ℝ) :=
  Temperature.toReal_lt_toReal h_lt

/-- If the coercion to `ℝ` satisfies `≤`, then the positive temperatures satisfy `≤`. -/
lemma le_of_toReal_le {T₁ T₂ : PositiveTemperature} (h_le : (T₁ : ℝ) ≤ (T₂ : ℝ)) : T₁ ≤ T₂ :=
  Temperature.le_of_toReal_le h_le

/-- If the coercion to `ℝ` satisfies `<`, then the positive temperatures satisfy `<`. -/
lemma lt_of_toReal_lt {T₁ T₂ : PositiveTemperature} (h_lt : (T₁ : ℝ) < (T₂ : ℝ)) : T₁ < T₂ :=
  Temperature.lt_of_toReal_lt h_lt

/-- `ofPosReal` preserves `≤`. -/
@[simp]
lemma ofPosReal_le_ofPosReal {a b : ℝ>0} : ofPosReal a ≤ ofPosReal b ↔ a.1 ≤ b.1 := Iff.rfl

/-- `ofPosReal` preserves `<`. -/
@[simp]
lemma ofPosReal_lt_ofPosReal {a b : ℝ>0} : ofPosReal a < ofPosReal b ↔ a.1 < b.1 := Iff.rfl

/-- The `val` of `min T₁ T₂` is `min T₁.1.val T₂.1.val`. -/
@[simp]
lemma val_min (T₁ T₂ : PositiveTemperature) : (min T₁ T₂).1.val = min T₁.1.val T₂.1.val := by
  simp only [min_def, le_def]
  split <;> rfl

/-- The `val` of `max T₁ T₂` is `max T₁.1.val T₂.1.val`. -/
@[simp]
lemma val_max (T₁ T₂ : PositiveTemperature) : (max T₁ T₂).1.val = max T₁.1.val T₂.1.val := by
  simp only [max_def, le_def]
  split <;> rfl

end PositiveTemperature

/-!
## Inverse temperature `β` and its inverse function `ofβ`
-/
namespace PositiveTemperature
open Constants

/-- Calculate the inverse temperature `β` corresponding to a given positive temperature `T`.

- Note: This has dimensions equivalent to `Energy` to the power `-1`.
Refer to the concept of "thermodynamic beta" in thermodynamics for more details.
-/
noncomputable def β (T : PositiveTemperature) : ℝ>0 :=
  ⟨1 / (kB * (T : ℝ)), by
    apply div_pos
    · exact one_pos
    · apply mul_pos
      · exact kB_pos
      · exact zero_lt_toReal T⟩

/-- The definition of `β T` unfolds to its explicit formula in terms of `kB` and `T`. -/
@[simp]
lemma β_eq (T : PositiveTemperature) : β T =
  ⟨1 / (kB * (T : ℝ)), by
    apply div_pos
    · exact one_pos
    · apply mul_pos
      · exact kB_pos
      · exact zero_lt_toReal T⟩ := rfl

/-- Coercing `β T` from `ℝ≥0` to `ℝ` gives the explicit formula `1 / (kB * (T : ℝ))`. -/
@[simp]
lemma β_toReal (T : PositiveTemperature) : (β T : ℝ) = (1 : ℝ) / (kB * (T : ℝ)) := rfl

/-- The inverse temperature `β` is strictly positive for positive temperatures. -/
lemma β_pos (T : PositiveTemperature) : 0 < (β T : ℝ) := (β T).2

/-- Construct a `PositiveTemperature` from a positive inverse temperature `β`. -/
noncomputable def ofβ (β : ℝ>0) : PositiveTemperature :=
  ⟨
    ⟨1 / (kB * β), by
      apply div_nonneg
      · exact zero_le_one
      · apply mul_nonneg
        · exact kB_nonneg
        · exact le_of_lt β.property⟩,
    div_pos one_pos (mul_pos kB_pos β.property)
  ⟩

/-- Applying `β` to the temperature constructed from `beta` returns `beta`. -/
@[simp]
lemma β_ofβ (beta : ℝ>0) : β (ofβ beta) = beta := by
  ext
  simp only [PositiveTemperature.β, PositiveTemperature.ofβ, PositiveTemperature.toReal,
             Temperature.toReal]
  simp only [NNReal.coe_mk]
  field_simp [kB_ne_zero]

/-- Rebuilding a positive temperature `T` from its inverse temperature `β` gives back the original.
-/
@[simp]
lemma ofβ_β (T : PositiveTemperature) : ofβ (β T) = T := by
  ext
  simp [β, ofβ, Temperature.toReal, PositiveTemperature.toReal]
  field_simp [kB_ne_zero]

/-- The thermodynamic equivalence between positive temperature and positive inverse temperature. -/
noncomputable def equiv_β : PositiveTemperature ≃ ℝ>0 where
  toFun := β
  invFun := ofβ
  left_inv := ofβ_β
  right_inv := β_ofβ

/-- The thermodynamic beta strictly reverses the order of temperatures. -/
lemma β_anti_comm {T₁ T₂ : PositiveTemperature} : T₁ ≤ T₂ ↔ β T₂ ≤ β T₁ := by
  have h_T₁_pos : (0 : ℝ) < (T₁ : ℝ) := zero_lt_toReal T₁
  have h_T₂_pos : (0 : ℝ) < (T₂ : ℝ) := zero_lt_toReal T₂
  constructor
  · intro h_T₁_le_T₂
    have h_βT₂_le_βT₁ : (β T₂ : ℝ) ≤ (β T₁ : ℝ) := by
      simp only [β_toReal]
      exact one_div_le_one_div_of_le (mul_pos kB_pos h_T₁_pos)
        (mul_le_mul_of_nonneg_left (toReal_le_toReal h_T₁_le_T₂) kB_pos.le)
    exact h_βT₂_le_βT₁
  · intro h_βT₂_le_βT₁
    have h_T₁_le_T₂ : (T₁ : ℝ) ≤ (T₂ : ℝ) := le_of_mul_le_mul_left
      ((one_div_le_one_div (mul_pos kB_pos h_T₂_pos) (mul_pos kB_pos h_T₁_pos)).mp h_βT₂_le_βT₁)
      kB_pos
    exact h_T₁_le_T₂

/-- The thermodynamic beta strictly reverses strict inequalities. -/
lemma β_strictAnti {T₁ T₂ : PositiveTemperature} : T₁ < T₂ ↔ β T₂ < β T₁ := by
  simp only [lt_iff_le_not_ge, β_anti_comm]

end PositiveTemperature
