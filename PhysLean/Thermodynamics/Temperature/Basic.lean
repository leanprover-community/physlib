/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trong-Nghia Be, Matteo Cipollina, Tan-Phuoc-Hung Le, Joseph Tooby-Smith
-/
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

For affine display scales with offsets (such as Celsius and Fahrenheit), see
`PhysLean.Thermodynamics.Temperature.TemperatureScales`.

For regularity properties of `ofβ`, see
`PhysLean.Thermodynamics.Temperature.Regularity`.

For convergence results, see
`PhysLean.Thermodynamics.Temperature.Convergence`.

For calculus relating T and β, see
`PhysLean.Thermodynamics.Temperature.Calculus`.
-/
open NNReal

/-- The type `Temperature` represents absolute thermodynamic temperature in kelvin.
-/
structure Temperature where
  val : ℝ≥0

/-- The type `PositiveTemperature` represents strictly positive absolute thermodynamic temperature
in kelvin.

It is defined as a subtype of `Temperature` where the `val` field is strictly positive.
-/
def PositiveTemperature := { T : Temperature // 0 < T.val }

/-!
## Basic instances and definitions for `Temperature`
-/
namespace Temperature
open Constants

/-- Type coercion (implicit casting) from `Temperature` to `ℝ≥0`.

Defined as a function that takes a `Temperature` and returns its underlying `ℝ≥0` value (by
accessing the `val` field).
-/
instance : Coe Temperature ℝ≥0 := ⟨fun (T : Temperature) => T.val⟩

/-- Function for `Temperature`:

Convert a `Temperature` to a real number in `ℝ`.
-/
def toReal (T : Temperature) : ℝ := NNReal.toReal T.val

/-- Type coercion (implicit casting) from `Temperature` to `ℝ`.

Defined as a function that takes a `Temperature` and returns the `val` field converted to `ℝ`.
-/
instance : Coe Temperature ℝ := ⟨fun (T : Temperature) => Temperature.toReal T⟩

/-- Topology on `Temperature` induced from `ℝ≥0`.

Defined using the `induced` topology from the coercion function that maps a `Temperature` to its
real number representation in `ℝ≥0`.
-/
instance : TopologicalSpace Temperature := TopologicalSpace.induced
  (fun (T : Temperature) => (T : ℝ≥0)) inferInstance

/-- The zero temperature (absolute zero) in kelvin. -/
instance : Zero Temperature := ⟨⟨0⟩⟩

/-- Extensionality lemma for `Temperature`.

Two `Temperature` instances are equal if their underlying `val` fields are equal.
-/
@[ext]
lemma ext {T₁ T₂ : Temperature} (h_eq : T₁.val = T₂.val) : T₁ = T₂ := by
  cases T₁ with
  | mk T₁val
  cases T₂ with
  | mk T₂val
  cases h_eq
  rfl

/-- Simplification lemma for `Temperature`:

Zero is less than or equal to the real number representation of a `Temperature` in `ℝ≥0`.
-/
@[simp]
lemma zero_le_nnreal (T : Temperature) : 0 ≤ (T : ℝ≥0) := by
  exact T.val.property

/-- Simplification lemma for `Temperature`:

The real number representation of a `Temperature` is greater or equal to zero in `ℝ≥0`.
-/
@[to_dual existing zero_le_nnreal]
lemma nnreal_ge_zero (T : Temperature) : (T : ℝ≥0) ≥ 0 := by
  exact zero_le_nnreal T

/-- Simplification lemma for `Temperature`:

Zero is less than or equal to the real number representation of a `Temperature` in `ℝ`.
-/
@[simp]
lemma zero_le_real (T : Temperature) : 0 ≤ (T : ℝ) := by
  exact zero_le_nnreal T

/-- Simplification lemma for `Temperature`:

The real number representation of a `Temperature` is greater or equal to zero.
-/
@[to_dual existing zero_le_real]
lemma real_ge_zero (T : Temperature) : (T : ℝ) ≥ 0 := by
  exact zero_le_real T

/-! ### Conversion to and from `ℝ≥0` -/

/-- Simplification function for `Temperature`:

Build a `Temperature` from a nonnegative real number.
-/
@[simp]
def ofNNReal (t : ℝ≥0) : Temperature :=
  ⟨t⟩

/-- Simplification lemma for `Temperature`:

The `val` field of a temperature constructed from a nonnegative real number `t` is equal to `t`.
-/
@[simp]
lemma ofNNReal_val (t : ℝ≥0) : (ofNNReal t).val = t := by
  rfl

/-- Simplification lemma for `Temperature`:

Coercing a temperature constructed from a nonnegative real number `t` back to `ℝ≥0` returns `t`.
-/
@[simp]
lemma coe_ofNNReal_coe (t : ℝ≥0) : ((ofNNReal t : Temperature) : ℝ≥0) = t := by
  rfl

/-- Simplification lemma for `Temperature`:

Coercing a temperature constructed from a nonnegative real number `t` to `ℝ` returns `t`.
-/
@[simp]
lemma coe_ofNNReal_real (t : ℝ≥0) : ((⟨t⟩ : Temperature) : ℝ) = t := by
  rfl

/-- Simplification function for `Temperature`:

Build a temperature from a real number, given a proof that it is nonnegative.
-/
@[simp]
noncomputable def ofRealNonneg (t : ℝ) (h_zero_le_t : 0 ≤ t) : Temperature := by
  exact ofNNReal ⟨t, h_zero_le_t⟩

/-- Simplification lemma for `Temperature`:

The `val` field of a temperature constructed from a nonnegative real number `t`
is equal to `⟨t, h_zero_le_t⟩`.
-/
@[simp]
lemma ofRealNonneg_val {t : ℝ} (h_zero_le_t : 0 ≤ t) :
    (ofRealNonneg t h_zero_le_t).val = ⟨t, h_zero_le_t⟩ := by
  rfl

/-! ### Linear order -/

/-- `Temperature` has a linear order inherited from `ℝ≥0` via the `val` field.

The ordering corresponds to the physical ordering of temperatures:
`T₁ ≤ T₂` if and only if `T₁.val ≤ T₂.val` in `ℝ≥0`.
-/
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

/-- Simplification lemma for `Temperature`:

`T₁ ≤ T₂` if and only if `T₁.val ≤ T₂.val` in `ℝ≥0`.
-/
@[simp]
lemma le_def {T₁ T₂ : Temperature} : T₁ ≤ T₂ ↔ T₁.val ≤ T₂.val := by
  exact Iff.rfl

/-- Simplification lemma for `Temperature`:

`T₁ < T₂` if and only if `T₁.val < T₂.val` in `ℝ≥0`.
-/
@[simp]
lemma lt_def {T₁ T₂ : Temperature} : T₁ < T₂ ↔ T₁.val < T₂.val := by
  exact Iff.rfl

/-- Simplification lemma for `Temperature`:

`⟨a⟩ ≤ ⟨b⟩` if and only if `a ≤ b` in `ℝ≥0`.
-/
@[simp]
lemma mk_le_mk {a b : ℝ≥0} : Temperature.mk a ≤ Temperature.mk b ↔ a ≤ b := by
  exact Iff.rfl

/-- Simplification lemma for `Temperature`:

`⟨a⟩ < ⟨b⟩` if and only if `a < b` in `ℝ≥0`.
-/
@[simp]
lemma mk_lt_mk {a b : ℝ≥0} : Temperature.mk a < Temperature.mk b ↔ a < b := by
  exact Iff.rfl

/-- Simplification lemma for `Temperature`:

Absolute zero is the minimum temperature.
-/
@[simp]
lemma zero_le (T : Temperature) : (0 : Temperature) ≤ T := by
  exact bot_le

/-- Simplification lemma for `Temperature`:

No temperature is strictly less than absolute zero.
-/
@[simp]
lemma not_lt_zero (T : Temperature) : ¬ T < 0 := by
  exact not_lt_bot

/-- Lemma for `Temperature`:

The coercion to `ℝ` preserves `≤`.
-/
lemma toReal_le_toReal {T₁ T₂ : Temperature} (h_le : T₁ ≤ T₂) : (T₁ : ℝ) ≤ (T₂ : ℝ) := by
  exact NNReal.coe_le_coe.mpr h_le

/-- Lemma for `Temperature`:

The coercion to `ℝ` preserves `<`.
-/
lemma toReal_lt_toReal {T₁ T₂ : Temperature} (h_lt : T₁ < T₂) : (T₁ : ℝ) < (T₂ : ℝ) := by
  exact NNReal.coe_lt_coe.mpr h_lt

/-- Lemma for `Temperature`:

If the coercion to `ℝ` satisfies `≤`, then the temperatures satisfy `≤`.
-/
lemma le_of_toReal_le {T₁ T₂ : Temperature} (h_le : (T₁ : ℝ) ≤ (T₂ : ℝ)) : T₁ ≤ T₂ := by
  exact NNReal.coe_le_coe.mp h_le

/-- Lemma for `Temperature`:

If the coercion to `ℝ` satisfies `<`, then the temperatures satisfy `<`.
-/
lemma lt_of_toReal_lt {T₁ T₂ : Temperature} (h_lt : (T₁ : ℝ) < (T₂ : ℝ)) : T₁ < T₂ := by
  exact NNReal.coe_lt_coe.mp h_lt

/-- Simplification lemma for `Temperature`:

`ofNNReal` preserves `≤`.
-/
@[simp]
lemma ofNNReal_le_ofNNReal {a b : ℝ≥0} : ofNNReal a ≤ ofNNReal b ↔ a ≤ b := by
  exact Iff.rfl

/-- Simplification lemma for `Temperature`:

`ofNNReal` preserves `<`.
-/
@[simp]
lemma ofNNReal_lt_ofNNReal {a b : ℝ≥0} : ofNNReal a < ofNNReal b ↔ a < b := by
  exact Iff.rfl

/-- Simplification lemma for `Temperature`:

The `val` of `min T₁ T₂` is `min T₁.val T₂.val`.
-/
@[simp]
lemma val_min (T₁ T₂ : Temperature) : (min T₁ T₂).val = min T₁.val T₂.val := by
  simp only [min_def, le_def]
  split <;> rfl

/-- Simplification lemma for `Temperature`:

The `val` of `max T₁ T₂` is `max T₁.val T₂.val`.
-/
@[simp]
lemma val_max (T₁ T₂ : Temperature) : (max T₁ T₂).val = max T₁.val T₂.val := by
  simp only [max_def, le_def]
  split <;> rfl

end Temperature

/-!
## Basic instances and definitions for `PositiveTemperature`
-/
namespace PositiveTemperature
open Constants

/-- Type coercion (implicit casting) from `PositiveTemperature` to `Temperature`.

Defined as a function that takes a `PositiveTemperature` and returns the underlying `Temperature`.
-/
instance : Coe PositiveTemperature Temperature := ⟨fun (T : PositiveTemperature) => T.1⟩

/-- Type coercion (implicit casting) from `PositiveTemperature` to `ℝ≥0`.

Defined as a function that takes a `PositiveTemperature` and returns the underlying `ℝ≥0` value.
-/
instance : Coe PositiveTemperature ℝ≥0 := ⟨fun (T : PositiveTemperature) => T.1.val⟩

/-- Type coercion (implicit casting) from `PositiveTemperature` to `ℝ>0`.

Defined as a function that takes a `PositiveTemperature` and returns the underlying `ℝ>0` value,
which is the `val` field of the underlying `Temperature` along with the proof that
it is strictly positive.
-/
instance : Coe PositiveTemperature ℝ>0 := ⟨fun (T : PositiveTemperature) => ⟨T.1.val, T.2⟩⟩

/-- Function for `PositiveTemperature`:

Convert a `PositiveTemperature` to a real number in `ℝ`.
-/
def toReal (T : PositiveTemperature) : ℝ := Temperature.toReal T.1

/-- Type coercion (implicit casting) from `PositiveTemperature` to `ℝ`.

Defined as a function that takes a `PositiveTemperature` and returns the value converted to `ℝ`.
-/
instance : Coe PositiveTemperature ℝ := ⟨fun (T : PositiveTemperature) => T.toReal⟩

/-- Topology on `PositiveTemperature` induced as a subtype of `Temperature`. -/
instance : TopologicalSpace PositiveTemperature := instTopologicalSpaceSubtype

/-- Extensionality lemma for `PositiveTemperature`.

Two `PositiveTemperature` instances are equal if their underlying `Temperature` values are equal.
-/
@[ext]
lemma ext {T₁ T₂ : PositiveTemperature} (h : T₁.1 = T₂.1) : T₁ = T₂ := by
  exact Subtype.ext h

/-- Simplification lemma for `PositiveTemperature`:

The `val` field (of type `ℝ≥0`) of the underlying `Temperature` is strictly positive.
-/
@[simp]
lemma val_pos (T : PositiveTemperature) : 0 < T.1.val := by
  exact T.2

/-- Simplification lemma for `PositiveTemperature`:

The real number representation of a `PositiveTemperature` is strictly positive.
-/
@[simp]
lemma zero_lt_toReal (T : PositiveTemperature) : 0 < (T : ℝ) := by
  exact T.2

/-- Function for `PositiveTemperature`:

Calculate the inverse temperature `β` corresponding to a given positive temperature `T`.

- Note:

1. This has dimensions equivalent to `Energy` to the power `-1`. Refer to the concept of
"thermodynamic beta" in thermodynamics for more details.
-/
noncomputable def β (T : PositiveTemperature) : ℝ>0 :=
  ⟨1 / (kB * (T : ℝ)), by
    apply div_pos
    · exact one_pos
    · apply mul_pos
      · exact kB_pos
      · exact zero_lt_toReal T⟩

/-- Simplification lemma for `PositiveTemperature`:

The definition of `β T` unfolds to its explicit formula in terms of `kB` and `T`.
-/
@[simp]
lemma β_eq (T : PositiveTemperature) : β T =
    ⟨1 / (kB * (T : ℝ)), by
      apply div_pos
      · exact one_pos
      · apply mul_pos
        · exact kB_pos
        · exact zero_lt_toReal T⟩ := by
  rfl

/-- Simplification lemma for `PositiveTemperature`:

Coercing `β T` from `ℝ≥0` to `ℝ` gives the explicit formula `1 / (kB * (T : ℝ))`.
-/
@[simp]
lemma β_toReal (T : PositiveTemperature) : (β T : ℝ) = (1 : ℝ) / (kB * (T : ℝ)) := by
  rfl

/-- Lemma for `PositiveTemperature`:

The inverse temperature `β` is strictly positive for positive temperatures.
-/
lemma β_pos (T : PositiveTemperature) : 0 < (T.β : ℝ) := by
  exact (β T).2

/-- Function for `PositiveTemperature`:

Construct a `PositiveTemperature` from a positive inverse temperature `β`.
-/
noncomputable def ofβ (β : ℝ>0): PositiveTemperature :=
  ⟨⟨⟨1 / (kB * β), by
    apply div_nonneg
    · exact zero_le_one
    · apply mul_nonneg
      · exact kB_nonneg
      · exact le_of_lt β.property⟩⟩,
   by
    exact div_pos one_pos (mul_pos kB_pos β.property)⟩

/-- Simplification lemma for `PositiveTemperature`:

Applying `β` to the temperature constructed from `β'` returns `β'`.
-/
@[simp]
lemma β_ofβ (β' : ℝ>0) : β (ofβ β') = β' := by
  ext
  simp only [PositiveTemperature.β, PositiveTemperature.ofβ, PositiveTemperature.toReal,
             Temperature.toReal]
  simp only [NNReal.coe_mk]
  field_simp [kB_ne_zero]

/-- Simplification lemma for `PositiveTemperature`:

Rebuilding a positive temperature `T` from its inverse temperature `β` gives back the original.
-/
@[simp]
lemma ofβ_β (T : PositiveTemperature) : ofβ (β T) = T := by
  ext
  simp [β, ofβ, Temperature.toReal, PositiveTemperature.toReal]
  field_simp [kB_ne_zero]

/-- The thermodynamic equivalence between positive temperature and positive inverse temperature.
-/
noncomputable def equiv_β : PositiveTemperature ≃ ℝ>0 where
  toFun := β
  invFun := ofβ
  left_inv := ofβ_β
  right_inv := β_ofβ

end PositiveTemperature
