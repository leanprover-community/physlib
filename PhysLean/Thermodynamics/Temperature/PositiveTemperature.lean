/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trong-Nghia Be, Matteo Cipollina, Tan-Phuoc-Hung Le, Joseph Tooby-Smith
-/
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Basic
import PhysLean.StatisticalMechanics.BoltzmannConstant
import PhysLean.Mathematics.PosReal
import PhysLean.Thermodynamics.Temperature.Basic
open NNReal
open Constants

/-!
# PositiveTemperature

In this module we define the type `PositiveTemperature` representing strictly positive
thermodynamic temperature in kelvin.
This is the version of temperature most often used in undergraduate and non-mathematical physics.

We also define the inverse temperature `β` (thermodynamic beta/coldness)
and its inverse function `ofβ`, which are commonly used in statistical mechanics and thermodynamics.
-/

/-- The type `PositiveTemperature` represents strictly positive absolute thermodynamic temperature
in kelvin.
It is defined as a subtype of `Temperature` where the `val` field is strictly positive.
-/
def PositiveTemperature := { T : Temperature // 0 < T.val }

/-!
## Type conversion from/to `PositiveTemperature`
-/
namespace PositiveTemperature
open Constants

/-- Type coercion (implicit casting) from `PositiveTemperature` to `Temperature`. -/
instance : Coe PositiveTemperature Temperature :=
  ⟨fun (T : PositiveTemperature) => T.1⟩

/-- Type coercion (implicit casting) from `PositiveTemperature` to `ℝ≥0`. -/
instance : Coe PositiveTemperature ℝ≥0 :=
  ⟨fun (T : PositiveTemperature) => T.1.val⟩

/-- Type coercion (implicit casting) from `PositiveTemperature` to `ℝ>0`. -/
instance : Coe PositiveTemperature ℝ>0 :=
  ⟨fun (T : PositiveTemperature) => ⟨T.1.val, T.2⟩⟩

/-- Convert a `PositiveTemperature` to a real number in `ℝ`. -/
def toReal (T : PositiveTemperature) : ℝ :=
  Temperature.toReal T.1

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

/-!
## Extensionality for `PositiveTemperature`
-/

/-- Two `PositiveTemperature` instances are equal
if their underlying `Temperature` values are equal. -/
@[ext]
lemma ext {T₁ T₂ : PositiveTemperature} (h_eq : T₁.1 = T₂.1) : T₁ = T₂ := Subtype.ext h_eq

/-!
## Topology on `PositiveTemperature` and related lemmas
-/

/-- Topology on `PositiveTemperature` induced as a subtype of `Temperature`. -/
instance : TopologicalSpace PositiveTemperature := instTopologicalSpaceSubtype

/-!
## Order structure on `PositiveTemperature` and related lemmas
-/

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

/-!
## Inverse temperature `β` and its inverse function `ofβ`
-/

/-- Calculate the inverse temperature `β` corresponding to a given positive temperature `T`.

- Note: This has dimensions equivalent to `Energy` to the power `-1`.
Refer to the concept of "thermodynamic beta" in thermodynamics for more details.
-/
noncomputable def β (T : PositiveTemperature) : ℝ>0 :=
  ⟨1 / (kB * (T : ℝ)), by
    positivity [kB_pos, zero_lt_toReal T]⟩

/-- The definition of `β T` unfolds to its explicit formula in terms of `kB` and `T`. -/
@[simp]
lemma β_eq (T : PositiveTemperature) : β T =
    ⟨1 / (kB * (T : ℝ)), by
    positivity [kB_pos, zero_lt_toReal T]⟩:= rfl

/-- Coercing `β T` from `ℝ≥0` to `ℝ` gives the explicit formula `1 / (kB * (T : ℝ))`. -/
@[simp]
lemma β_toReal (T : PositiveTemperature) : (β T : ℝ) = (1 : ℝ) / (kB * (T : ℝ)) := rfl

/-- The inverse temperature `β` is strictly positive for positive temperatures. -/
lemma β_pos (T : PositiveTemperature) : 0 < (β T : ℝ) := (β T).2

/-- Construct a `PositiveTemperature` from a positive inverse temperature `β`. -/
noncomputable def ofβ (β : ℝ>0) : PositiveTemperature :=
  ⟨
    ⟨1 / (kB * β), by positivity [kB_nonneg, β.property]⟩,
    -- div_pos one_pos (mul_pos kB_pos β.property)
    by
      change (0 : ℝ) < _
      positivity [kB_pos, β.property]
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
lemma β_antitone : Antitone β := by
  intro T₁ T₂ h
  show (β T₂ : ℝ) ≤ (β T₁ : ℝ)
  simp only [β_toReal]
  exact one_div_le_one_div_of_le (mul_pos kB_pos (zero_lt_toReal T₁))
    (mul_le_mul_of_nonneg_left (toReal_le_toReal h) kB_pos.le)

/-- The thermodynamic beta strictly reverses strict inequalities. -/
lemma β_strictAnti : StrictAnti β :=
  β_antitone.strictAnti_of_injective (equiv_β.injective)

end PositiveTemperature
