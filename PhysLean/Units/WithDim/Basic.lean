/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Units.UnitDependent
/-!

## WithDim

WithDim is the type `M` which carrying the dimension `d`.

-/

@[expose] public section

open NNReal

/-- The type `M` carrying an instance of a dimension `d`. -/
structure WithDim (d : Dimension) (M : Type) where
  /-- The underlying value of `M`. -/
  val : M

namespace WithDim

@[ext]
lemma ext {d M} (x1 x2 : WithDim d M) (h : x1.val = x2.val) : x1 = x2 := by
  cases x1
  cases x2
  simp_all

instance (d : Dimension) (M : Type) : HasDim (WithDim d M) where
  d := d

@[simp]
lemma dim_apply (d : Dimension) (M : Type) :
    dim (WithDim d M) = d := rfl

instance (d : Dimension) (M : Type) [MulAction ℝ≥0 M] : MulAction ℝ≥0 (WithDim d M) where
  smul a m := ⟨a • m.val⟩
  one_smul m := ext _ _ (one_smul ℝ≥0 m.val)
  mul_smul a b m := by
    ext
    exact mul_smul a b m.val

@[simp]
lemma smul_val {d : Dimension} {M : Type} [MulAction ℝ≥0 M] (a : ℝ≥0) (m : WithDim d M) :
    (a • m).val = a • m.val := rfl

instance {d1 d2 : Dimension} :
    HMul (WithDim d1 ℝ) (WithDim d2 ℝ) (WithDim (d1 * d2) ℝ) where
  hMul m1 m2 := ⟨m1.val * m2.val⟩

lemma withDim_hMul_val {d1 d2 : Dimension} (m1 : WithDim d1 ℝ) (m2 : WithDim d2 ℝ) :
    (m1 * m2).val = m1.val * m2.val := rfl

instance {d1 d2 : Dimension} :
    DMul (WithDim d1 ℝ) (WithDim d2 ℝ) (WithDim (d1 * d2) ℝ) where
  mul_dim m1 m2 := by
    intro u1 u2
    ext
    simp only [withDim_hMul_val, dim_apply, map_mul, smul_val]
    rw [m1.2 u1, m2.2 u1]
    simp only [dim_apply, smul_val, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
    rw [smul_smul]
    congr 1
    rw [mul_comm]

open UnitDependent

@[simp]
lemma val_mul_eq_mul {d1 d2 : Dimension} (m1 : WithDim d1 ℝ) (m2 : WithDim d2 ℝ) :
    m1.val * m2.val = (m1 * m2).val := by
  simp only [withDim_hMul_val]

@[simp]
lemma val_pow_two_eq_mul {d1 : Dimension} (m1 : WithDim d1 ℝ) :
    m1.val ^ 2 = (m1 * m1).val := by
  rw [sq]
  rfl

@[simp]
lemma scaleUnit_val_eq_scaleUnit_val {d : Dimension} (M : Type) [MulAction ℝ≥0 M]
    (u1 u2 : UnitChoices) (m1 m2 : WithDim d M) :
    (scaleUnit u1 u2 m1).val = (scaleUnit u1 u2 m2).val ↔ m1.val = m2.val := by
  rw [← WithDim.ext_iff]
  simp only [scaleUnit_injective]
  exact WithDim.ext_iff

lemma scaleUnit_val_eq_scaleUnit_val_of_dim_eq {d1 d2 : Dimension} {M : Type} [MulAction ℝ≥0 M]
    {u1 u2 : UnitChoices} {m1 : WithDim d1 M} {m2 : WithDim d2 M}
    (h : d1 = d2 := by ext <;> {simp; try ring}) :
    (scaleUnit u1 u2 m1).val = (scaleUnit u1 u2 m2).val ↔ m1.val = m2.val := by
  subst h
  simp

lemma scaleUnit_val {d : Dimension} (M : Type) [MulAction ℝ≥0 M]
    (u1 u2 : UnitChoices) (m1 : WithDim d M) :
    (scaleUnit u1 u2 m1).val = u1.dimScale u2 d • m1.val := rfl

/-!

## Division

-/

noncomputable instance (d1 d2 : Dimension) :
    HDiv (WithDim d1 ℝ) (WithDim d2 ℝ) (WithDim (d1 * d2⁻¹) ℝ) where
  hDiv m1 m2 := ⟨m1.val / m2.val⟩

@[simp]
lemma val_div_val {d1 d2 : Dimension} (m1 : WithDim d1 ℝ) (m2 : WithDim d2 ℝ) :
    (m1.val / m2.val) = (m1 / m2).val := rfl

@[simp]
lemma div_scaleUnit {d1 d2 : Dimension} (m1 : WithDim d1 ℝ) (m2 : WithDim d2 ℝ)
    (u1 u2 : UnitChoices) :
    (scaleUnit u1 u2 m1) / (scaleUnit u1 u2 m2) = scaleUnit u1 u2 (m1 / m2) := by
  symm
  ext
  simp only [← val_div_val, scaleUnit_val]
  simp only [map_mul, map_inv, val_div_val]
  field_simp
  change ((u1.dimScale u2) d1 / (u1.dimScale u2) d2) * (m1 / m2).val =
    u1.dimScale u2 d1 * m1.val / (u1.dimScale u2 d2 * m2.val)
  rw [← val_div_val]
  exact div_mul_div_comm (↑((u1.dimScale u2) d1)) (↑((u1.dimScale u2) d2)) m1.val m2.val

@[simp]
lemma scaleUnit_dim_eq_zero {d : Dimension} (m : WithDim d ℝ) (u1 u2 : UnitChoices)
    (h : d = 1 := by ext <;> {simp; try ring}) : scaleUnit u1 u2 m = m := by
  subst h
  ext
  rw [scaleUnit_val]
  simp

/-!
## Casting
-/

set_option linter.unusedVariables false in
/-- The casting from `WithDim d M` to `WithDim d2 M` when `d = d2`. -/
@[nolint unusedArguments]
def cast {d d2 : Dimension} {M : Type} (m : WithDim d M)
    (h : d = d2 := by ext <;> {simp; try ring}) : WithDim d2 M := ⟨m.val⟩

@[simp]
lemma cast_refl {d : Dimension} {M : Type} (m : WithDim d M) :
    cast m rfl = m := rfl

@[simp]
lemma cast_scaleUnit {d d2 : Dimension} {M : Type} [MulAction ℝ≥0 M] (m : WithDim d M)
    (h : d = d2) (u1 u2 : UnitChoices) :
    cast (scaleUnit u1 u2 m) h = scaleUnit u1 u2 (cast m h) := by
  subst h
  simp

TODO "LPWE4" "Induce instances on `WithDim d M` from instances on `M`."

end WithDim
