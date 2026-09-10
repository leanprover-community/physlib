/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Units.UnitDependent
/-!

## WithDim

WithDim is the type `M` which carrying the dimension `d`.

The dimension `d : Dimension B` may be taken over any basis `B` of base dimensions.
The *algebraic* structure of `WithDim d M` (its additive, order, scalar-action,
multiplication, division and casting instances) is available for every basis `B`.
The *unit-scaling* structure (`HasDim`, `DMul`, and the `scaleUnit` lemmas), which
routes through `LTMCTUnitChoices.dimScale`, is provided for the standard basis
`LTMCTDimensionBase`.

Real scalar multiplication acts on numerical values. Import
`Physlib.Units.WithDim.Analysis` for the normed-space structures and explicit
coordinate equivalences used to reuse existing analytic results.

-/

@[expose] public section

open NNReal

/-- The type `M` carrying an instance of a dimension `d`. -/
structure WithDim {B : Type} [DimensionBasis B] (d : Dimension B) (M : Type) where
  /-- The underlying value of `M`. -/
  val : M

namespace WithDim

@[ext]
lemma ext {B : Type} [DimensionBasis B] {d : Dimension B} {M}
    (x1 x2 : WithDim d M) (h : x1.val = x2.val) :
    x1 = x2 := by
  cases x1
  cases x2
  simp_all

instance (d : Dimension LTMCTDimensionBase) (M : Type) : HasDim (WithDim d M) where
  d := d

@[simp]
lemma dim_apply (d : Dimension LTMCTDimensionBase) (M : Type) :
    dim (WithDim d M) = d := rfl

/-!
## Inherited instances
-/

instance {B : Type} [DimensionBasis B] (d : Dimension B) (M : Type) [Inhabited M] :
    Inhabited (WithDim d M) where
  default := ⟨default⟩

instance {B : Type} [DimensionBasis B] (d : Dimension B) (M : Type) [Zero M] :
    Zero (WithDim d M) where
  zero := ⟨0⟩

@[simp]
lemma val_zero {B : Type} [DimensionBasis B] {d : Dimension B} {M : Type} [Zero M] :
    (0 : WithDim d M).val = 0 := rfl

instance {B : Type} [DimensionBasis B] (d : Dimension B) (M : Type) [Add M] :
    Add (WithDim d M) where
  add m1 m2 := ⟨m1.val + m2.val⟩

@[simp]
lemma val_add {B : Type} [DimensionBasis B] {d : Dimension B} {M : Type} [Add M]
    (m1 m2 : WithDim d M) :
    (m1 + m2).val = m1.val + m2.val := rfl

instance {B : Type} [DimensionBasis B] (d : Dimension B) (M : Type) [Neg M] :
    Neg (WithDim d M) where
  neg m := ⟨-m.val⟩

@[simp]
lemma val_neg {B : Type} [DimensionBasis B] {d : Dimension B} {M : Type} [Neg M]
    (m : WithDim d M) :
    (-m).val = -m.val := rfl

instance {B : Type} [DimensionBasis B] (d : Dimension B) (M : Type) [Sub M] :
    Sub (WithDim d M) where
  sub m1 m2 := ⟨m1.val - m2.val⟩

@[simp]
lemma val_sub {B : Type} [DimensionBasis B] {d : Dimension B} {M : Type} [Sub M]
    (m1 m2 : WithDim d M) :
    (m1 - m2).val = m1.val - m2.val := rfl

instance {B : Type} [DimensionBasis B] (d : Dimension B) (M : Type) [AddSemigroup M] :
    AddSemigroup (WithDim d M) where
  add_assoc m1 m2 m3 := by
    ext
    simp [add_assoc]

instance {B : Type} [DimensionBasis B] (d : Dimension B) (M : Type) [AddCommSemigroup M] :
    AddCommSemigroup (WithDim d M) where
  add_comm m1 m2 := by
    ext
    simp [add_comm]

instance {B : Type} [DimensionBasis B] (d : Dimension B) (M : Type) [AddMonoid M] :
    AddMonoid (WithDim d M) where
  zero_add m := by
    ext
    simp [zero_add]
  add_zero m := by
    ext
    simp [add_zero]
  nsmul := nsmulRec

instance {B : Type} [DimensionBasis B] (d : Dimension B) (M : Type) [AddCommMonoid M] :
    AddCommMonoid (WithDim d M) where
  add_comm m1 m2 := by
    ext
    simp [add_comm]

instance {B : Type} [DimensionBasis B] (d : Dimension B) (M : Type) [AddGroup M] :
    AddGroup (WithDim d M) where
  sub_eq_add_neg m1 m2 := by
    ext
    simp [sub_eq_add_neg]
  neg_add_cancel m := by
    ext
    simp [neg_add_cancel]
  zsmul := zsmulRec

instance {B : Type} [DimensionBasis B] (d : Dimension B) (M : Type) [AddCommGroup M] :
    AddCommGroup (WithDim d M) where
  add_comm m1 m2 := by
    ext
    simp [add_comm]

instance {B : Type} [DimensionBasis B] (d : Dimension B) (M : Type) [LE M] :
    LE (WithDim d M) where
  le m1 m2 := m1.val ≤ m2.val

@[simp]
lemma le_def {B : Type} [DimensionBasis B] {d : Dimension B} {M : Type} [LE M]
    (m1 m2 : WithDim d M) :
    m1 ≤ m2 ↔ m1.val ≤ m2.val := Iff.rfl

instance {B : Type} [DimensionBasis B] (d : Dimension B) (M : Type) [LT M] :
    LT (WithDim d M) where
  lt m1 m2 := m1.val < m2.val

@[simp]
lemma lt_def {B : Type} [DimensionBasis B] {d : Dimension B} {M : Type} [LT M]
    (m1 m2 : WithDim d M) :
    m1 < m2 ↔ m1.val < m2.val := Iff.rfl

instance {B : Type} [DimensionBasis B] (d : Dimension B) (M : Type) [Preorder M] :
    Preorder (WithDim d M) where
  le_refl m := by
    exact le_refl m.val
  le_trans m1 m2 m3 h12 h23 := by
    change m1.val ≤ m3.val
    exact le_trans h12 h23
  lt_iff_le_not_ge m1 m2 := by
    change m1.val < m2.val ↔ m1.val ≤ m2.val ∧ ¬ m2.val ≤ m1.val
    exact lt_iff_le_not_ge

instance {B : Type} [DimensionBasis B] (d : Dimension B) (M : Type) [PartialOrder M] :
    PartialOrder (WithDim d M) where
  le_antisymm m1 m2 h12 h21 := by
    ext
    exact le_antisymm h12 h21

instance {B : Type} [DimensionBasis B] (d : Dimension B) (M : Type) [MulAction ℝ≥0 M] :
    MulAction ℝ≥0 (WithDim d M) where
  smul a m := ⟨a • m.val⟩
  one_smul m := ext _ _ (one_smul ℝ≥0 m.val)
  mul_smul a b m := by
    ext
    exact mul_smul a b m.val

@[simp]
lemma smul_val {B : Type} [DimensionBasis B] {d : Dimension B} {M : Type} [MulAction ℝ≥0 M]
    (a : ℝ≥0) (m : WithDim d M) :
    (a • m).val = a • m.val := rfl

/-
Real scalar multiplication.

Real scalars here are dimensionless coefficients. This instance leaves the existing
`NNReal` action in place and uses the same underlying operations on `M`.
-/

/-- Dimensionless real scalars act on the numerical value of a tagged quantity. -/
instance instModuleReal {B : Type} [DimensionBasis B] (d : Dimension B) (M : Type)
    [AddCommMonoid M] [Module ℝ M] : Module ℝ (WithDim d M) where
  smul r x := ⟨r • x.val⟩
  one_smul x := WithDim.ext _ _ (one_smul ℝ x.val)
  mul_smul r s x := WithDim.ext _ _ (mul_smul r s x.val)
  smul_zero r := WithDim.ext _ _ (smul_zero r)
  smul_add r x y := WithDim.ext _ _ (smul_add r x.val y.val)
  add_smul r s x := WithDim.ext _ _ (add_smul r s x.val)
  zero_smul x := WithDim.ext _ _ (zero_smul ℝ x.val)

@[simp]
lemma real_smul_val {B : Type} [DimensionBasis B] {d : Dimension B} {M : Type}
    [AddCommMonoid M] [Module ℝ M] (r : ℝ) (x : WithDim d M) :
    (r • x).val = r • x.val := rfl

instance {B : Type} [DimensionBasis B] {d1 d2 : Dimension B} :
    HMul (WithDim d1 ℝ) (WithDim d2 ℝ) (WithDim (d1 * d2) ℝ) where
  hMul m1 m2 := ⟨m1.val * m2.val⟩

lemma withDim_hMul_val {B : Type} [DimensionBasis B] {d1 d2 : Dimension B}
    (m1 : WithDim d1 ℝ) (m2 : WithDim d2 ℝ) :
    (m1 * m2).val = m1.val * m2.val := rfl

instance {d1 d2 : Dimension LTMCTDimensionBase} :
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
lemma val_mul_eq_mul {B : Type} [DimensionBasis B] {d1 d2 : Dimension B}
    (m1 : WithDim d1 ℝ) (m2 : WithDim d2 ℝ) :
    m1.val * m2.val = (m1 * m2).val := by
  simp only [withDim_hMul_val]

@[simp]
lemma val_pow_two_eq_mul {B : Type} [DimensionBasis B] {d1 : Dimension B}
    (m1 : WithDim d1 ℝ) :
    m1.val ^ 2 = (m1 * m1).val := by
  rw [sq]
  rfl

@[simp]
lemma scaleUnit_val_eq_scaleUnit_val {d : Dimension LTMCTDimensionBase} (M : Type) [MulAction ℝ≥0 M]
    (u1 u2 : LTMCTUnitChoices) (m1 m2 : WithDim d M) :
    (scaleUnit u1 u2 m1).val = (scaleUnit u1 u2 m2).val ↔ m1.val = m2.val := by
  rw [← WithDim.ext_iff]
  simp only [scaleUnit_injective]
  exact WithDim.ext_iff

lemma scaleUnit_val_eq_scaleUnit_val_of_dim_eq {d1 d2 : Dimension LTMCTDimensionBase} {M : Type}
    [MulAction ℝ≥0 M]
    {u1 u2 : LTMCTUnitChoices} {m1 : WithDim d1 M} {m2 : WithDim d2 M}
    (h : d1 = d2 := by ext <;> {simp; try ring}) :
    (scaleUnit u1 u2 m1).val = (scaleUnit u1 u2 m2).val ↔ m1.val = m2.val := by
  subst h
  simp

lemma scaleUnit_val {d : Dimension LTMCTDimensionBase} (M : Type) [MulAction ℝ≥0 M]
    (u1 u2 : LTMCTUnitChoices) (m1 : WithDim d M) :
    (scaleUnit u1 u2 m1).val = u1.dimScale u2 d • m1.val := rfl

/-!

## Division

-/

noncomputable instance {B : Type} [DimensionBasis B] (d1 d2 : Dimension B) :
    HDiv (WithDim d1 ℝ) (WithDim d2 ℝ) (WithDim (d1 * d2⁻¹) ℝ) where
  hDiv m1 m2 := ⟨m1.val / m2.val⟩

@[simp]
lemma val_div_val {B : Type} [DimensionBasis B] {d1 d2 : Dimension B}
    (m1 : WithDim d1 ℝ) (m2 : WithDim d2 ℝ) :
    (m1.val / m2.val) = (m1 / m2).val := rfl

@[simp]
lemma div_scaleUnit {d1 d2 : Dimension LTMCTDimensionBase} (m1 : WithDim d1 ℝ) (m2 : WithDim d2 ℝ)
    (u1 u2 : LTMCTUnitChoices) :
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
lemma scaleUnit_dim_eq_zero {d : Dimension LTMCTDimensionBase} (m : WithDim d ℝ)
    (u1 u2 : LTMCTUnitChoices) (h : d = 1 := by ext <;> {simp; try ring}) :
    scaleUnit u1 u2 m = m := by
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
def cast {B : Type} [DimensionBasis B] {d d2 : Dimension B} {M : Type} (m : WithDim d M)
    (h : d = d2 := by ext <;> {simp; try ring}) : WithDim d2 M := ⟨m.val⟩

@[simp]
lemma cast_refl {B : Type} [DimensionBasis B] {d : Dimension B} {M : Type} (m : WithDim d M) :
    cast m rfl = m := rfl

@[simp]
lemma cast_scaleUnit {d d2 : Dimension LTMCTDimensionBase} {M : Type} [MulAction ℝ≥0 M]
    (m : WithDim d M)
    (h : d = d2) (u1 u2 : LTMCTUnitChoices) :
    cast (scaleUnit u1 u2 m) h = scaleUnit u1 u2 (cast m h) := by
  subst h
  simp

TODO "Induce further non-additive algebraic, additional order, and topological instances
  on `WithDim d M` from instances on `M`."

end WithDim
