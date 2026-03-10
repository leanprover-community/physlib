/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Units.Basic
/-!

## Types which depend on dimensions

In addition to types which carry a dimension, we also have types whose elements
depend on a choice of a units. For example a function
`f : M1 → M2` between two types `M1` and `M2` which carry dimensions does not itself
carry a dimensions, but is dependent on a choice of units.

We define three versions
- `UnitDependent M` having a function `scaleUnit : UnitChoices → UnitChoices → M → M`
  subject to two conditions `scaleUnit_trans` and `scaleUnit_id`
- `LinearUnitDependent M` extends `UnitDependent M` with additional linearity conditions
  on `scaleUnit`.
- `ContinuousLinearUnitDependent M` extends `LinearUnitDependent M` with an additional
  continuity condition on `scaleUnit`.

-/

@[expose] public section

open CarriesDimension
open NNReal

/-- A type carries the instance `UnitDependent M` if it depends on a choice of units.
  This dependence is manifested in `scaleUnit u1 u2` which describes how elements of `M` change
  under a scaling of units which would take `u1` to `u2`.

  This type is used for functions, and propositions etc.
-/
class UnitDependent (M : Type) where
  /-- `scaleUnit u1 u2` is the map transforming elements of `M` under a
    scaling of units which would take the unit `u1` to the unit `u2`. This is not
    to say that in `scaleUnit u1 u2 m` that `m` should be interpreted as being in the units `u1`,
    although this is often the case.
  -/
  scaleUnit : UnitChoices → UnitChoices → M → M
  scaleUnit_trans : ∀ u1 u2 u3 m, scaleUnit u2 u3 (scaleUnit u1 u2 m) = scaleUnit u1 u3 m
  scaleUnit_trans' : ∀ u1 u2 u3 m, scaleUnit u1 u2 (scaleUnit u2 u3 m) = scaleUnit u1 u3 m
  scaleUnit_id : ∀ u m, scaleUnit u u m = m

/--
  A type `M` with an instance of `UnitDependent M` such that `scaleUnit u1 u2` is compatible
  with the `MulAction ℝ≥0 M` instance on `M`.
-/
class MulUnitDependent (M : Type) [MulAction ℝ≥0 M] extends
    UnitDependent M where
  scaleUnit_mul : ∀ u1 u2 (r : ℝ≥0) m,
    scaleUnit u1 u2 (r • m) = r • scaleUnit u1 u2 m

/--
  A type `M` with an instance of `UnitDependent M` such that `scaleUnit u1 u2` is compatible
  with the `Module ℝ M` instance on `M`.
-/
class LinearUnitDependent (M : Type) [AddCommMonoid M] [Module ℝ M] extends UnitDependent M where
  scaleUnit_add : ∀ u1 u2 m1 m2,
    scaleUnit u1 u2 (m1 + m2) = scaleUnit u1 u2 m1 + scaleUnit u1 u2 m2
  scaleUnit_smul : ∀ u1 u2 (r : ℝ) m,
    scaleUnit u1 u2 (r • m) = r • scaleUnit u1 u2 m

/--
  A type `M` with an instance of `UnitDependent M` such that `scaleUnit u1 u2` is compatible
  with the `Module ℝ M` instance on `M`, and is continuous.
-/
class ContinuousLinearUnitDependent (M : Type) [AddCommMonoid M] [Module ℝ M]
    [TopologicalSpace M] extends LinearUnitDependent M where
  scaleUnit_cont : ∀ u1 u2, Continuous (scaleUnit u1 u2)

/-!

## Basic properties of scaleUnit

-/

@[simp]
lemma UnitDependent.scaleUnit_symm_apply {M : Type} [UnitDependent M]
    (u1 u2 : UnitChoices) (m : M) :
    scaleUnit u2 u1 (scaleUnit u1 u2 m) = m := by
  rw [scaleUnit_trans, scaleUnit_id]

@[simp]
lemma UnitDependent.scaleUnit_injective {M : Type} [UnitDependent M]
    (u1 u2 : UnitChoices) (m1 m2 : M) :
    scaleUnit u1 u2 m1 = scaleUnit u1 u2 m2 ↔ m1 = m2 := by
  constructor
  · intro h1
    have h2 : scaleUnit u2 u1 (scaleUnit u1 u2 m1) =
        scaleUnit u2 u1 (scaleUnit u1 u2 m2) := by rw [h1]
    simpa using h2
  · intro h
    subst h
    rfl

/-!

### Variations on the map scaleUnit

-/

open UnitDependent
/-- For an `M` with an instance of `UnitDependent M`, `scaleUnit u1 u2` as an equivalence. -/
def UnitDependent.scaleUnitEquiv {M : Type} [UnitDependent M]
    (u1 u2 : UnitChoices) : M ≃ M where
  toFun m := scaleUnit u1 u2 m
  invFun m := scaleUnit u2 u1 m
  right_inv m := by simp
  left_inv m := by simp

/-- For an `M` with an instance of `LinearUnitDependent M`, `scaleUnit u1 u2` as a
  linear map. -/
def LinearUnitDependent.scaleUnitLinear
    {M : Type} [AddCommMonoid M] [Module ℝ M] [LinearUnitDependent M]
    (u1 u2 : UnitChoices) :
    M →ₗ[ℝ] M where
  toFun m := scaleUnit u1 u2 m
  map_add' m1 m2 := by simp [LinearUnitDependent.scaleUnit_add]
  map_smul' r m2 := by simp [LinearUnitDependent.scaleUnit_smul]

/-- For an `M` with an instance of `LinearUnitDependent M`, `scaleUnit u1 u2` as a
  linear equivalence. -/
def LinearUnitDependent.scaleUnitLinearEquiv {M : Type} [AddCommMonoid M]
    [Module ℝ M] [LinearUnitDependent M] (u1 u2 : UnitChoices) :
    M ≃ₗ[ℝ] M :=
    LinearEquiv.ofLinear (scaleUnitLinear u1 u2) (scaleUnitLinear u2 u1)
    (by ext u; simp [scaleUnitLinear])
    (by ext u; simp [scaleUnitLinear])

/-- For an `M` with an instance of `ContinuousLinearUnitDependent M`, `scaleUnit u1 u2` as a
  continuous linear map. -/
def ContinuousLinearUnitDependent.scaleUnitContLinear {M : Type} [AddCommMonoid M] [Module ℝ M]
    [TopologicalSpace M] [ContinuousLinearUnitDependent M]
    (u1 u2 : UnitChoices) : M →L[ℝ] M where
  toLinearMap := LinearUnitDependent.scaleUnitLinear u1 u2
  cont := ContinuousLinearUnitDependent.scaleUnit_cont u1 u2

/-- For an `M` with an instance of `ContinuousLinearUnitDependent M`, `scaleUnit u1 u2` as a
  continuous linear equivalence. -/
def ContinuousLinearUnitDependent.scaleUnitContLinearEquiv {M : Type} [AddCommMonoid M] [Module ℝ M]
    [TopologicalSpace M] [ContinuousLinearUnitDependent M]
    (u1 u2 : UnitChoices) : M ≃L[ℝ] M :=
    ContinuousLinearEquiv.mk (LinearUnitDependent.scaleUnitLinearEquiv u1 u2)
    (ContinuousLinearUnitDependent.scaleUnit_cont u1 u2)
    (ContinuousLinearUnitDependent.scaleUnit_cont u2 u1)

@[simp]
lemma ContinuousLinearUnitDependent.scaleUnitContLinearEquiv_apply
    {M : Type} [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    [ContinuousLinearUnitDependent M]
    (u1 u2 : UnitChoices) (m : M) :
    (ContinuousLinearUnitDependent.scaleUnitContLinearEquiv u1 u2) m =
      scaleUnit u1 u2 m := rfl

@[simp]
lemma ContinuousLinearUnitDependent.scaleUnitContLinearEquiv_symm_apply
    {M : Type} [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    [ContinuousLinearUnitDependent M]
    (u1 u2 : UnitChoices) (m : M) :
    (ContinuousLinearUnitDependent.scaleUnitContLinearEquiv u1 u2).symm m =
      scaleUnit u2 u1 m := rfl
/-!

### Instances of the type classes

We construct instance of the `UnitDependent`, `LinearUnitDependent` and
  `ContinuousLinearUnitDependent` type classes based on `CarriesDimension`
  and functions.

-/

open UnitDependent

noncomputable instance : UnitDependent UnitChoices where
  scaleUnit u1 u2 u := ⟨
      LengthUnit.scale (u2.length/u1.length) u.length (by simp),
      TimeUnit.scale (u2.time/u1.time) u.time (by simp),
      MassUnit.scale (u2.mass/u1.mass) u.mass (by simp),
      ChargeUnit.scale (u2.charge/u1.charge) u.charge (by simp),
      TemperatureUnit.scale (u2.temperature/u1.temperature) u.temperature (by simp)⟩
  scaleUnit_trans u1 u2 u3 u := by
    congr 1 <;> simp
  scaleUnit_trans' u1 u2 u3 u := by
    congr 1
    · simp [LengthUnit.div_eq_val]
    · simp [TimeUnit.div_eq_val]
    · simp [MassUnit.div_eq_val]
    · simp [ChargeUnit.div_eq_val]
    · simp [TemperatureUnit.div_eq_val]
  scaleUnit_id u1 u := by simp

@[simp]
lemma UnitChoices.scaleUnit_apply_fst (u1 u2 : UnitChoices) :
    (scaleUnit u1 u2 u1) = u2 := by
  simp [scaleUnit]
  apply UnitChoices.ext
  · simp [LengthUnit.scale, LengthUnit.div_eq_val]
  · simp [TimeUnit.scale, TimeUnit.div_eq_val]
  · simp [MassUnit.scale, MassUnit.div_eq_val]
  · simp [ChargeUnit.scale, ChargeUnit.div_eq_val]
  · simp [TemperatureUnit.scale, TemperatureUnit.div_eq_val]

@[simp]
lemma UnitChoices.dimScale_scaleUnit {u1 u2 u : UnitChoices} (d : Dimension) :
    u.dimScale (scaleUnit u1 u2 u) d = u1.dimScale u2 d := by
  simp [dimScale]
  congr 1
  congr 1
  congr 1
  congr 1
  · congr 1
    simp [scaleUnit]
    simp [LengthUnit.div_eq_val]
  · congr 1
    simp [scaleUnit]
    simp [TimeUnit.div_eq_val]
  · congr 1
    simp [scaleUnit]
    simp [MassUnit.div_eq_val]
  · congr 1
    simp [scaleUnit]
    simp [ChargeUnit.div_eq_val]
  · congr 1
    simp [scaleUnit]
    simp [TemperatureUnit.div_eq_val]

lemma Dimensionful.of_scaleUnit {M : Type} [CarriesDimension M] {u1 u2 u : UnitChoices}
    (c : Dimensionful M) :
    c.1 (scaleUnit u1 u2 u) =
    u1.dimScale u2 (dim M) • c.1 (u) := by
  rw [c.2 u (scaleUnit u1 u2 u)]
  congr 1
  simp

noncomputable instance {M1 : Type} [CarriesDimension M1] : MulUnitDependent M1 where
  scaleUnit u1 u2 m := (toDimensionful u1 m).1 u2
  scaleUnit_trans u1 u2 u3 m := by
    simp [toDimensionful]
    rw [smul_smul, mul_comm, UnitChoices.dimScale_transitive]
  scaleUnit_trans' u1 u2 u3 m := by
    simp [toDimensionful, smul_smul, UnitChoices.dimScale_transitive]
  scaleUnit_id u m := by
    simp [toDimensionful, UnitChoices.dimScale_self]
  scaleUnit_mul u1 u2 r m := by
    simp [toDimensionful]
    exact smul_comm (u1.dimScale u2 (dim M1)) r m

lemma HasDim.scaleUnit_apply {M : Type} [CarriesDimension M]
    (u1 u2 : UnitChoices) (m : M) :
    scaleUnit u1 u2 m = (u1.dimScale u2 (dim M)) • m := by
  simp [scaleUnit, toDimensionful_apply_apply]

noncomputable instance {M : Type} [AddCommMonoid M] [Module ℝ M] [HasDim M] :
    LinearUnitDependent M where
  scaleUnit_add u1 u2 m1 m2 := by
    change (toDimensionful u1 (m1 + m2)).1 u2 = _
    rw [toDimensionful_apply_apply]
    simp
    rfl
  scaleUnit_smul u1 u2 r m := by
    change (toDimensionful u1 (r • m)).1 u2 = _
    rw [toDimensionful_apply_apply]
    rw [smul_comm]
    rfl

noncomputable instance {M : Type} [AddCommMonoid M] [Module ℝ M]
    [HasDim M] [TopologicalSpace M]
    [ContinuousConstSMul ℝ M] : ContinuousLinearUnitDependent M where
  scaleUnit_cont u1 u2 := by
    change Continuous fun m => (toDimensionful u1 m).1 u2
    conv =>
      enter [1, m]
      rw [toDimensionful_apply_apply]
    change Continuous fun m => (u1.dimScale u2 (dim M)).1 • m
    apply Continuous.const_smul
    exact continuous_id'

/-!

### Functions

-/

noncomputable instance {M1 M2 : Type} [UnitDependent M2] :
    UnitDependent (M1 → M2) where
  scaleUnit u1 u2 f := fun m1 => scaleUnit u1 u2 (f m1)
  scaleUnit_trans u1 u2 u3 f := by
    funext m1
    exact scaleUnit_trans u1 u2 u3 (f m1)
  scaleUnit_trans' u1 u2 u3 f := by
    funext m1
    exact scaleUnit_trans' u1 u2 u3 (f m1)
  scaleUnit_id u f := by
    funext m1
    exact scaleUnit_id u (f m1)

@[simp]
lemma UnitDependent.scaleUnit_apply_fun_right {M1 M2 : Type} [UnitDependent M2]
    (u1 u2 : UnitChoices) (f : M1 → M2) (m1 : M1) :
    scaleUnit u1 u2 f m1 = scaleUnit u1 u2 (f m1) := rfl

open LinearUnitDependent in
noncomputable instance {M1 M2 : Type} [AddCommMonoid M1] [Module ℝ M1]
    [AddCommMonoid M2] [Module ℝ M2] [LinearUnitDependent M2] :
    LinearUnitDependent (M1 →ₗ[ℝ] M2) where
  scaleUnit u1 u2 f := {
      toFun m1 := scaleUnit u1 u2 (f m1)
      map_add' m1 m2 := by simp [scaleUnit_add]
      map_smul' := by simp [scaleUnit_smul]}
  scaleUnit_trans u1 u2 u3 f := by
    ext m1
    exact scaleUnit_trans u1 u2 u3 (f m1)
  scaleUnit_trans' u1 u2 u3 f := by
    ext m1
    exact scaleUnit_trans' u1 u2 u3 (f m1)
  scaleUnit_id u f := by
    ext m1
    exact scaleUnit_id u (f m1)
  scaleUnit_add u1 u2 f1 f2 := by
    ext m
    simp [scaleUnit_add]
  scaleUnit_smul u1 u2 r f := by
    ext m
    simp [scaleUnit_smul]

open LinearUnitDependent ContinuousLinearUnitDependent in
noncomputable instance {M1 M2 : Type} [AddCommGroup M1] [Module ℝ M1]
    [TopologicalSpace M1]
    [AddCommGroup M2] [Module ℝ M2] [TopologicalSpace M2] [ContinuousConstSMul ℝ M2]
    [IsTopologicalAddGroup M2]
    [ContinuousLinearUnitDependent M2] :
    ContinuousLinearUnitDependent (M1 →L[ℝ] M2) where
  scaleUnit u1 u2 f :=
    ContinuousLinearEquiv.arrowCongr (ContinuousLinearEquiv.refl ℝ _)
      (scaleUnitContLinearEquiv u1 u2) f
  scaleUnit_trans u1 u2 u3 f := by
    ext m1
    exact scaleUnit_trans u1 u2 u3 (f m1)
  scaleUnit_trans' u1 u2 u3 f := by
    ext m1
    exact scaleUnit_trans' u1 u2 u3 (f m1)
  scaleUnit_id u f := by
    ext m1
    exact scaleUnit_id u (f m1)
  scaleUnit_add u1 u2 f1 f2 := by simp
  scaleUnit_smul u1 u2 r f := by simp
  scaleUnit_cont u1 u2 := ContinuousLinearEquiv.continuous
      ((ContinuousLinearEquiv.refl ℝ M1).arrowCongr (scaleUnitContLinearEquiv u1 u2))

noncomputable instance {M1 M2 : Type} [UnitDependent M1] :
    UnitDependent (M1 → M2) where
  scaleUnit u1 u2 f := fun m1 => f (scaleUnit u2 u1 m1)
  scaleUnit_trans u1 u2 u3 f := by
    funext m1
    simp [scaleUnit_trans]
  scaleUnit_trans' u1 u2 u3 f := by
    funext m1
    simp [scaleUnit_trans']
  scaleUnit_id u f := by
    funext m1
    simp [scaleUnit_id]

@[simp]
lemma UnitDependent.scaleUnit_apply_fun_left {M1 M2 : Type} [UnitDependent M1]
    (u1 u2 : UnitChoices) (f : M1 → M2) (m1 : M1) :
    scaleUnit u1 u2 f m1 = f (scaleUnit u2 u1 m1) := rfl

noncomputable instance instUnitDependentTwoSided
    {M1 M2 : Type} [UnitDependent M1] [UnitDependent M2] :
    UnitDependent (M1 → M2) where
  scaleUnit u1 u2 f := fun m1 => scaleUnit u1 u2 (f (scaleUnit u2 u1 m1))
  scaleUnit_trans u1 u2 u3 f := by
    funext m1
    simp [scaleUnit_trans]
  scaleUnit_trans' u1 u2 u3 f := by
    funext m1
    simp [scaleUnit_trans']
  scaleUnit_id u f := by
    funext m1
    simp [scaleUnit_id]

@[simp]
lemma UnitDependent.scaleUnit_apply_fun {M1 M2 : Type} [UnitDependent M1]
    [UnitDependent M2] (u1 u2 : UnitChoices) (f : M1 → M2) (m1 : M1) :
    scaleUnit u1 u2 f m1 = scaleUnit u1 u2 (f (scaleUnit u2 u1 m1)) := rfl

noncomputable instance instUnitDependentTwoSidedMul
    {M1 M2 : Type} [UnitDependent M1] [MulAction ℝ≥0 M2] [MulUnitDependent M2] :
    MulUnitDependent (M1 → M2) where
  scaleUnit u1 u2 f := fun m1 => scaleUnit u1 u2 (f (scaleUnit u2 u1 m1))
  scaleUnit_trans u1 u2 u3 f := by
    funext m1
    simp [scaleUnit_trans]
  scaleUnit_trans' u1 u2 u3 f := by
    funext m1
    simp [scaleUnit_trans']
  scaleUnit_id u f := by
    funext m1
    simp [scaleUnit_id]
  scaleUnit_mul u1 u2 r f := by
    funext m1
    simp [MulUnitDependent.scaleUnit_mul]

open LinearUnitDependent ContinuousLinearUnitDependent in
noncomputable instance instContinuousLinearUnitDependentMap
    {M1 M2 : Type} [AddCommGroup M1] [Module ℝ M1]
    [TopologicalSpace M1] [ContinuousLinearUnitDependent M1]
    [AddCommGroup M2] [Module ℝ M2] [TopologicalSpace M2] [ContinuousConstSMul ℝ M2]
    [IsTopologicalAddGroup M2]
    [ContinuousLinearUnitDependent M2] :
    ContinuousLinearUnitDependent (M1 →L[ℝ] M2) where
  scaleUnit u1 u2 f :=
    ContinuousLinearEquiv.arrowCongr (scaleUnitContLinearEquiv u1 u2)
      (scaleUnitContLinearEquiv u1 u2) f
  scaleUnit_trans u1 u2 u3 f := by
    ext m1
    simp [scaleUnit_trans]
  scaleUnit_trans' u1 u2 u3 f := by
    ext m1
    simp [scaleUnit_trans']
  scaleUnit_id u f := by
    ext m1
    simp [scaleUnit_id]
  scaleUnit_add u1 u2 f1 f2 := by simp
  scaleUnit_smul u1 u2 r f := by simp
  scaleUnit_cont u1 u2 := ContinuousLinearEquiv.continuous
      ((scaleUnitContLinearEquiv u1 u2).arrowCongr (scaleUnitContLinearEquiv u1 u2))

@[simp]
lemma ContinuousLinearUnitDependent.scaleUnit_apply_fun {M1 M2 : Type}
    [AddCommGroup M1] [Module ℝ M1]
    [TopologicalSpace M1] [ContinuousLinearUnitDependent M1]
    [AddCommGroup M2] [Module ℝ M2] [TopologicalSpace M2] [ContinuousConstSMul ℝ M2]
    [IsTopologicalAddGroup M2]
    [ContinuousLinearUnitDependent M2]
    (u1 u2 : UnitChoices) (f : M1 →L[ℝ] M2) (m1 : M1) :
    scaleUnit u1 u2 f m1 =
      scaleUnit u1 u2 (f (scaleUnit u2 u1 m1)) := rfl

/-!

### isDimensionallyCorrect

-/

/-- A term of type `M` carrying an instance of `UnitDependent M` is said to be
  dimensionally correct if under a change of units it remains the same.

  More colloquially, something is dimensionally correct if it (e.g. it's value or its truth
  for a proposition) does not depend on the units it is written in.

  For the case of `m : M` with `CarriesDimension M` then `IsDimensionallyCorrect m`
  corresponds to the statement that `m` does not depend on units, e.g. is zero
  or the dimension of `M` is zero.
-/
def IsDimensionallyCorrect {M : Type} [UnitDependent M] (m : M) : Prop :=
  ∀ u1 u2 : UnitChoices, scaleUnit u1 u2 m = m

lemma isDimensionallyCorrect_iff {M : Type} [UnitDependent M] (m : M) :
    IsDimensionallyCorrect m ↔ ∀ u1 u2 : UnitChoices,
      scaleUnit u1 u2 m = m := by rfl

@[simp]
lemma isDimensionallyCorrect_fun_iff {M1 M2 : Type} [UnitDependent M1] [UnitDependent M2]
    {f : M1 → M2} :
    IsDimensionallyCorrect f ↔
    ∀ u1 u2 : UnitChoices, ∀ m, scaleUnit u1 u2 (f (scaleUnit u2 u1 m)) = f m := by
  constructor
  · intro h u1 u2 m
    have h1 := h u1 u2
    conv_rhs => rw [← h1]
    rfl
  · intro h u1 u2
    funext m
    exact h u1 u2 m

@[simp]
lemma isDimensionallyCorrect_fun_left {M1 M2 : Type} [UnitDependent M1]
    {f : M1 → M2} :
    IsDimensionallyCorrect f ↔
    ∀ u1 u2 : UnitChoices, ∀ m, (f (scaleUnit u2 u1 m)) = f m := by
  constructor
  · intro h u1 u2 m
    have h1 := h u1 u2
    conv_rhs => rw [← h1]
    rfl
  · intro h u1 u2
    funext m
    exact h u1 u2 m

@[simp]
lemma isDimensionallyCorrect_fun_right {M1 M2 : Type} [UnitDependent M2]
    {f : M1 → M2} :
    IsDimensionallyCorrect f ↔
    ∀ u1 u2 : UnitChoices, ∀ m, scaleUnit u1 u2 (f m) = f m := by
  constructor
  · intro h u1 u2 m
    have h1 := h u1 u2
    conv_rhs => rw [← h1]
    rfl
  · intro h u1 u2
    funext m
    exact h u1 u2 m
/-!

## Some type classes to help track dimensions

-/

/-- The multiplication of an element of `M1` with an element of `M2` to get an element
  of `M3` in such a way that dimensions are preserved. -/
class DMul (M1 M2 M3 : Type) [CarriesDimension M1] [CarriesDimension M2] [CarriesDimension M3]
    extends HMul M1 M2 M3 where
  mul_dim : ∀ (m1 : Dimensionful M1) (m2 : Dimensionful M2),
    HasDimension (fun u => hMul (m1.1 u) (m2.1 u))

@[simp]
lemma DMul.hMul_scaleUnit {M1 M2 M3 : Type} [CarriesDimension M1] [CarriesDimension M2]
    [CarriesDimension M3]
    [DMul M1 M2 M3] (m1 : M1) (m2 : M2) (u1 u2 : UnitChoices) :
    (scaleUnit u1 u2 m1) * (scaleUnit u1 u2 m2) =
    scaleUnit u1 u2 (m1 * m2) := by
  simp [scaleUnit, toDimensionful]
  have h1 := DMul.mul_dim (M3 := M3) (toDimensionful u1 m1) (toDimensionful u1 m2) u2 u1
  simp [toDimensionful_apply_apply] at h1
  conv_rhs =>
    rw [h1, smul_smul]
    simp

/-!

## Dim Subtype

-/

/-- Given a type `M` that depends on units, e.g. the function type `M1 → M2` between two types
  carrying a dimension, the subtype of `M` which scales according to the dimension `d`. -/
def DimSet (M : Type) [MulAction ℝ≥0 M] [MulUnitDependent M] (d : Dimension) : Set M :=
  {m : M | ∀ u1 u2, scaleUnit u1 u2 m = (UnitChoices.dimScale u1 u2 d) • m}

instance (M : Type) [MulAction ℝ≥0 M] [MulUnitDependent M] (d : Dimension) :
    MulAction ℝ≥0 (DimSet M d) where
  smul a f := ⟨a • f.1, fun u1 u2 => by
    rw [smul_comm, ← f.2]
    rw [MulUnitDependent.scaleUnit_mul]⟩
  one_smul f := by
    ext
    change (1 : ℝ≥0) • f.1 = f.1
    simp
  mul_smul a b f := by
    ext
    change (a * b) • f.1 = a • (b • f.1)
    rw [smul_smul]

instance (M : Type) [MulAction ℝ≥0 M] [MulUnitDependent M] (d : Dimension) :
    CarriesDimension (DimSet M d) where
  d := d

@[simp]
lemma scaleUnit_dimSet_val {M : Type} [MulAction ℝ≥0 M] [MulUnitDependent M] (d : Dimension)
    (m : DimSet M d) (u1 u2 : UnitChoices) :
    (scaleUnit u1 u2 m).1 = scaleUnit u1 u2 m.1 := by
  rw [HasDim.scaleUnit_apply, m.2]
  rfl

lemma DimSet.mem_iff {M : Type} [MulAction ℝ≥0 M] [MulUnitDependent M] (d : Dimension) (m : M) :
    m ∈ DimSet M d ↔ ∀ u1 u2, scaleUnit u1 u2 m = (UnitChoices.dimScale u1 u2 d) • m := by rfl
