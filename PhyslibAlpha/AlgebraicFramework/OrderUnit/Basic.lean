/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Algebra.Order.Nonneg.Basic
public import Mathlib.Data.NNReal.Defs
public import Mathlib.Geometry.Convex.Cone.Pointed

/-!

# Order units and the positive cone

## i. Overview

`E` is where measurement outcomes and expectation values live, and `≤` is the natural order on
them: `0 ≤ x` means `x` could be a probability, or the expectation value of a
positive observable — since no measurement ever returns something negative.

`1 : E` is the certain outcome, i.e. the identity operator. `IsOrderUnit` says it's the biggest
thing around: every outcome is bounded by finitely many copies of `1`, which is what lets us later
squeeze an effect between `0` and `1` or normalize a state. `IsArchimedeanOrderUnit` adds one more
thing: nothing is infinitesimally smaller than `1` without actually being `≤ 0`. That's what lets
`≤` become an actual distance between states later, not just a comparison.

`PosCone E` is just the possible outcomes on their own. Adding two of them, or scaling one down by
a probability, keeps you among possible outcomes, and does so as a `ℝ≥0`-module.

## ii. Key definitions and results

- `IsOrderUnit E`
- `IsArchimedeanOrderUnit E`
- `IsOrderUnitElement u`
- `IsArchimedeanOrderUnitElement u`
- `PosCone E`
- `IsOrderUnit.exists_eq_sub_nonneg`

## iii. Table of contents

- A. Order units
- B. The positive cone

-/

@[expose] public section

open scoped NNReal

/-!

## A. Order units
-/

/-- An element `u` is an order unit when it is nonnegative and every element is bounded above by
a natural multiple of `u`. In an ordered additive group, applying the same condition to `-x`
supplies the corresponding lower bound. -/
def IsOrderUnitElement {E : Type*} [AddCommMonoid E] [PartialOrder E] (u : E) : Prop :=
  0 ≤ u ∧ ∀ x : E, ∃ n : ℕ, x ≤ n • u

/-- An element `u` is an Archimedean order unit when it is an order unit and an element lying
below every positive real multiple of `u` is nonpositive. -/
def IsArchimedeanOrderUnitElement {E : Type*} [AddCommGroup E] [PartialOrder E] [Module ℝ E]
    (u : E) : Prop :=
  IsOrderUnitElement u ∧ ∀ x : E, (∀ ε : ℝ, 0 < ε → x ≤ ε • u) → x ≤ 0

/-- The identity is the biggest outcome around: everything else is bounded by finitely many
copies of it. -/
class IsOrderUnit (E : Type*) [AddCommMonoid E] [PartialOrder E] [One E] : Prop where
  /-- The identity is itself a possible outcome. -/
  one_nonneg : 0 ≤ (1 : E)
  /-- Every outcome is bounded by some finite multiple of the identity. -/
  exists_nsmul_one_le : ∀ x : E, ∃ n : ℕ, x ≤ n • (1 : E)

/-- Same as `IsOrderUnit`, plus: nothing is infinitesimally smaller than `1` without actually
being `≤ 0`. -/
class IsArchimedeanOrderUnit (E : Type*) [AddCommGroup E] [PartialOrder E] [Module ℝ E] [One E] :
    Prop extends IsOrderUnit E where
  /-- If `x` is smaller than every positive multiple of `1`, however small, `x` is already
  `≤ 0`. -/
  le_zero_of_forall_pos_smul_one_le : ∀ x : E,
    (∀ ε : ℝ, 0 < ε → x ≤ ε • (1 : E)) → x ≤ 0

/-- The distinguished unit is an order-unit element whenever `E` carries `IsOrderUnit`. -/
lemma isOrderUnitElement_one {E : Type*} [AddCommMonoid E] [PartialOrder E] [One E]
    [IsOrderUnit E] : IsOrderUnitElement (1 : E) :=
  ⟨IsOrderUnit.one_nonneg, IsOrderUnit.exists_nsmul_one_le⟩

/-- The distinguished unit is an Archimedean order-unit element whenever `E` carries
`IsArchimedeanOrderUnit`. -/
lemma isArchimedeanOrderUnitElement_one {E : Type*} [AddCommGroup E] [PartialOrder E]
    [Module ℝ E] [One E] [IsArchimedeanOrderUnit E] :
    IsArchimedeanOrderUnitElement (1 : E) :=
  ⟨isOrderUnitElement_one, IsArchimedeanOrderUnit.le_zero_of_forall_pos_smul_one_le⟩

namespace IsOrderUnitElement

variable {E : Type*} [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]

/-- Every vector is a difference of two nonnegative vectors when a specified order unit exists. -/
lemma exists_eq_sub_nonneg {u : E} (hu : IsOrderUnitElement u) (x : E) :
    ∃ xp xn : E, 0 ≤ xp ∧ 0 ≤ xn ∧ x = xp - xn := by
  obtain ⟨n, hn⟩ := hu.2 (-x)
  refine ⟨n • u + x, n • u, ?_, nsmul_nonneg hu.1 n, ?_⟩
  · simpa [sub_eq_add_neg] using sub_nonneg.mpr hn
  · abel

end IsOrderUnitElement

namespace IsOrderUnit

variable {E : Type*} [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [One E]
  [IsOrderUnit E]

/-- Every element of an order-unit space is a difference of two nonnegative elements. In cone
language, the positive cone is reproducing. -/
lemma exists_eq_sub_nonneg (x : E) :
    ∃ xp xn : E, 0 ≤ xp ∧ 0 ≤ xn ∧ x = xp - xn :=
  isOrderUnitElement_one.exists_eq_sub_nonneg x

end IsOrderUnit

/-!

## B. The positive cone
-/

/-- The possible measurement outcomes on their own. -/
abbrev PosCone (E : Type*) [AddCommMonoid E] [PartialOrder E] := {x : E // 0 ≤ x}

namespace PosCone

variable {E : Type*}

/-- Two possible outcomes add up to a possible outcome. -/
instance [AddCommMonoid E] [PartialOrder E] [IsOrderedAddMonoid E] :
    AddCommMonoid (PosCone E) :=
  inferInstanceAs (AddCommMonoid {x : E // 0 ≤ x})

variable [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module ℝ E] [PosSMulMono ℝ E]

/-- Scaling a possible outcome by a nonnegative number keeps it a possible outcome and does so
compatibly with addition to make `PosCone E` a `ℝ≥0`-module. -/
instance instModule : Module ℝ≥0 (PosCone E) where
  smul c x := ⟨(c : ℝ) • (x : E), smul_nonneg c.2 x.2⟩
  one_smul _ := Subtype.ext (one_smul ℝ _)
  mul_smul c d _ := Subtype.ext (mul_smul (c : ℝ) (d : ℝ) _)
  smul_zero _ := Subtype.ext (smul_zero _)
  smul_add c _ _ := Subtype.ext (smul_add (c : ℝ) _ _)
  add_smul c d _ := Subtype.ext (by push_cast; exact add_smul (c : ℝ) (d : ℝ) _)
  zero_smul _ := Subtype.ext (by push_cast; exact zero_smul ℝ _)

@[simp, norm_cast]
lemma coe_smul (c : ℝ≥0) (x : PosCone E) : ((c • x : PosCone E) : E) = (c : ℝ) • (x : E) := rfl

@[simp]
lemma mk_smul (c : ℝ≥0) {x : E} (hx : 0 ≤ x) :
    c • (⟨x, hx⟩ : PosCone E) = ⟨(c : ℝ) • x, smul_nonneg c.2 hx⟩ := rfl

end PosCone
