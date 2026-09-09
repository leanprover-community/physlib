/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Data.ENNReal.Action
public import PhyslibAlpha.AlgebraicFramework.OrderUnit.Basic

/-!

# Weights

## i. Overview

A weight is a statistical weight: a number in `[0, ∞]` on each outcome saying how much of it
there is, with no requirement that the total be finite or normalized to 1 — hence the `∞` and
the fact that weights are compared, never subtracted. They live on `PosCone E`, the space of
possible outcomes from `OrderUnit/Basic.lean`.

Being an honest linear map, `Weight E` is automatically an `ℝ≥0`-module in its own right: combining
two weights with nonnegative coefficients is again a weight, for free, with no boundedness proof to
give (contrast `Effect`, a bounded slice of `E` that needs `Effect.convex` to stay closed under
mixing). `Weight.IsState.mix` is the one thing that *does* need proving: that this combination
preserves normalization when the coefficients sum to `1`.

## ii. Key definitions and results

- `Weight E`
- `Weight.IsFaithful`, `Weight.IsFinite`, `Weight.IsSemifinite`, `Weight.IsNormal` : the standard
  refinements.
- `Weight.IsState` : a finite weight normalized at the order unit — an actual state.
- `Weight.mix`, `Weight.IsState.mix` : mixing two (state) weights.

## iii. Table of contents

- A. Weights on the positive cone
- B. Standard properties of weights
- C. Mixtures
- D. State weights

-/

@[expose] public section

open scoped ENNReal NNReal

variable {E : Type*} [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]
  [Module ℝ E] [PosSMulMono ℝ E]

/-- The weight of each possible outcome, valued in `[0, ∞]`. -/
abbrev Weight (E : Type*) [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]
    [Module ℝ E] [PosSMulMono ℝ E] := PosCone E →ₗ[ℝ≥0] ℝ≥0∞

namespace Weight

/-! ## A. Weights on the positive cone -/

@[ext]
lemma ext {w₁ w₂ : Weight E} (h : ∀ x, w₁ x = w₂ x) : w₁ = w₂ :=
  LinearMap.ext h

@[simp]
lemma map_zero (w : Weight E) : w 0 = 0 := _root_.map_zero w

@[simp]
lemma map_add (w : Weight E) (x y : PosCone E) : w (x + y) = w x + w y := _root_.map_add w x y

/-- A bigger outcome never gets less weight. -/
lemma mono (w : Weight E) : Monotone (w : PosCone E → ℝ≥0∞) := by
  intro x y hxy
  have hz : (0 : E) ≤ (y : E) - (x : E) := sub_nonneg.mpr hxy
  set z : PosCone E := ⟨(y : E) - (x : E), hz⟩
  have hxz : x + z = y := by
    ext
    show (x : E) + ((y : E) - (x : E)) = (y : E)
    abel
  calc w x ≤ w x + w z := le_self_add
    _ = w (x + z) := (map_add w x z).symm
    _ = w y := by rw [hxz]

/-! ## B. Standard properties of weights -/

/-- Only the impossible outcome carries no weight at all. -/
def IsFaithful (w : Weight E) : Prop := ∀ x : PosCone E, w x = 0 → x = 0

/-- The weight never blows up to `∞`. -/
def IsFinite (w : Weight E) : Prop := ∀ x : PosCone E, w x ≠ ⊤

/-- Every outcome, however large, contains some piece of finite weight. -/
def IsSemifinite (w : Weight E) : Prop :=
  ∀ x : PosCone E, x ≠ 0 → ∃ y : PosCone E, y ≠ 0 ∧ (y : E) ≤ x ∧ w y ≠ ⊤

/-- The weight of a limit of outcomes is the limit of their weights: it doesn't jump when you
take a supremum. -/
def IsNormal (w : Weight E) : Prop :=
  ∀ (D : Set (PosCone E)) (x : PosCone E), D.Nonempty → DirectedOn (· ≤ ·) D → IsLUB D x →
    IsLUB (w '' D) (w x)

/-! ## C. Mixtures -/

/-- Mixing two weights with `ℝ≥0` coefficients: already a weight, for free, since `Weight E` is
itself an `ℝ≥0`-module. -/
noncomputable def mix (w₁ w₂ : Weight E) (a b : ℝ≥0) : Weight E := a • w₁ + b • w₂

@[simp]
lemma mix_apply (w₁ w₂ : Weight E) (a b : ℝ≥0) (x : PosCone E) :
    mix w₁ w₂ a b x = a • w₁ x + b • w₂ x := rfl

variable [One E] [IsOrderUnit E]

/-! ## D. State weights -/

/-- The certain outcome, as a point of the cone. -/
def unit : PosCone E := ⟨1, IsOrderUnit.one_nonneg⟩

/-- A weight that's finite everywhere and gives the certain outcome weight exactly `1`: an actual
(normalized) state. -/
structure IsState (w : Weight E) : Prop where
  /-- A state is finite everywhere. -/
  finite : w.IsFinite
  /-- A state gives the certain outcome weight exactly `1`. -/
  normalized : w unit = 1

/-- Mixing two states with coefficients summing to `1` gives another state: the mixture stays
finite (a nonnegative combination of finite weights is finite) and stays normalized (the
coefficients summing to `1` exactly cancels the normalization of each). -/
lemma IsState.mix {w₁ w₂ : Weight E} (hw₁ : w₁.IsState) (hw₂ : w₂.IsState) {a b : ℝ≥0}
    (hab : a + b = 1) : (Weight.mix w₁ w₂ a b).IsState where
  finite x := by
    show a • w₁ x + b • w₂ x ≠ ⊤
    simp [ENNReal.smul_def, ENNReal.mul_eq_top, hw₁.finite x, hw₂.finite x]
  normalized := by
    show a • w₁ unit + b • w₂ unit = 1
    rw [hw₁.normalized, hw₂.normalized]
    simp [ENNReal.smul_def, ← ENNReal.coe_add, hab]

end Weight
