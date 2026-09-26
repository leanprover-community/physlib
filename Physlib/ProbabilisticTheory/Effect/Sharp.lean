/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.Convex.Strict.Extreme
public import Physlib.ProbabilisticTheory.Effect.Complement

/-!
# Sharp effects

## i. Overview

The effect interval `[0, 1]` is convex. A sharp effect is an extreme point of it: one that cannot
be written as a nontrivial mixture of two distinct effects. Sharp effects generalize projections.

## ii. Key results

- `Effect.IsSharp` : an effect that cannot be written as a nontrivial mixture of two distinct
  effects.
- `Effect.isSharp_complement_iff` : sharpness is preserved by taking the complement.

## iii. Table of contents

- A. Sharp effects

-/

@[expose] public section

namespace Effect

variable {E : Type*} [OrderUnitSpace E]

/-!

## A. Sharp effects

-/

/-- An effect is sharp when it is an extreme point of the effect interval: it cannot be written as
a nontrivial mixture of two distinct effects. -/
def IsSharp (e : Effect E) : Prop := (e : E) ∈ Set.extremePoints ℝ (Effect E : Set E)

/-- The impossible outcome 0 is sharp. -/
lemma isSharp_zero : IsSharp (0 : Effect E) := by
  refine ⟨(0 : Effect E).2, fun x₁ hx₁ x₂ hx₂ ⟨a, b, ha, hb, _, hz⟩ => ?_⟩
  have hax := (add_eq_zero_iff_of_nonneg (smul_nonneg ha.le hx₁.1)
    (smul_nonneg hb.le hx₂.1)).mp (by simpa using hz) |>.1
  exact (smul_eq_zero.mp hax).resolve_left ha.ne'

/-- Sharpness is preserved by taking the complement:
`e ↦ 1 - e` is an affine involution of the effect interval. -/
lemma isSharp_complement {e : Effect E} (h : IsSharp e) : IsSharp (complement e) := by
  refine ⟨(complement e).2, fun x₁ hx₁ x₂ hx₂ ⟨a, b, ha, hb, hab, hz⟩ => ?_⟩
  have key : a • (1 - x₁) + b • (1 - x₂) = (e : E) := by
    rw [show a • (1 - x₁) + b • (1 - x₂) = (a • (1 : E) + b • (1 : E)) - (a • x₁ + b • x₂) from
      by module, ← add_smul, hab, one_smul, hz]
    show (1 : E) - (1 - (e : E)) = (e : E)
    abel
  have x1eq := (mem_extremePoints_iff_left.mp h).2 (1 - x₁)
    ⟨sub_nonneg.mpr hx₁.2, sub_le_self 1 hx₁.1⟩ (1 - x₂)
    ⟨sub_nonneg.mpr hx₂.2, sub_le_self 1 hx₂.1⟩ ⟨a, b, ha, hb, hab, key⟩
  exact eq_sub_of_add_eq (by rw [← x1eq]; abel)

/-- Sharpness is preserved by taking the complement, in either direction. -/
lemma isSharp_complement_iff {e : Effect E} : IsSharp (complement e) ↔ IsSharp e :=
  ⟨fun h => complement_complement e ▸ isSharp_complement h, isSharp_complement⟩

/-- The certain outcome 1 is sharp. -/
lemma isSharp_one : IsSharp (1 : Effect E) :=
  complement_zero (E := E) ▸ isSharp_complement isSharp_zero

end Effect
