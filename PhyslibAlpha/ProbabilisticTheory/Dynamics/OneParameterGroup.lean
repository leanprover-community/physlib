/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Logic.Function.Basic

/-!

# One-parameter groups

Defines one-parameter groups `α : ℝ → E → E` satisfying `α 0 = id` and the group law.

## i. Overview

A one-parameter group is a family `α : ℝ → E → E` with `α 0 = id` and `α (s + t) = α s ∘ α t`. It is
stated for an arbitrary type `E`; preservation of structure and continuity are separate conditions.

## ii. Key results

- `IsOneParameterGroup` : one-parameter groups.

## iii. Table of contents

- A. The group law

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory

/-! ## A. The group law -/

/-- `α : ℝ → E → E` is a one-parameter group of (not-yet-specified-as-anything) transformations of
`E`: `α 0 = id` and `α (s + t) = α s ∘ α t`. Nothing about linearity, order, a product, or
continuity is assumed — those are independent, composable hypotheses to add at the point of use. -/
structure IsOneParameterGroup {E : Type*} (α : ℝ → E → E) : Prop where
  /-- Evolving for zero time does nothing. -/
  map_zero : ∀ a : E, α 0 a = a
  /-- Evolving for `s` then `t` is the same as evolving for `s + t`. -/
  map_add : ∀ s t a, α (s + t) a = α s (α t a)

namespace IsOneParameterGroup

variable {E : Type*} {α : ℝ → E → E} (h : IsOneParameterGroup α)
include h

/-- Every time-`t` map has a two-sided inverse, `α (-t)`: an immediate consequence of the group
law, recorded once here rather than re-derived at each point of use. -/
lemma left_inv (t : ℝ) (a : E) : α (-t) (α t a) = a := by
  have := h.map_add (-t) t a
  simpa [h.map_zero] using this.symm

lemma right_inv (t : ℝ) (a : E) : α t (α (-t) a) = a := by
  have := h.map_add t (-t) a
  simpa [h.map_zero] using this.symm

lemma bijective (t : ℝ) : Function.Bijective (α t) :=
  Function.bijective_iff_has_inverse.mpr ⟨α (-t), h.left_inv t, h.right_inv t⟩

end IsOneParameterGroup

end ProbabilisticTheory
