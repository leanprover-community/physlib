/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Logic.Function.Basic

/-!

# One-parameter groups acting on a bare carrier

## i. Overview

The most primitive notion of time evolution is a group action `α : G → E → E`. This file
specializes only the group to `G = (ℝ, +)` — nothing about *what `α` preserves* (linearity, order,
a Jordan product, a `⋆`-structure, ...) and nothing about *continuity* belongs here. Those are
independent axes:

- structure preservation is a predicate about `α t` for each fixed `t` (see e.g.
  `Algebra/Derivation.lean`'s companion notion for the infinitesimal picture, or state directly
  `∀ t a b, α t (a * b) = α t a * α t b` at the point of use — no dedicated class is introduced here
  since the right notion of "automorphism" depends on which structure `E` carries);
- continuity, and the existence of a generator, is `Dynamics/Generator.lean`, requiring a topology
  `E` need not have at all to be a one-parameter group in the sense below.

This mirrors the point that an Archimedean order-unit space's topology (`OrderUnit/Norm.lean`) is
not "AOU has dynamics" — it only supplies enough structure that a generic dynamical construction
can later be instantiated there. Likewise here: `E` need not be an order-unit space, a Jordan
algebra, or carry any topology for `IsOneParameterGroup` to be meaningful.

## ii. Key definitions and results

- `IsOneParameterGroup`

## iii. Table of contents

- A. The group law

-/

@[expose] public section

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
theorem left_inv (t : ℝ) (a : E) : α (-t) (α t a) = a := by
  have := h.map_add (-t) t a
  simpa [h.map_zero] using this.symm

theorem right_inv (t : ℝ) (a : E) : α t (α (-t) a) = a := by
  have := h.map_add t (-t) a
  simpa [h.map_zero] using this.symm

theorem bijective (t : ℝ) : Function.Bijective (α t) :=
  Function.bijective_iff_has_inverse.mpr ⟨α (-t), h.left_inv t, h.right_inv t⟩

end IsOneParameterGroup
