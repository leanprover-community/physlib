/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Dynamics.OneParameterGroup
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!

# Generators of one-parameter groups

The generator of a one-parameter family on a normed space, and its uniqueness.

## i. Overview

The generator of a one-parameter family `α` on a normed space is `D a = lim_{t → 0} (α t a - a) /
t`, stated with `HasDerivAt`. It needs a topology but no algebraic structure, and it is unique when
it exists.

## ii. Key results

- `IsGenerator` : `D` generates `α`.
- `IsGenerator.unique` : the generator is unique.

## iii. Table of contents

- A. The generator

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## A. The generator -/

/-- `D` is the infinitesimal generator, at `t = 0`, of the one-parameter family `α`: for every `a`,
`t ↦ α t a` is differentiable at `0` with derivative `D a`. No algebraic structure on `E` (product,
order, `⋆`) is assumed — this is purely about the curve `t ↦ α t a` in a normed space. -/
def IsGenerator (α : ℝ → E → E) (D : E → E) : Prop :=
  ∀ a : E, HasDerivAt (fun t => α t a) (D a) 0

/-- The generator of a one-parameter family, if it exists, is unique — immediate from uniqueness of
derivatives (`HasDerivAt.unique`). -/
lemma IsGenerator.unique {α : ℝ → E → E} {D₁ D₂ : E → E} (h₁ : IsGenerator α D₁)
    (h₂ : IsGenerator α D₂) : D₁ = D₂ :=
  funext fun a => (h₁ a).unique (h₂ a)

end ProbabilisticTheory
