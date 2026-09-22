/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.Dynamics.OneParameterGroup
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!

# The infinitesimal generator of a one-parameter group

## i. Overview

A generator is analytic/dynamical, not algebraic: `D a := lim_{t→0} (α_t(a) - a)/t`, requiring a
topology on `E` (here, a normed real vector space — enough to make sense of the limit) but *not*
requiring `E` to carry any multiplication, order, or star structure at all. This is the deliberate
converse emphasis of `Algebra/Derivation.lean`: derivation is pure algebra with no analysis;
generator is pure analysis with no algebra. `GeneratorIsDerivation.lean` is the bridge connecting
the two, once `E` happens to also carry a compatible multiplication.

`IsGenerator` is phrased via `HasDerivAt` rather than `deriv` directly, which keeps every
downstream theorem a clean implication (`differentiable ⇒ conclusion`) instead of needing to first
discharge a `DifferentiableAt` side goal to unfold `deriv`.

## ii. Key definitions and results

- `IsGenerator`
- `IsGenerator.unique` : the generator, if it exists, is unique (immediate from uniqueness of
  derivatives)

## iii. Table of contents

- A. The generator

-/

@[expose] public section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## A. The generator -/

/-- `D` is the infinitesimal generator, at `t = 0`, of the one-parameter family `α`: for every `a`,
`t ↦ α t a` is differentiable at `0` with derivative `D a`. No algebraic structure on `E` (product,
order, `⋆`) is assumed — this is purely about the curve `t ↦ α t a` in a normed space. -/
def IsGenerator (α : ℝ → E → E) (D : E → E) : Prop :=
  ∀ a : E, HasDerivAt (fun t => α t a) (D a) 0

/-- The generator of a one-parameter family, if it exists, is unique — immediate from uniqueness of
derivatives (`HasDerivAt.unique`). -/
theorem IsGenerator.unique {α : ℝ → E → E} {D₁ D₂ : E → E} (h₁ : IsGenerator α D₁)
    (h₂ : IsGenerator α D₂) : D₁ = D₂ :=
  funext fun a => (h₁ a).unique (h₂ a)
