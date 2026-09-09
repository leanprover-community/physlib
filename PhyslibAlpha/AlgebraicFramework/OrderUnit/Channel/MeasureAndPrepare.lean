/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.Measurement.ClassicalSystem
public import PhyslibAlpha.AlgebraicFramework.OrderUnit.Channel.Basic

/-!

# Measure-and-prepare channels

## i. Overview

A channel `E₂ →ₚ₁[ℝ] E₁` (the Heisenberg picture of a Schrödinger channel `E₁ → E₂`) is
measure-and-prepare when it factors through a finite classical system: measure the input, then
prepare a (possibly different) output state for each outcome. Dually, this is exactly
`Φ = M.comp P` for a measurement `M : (ι → ℝ) →ₚ₁[ℝ] E₁` (`Measurement/ClassicalSystem.lean`) and
a "preparation" `P : E₂ →ₚ₁[ℝ] (ι → ℝ)` — itself a channel into the classical system, so a family
of states on `E₂` indexed by `ι`, bundled the same way `Measurement` bundles a family of effects.

This is the abstract, order-unit-level version of an entanglement-breaking channel: the
factorization definition extends to any outcome type (not just finite ones) with no change, unlike
a hard-coded sum over a fixed outcome set.

## ii. Key definitions

- `UnitalPositiveLinearMap.IsMeasureAndPrepare`

## iii. Table of contents

- A. Factorization through a finite classical system

-/

@[expose] public section

variable {E₁ E₂ : Type*}
  [AddCommGroup E₁] [PartialOrder E₁] [IsOrderedAddMonoid E₁] [Module ℝ E₁] [PosSMulMono ℝ E₁]
  [One E₁]
  [AddCommGroup E₂] [PartialOrder E₂] [IsOrderedAddMonoid E₂] [Module ℝ E₂] [PosSMulMono ℝ E₂]
  [One E₂]

namespace UnitalPositiveLinearMap

/-! ## A. Factorization through a finite classical system -/

/-- A channel is measure-and-prepare when it factors through a finite classical system: measure,
then prepare a state for each outcome. This is the general-probabilistic-theory abstraction of an
entanglement-breaking channel. -/
def IsMeasureAndPrepare (Φ : E₂ →ₚ₁[ℝ] E₁) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (M : (ι → ℝ) →ₚ₁[ℝ] E₁) (P : E₂ →ₚ₁[ℝ] (ι → ℝ)), Φ = M.comp P

end UnitalPositiveLinearMap
