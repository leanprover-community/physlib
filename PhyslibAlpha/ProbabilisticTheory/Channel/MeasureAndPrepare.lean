/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Classical.FiniteSystem
public import PhyslibAlpha.ProbabilisticTheory.Channel.Basic

/-!

# Measure-and-prepare channels

## i. Overview

A channel `Channel E₂ E₁` (the Heisenberg picture of a Schrödinger channel `E₁ → E₂`) is
measure-and-prepare when it factors through a finite classical system: measure the input, then
prepare a (possibly different) output state for each outcome. Dually, this is exactly
`Φ = M.comp P` for a measurement `M : Channel (ι → ℝ) E₁` and
a "preparation" `P : Channel E₂ (FiniteClassicalSystem ι)` — itself a channel into the classical
system, so a family of states on `E₂` indexed by `ι`, bundled the same way `Measurement` bundles a
family of effects.

This is the abstract, order-unit-level version of an entanglement-breaking channel. Quantifying
over the finite outcome type avoids hard-coding a particular classical system.

## ii. Key definitions

- `UnitalPositiveLinearMap.IsMeasureAndPrepare`

## iii. Table of contents

- A. Factorization through a finite classical system

-/

@[expose] public section

namespace ProbabilisticTheory

variable {E₁ E₂ : Type*} [OrderUnitSpace E₁] [OrderUnitSpace E₂]

namespace UnitalPositiveLinearMap

/-! ## A. Factorization through a finite classical system -/

/-- A channel is measure-and-prepare when it factors through a finite classical system: measure,
then prepare a state for each outcome. This is the general-probabilistic-theory abstraction of an
entanglement-breaking channel. -/
def IsMeasureAndPrepare (Φ : Channel E₂ E₁) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (M : Channel (FiniteClassicalSystem ι) E₁)
    (P : Channel E₂ (FiniteClassicalSystem ι)), Φ = M.comp P

end UnitalPositiveLinearMap

end ProbabilisticTheory
