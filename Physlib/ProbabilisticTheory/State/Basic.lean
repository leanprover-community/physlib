/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.Channel.Basic
public import Physlib.ProbabilisticTheory.OrderUnit.Basic

/-!
# States

## i. Overview

A state assigns each observable its expectation value: a positive linear functional
(`0 ≤ A ⟹ 0 ≤ ω A`), normalized so the certain outcome reads `ω 1 = 1`. In quantum mechanics,
`ω A = tr(ρA)` for a density matrix `ρ`.

## ii. Key results

- `𝓢[𝕜, A]` : states on an ordered `𝕜`-vector space with a distinguished unit.
- `UnitalPositiveLinearMap.comap` : the state on the input of a channel that evaluates an
  observable by first sending it through the channel.

## iii. Table of contents

- A. Notation for positive functionals and states
- B. Transporting states along channels

## iv. References

-/

@[expose] public section

/-!

## A. Notation for positive functionals and states

-/

/-- Positive linear functionals on an ordered `𝕜`-vector space. -/
notation " 𝓟[" 𝕜 ", " A "] " => A →ₚ[𝕜] 𝕜

/-- States on an ordered `𝕜`-vector space with a distinguished unit. -/
notation " 𝓢[" 𝕜 ", " A "] " => A →ₚ₁[𝕜] 𝕜

/-!

## B. Transporting states along channels

-/

open ProbabilisticTheory

namespace UnitalPositiveLinearMap

variable {E F : Type*} [OrderUnitSpace E] [OrderUnitSpace F]

/-- The state on `E` that evaluates an observable by first sending it through a channel `f` and
then evaluating the state `ω` on the result. -/
def comap (f : E →ₚ₁[ℝ] F) (ω : 𝓢[ℝ, F]) : 𝓢[ℝ, E] where
  toPositiveLinearMap := ω.toPositiveLinearMap.comp f.toPositiveLinearMap
  map_one' := (congrArg ω f.map_one').trans ω.map_one'

@[simp]
lemma comap_apply (f : E →ₚ₁[ℝ] F) (ω : 𝓢[ℝ, F]) (x : E) : comap f ω x = ω (f x) := rfl

end UnitalPositiveLinearMap
