/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.Channel.Basic

/-!
# States

## i. Overview

A state assigns each observable its expectation value: a positive linear functional
(`0 ≤ A ⟹ 0 ≤ ω A`), normalized so the certain outcome reads `ω 1 = 1`. In quantum mechanics,
`ω A = tr(ρA)` for a density matrix `ρ`.

## ii. Key results

- `𝓢[𝕜, A]` : states on an ordered `𝕜`-vector space with a distinguished unit.

## iii. Table of contents

- A. Notation for positive functionals and states

-/

@[expose] public section

/-!

## A. Notation for positive functionals and states

-/

/-- Positive linear functionals on an ordered `𝕜`-vector space. -/
notation " 𝓟[" 𝕜 ", " A "] " => A →ₚ[𝕜] 𝕜

/-- States on an ordered `𝕜`-vector space with a distinguished unit. -/
notation " 𝓢[" 𝕜 ", " A "] " => A →ₚ₁[𝕜] 𝕜
