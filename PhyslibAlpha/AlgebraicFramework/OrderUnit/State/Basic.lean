/-
Copyright (c) 2026 David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross
-/
module

public import PhyslibAlpha.AlgebraicFramework.OrderUnit.Channel.Basic

/-!

# States

## i. Overview

A state is a normalized positive linear functional: an element of `𝓟[𝕜, A]`, the positive linear
functionals on `A`, that sends the unit to `1`. `𝓢[𝕜, A]` is just `A →ₚ₁[𝕜] 𝕜` — the state space
is a special case of the channel type, with the target system the base field itself.

## ii. Key definitions

- `𝓟[𝕜, A]` is the type of positive linear functionals on an ordered `𝕜`-vector space.
- `𝓢[𝕜, A]` is the state space of an ordered `𝕜`-vector space with unit.

## iii. Table of contents

- A. Positive functionals and states

-/

@[expose] public section

/-! ## A. Positive functionals and states -/

/-- Positive linear functionals on an ordered `𝕜`-vector space. -/
notation " 𝓟[" 𝕜 ", " A "] " => A →ₚ[𝕜] 𝕜

/-- Positive linear functionals on an ordered complex vector space. -/
notation " 𝓟[" A "] " => A →ₚ[ℂ] ℂ

/-- State space of an ordered `𝕜`-vector space with unit. -/
notation " 𝓢[" 𝕜 ", " A "] " => A →ₚ₁[𝕜] 𝕜

/-- State space of an ordered complex vector space with unit. -/
notation " 𝓢[" A "] " => A →ₚ₁[ℂ] ℂ
