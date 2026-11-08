/-
Copyright (c) 2026 David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross
-/
module

public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# Vector functionals

A vector gives a positive expectation functional before normalisation.

## i. Overview

The functional `A ↦ ⟪ψ, A ψ⟫` is positive. A unit vector makes it unital. This construction
works over any `RCLike` field and does not require completeness.

## ii. Key results

- `PositiveLinearMap.ofVec` : the positive vector functional.

## iii. Table of contents

- A. Vector functionals

## iv. References
-/

@[expose] public section

open ComplexOrder
open scoped InnerProductSpace

/-!
## A. Vector functionals
-/

namespace PositiveLinearMap

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The positive vector functional before normalising its vector. -/
@[simps apply]
def ofVec (ψ : H) : (H →L[𝕜] H) →ₚ[𝕜] 𝕜 where
  toFun x := ⟪ψ, x ψ⟫_𝕜
  map_add' x y := by simp [inner_add_right]
  map_smul' c x := by simp [inner_smul_right]
  monotone' x y hxy := by
    simpa [inner_sub_right] using (ContinuousLinearMap.le_def.mp hxy).inner_nonneg_right ψ

end PositiveLinearMap
