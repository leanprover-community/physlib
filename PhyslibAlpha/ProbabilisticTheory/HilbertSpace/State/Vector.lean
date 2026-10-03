/-
Copyright (c) 2026 David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross
-/
module

public import PhyslibAlpha.ProbabilisticTheory.StarAlgebra.Restrict
public import PhyslibAlpha.ProbabilisticTheory.State.Basic
public import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!

# Vector states

A unit vector `ψ` defines the vector state `x ↦ ⟪ψ, x ψ⟫` on the bounded operators.

## i. Overview

A unit vector `ψ` defines the vector state `x ↦ ⟪ψ, x ψ⟫` on the bounded operators.

## ii. Key results

- `PositiveLinearMap.ofVec` : the positive functional of a vector.
- `UnitalPositiveLinearMap.ofVec` : the vector state of a unit vector.

## iii. Table of contents

- A. Vector states
- B. Example

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory

open ComplexOrder ContinuousLinearMap
open scoped InnerProductSpace

/-!

## A. Vector states

-/

section ofVec

variable {H 𝕜 : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The vector functional associated with `ψ`. -/
@[simps apply]
def _root_.PositiveLinearMap.ofVec (ψ : H) : 𝓟[𝕜, H →L[𝕜] H] where
  toFun x := ⟪ψ, x • ψ⟫_𝕜
  map_add' x y := by simp [inner_add_right]
  map_smul' x y := by simp [inner_smul_right]
  monotone' x y hxy := by
    simpa [inner_sub_right] using (ContinuousLinearMap.le_def.mp hxy).inner_nonneg_right ψ

/-- The vector state associated with a unit vector. -/
def UnitalPositiveLinearMap.ofVec {ψ : H} (h : ‖ψ‖ = 1) : 𝓢[𝕜, H →L[𝕜] H] :=
  { PositiveLinearMap.ofVec ψ with map_one' := by simp [h] }

/-- Evaluation of a vector state is the corresponding quadratic form. -/
@[simp]
lemma UnitalPositiveLinearMap.ofVec_apply {ψ : H} (h : ‖ψ‖ = 1) (x : H →L[𝕜] H) :
    UnitalPositiveLinearMap.ofVec h x = ⟪ψ, x • ψ⟫_𝕜 := rfl

end ofVec

/-!

## B. Example

-/

section Example

open UnitalPositiveLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

example (ψ : H) (h : ‖ψ‖ = 1) :
    (ofVec h).restrictSAC (1 : selfAdjoint (H →L[ℂ] H)) = (1 : ℝ) := by
  simp

end Example

end ProbabilisticTheory
