/-
Copyright (c) 2026 David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross
-/
module

public import PhyslibAlpha.AlgebraicFramework.StarAlgebra.Restrict
public import PhyslibAlpha.AlgebraicFramework.OrderUnit.State.Basic
public import Mathlib

/-!

# Vector states

Vector states on spaces of continuous linear endomorphisms.

-/

@[expose] public section

open ComplexOrder ContinuousLinearMap
open scoped InnerProductSpace

section ofVec

variable {H 𝕜 : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The vector functional associated with `ψ`. -/
@[simps apply]
def PositiveLinearMap.ofVec (ψ : H) : 𝓟[𝕜, H →L[𝕜] H] where
  toFun x := ⟪ψ, x • ψ⟫_𝕜
  map_add' x y := by simp [inner_add_right]
  map_smul' x y := by simp [inner_smul_right]
  monotone' x y hxy := by
    simpa [inner_sub_right] using ((le_def x y).mp hxy).inner_nonneg_right ψ

/-- The vector state associated with a unit vector. -/
@[simps! apply]
def UnitalPositiveLinearMap.ofVec {ψ : H} (h : ‖ψ‖ = 1) : 𝓢[𝕜, H →L[𝕜] H] :=
  { PositiveLinearMap.ofVec ψ with map_one' := by simp [h] }

end ofVec

section Example

open UnitalPositiveLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

example (ψ : H) (h : ‖ψ‖ = 1) :
    (ofVec h).restrictSAC (1 : selfAdjoint (H →L[ℂ] H)) = (1 : ℝ) := by
  simp

end Example
