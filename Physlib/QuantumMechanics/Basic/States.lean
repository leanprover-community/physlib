/-
Copyright (c) 2026 David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross
-/
module

public import Physlib.QuantumMechanics.Basic.PositiveLinearMap.Restrict
public import Physlib.QuantumMechanics.Basic.PositiveLinearMap.Trace

/-!

# States

Some definitions on states.

This file is a stub.

-/

@[expose] public section

section Notation

/-- Positive linear functionals on an ordered `𝕜`-vector space -/
notation " 𝓟[" 𝕜 ", " A "] " => A →ₚ[𝕜] 𝕜

/-- Positive linear functionals on an ordered complex vector space -/
notation " 𝓟[" A "] " => A →ₚ[ℂ] ℂ

/-- State space of an ordered `𝕜`-vector space with unit -/
notation " 𝓢[" 𝕜 ", " A "] " => A →ₚ₁[𝕜] 𝕜

/-- State space of an ordered complex vector space with unit -/
notation " 𝓢[" A "] " => A →ₚ₁[ℂ] ℂ

end Notation

open ComplexOrder ContinuousLinearMap
open scoped InnerProductSpace

section ofVec

variable {H 𝕜 : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

@[simps apply]
def PositiveLinearMap.ofVec (ψ : H) : 𝓟[𝕜, H →L[𝕜] H] where
  toFun x := ⟪ψ, x • ψ⟫_𝕜
  map_add' x y := by simp [inner_add_right]
  map_smul' x y := by simp [inner_smul_right]
  monotone' x y hxy := by
    simpa [inner_sub_right] using ((le_def x y).mp hxy).inner_nonneg_right ψ

@[simps! apply]
def UnitalPositiveLinearMap.ofVec {ψ : H} (h : ‖ψ‖ = 1) : 𝓢[𝕜, H →L[𝕜] H] :=
  { PositiveLinearMap.ofVec ψ with map_one' := by simp [h] }

end ofVec

section ofDensity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace UnitalPositiveLinearMap

variable {ρ : H →L[ℂ] H} (hpos : 0 ≤ ρ) (hnorm : (ρ : H →ₗ[ℂ] H).trace ℂ H = 1)

/-- A trace-one positive linear map defines a state -/
noncomputable def ofDensity : 𝓢[H →L[ℂ] H] :=
  { ρ.traceMulOpₚ with map_one' := by simp_all }

@[simp]
theorem ofDensity_apply {ρ : H →L[ℂ] H} (hpos : 0 ≤ ρ)
    (hnorm : (ρ : H →ₗ[ℂ] H).trace ℂ H = 1) (x : H →L[ℂ] H) :
    ofDensity hpos hnorm x = (↑x * ↑ρ : H →ₗ[ℂ] H).trace ℂ H :=
  ρ.traceMulOpₚ_apply_of_nonneg hpos x

example {ρ : H →L[ℂ] H} (hpos : 0 ≤ ρ) (hnorm : (ρ : H →ₗ[ℂ] H).trace ℂ H = 1) :
    ofDensity hpos hnorm 1 = 1 :=
  map_one _

end ofDensity.UnitalPositiveLinearMap

section Example

open UnitalPositiveLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The restriction of a state to self-adjoint elements, giving real-valued results -/
example (ψ : H) (h : ‖ψ‖ = 1) :
    (ofVec h).restrictSAC (1 : selfAdjoint (H →L[ℂ] H)) = (1 : ℝ) := by
  simp

end Example
