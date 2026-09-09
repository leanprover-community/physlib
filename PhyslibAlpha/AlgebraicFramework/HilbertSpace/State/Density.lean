/-
Copyright (c) 2026 David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Trace
public import PhyslibAlpha.AlgebraicFramework.OrderUnit.State.Basic

/-!

# Density-operator states

Construction of states from positive trace-one continuous linear endomorphisms.

-/

@[expose] public section

open ComplexOrder ContinuousLinearMap

namespace UnitalPositiveLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ρ : H →L[ℂ] H} (hpos : 0 ≤ ρ) (hnorm : (ρ : H →ₗ[ℂ] H).trace ℂ H = 1)

/-- A trace-one positive continuous linear map defines a state. -/
noncomputable def ofDensity : 𝓢[H →L[ℂ] H] :=
  { ρ.traceMulOpₚ with map_one' := by simp_all }

@[simp]
lemma ofDensity_apply {ρ : H →L[ℂ] H} (hpos : 0 ≤ ρ)
    (hnorm : (ρ : H →ₗ[ℂ] H).trace ℂ H = 1) (x : H →L[ℂ] H) :
    ofDensity hpos hnorm x = (↑x * ↑ρ : H →ₗ[ℂ] H).trace ℂ H :=
  ρ.traceMulOpₚ_apply_of_nonneg hpos x

end UnitalPositiveLinearMap
