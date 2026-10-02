/-
Copyright (c) 2026 David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross
-/
module

public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Trace
public import PhyslibAlpha.ProbabilisticTheory.State.Basic

/-!

# Density operators

## i. Overview

A positive operator `ρ` with trace `1` defines the state `x ↦ Tr (x ρ)`. The trace here is the
linear-algebra trace, so this applies to finite-dimensional Hilbert spaces.

## ii. Key results

- `UnitalPositiveLinearMap.ofDensity` : the state of a density operator.

-/

@[expose] public section

namespace ProbabilisticTheory

open ComplexOrder ContinuousLinearMap

namespace UnitalPositiveLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ρ : H →L[ℂ] H} (hpos : 0 ≤ ρ) (hnorm : (ρ : H →ₗ[ℂ] H).trace ℂ H = 1)

/-- A trace-one positive continuous linear map defines a state. -/
noncomputable def ofDensity : 𝓢[ℂ, H →L[ℂ] H] :=
  { ρ.traceMulOpₚ with map_one' := by simp_all }

@[simp]
lemma ofDensity_apply {ρ : H →L[ℂ] H} (hpos : 0 ≤ ρ)
    (hnorm : (ρ : H →ₗ[ℂ] H).trace ℂ H = 1) (x : H →L[ℂ] H) :
    ofDensity hpos hnorm x = (↑x * ↑ρ : H →ₗ[ℂ] H).trace ℂ H :=
  ρ.traceMulOpₚ_apply_of_nonneg hpos x

end UnitalPositiveLinearMap

end ProbabilisticTheory
