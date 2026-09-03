/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The trace of a continuous endomorphism as a continuous linear functional

On a finite-dimensional normed space `V` over a complete nontrivially normed field `𝕜`, the trace
`T ↦ trace T` of a continuous endomorphism is itself a continuous linear functional
`TauCeti.traceCLM 𝕜 V : (V →L[𝕜] V) →L[𝕜] 𝕜`. Continuity is not something the algebraic
`LinearMap.trace` can see: it holds because `V →L[𝕜] V` is finite-dimensional over the complete
field `𝕜`, and every linear map out of such a space is continuous.

This bundled form is what lets the trace pass through the continuity of a representation
(`TauCeti/RepresentationTheory/Continuous/Character.lean`) and commute with a Bochner integral
(`TauCeti/RepresentationTheory/Compact/Intertwiner/Basic.lean`); both need the trace as a continuous
linear map rather than as a bare linear map.
-/

public section

namespace TauCeti

variable (𝕜 V : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]

/-- The trace of a continuous endomorphism of a finite-dimensional space, as a continuous linear
functional. Continuity is automatic: `V →L[𝕜] V` is finite-dimensional over the complete field
`𝕜`, and every linear map out of such a space is continuous. -/
noncomputable def traceCLM : (V →L[𝕜] V) →L[𝕜] 𝕜 :=
  LinearMap.toContinuousLinearMap ((LinearMap.trace 𝕜 V).comp (ContinuousLinearMap.coeLM 𝕜))

variable {𝕜 V}

/-- `TauCeti.traceCLM` evaluates to the trace of the underlying linear map. -/
@[simp]
theorem traceCLM_apply (T : V →L[𝕜] V) :
    traceCLM 𝕜 V T = LinearMap.trace 𝕜 V (T : V →ₗ[𝕜] V) := by
  rw [traceCLM, LinearMap.coe_toContinuousLinearMap']
  rfl

end TauCeti
