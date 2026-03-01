/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QuantumMechanics.OneDimension.HilbertSpace.SchwartzSubmodule
import Mathlib.Analysis.Distribution.TemperedDistribution
/-!

# Plane waves

We define plane waves as a member of the dual of the
Schwartz submodule of the Hilbert space.

-/

namespace QuantumMechanics

namespace OneDimension

noncomputable section

namespace HilbertSpace
open MeasureTheory SchwartzMap TemperedDistribution

/-- Plane waves as a member of the dual of the
  Schwartz submodule of the Hilbert space.

  For a given `k` this corresponds to the plane wave
  `exp (2π I k x)`. -/
def planewaveFunctional (k : ℝ) : 𝓢(ℝ, ℂ) →L[ℂ] ℂ :=
  (TemperedDistribution.delta k : SchwartzMap ℝ ℂ →L[ℂ] ℂ) ∘L (SchwartzMap.fourierTransformCLM ℂ)

open FourierTransform in
lemma planewaveFunctional_apply (k : ℝ) (ψ : 𝓢(ℝ, ℂ)) :
    planewaveFunctional k ψ = 𝓕 ψ k := rfl

/-- Two elements of the Schwartz submodule are equal if and only if they are equal on
  all applications of `planewaveFunctional`. -/
lemma eq_of_eq_planewaveFunctional {ψ1 ψ2 : 𝓢(ℝ, ℂ)}
    (h : ∀ k, planewaveFunctional k ψ1 = planewaveFunctional k ψ2) :
    ψ1 = ψ2 := by
  apply (FourierTransform.fourierCLE ℂ 𝓢(ℝ, ℂ)).injective
  ext k
  exact h k

end HilbertSpace
end
end OneDimension
end QuantumMechanics
