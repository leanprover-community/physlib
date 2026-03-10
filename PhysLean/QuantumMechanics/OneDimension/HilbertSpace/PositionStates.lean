/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.QuantumMechanics.OneDimension.HilbertSpace.SchwartzSubmodule
public import Mathlib.Analysis.Distribution.TemperedDistribution
/-!

# Position states

We define plane waves as a member of the dual of the
Schwartz submodule of the Hilbert space.

-/

@[expose] public section
namespace QuantumMechanics

namespace OneDimension

noncomputable section

namespace HilbertSpace
open MeasureTheory SchwartzMap

/-- Position state as a member of the dual of the
  Schwartz submodule of the Hilbert space. -/
def positionState (x : ℝ) : 𝓢(ℝ, ℂ) →L[ℂ] ℂ := TemperedDistribution.delta x

lemma positionState_apply (x : ℝ) (ψ : 𝓢(ℝ, ℂ)) :
    positionState x ψ = ψ x := rfl

/-- Two elements of the `𝓢(ℝ, ℂ)` are equal if they
  are equal on all position states. -/
lemma eq_of_eq_positionState {ψ1 ψ2 : 𝓢(ℝ, ℂ)}
    (h : ∀ x, positionState x ψ1 = positionState x ψ2) :
    ψ1 = ψ2 := by
  ext x
  exact h x

end HilbertSpace
end
end OneDimension
end QuantumMechanics
