/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QuantumMechanics.OneDimension.HilbertSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
/-!

# Schwartz submodule of the Hilbert space

This can be used to define e.g.
the rigged Hilbert space.

-/

namespace QuantumMechanics

namespace OneDimension

noncomputable section

namespace HilbertSpace
open MeasureTheory
open SchwartzMap InnerProductSpace

/-- The continuous linear map including Schwartz functions into the hilbert space. -/
def schwartzIncl : 𝓢(ℝ, ℂ) →L[ℂ] HilbertSpace :=
  SchwartzMap.toLpCLM ℂ (E := ℝ) ℂ 2 MeasureTheory.volume

lemma schwartzIncl_injective : Function.Injective schwartzIncl :=
  SchwartzMap.injective_toLp _ _

lemma schwartzIncl_coe_ae (ψ : 𝓢(ℝ, ℂ)) :
    ψ.1 =ᶠ[ae volume] (schwartzIncl ψ) := (SchwartzMap.coeFn_toLp _ 2 volume).symm

lemma schwartzIncl_inner (ψ1 ψ2 : 𝓢(ℝ, ℂ)) :
    ⟪schwartzIncl ψ1, schwartzIncl ψ2⟫_ℂ = ∫ x : ℝ, starRingEnd ℂ (ψ1 x) * ψ2 x := by
  apply MeasureTheory.integral_congr_ae
  have h1 : ψ1.1 =ᶠ[ae volume] (schwartzIncl ψ1) :=
    schwartzIncl_coe_ae ψ1
  have h2 : ψ2.1 =ᶠ[ae volume] (schwartzIncl ψ2) :=
    schwartzIncl_coe_ae ψ2
  filter_upwards [h1, h2] with _ h1 h2
  rw [← h1, ← h2]
  simp only [RCLike.inner_apply]
  rw [mul_comm]
  rfl

end HilbertSpace
end
end OneDimension
end QuantumMechanics
