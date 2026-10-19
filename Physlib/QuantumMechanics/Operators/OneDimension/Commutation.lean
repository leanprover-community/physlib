/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QuantumMechanics.Operators.OneDimension.Position
public import Physlib.QuantumMechanics.Operators.OneDimension.Momentum
/-!

# Commutation relations

The commutation relations between different operators.

-/

@[expose] public section

namespace QuantumMechanics

namespace OneDimension
noncomputable section
open Constants
open _root_.QuantumMechanics.OneDimension.HilbertSpace
open SchwartzMap

/-!

## Commutation relation between position and momentum operators

-/

lemma positionOperatorSchwartz_commutation_momentumOperatorSchwartz
    (ψ : 𝓢(ℝ, ℂ)) : positionOperatorSchwartz (momentumOperatorSchwartz ψ)
    - momentumOperatorSchwartz (positionOperatorSchwartz ψ)
    = (Complex.I * ℏ) • ψ := by
  ext x
  simp [momentumOperatorSchwartz_apply, positionOperatorSchwartz_apply,
    positionOperatorSchwartz_apply_fun]
  have h1 : deriv Complex.ofReal x = 1 := Complex.ofRealCLM.deriv.trans (by simp)
  rw [deriv_fun_mul, h1]
  · ring
  · exact Complex.ofRealCLM.differentiableAt
  · exact ψ.differentiableAt

lemma positionOperatorSchwartz_momentumOperatorSchwartz_eq (ψ : 𝓢(ℝ, ℂ)) :
    positionOperatorSchwartz (momentumOperatorSchwartz ψ)
    = momentumOperatorSchwartz (positionOperatorSchwartz ψ)
    + (Complex.I * ℏ) • ψ :=
  sub_eq_iff_eq_add'.mp (positionOperatorSchwartz_commutation_momentumOperatorSchwartz ψ)

lemma momentumOperatorSchwartz_positionOperatorSchwartz_eq (ψ : 𝓢(ℝ, ℂ)) :
    momentumOperatorSchwartz (positionOperatorSchwartz ψ)
    = positionOperatorSchwartz (momentumOperatorSchwartz ψ)
    - (Complex.I * ℏ) • ψ := by
  simp [← positionOperatorSchwartz_commutation_momentumOperatorSchwartz ψ]

end
end OneDimension
end QuantumMechanics
