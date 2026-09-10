/-
Copyright (c) 2026 Hirotaka Monya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hirotaka Monya
-/
module

public import Physlib.ClassicalMechanics.HarmonicOscillator.Basic
public import Physlib.Units.WithDim.Analysis

/-!
# A. Harmonic-oscillator energy in dimension-tagged coordinates

This module is an application of `WithDim` to an existing Physlib model, not a second
model of the harmonic oscillator. `potentialEnergyWithDim` reuses `potentialEnergy`
and its coordinate time derivative reuses `potentialEnergy_deriv`.

The oscillator parameters are numerical values in the chosen units. In particular,
this fixed-coordinate adapter does not assert unit invariance with `S.k` held fixed.
A full change of units must also rescale model parameters. The derivative below is
an ordinary continuous linear map; it is not automatically a quotient-dimension tag.
-/

@[expose] public section

namespace ClassicalMechanics.HarmonicOscillator

open Dimension InnerProductSpace Time
open scoped ContDiff

/-!
## A.1. Reusing the numerical energy function
-/

/-- The existing potential energy with length input and energy output tags, in fixed units. -/
noncomputable def potentialEnergyWithDim (S : HarmonicOscillator) :
    WithDim L𝓭 (EuclideanSpace ℝ (Fin 1)) →
      WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ :=
  WithDim.transport L𝓭 (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) S.potentialEnergy

@[simp]
lemma potentialEnergyWithDim_val (S : HarmonicOscillator)
    (x : WithDim L𝓭 (EuclideanSpace ℝ (Fin 1))) :
    (S.potentialEnergyWithDim x).val = S.potentialEnergy x.val := rfl

/-- The tagged model is differentiable, with the transported numerical derivative. -/
lemma hasFDerivAt_potentialEnergyWithDim (S : HarmonicOscillator)
    (x : WithDim L𝓭 (EuclideanSpace ℝ (Fin 1))) :
    HasFDerivAt S.potentialEnergyWithDim
      (WithDim.transportLinearMap L𝓭 (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹)
        (fderiv ℝ S.potentialEnergy x.val)) x := by
  unfold potentialEnergyWithDim
  apply WithDim.hasFDerivAt_transport
  have hf : Differentiable ℝ S.potentialEnergy := by
    unfold potentialEnergy
    fun_prop
  exact (hf x.val).hasFDerivAt

/-- The fixed-unit tagged potential energy is continuous. -/
lemma continuous_potentialEnergyWithDim (S : HarmonicOscillator) :
    Continuous S.potentialEnergyWithDim :=
  (show Differentiable ℝ S.potentialEnergyWithDim from
    fun x => (hasFDerivAt_potentialEnergyWithDim S x).differentiableAt).continuous

/-!
## A.2. Reusing the existing physical derivative theorem
-/

/-- The coordinate time derivative is the existing oscillator theorem, not a new energy proof. -/
lemma potentialEnergyWithDim_deriv_val (S : HarmonicOscillator)
    (x : Time → WithDim L𝓭 (EuclideanSpace ℝ (Fin 1))) (hx : ContDiff ℝ ∞ x) :
    ∂ₜ (fun t => (S.potentialEnergyWithDim (x t)).val) =
      fun t => ⟪∂ₜ (fun s => (x s).val) t, S.k • (x t).val⟫_ℝ := by
  let e := WithDim.toValueLinearIsometryEquiv L𝓭 (EuclideanSpace ℝ (Fin 1))
  have hv : ContDiff ℝ ∞ (fun t => (x t).val) :=
    e.toContinuousLinearEquiv.contDiff.comp hx
  exact S.potentialEnergy_deriv (fun t => (x t).val) hv

end ClassicalMechanics.HarmonicOscillator
