/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.DimensionRaising.Descent

/-!

# Rotation invariance of the sine evolution

The sine evolution commutes with linear isometries. It therefore maps radial functions to radial
functions.

## i. Overview

The multiplier of the sine evolution depends on the norm of the frequency. The Fourier transform
commutes with linear isometries. So the sine evolution of a rotated function is the rotation of the
sine evolution. A radial function is invariant under all rotations. So is its evolution.

## ii. Key results

- `sineEvolution_comp_isometry` : the sine evolution commutes with linear isometries.
- `isRadial_sineEvolution` : the sine evolution of a radial function is radial.

## iii. Table of contents

- A. Isometries

## iv. References

None.

## A. Isometries

- `sineEvolution_comp_isometry` : the sine evolution commutes with linear isometries.
- `isRadial_sineEvolution` : the sine evolution of a radial function is radial.
-/

@[expose] public section

noncomputable section

open scoped FourierTransform SchwartzMap
open MeasureTheory

namespace KleinGordon

variable {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V] [FiniteDimensional ℝ V] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [MeasurableSpace W] [BorelSpace W] [FiniteDimensional ℝ W]

omit [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] [MeasurableSpace W]
  [BorelSpace W] [FiniteDimensional ℝ W] in
lemma multiplier_comp_isometry (A : V ≃ₗᵢ[ℝ] W) (r μ : ℝ) (ξ : V) :
    multiplier r μ (A ξ) = multiplier r μ ξ := by
  unfold multiplier dispersion
  rw [A.norm_map]

/-- **The sine evolution commutes with rotations.** -/
lemma sineEvolution_comp_isometry {μ : ℝ} (hμ : 0 ≤ μ) (A : V ≃ₗᵢ[ℝ] W) (r : ℝ) (g : 𝓢(W, ℂ))
    (x : V) :
    sineEvolution ℂ r μ (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv g)
        x = sineEvolution ℂ r μ g (A x) := by
  rw [sineEvolution_apply_eq ℂ r hμ, sineEvolution_apply_eq ℂ r hμ]
  have h := A.measurePreserving.integral_comp' (f := A.toMeasurableEquiv)
    (fun y : W => 𝐞 (inner ℝ y (A x)) • (multiplier r μ y • 𝓕 g y))
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  have e : 𝓕 (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv g) ξ =
      𝓕 g (A ξ) := by
    rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
    exact Fourier.fourier_comp_isometry A g ξ
  simp [e, multiplier_comp_isometry, LinearIsometryEquiv.inner_map_map]

/-- **The sine evolution of a radial function is radial.** -/
lemma isRadial_sineEvolution {μ : ℝ} (hμ : 0 ≤ μ) (r : ℝ) {g : 𝓢(V, ℂ)} (hg : Function.IsRadial g) :
    Function.IsRadial (sineEvolution ℂ r μ g) := by
  rw [Function.isRadial_iff_comp_linearIsometryEquiv] at hg ⊢
  intro A
  funext x
  have h1 : SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv g = g := by
    ext y
    exact congrFun (hg A) y
  have := sineEvolution_comp_isometry hμ A r g x
  rw [h1] at this
  exact this.symm

end KleinGordon
