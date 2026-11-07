/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.Solution
public import PhyslibAlpha.Mathematics.Fourier.Marginal

/-!

# Descent from `d + k` to `d` space dimensions

Integrating the sine evolution in `d + k` space dimensions over the extra variables gives the sine
evolution in `d` space dimensions of the integrated data.

## i. Overview

Let `E'` be the Euclidean product of `E` and `F`. The Fourier transform of the integral over `F`
of a function on `E'` is the restriction of its transform to the frequencies `(ξ, 0)`. The
multiplier of the sine evolution depends on the norm of the frequency, so the restriction to
`(ξ, 0)` is the multiplier of `E`. This is Hadamard's method of descent. It holds for every mass.

## ii. Key results

- `integral_sineEvolution_marginal` : descent for the sine evolution, for every mass.

## iii. Table of contents

- A. Descent

## iv. References

None.

## A. Descent

- `integral_sineEvolution_marginal` : descent for the sine evolution, for every mass.
-/

@[expose] public section

noncomputable section

open scoped FourierTransform SchwartzMap
open MeasureTheory EuclideanProd Fourier

namespace KleinGordon

variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]

/-- **Descent.** Integrating the sine evolution in `E × F` over `F` gives the sine evolution in
`E` of the integrated data. -/
lemma integral_sineEvolution_marginal {μ : ℝ} (hμ : 0 ≤ μ) (r : ℝ)
    (g' : 𝓢(WithLp 2 (E × F), ℂ)) (gb : 𝓢(E, ℂ))
    (hgb : ∀ x, gb x = ∫ y : F, g' (WithLp.toLp 2 (x, y))) (x : E) :
    ∫ y : F, sineEvolution ℂ r μ g' (WithLp.toLp 2 (x, y)) = sineEvolution ℂ r μ gb x := by
  set h : 𝓢(WithLp 2 (E × F), ℂ) := sineEvolution ℂ r μ g' with hh
  have hFH : ∀ ξ : E, 𝓕 (fun x : E => ∫ y : F, h (WithLp.toLp 2 (x, y))) ξ =
      𝓕 (sineEvolution ℂ r μ gb) ξ := fun ξ => by
    have e1 := fourier_marginal (F := F) h.integrable ξ
    have e2 := fourier_marginal (F := F) g'.integrable ξ
    have e3 := Solution.fourier_sineEvolution ℂ hμ r g' (WithLp.toLp 2 (ξ, (0 : F)))
    have e4 := Solution.fourier_sineEvolution ℂ hμ r gb ξ
    have e5 : 𝓕 g' (WithLp.toLp 2 (ξ, (0 : F))) = 𝓕 gb ξ := by
      rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, fourier_eq_complex,
        fourier_eq_complex, ← e2]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp [hgb x]
    have hd : dispersion μ (WithLp.toLp 2 (ξ, (0 : F))) = dispersion μ ξ := by
      unfold dispersion
      rw [norm_toLp_zero]
    calc 𝓕 (fun x : E => ∫ y : F, h (WithLp.toLp 2 (x, y))) ξ
        = ∫ x : E, (𝐞 (-inner ℝ x ξ) : ℂ) • ∫ y : F, h (WithLp.toLp 2 (x, y)) :=
          fourier_eq_complex _ _
      _ = ∫ z, (𝐞 (-inner ℝ z (WithLp.toLp 2 (ξ, (0 : F)))) : ℂ) • h z := e1
      _ = 𝓕 (⇑h) (WithLp.toLp 2 (ξ, (0 : F))) := (fourier_eq_complex _ _).symm
      _ = (𝓕 h : 𝓢(WithLp 2 (E × F), ℂ)) (WithLp.toLp 2 (ξ, (0 : F))) := by
          rw [SchwartzMap.fourier_coe]
      _ = (Real.sincPropagator r (dispersion μ ξ) : ℂ) • 𝓕 gb ξ := by
          rw [hh, e3, hd, e5]
      _ = 𝓕 (sineEvolution ℂ r μ gb) ξ := e4.symm
  have hHc := continuous_marginal h
  have hHi := integrable_marginal h
  have hF : 𝓕 (fun x : E => ∫ y : F, h (WithLp.toLp 2 (x, y))) =
      ⇑(SchwartzMap.fourierTransformCLM ℂ (sineEvolution ℂ r μ gb)) := funext hFH
  have hI : Integrable (𝓕 (fun x : E => ∫ y : F, h (WithLp.toLp 2 (x, y)))) := by
    rw [hF]
    exact (SchwartzMap.fourierTransformCLM ℂ (sineEvolution ℂ r μ gb)).integrable
  have := congrFun (hHc.fourierInv_fourier_eq hHi hI) x
  rw [hF, ← SchwartzMap.fourierInv_coe] at this
  have hinv := congrArg (fun g : 𝓢(E, ℂ) => g x)
    (FourierTransform.fourierInv_fourier_eq (E := 𝓢(E, ℂ)) (F := 𝓢(E, ℂ))
      (sineEvolution ℂ r μ gb))
  exact (hinv.symm.trans this).symm

end KleinGordon
