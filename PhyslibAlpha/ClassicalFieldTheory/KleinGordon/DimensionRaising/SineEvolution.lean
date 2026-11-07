/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.DimensionRaising.Rotation
public import PhyslibAlpha.Mathematics.Distribution.SchwartzPointwise
public import PhyslibAlpha.Mathematics.MeasureTheory.RadialPlane

/-!

# Dimension raising for the sine evolution

The sine evolution in `d + 2` space dimensions is `-(1 / (2π ρ)) ∂ρ` of the one in `d` dimensions.

## i. Overview

In one space dimension the massless retarded Green function is `½ Θ(t - |x|)`. In three space
dimensions it is `δ(t - r) / (4π r)`. The second is `-(1 / (2π r)) ∂ᵣ` of the first. This holds in
general: `G_{d+2} = -(1 / (2π r)) ∂ᵣ G_d` for every `d` and every mass.

The proof has three steps. Descent (`Descent`) shows that the integral over the two extra
variables of the sine evolution in `d + 2` dimensions is the sine evolution in `d` dimensions of
the integrated data. The sine evolution of a radial function is radial (`Rotation`). The integral
of a radial function over the plane is the tail integral of its profile, whose derivative is
`-ρ Φ(ρ)` (`RadialPlane`). Together they give the identity on the sine evolutions of radial data.

## ii. Key results

- `hasDerivAt_sineEvolution_radial` : dimension raising on the slices for every `d` and every mass.

## iii. Table of contents

- A. Radial slices in every dimension

## iv. References

None.

## A. Radial slices in every dimension

- `hasDerivAt_sineEvolution_radial` : dimension raising on the slices for every `d` and every mass.
-/

@[expose] public section

noncomputable section

open scoped FourierTransform SchwartzMap
open MeasureTheory TopologicalSpace TimeSlice RadialPlane

namespace KleinGordon

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E]

/-- **Dimension raising on the slices.** Let `g'` be a radial Schwartz function on `E × ℝ²` and let
`gb` be its integral over the plane. The sine evolution of `gb` along a ray has the derivative
`-(2π ρ)` times the sine evolution of `g'` at distance `ρ`. This is `S_{d+2} g' = -(1 / (2π ρ))
∂ρ S_d gb` for every dimension `d` and every mass. -/
lemma hasDerivAt_sineEvolution_radial {μ : ℝ} (hμ : 0 ≤ μ) (r : ℝ)
    (g' : 𝓢(WithLp 2 (E × EuclideanSpace ℝ (Fin 2)), ℂ)) (hrad : Function.IsRadial g')
    (gb : 𝓢(E, ℂ)) (hgb : ∀ x, gb x = ∫ y : EuclideanSpace ℝ (Fin 2),
      g' (WithLp.toLp 2 (x, y))) {e : E} (he : ‖e‖ = 1) {ρ : ℝ} (hρ : 0 < ρ) :
    HasDerivAt (fun t : ℝ => sineEvolution ℂ r μ gb (t • e))
      (-(2 * Real.pi * ρ : ℝ) • sineEvolution ℂ r μ g' (WithLp.toLp 2 (ρ • e, 0))) ρ := by
  set U := sineEvolution ℂ r μ g' with hU
  have hUr : Function.IsRadial U := isRadial_sineEvolution hμ r hrad
  set Φ : ℝ → ℂ := fun u => U (WithLp.toLp 2 (u • e, 0)) with hΦdef
  have hnorm : ∀ u : ℝ, 0 ≤ u → ‖(WithLp.toLp 2 (u • e, (0 : EuclideanSpace ℝ (Fin 2))) :
      WithLp 2 (E × EuclideanSpace ℝ (Fin 2)))‖ = u := fun u hu => by
    rw [EuclideanProd.norm_toLp_zero, norm_smul, he, mul_one, Real.norm_of_nonneg hu]
  have hUΦ : ∀ z, U z = Φ ‖z‖ := fun z => by
    exact hUr (hnorm _ (norm_nonneg z)).symm
  have hcont : Continuous Φ := by
    have : Continuous fun u : ℝ => (WithLp.toLp 2 (u • e, (0 : EuclideanSpace ℝ (Fin 2))) :
        WithLp 2 (E × EuclideanSpace ℝ (Fin 2))) := by fun_prop
    exact U.continuous.comp this
  obtain ⟨C, -, hC⟩ := U.exists_norm_le_rpow_neg 3
  have hdecay : RadialDecay Φ := ⟨hcont, C, fun u hu => by
    have := hC (WithLp.toLp 2 (u • e, (0 : EuclideanSpace ℝ (Fin 2))))
    rwa [hnorm u hu] at this⟩
  have hV : ∀ t : ℝ, 0 < t → sineEvolution ℂ r μ gb (t • e) =
      (2 * Real.pi : ℝ) • ∫ u in Set.Ioi t, u • Φ u := fun t ht => by
    rw [← integral_sineEvolution_marginal hμ r g' gb hgb (t • e), ← integral_plane_radial hdecay ht]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show U (WithLp.toLp 2 (t • e, y)) = Φ (Real.sqrt (t ^ 2 + ‖y‖ ^ 2))
    rw [hUΦ]
    congr 1
    rw [WithLp.prod_norm_eq_of_L2]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, norm_smul, he, mul_one,
      Real.norm_of_nonneg ht.le]
  have hd := (hasDerivAt_tail hdecay hρ).const_smul (2 * Real.pi : ℝ)
  refine (hd.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [Ioi_mem_nhds hρ] with t ht using hV t ht
  · simp only [Complex.real_smul, hΦdef]
    push_cast
    ring

end KleinGordon
