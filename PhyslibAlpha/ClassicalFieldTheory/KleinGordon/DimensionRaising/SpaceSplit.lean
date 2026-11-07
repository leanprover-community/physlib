/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.DimensionRaising.Retarded
public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.DimensionRaising.Rotation
public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.GreenOperators
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!

# Splitting off two space dimensions

`Space (d + 2)` is isometric to the Euclidean product of `Space d` and the plane.

## i. Overview

Dimension raising compares the sine evolution in `d + 2` space dimensions with the one in `d`
dimensions. The statements `hasDerivAt_sineEvolution_radial` and `hasDerivAt_solution_radial` live
on the Euclidean product `WithLp 2 (E × EuclideanSpace ℝ (Fin 2))`. This file transports them to
`Space (d + 2)` along a linear isometry.

## ii. Key results

- `spaceSplit` : the isometry `Space (d + 2) ≃ₗᵢ WithLp 2 (Space d × EuclideanSpace ℝ (Fin 2))`.
- `solution_transportSource` : the retarded solution commutes with isometries of space.
- `hasDerivAt_sineEvolution_radial_space` : dimension raising on the slices of `Space (d + 2)`.
- `hasDerivAt_solution_radial_space` : dimension raising on `Space (d + 2)`.
- `hasDerivAt_retardedResponse_radial` : dimension raising for the retarded response on spacetime.
- `spaceThree` : `Space 3` is isometric to the Euclidean three-space.

## iii. Table of contents

- A. The isometry
- B. Dimension raising
- C. Three space dimensions

## iv. References

None.

## A. The isometry

- `spaceSplit` : the isometry `Space (d + 2) ≃ₗᵢ WithLp 2 (Space d × EuclideanSpace ℝ (Fin 2))`.
- `transportSource` : a source pulled back along an isometry of space.
- `solution_transportSource` : the retarded solution commutes with isometries of space.

## B. Dimension raising

- `hasDerivAt_sineEvolution_radial_space` : dimension raising on the slices of `Space (d + 2)`.
- `hasDerivAt_solution_radial_space` : dimension raising on `Space (d + 2)`.
- `hasDerivAt_retardedResponse_radial` : dimension raising for the retarded response on spacetime.

## C. Three space dimensions

- `Eucl3` : the Euclidean three-space as a product of the line and the plane.
- `spaceThree` : `Space 3` is isometric to the Euclidean three-space.
-/

@[expose] public section

noncomputable section

open scoped SchwartzMap Distributions
open MeasureTheory TopologicalSpace TimeSlice

namespace KleinGordon

section Transport

variable {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V] [FiniteDimensional ℝ V] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [MeasurableSpace W] [BorelSpace W] [FiniteDimensional ℝ W]

/-- A source on time and `W` pulled back along an isometry `V ≃ W` of space. -/
def transportSource (A : V ≃ₗᵢ[ℝ] W) :
    𝓓((⊤ : Opens (ℝ × W)), ℂ) →L[ℝ] 𝓓((⊤ : Opens (ℝ × V)), ℂ) :=
  TestFunction.precompLinearEquivCLM
    ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr A.toContinuousLinearEquiv)

omit [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] [MeasurableSpace W]
  [BorelSpace W] [FiniteDimensional ℝ W] in
lemma transportSource_apply (A : V ≃ₗᵢ[ℝ] W) (ψ : 𝓓((⊤ : Opens (ℝ × W)), ℂ)) (s : ℝ) (x : V) :
    transportSource A ψ (s, x) = ψ (s, A x) := rfl

omit [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] [MeasurableSpace W]
  [BorelSpace W] [FiniteDimensional ℝ W] in
lemma slice_transportSource (A : V ≃ₗᵢ[ℝ] W) (ψ : 𝓓((⊤ : Opens (ℝ × W)), ℂ)) (s : ℝ) :
    slice ℂ (transportSource A ψ) s =
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv (slice ℂ ψ s) := rfl

/-- **The retarded solution commutes with isometries of space.** -/
lemma solution_transportSource {μ : ℝ} (hμ : 0 ≤ μ) (A : V ≃ₗᵢ[ℝ] W)
    (ψ : 𝓓((⊤ : Opens (ℝ × W)), ℂ)) (t : ℝ) (x : V) :
    solution ℂ (transportSource A ψ) μ t x = solution ℂ ψ μ t (A x) := by
  rw [solution_eq_integral ℂ _ hμ, solution_eq_integral ℂ _ hμ]
  refine setIntegral_congr_fun measurableSet_Iic fun s _ => ?_
  rw [slice_transportSource]
  exact sineEvolution_comp_isometry hμ A (t - s) (slice ℂ ψ s) x

end Transport

/-- `Space (d + 2)` is isometric to the Euclidean product of `Space d` and the plane. -/
def spaceSplit (d : ℕ) :
    Space (d + 2) ≃ₗᵢ[ℝ] WithLp 2 (Space d × EuclideanSpace ℝ (Fin 2)) :=
  (((Space.basis (d := d + 2)).repr.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finSumFinEquiv (m := d) (n := 2)).symm)).trans
    (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ => ℝ))).trans
    (LinearIsometryEquiv.withLpProdCongr 2 (Space.basis (d := d)).repr.symm
      (LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin 2))))

/-- **Dimension raising on `Space (d + 2)`.** Let `ψ'` be a source on time and `Space (d + 2)` that
is radial in space at each time and let `ψb` be its integral over the plane. The massive retarded
solution of `ψb` along a ray in `Space d` has the derivative `-(2π ρ)` times the retarded
solution of `ψ'` at distance `ρ`. This is `G_{d+2} = -(1 / (2π r)) ∂ᵣ G_d`. -/
lemma hasDerivAt_solution_radial_space {μ : ℝ} (hμ : 0 ≤ μ) (d : ℕ)
    (ψ' : 𝓓((⊤ : Opens (ℝ × Space (d + 2))), ℂ)) (ψb : 𝓓((⊤ : Opens (ℝ × Space d)), ℂ))
    (hrad : ∀ s, Function.IsRadial (slice ℂ ψ' s))
    (hψb : ∀ s x, ψb (s, x) = ∫ y : EuclideanSpace ℝ (Fin 2),
      ψ' (s, (spaceSplit d).symm (WithLp.toLp 2 (x, y))))
    {e : Space d} (he : ‖e‖ = 1) (t : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    HasDerivAt (fun τ : ℝ => solution ℂ ψb μ t (τ • e))
      (-(2 * Real.pi * ρ : ℝ) •
        solution ℂ ψ' μ t ((spaceSplit d).symm (WithLp.toLp 2 (ρ • e, 0)))) ρ := by
  have h := hasDerivAt_solution_radial hμ (transportSource (spaceSplit d).symm ψ') ψb
    (fun s ⦃z z'⦄ hzz => by
      change slice ℂ ψ' s ((spaceSplit d).symm z) = slice ℂ ψ' s ((spaceSplit d).symm z')
      exact hrad s (by simpa using hzz))
    (fun s x => by rw [hψb]; rfl) he t hρ
  rw [solution_transportSource hμ] at h
  exact h


/-- **Dimension raising on the slices of `Space (d + 2)`.** -/
lemma hasDerivAt_sineEvolution_radial_space {μ : ℝ} (hμ : 0 ≤ μ) (d : ℕ) (r : ℝ)
    (g' : 𝓢(Space (d + 2), ℂ)) (hrad : Function.IsRadial g') (gb : 𝓢(Space d, ℂ))
    (hgb : ∀ x, gb x = ∫ y : EuclideanSpace ℝ (Fin 2),
      g' ((spaceSplit d).symm (WithLp.toLp 2 (x, y))))
    {e : Space d} (he : ‖e‖ = 1) {ρ : ℝ} (hρ : 0 < ρ) :
    HasDerivAt (fun t : ℝ => sineEvolution ℂ r μ gb (t • e))
      (-(2 * Real.pi * ρ : ℝ) •
        sineEvolution ℂ r μ g' ((spaceSplit d).symm (WithLp.toLp 2 (ρ • e, 0)))) ρ := by
  set A := (spaceSplit d).symm with hA
  set g'' := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv g' with hg''
  have h := hasDerivAt_sineEvolution_radial hμ r g'' (fun z z' hzz => by
      change g' (A z) = g' (A z')
      exact hrad (by simpa using hzz)) gb (fun x => by rw [hgb]; rfl) he hρ
  rw [hg'', sineEvolution_comp_isometry hμ A] at h
  exact h

open KleinGordon.Spacetime in
/-- **Dimension raising for the retarded response on spacetime.** The sources are transported to
time and space by `sourceEquiv`. -/
lemma hasDerivAt_retardedResponse_radial {μ : ℝ} (hμ : 0 ≤ μ) (d : ℕ)
    (f' : 𝓓((⊤ : Opens (SpaceTime (d + 2))), ℂ)) (f : 𝓓((⊤ : Opens (SpaceTime d)), ℂ))
    (hrad : ∀ s, Function.IsRadial (slice ℂ (sourceEquiv ℂ f') s))
    (hmarg : ∀ s x, sourceEquiv ℂ f (s, x) = ∫ y : EuclideanSpace ℝ (Fin 2),
      sourceEquiv ℂ f' (s, (spaceSplit d).symm (WithLp.toLp 2 (x, y))))
    {e : Space d} (he : ‖e‖ = 1) (t : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    HasDerivAt (fun τ : ℝ => retardedResponse ℂ μ f ((coordinates d).symm (t, τ • e)))
      (-(2 * Real.pi * ρ : ℝ) • retardedResponse ℂ μ f'
        ((coordinates (d + 2)).symm (t, (spaceSplit d).symm (WithLp.toLp 2 (ρ • e, 0))))) ρ := by
  simpa [retardedResponse] using
    hasDerivAt_solution_radial_space hμ d (sourceEquiv ℂ f') (sourceEquiv ℂ f) hrad hmarg he t hρ

/-- The Euclidean three-space. -/
abbrev Eucl3 : Type := WithLp 2 (ℝ × EuclideanSpace ℝ (Fin 2))

/-- `Space 3` is isometric to the Euclidean three-space. -/
def spaceThree : Space 3 ≃ₗᵢ[ℝ] Eucl3 :=
  (spaceSplit 1).trans (LinearIsometryEquiv.withLpProdCongr 2 Space.oneEquiv
    (LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin 2))))

end KleinGordon
