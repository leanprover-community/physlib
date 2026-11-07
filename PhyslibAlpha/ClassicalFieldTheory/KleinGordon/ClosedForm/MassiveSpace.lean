/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.ClosedForm.MasslessSpace
public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.ClosedForm.MassDeformation

/-!

# The massive Kirchhoff formula for every test source

In three space dimensions the massive retarded solution of any test source is the massless
Kirchhoff solution plus a Bessel average of the Kirchhoff propagators.

## i. Overview

In three space dimensions the massless sine evolution is Kirchhoff's spherical mean. Inserting it
into the Bessel average of `ClosedForm.MassDeformation` gives the retarded Green function
`δ(t - r) / (4π r) - m J₁ (m √(t² - r²)) / (4π √(t² - r²)) Θ (t - r)` as an identity for the
retarded solution of any test source at any point.

## ii. Key results

- `sineEvolution_mass_three` : the Kirchhoff–Bessel formula for the sine evolution.
- `solution_mass_three` : the Kirchhoff–Bessel formula for the retarded solution.
- `solution_mass_three_besselJ1` : the same formula with `J₁`.

## iii. Table of contents

- A. Three space dimensions

## iv. References

None.

## A. Three space dimensions

- `sineEvolution_mass_three` : the Kirchhoff–Bessel formula for the sine evolution.
- `solution_mass_three` : the Kirchhoff–Bessel formula for the retarded solution.
- `solution_mass_three_besselJ1` : the same formula with `J₁`.
-/

@[expose] public section

noncomputable section

open scoped FourierTransform SchwartzMap
open MeasureTheory

namespace KleinGordon

section Three

open TopologicalSpace TimeSlice WaveEquation.Kirchhoff

/-- **The Kirchhoff–Bessel formula for the sine evolution on `Space 3`.** For every Schwartz
source the massive sine evolution is the Kirchhoff propagator at the radius plus a Bessel
average of the Kirchhoff propagators at smaller radii. -/
lemma sineEvolution_mass_three {r : ℝ} (hr : 0 ≤ r) (m : ℝ) (g : 𝓢(Space 3, ℂ)) (x : Space 3) :
    sineEvolution ℂ r (m ^ 2) g x = wavePropagator 1 r g x +
      ∫ u in (0 : ℝ)..r, ((2 * m ^ 2 * u * Real.besselSqDeriv (m ^ 2 * (r ^ 2 - u ^ 2)) : ℝ) : ℂ) *
        wavePropagator 1 u g x := by
  rw [sineEvolution_mass_zero hr m g x, sineEvolution_zero_mass_three]
  simp_rw [sineEvolution_zero_mass_three]

/-- **The Kirchhoff–Bessel formula for the retarded solution of a test source.** In three space
dimensions the massive retarded solution at `(t, x)` is the massless Kirchhoff solution plus a
Bessel average of the Kirchhoff propagators of the slices. -/
lemma solution_mass_three (m : ℝ) (ψ : TestFunction (⊤ : Opens (ℝ × Space 3)) ℂ ⊤) (t : ℝ)
    (x : Space 3) :
    solution ℂ ψ (m ^ 2) t x = ∫ s in Set.Iic t, (wavePropagator 1 (t - s) (slice ℂ ψ s) x +
      ∫ u in (0 : ℝ)..(t - s),
        ((2 * m ^ 2 * u * Real.besselSqDeriv (m ^ 2 * ((t - s) ^ 2 - u ^ 2)) : ℝ) : ℂ) *
          wavePropagator 1 u (slice ℂ ψ s) x) := by
  rw [solution_eq_integral ℂ ψ (sq_nonneg m) t x]
  exact setIntegral_congr_fun measurableSet_Iic fun s hs =>
    sineEvolution_mass_three (sub_nonneg.2 hs) m (slice ℂ ψ s) x

/-- **The Kirchhoff–Bessel formula with `J₁`.** For `m ≠ 0` the retarded solution of a test source
in three space dimensions is the Duhamel integral of
`wavePropagator 1 τ g x - m ∫₀^τ u J₁ (m √(τ² - u²)) / √(τ² - u²) wavePropagator 1 u g x du`.
The first term is the Green function `δ(t - r) / (4π r)`. The second is
`- m J₁ (m √(t² - r²)) / (4π √(t² - r²)) Θ (t - r)`. -/
lemma solution_mass_three_besselJ1 {m : ℝ} (hm : m ≠ 0)
    (ψ : TestFunction (⊤ : Opens (ℝ × Space 3)) ℂ ⊤) (t : ℝ) (x : Space 3) :
    solution ℂ ψ (m ^ 2) t x = ∫ s in Set.Iic t, (wavePropagator 1 (t - s) (slice ℂ ψ s) x -
      (m : ℂ) * ∫ u in (0 : ℝ)..(t - s),
        ((u * (Real.besselJ1 (m * Real.sqrt ((t - s) ^ 2 - u ^ 2)) /
          Real.sqrt ((t - s) ^ 2 - u ^ 2)) : ℝ) : ℂ) * wavePropagator 1 u (slice ℂ ψ s) x) := by
  rw [solution_mass_three]
  refine setIntegral_congr_fun measurableSet_Iic fun s hs => ?_
  have hτ : 0 ≤ t - s := sub_nonneg.2 hs
  have key : (∫ u in (0 : ℝ)..(t - s),
      ((2 * m ^ 2 * u * Real.besselSqDeriv (m ^ 2 * ((t - s) ^ 2 - u ^ 2)) : ℝ) : ℂ) *
        wavePropagator 1 u (slice ℂ ψ s) x) = -((m : ℂ) * ∫ u in (0 : ℝ)..(t - s),
          ((u * (Real.besselJ1 (m * Real.sqrt ((t - s) ^ 2 - u ^ 2)) /
            Real.sqrt ((t - s) ^ 2 - u ^ 2)) : ℝ) : ℂ) * wavePropagator 1 u (slice ℂ ψ s) x) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr_ae ?_
    have hne : ∀ᵐ u : ℝ, u ≠ t - s := by
      rw [ae_iff]
      simp
    filter_upwards [hne] with u hu hmem
    rw [Set.uIoc_of_le hτ] at hmem
    have hlt : |u| < t - s := by
      rw [abs_of_pos hmem.1]
      exact lt_of_le_of_ne hmem.2 hu
    have h0 := Real.mul_besselSqDeriv_eq_besselJ1 hm hlt u
    have hc : ((2 * m ^ 2 * (u * Real.besselSqDeriv (m ^ 2 * ((t - s) ^ 2 - u ^ 2))) : ℝ) :
        ℂ) = ((-(m * (u * (Real.besselJ1 (m * Real.sqrt ((t - s) ^ 2 - u ^ 2)) /
          Real.sqrt ((t - s) ^ 2 - u ^ 2)))) : ℝ) : ℂ) := by rw [h0]
    push_cast at hc ⊢
    linear_combination (wavePropagator 1 u (slice ℂ ψ s) x) * hc
  rw [key]
  ring

end Three

end KleinGordon
