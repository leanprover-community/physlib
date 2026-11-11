/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.RetardedSolution
public import PhyslibAlpha.ClassicalFieldTheory.WaveEquation.Kirchhoff.Propagator

/-!

# Kirchhoff's formula for the massless retarded solution in three dimensions

The massless sine evolution in three space dimensions is Kirchhoff's spherical mean.

## i. Overview

The Fourier multiplier of the sphere mean is `sin (2π |ξ| t) / (2π |ξ|)`. This is the multiplier
of the massless sine evolution. Fourier inversion identifies the two operators on Schwartz
functions. The Duhamel integral of the sphere means is the retarded solution. This is the kernel
`δ(t - r) / (4π r)`.

The sphere integrals and their Fourier transform are taken from the worktree
`causal-green-operators` (`FieldTheory/Wave/Kirchhoff` and `FieldTheory/Wave/Proofs/Fourier`).

## ii. Key results

- `fourier_wavePropagator` : the transform of the Kirchhoff propagator.
- `sineEvolution_zero_mass_three` : the massless sine evolution is the Kirchhoff propagator.
- `solution_zero_mass_three` : the massless retarded solution is the Duhamel integral of the
  spherical means.

## iii. Table of contents

- A. The sine evolution
- B. The retarded solution

## iv. References

None.

## A. The sine evolution

- `continuous_wavePropagator` : the Kirchhoff propagator of a Schwartz function is continuous.
- `fourier_wavePropagator` : the transform of the Kirchhoff propagator.
- `sineEvolution_zero_mass_three` : the massless sine evolution is the Kirchhoff propagator.

## B. The retarded solution

- `solution_zero_mass_three` : the massless retarded solution is the Duhamel integral of the
  spherical means.
-/

@[expose] public section

noncomputable section

open scoped FourierTransform SchwartzMap
open MeasureTheory WaveEquation.Kirchhoff Sphere3

namespace KleinGordon

/-- The wave propagator of a Schwartz function is continuous. -/
lemma continuous_wavePropagator (g : 𝓢(Space 3, ℂ)) (t : ℝ) :
    Continuous (wavePropagator 1 t g) := by
  have hs : Continuous (sphericalIntegral (1 * t) g) := by
    unfold sphericalIntegral
    have hf : Continuous (Function.uncurry fun (x : Space 3) (n : Sph) =>
        g (x + (1 * t) • n.1)) :=
      g.continuous.comp (by fun_prop)
    have := continuous_parametric_integral_of_continuous (μ := sphereMeasure) hf
      (isCompact_univ_iff.mpr (inferInstance : CompactSpace Sph))
    simpa using this
  unfold wavePropagator
  exact continuous_const.mul hs

/-- **Kirchhoff's formula in Fourier space.** The Fourier transform of the wave propagator is
the multiplier of the massless sine evolution times the transform of the data. -/
lemma fourier_wavePropagator (g : 𝓢(Space 3, ℂ)) (t : ℝ) {ξ : Space 3} (hξ : ξ ≠ 0) :
    𝓕 (wavePropagator 1 t g) ξ = multiplier t 0 ξ * 𝓕 g ξ := by
  have h := wavePropagator_fourier g (c := 1) one_pos (t := t) hξ
  have hd : dispersion (0 : ℝ) ξ = 2 * Real.pi * ‖ξ‖ := by
    unfold dispersion
    rw [add_zero, ← mul_pow, Real.sqrt_sq (by positivity)]
  have hω : 2 * Real.pi * ‖ξ‖ ≠ 0 := by positivity
  have hm : multiplier t 0 ξ = ((Real.sin (2 * Real.pi * 1 * ‖ξ‖ * t) /
      (2 * Real.pi * 1 * ‖ξ‖) : ℝ) : ℂ) := by
    unfold multiplier
    rw [hd, Real.sincPropagator_eq_sin_div hω, mul_one]
  have e1 : 𝓕 (wavePropagator 1 t g) ξ =
      ∫ x : Space 3, phase (inner ℝ x ξ) * wavePropagator 1 t g x := by
    rw [Real.fourier_eq]
    simp [phase_eq_fourierChar, Circle.smul_def]
  have e2 : 𝓕 g ξ = ∫ x : Space 3, phase (inner ℝ x ξ) * g x := by
    rw [SchwartzMap.fourier_coe, Real.fourier_eq]
    simp [phase_eq_fourierChar, Circle.smul_def]
  rw [hm, e1, h, e2]

/-- **The massless sine evolution is Kirchhoff's propagator.** In three space dimensions the
massless sine evolution of a Schwartz function is the spherical mean `t M_t g`. -/
lemma sineEvolution_zero_mass_three (t : ℝ) (g : 𝓢(Space 3, ℂ)) (x : Space 3) :
    sineEvolution ℂ t 0 g x = wavePropagator 1 t g x := by
  have hint : Integrable (wavePropagator 1 t g) := by
    unfold wavePropagator
    exact (integrable_sphericalIntegral g (1 * t)).const_mul _
  have hcont := continuous_wavePropagator g t
  have hae : ∀ᵐ ξ : Space 3, ξ ≠ 0 := by
    rw [ae_iff]
    simp
  have hcF : Continuous (𝓕 (wavePropagator 1 t g)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hint
  have hFint : Integrable (𝓕 (wavePropagator 1 t g)) := by
    refine ((𝓕 g).integrable.norm.const_mul |t|).mono' hcF.aestronglyMeasurable ?_
    filter_upwards [hae] with ξ hξ
    rw [fourier_wavePropagator g t hξ, norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_multiplier_le t 0 ξ) (norm_nonneg _)
  have hinv := congrFun (hcont.fourierInv_fourier_eq hint hFint) x
  rw [Real.fourierInv_eq] at hinv
  rw [← hinv, sineEvolution_apply_eq ℂ t le_rfl g x]
  refine integral_congr_ae ?_
  filter_upwards [hae] with ξ hξ
  rw [fourier_wavePropagator g t hξ]
  simp only [Circle.smul_def, smul_eq_mul]

open TopologicalSpace TimeSlice in
/-- **Kirchhoff's formula for the retarded solution.** The massless retarded solution in three
space dimensions is the Duhamel integral of the spherical means of the source over the earlier
times. This is the retarded Green function `δ(t - r) / (4π r)`. -/
lemma solution_zero_mass_three (ψ : TestFunction (⊤ : Opens (ℝ × Space 3)) ℂ ⊤) (t : ℝ)
    (x : Space 3) :
    solution ℂ ψ 0 t x = ∫ s in Set.Iic t, wavePropagator 1 (t - s) (slice ℂ ψ s) x := by
  rw [solution_eq_integral ℂ ψ le_rfl t x]
  exact setIntegral_congr_fun measurableSet_Iic fun s _ =>
    sineEvolution_zero_mass_three (t - s) (slice ℂ ψ s) x

/-- The Kirchhoff propagator at the origin of a radial function is the radius times its value. -/
lemma wavePropagator_radial {Φ : ℝ → ℂ} {g : Space 3 → ℂ} (hg : ∀ x, g x = Φ ‖x‖) {τ : ℝ}
    (hτ : 0 ≤ τ) : wavePropagator 1 τ g 0 = τ * Φ τ := by
  have hc : ∀ n : Sph, g (0 + (1 * τ) • n.1) = Φ τ := fun n => by
    have hn : ‖n.1‖ = 1 := by simp
    rw [hg, zero_add, norm_smul, hn, one_mul, mul_one, Real.norm_of_nonneg hτ]
  unfold wavePropagator sphericalIntegral
  simp_rw [hc]
  rw [integral_const]
  have hm : (sphereMeasure.real Set.univ) = 4 * Real.pi := by
    rw [Measure.real, sphereMeasure_univ, ENNReal.toReal_ofReal (by positivity)]
  rw [hm, Complex.real_smul]
  push_cast
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

end KleinGordon
