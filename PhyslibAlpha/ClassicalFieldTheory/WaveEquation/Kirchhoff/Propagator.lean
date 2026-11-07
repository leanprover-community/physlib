/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.WaveEquation.Kirchhoff.SphericalMean
/-!
# Properties of the wave propagator

The wave propagator has the Fourier multiplier `sin(ω t) / ω`, finite propagation speed and the
Huygens property.

## i. Overview

The multiplier is `sin(ω t) / ω` with `ω = 2π c |ξ|`. A function supported in a ball is carried by
the
propagator to the shell around the ball. Points inside the light cone of the support see nothing.
The propagator is odd in time. The statements are first proved for positive time. The oddness of the
spherical integral extends them to negative time.

## ii. Key results

* `wavePropagator_fourier`: the Fourier multiplier.
* `wavePropagator_eq_zero_of_far`: finite propagation speed.
* `wavePropagator_eq_zero_of_near`: Huygens' principle.
* `wavePropagator_neg`: oddness in time.
* `wavePropagator_eq_of_eq_on_sphere`: the field depends on the data only on a sphere.
* `wavePropagator_isWavePropagator`: the three properties together.

## iii. Table of contents

- A. The Fourier multiplier for positive time
- B. Light-cone support for positive time
- C. Two-sided time
- D. The free three-dimensional propagator

## iv. References

* None.
-/

@[expose] public section

namespace WaveEquation.Kirchhoff

open MeasureTheory Sphere3
open scoped Pointwise FourierTransform SchwartzMap

/-! ## A. The Fourier multiplier for positive time -/

/-- **Kirchhoff's formula in Fourier space.** For `c > 0`, `t > 0` and `ξ ≠ 0` the mean has the
Fourier multiplier `sin(ω t) / ω` with `ω = 2π c |ξ|`, the wave propagator multiplier. -/
lemma wavePropagator_fourier_of_pos (f : 𝓢(Space 3, ℂ)) {c t : ℝ} (hc : 0 < c) (ht : 0 < t)
    {ξ : Space 3} (hξ : ξ ≠ 0) :
    ∫ x : Space 3, phase (inner ℝ x ξ) * wavePropagator c t f x =
      ((Real.sin (2 * Real.pi * c * ‖ξ‖ * t) / (2 * Real.pi * c * ‖ξ‖) : ℝ) : ℂ) *
        ∫ x : Space 3, phase (inner ℝ x ξ) * f x := by
  have hr : 0 < c * t := mul_pos hc ht
  have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  have h := sphericalIntegral_fourier f hr hξ
  unfold wavePropagator
  have hpull : ∫ x : Space 3, phase (inner ℝ x ξ) *
      (((t / (4 * Real.pi) : ℝ) : ℂ) * sphericalIntegral (c * t) f x) =
      ((t / (4 * Real.pi) : ℝ) : ℂ) *
        ∫ x : Space 3, phase (inner ℝ x ξ) * sphericalIntegral (c * t) f x := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  rw [hpull]
  have e : ∫ x : Space 3, phase (inner ℝ x ξ) * sphericalIntegral (c * t) f x =
      ((4 * Real.pi * Real.sin (2 * Real.pi * (c * t) * ‖ξ‖) /
        (2 * Real.pi * (c * t) * ‖ξ‖) : ℝ) : ℂ) *
        ∫ x : Space 3, phase (inner ℝ x ξ) * f x := h
  rw [e, ← mul_assoc]
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hnc : ((‖ξ‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  push_cast
  field_simp

/-! ## B. Light-cone support for positive time -/

lemma sphericalIntegral_eq_zero_of_forall {r : ℝ} {f : Space 3 → ℂ} {x : Space 3}
    (h : ∀ n : Sph, f (x + r • n.1) = 0) : sphericalIntegral r f x = 0 := by
  unfold sphericalIntegral
  have : (fun n : Sph => f (x + r • n.1)) = fun _ => 0 := funext h
  rw [this, integral_zero]

/-- **Finite propagation speed.** If `f` vanishes outside the ball of radius `ρ` about `x₀`, then
`S_t f` vanishes at every point farther than `ρ + c t` from `x₀`. -/
lemma wavePropagator_eq_zero_of_far_of_pos {c t ρ : ℝ} (hc : 0 < c) (ht : 0 < t) {f : Space 3 → ℂ}
    {x₀ : Space 3} (hf : ∀ y, ρ < ‖y - x₀‖ → f y = 0) {x : Space 3}
    (hx : ρ + c * t < ‖x - x₀‖) : wavePropagator c t f x = 0 := by
  unfold wavePropagator
  rw [sphericalIntegral_eq_zero_of_forall, mul_zero]
  intro n
  apply hf
  have hn : ‖n.1‖ = 1 := by simp
  have h1 : ‖(c * t) • n.1‖ = c * t := by
    rw [norm_smul, hn, mul_one, Real.norm_eq_abs, abs_of_pos (mul_pos hc ht)]
  have h2 : x + (c * t) • n.1 - x₀ = (x - x₀) + (c * t) • n.1 := by abel
  have h3 : ‖x - x₀‖ ≤ ‖(x - x₀) + (c * t) • n.1‖ + ‖(c * t) • n.1‖ := by
    calc ‖x - x₀‖ = ‖((x - x₀) + (c * t) • n.1) - (c * t) • n.1‖ := by rw [add_sub_cancel_right]
      _ ≤ _ := norm_sub_le _ _
  rw [h2]
  linarith

/-- **Strong Huygens principle.** If `f` vanishes outside the ball of radius `ρ` about `x₀`, then
`S_t f` vanishes at every point `x` with `‖x - x₀‖ + ρ < c t`. -/
lemma wavePropagator_eq_zero_of_near_of_pos {c t ρ : ℝ} (hc : 0 < c) (ht : 0 < t) {f : Space 3 → ℂ}
    {x₀ : Space 3} (hf : ∀ y, ρ < ‖y - x₀‖ → f y = 0) {x : Space 3}
    (hx : ‖x - x₀‖ + ρ < c * t) : wavePropagator c t f x = 0 := by
  unfold wavePropagator
  rw [sphericalIntegral_eq_zero_of_forall, mul_zero]
  intro n
  apply hf
  have hn : ‖n.1‖ = 1 := by simp
  have h1 : ‖(c * t) • n.1‖ = c * t := by
    rw [norm_smul, hn, mul_one, Real.norm_eq_abs, abs_of_pos (mul_pos hc ht)]
  have h2 : x + (c * t) • n.1 - x₀ = (x - x₀) + (c * t) • n.1 := by abel
  have h3 : ‖(c * t) • n.1‖ ≤ ‖(x - x₀) + (c * t) • n.1‖ + ‖x - x₀‖ := by
    calc ‖(c * t) • n.1‖ = ‖((x - x₀) + (c * t) • n.1) - (x - x₀)‖ := by rw [add_sub_cancel_left]
      _ ≤ _ := norm_sub_le _ _
  rw [h2]
  linarith

/-! ## C. Two-sided time -/

/-- The spherical integral over the sphere of radius `-r` equals the one over radius `r`. -/
lemma sphericalIntegral_neg (r : ℝ) (f : Space 3 → ℂ) (x : Space 3) :
    sphericalIntegral (-r) f x = sphericalIntegral r f x := by
  unfold sphericalIntegral
  let U : Space 3 ≃ₗᵢ[ℝ] Space 3 := LinearIsometryEquiv.neg ℝ
  have hmp := sphereEquiv_measurePreserving U
  have h := hmp.integral_comp (sphereEquiv U).measurableEmbedding
    (fun n : Sph => f (x + r • n.1))
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
  simp [sphereEquiv_coe, U]

/-- The wave propagator vanishes at time zero. -/
lemma wavePropagator_zero (c : ℝ) (f : Space 3 → ℂ) (x : Space 3) : wavePropagator c 0 f x = 0 := by
  simp [wavePropagator]

/-- The wave propagator is odd in time. -/
lemma wavePropagator_neg (c t : ℝ) (f : Space 3 → ℂ) (x : Space 3) :
    wavePropagator c (-t) f x = -wavePropagator c t f x := by
  unfold wavePropagator
  have : c * -t = -(c * t) := by ring
  rw [this, sphericalIntegral_neg]
  push_cast
  ring

/-- The wave propagator at `(t, x)` reads the data only on the sphere `‖y - x‖ = c |t|`, where the
light cone of `(t, x)` meets the initial time. Data that agree there give the same field. -/
lemma wavePropagator_eq_of_eq_on_sphere {c t : ℝ} (hc : 0 < c) {f g : Space 3 → ℂ}
    {x : Space 3} (h : ∀ y, ‖y - x‖ = c * |t| → f y = g y) :
    wavePropagator c t f x = wavePropagator c t g x := by
  unfold wavePropagator sphericalIntegral
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
  apply h
  have hn : ‖n.1‖ = 1 := by simp
  simp [norm_smul, hn, abs_of_pos hc]

/-- **Finite propagation speed** for both signs of time. -/
lemma wavePropagator_eq_zero_of_far {c t ρ : ℝ} (hc : 0 < c) {f : Space 3 → ℂ}
    {x₀ : Space 3} (hf : ∀ y, ρ < ‖y - x₀‖ → f y = 0) {x : Space 3}
    (hx : ρ + c * |t| < ‖x - x₀‖) : wavePropagator c t f x = 0 := by
  rcases lt_trichotomy t 0 with h | h | h
  · have := wavePropagator_neg c (-t) f x
    rw [neg_neg] at this
    rw [this, wavePropagator_eq_zero_of_far_of_pos hc (neg_pos.mpr h) hf
      (by rwa [abs_of_neg h] at hx), neg_zero]
  · subst h; exact wavePropagator_zero c f x
  · exact wavePropagator_eq_zero_of_far_of_pos hc h hf (by rwa [abs_of_pos h] at hx)

/-- **Strong Huygens principle** for both signs of time. -/
lemma wavePropagator_eq_zero_of_near {c t ρ : ℝ} (hc : 0 < c) {f : Space 3 → ℂ}
    {x₀ : Space 3} (hf : ∀ y, ρ < ‖y - x₀‖ → f y = 0) {x : Space 3}
    (hx : ‖x - x₀‖ + ρ < c * |t|) : wavePropagator c t f x = 0 := by
  rcases lt_trichotomy t 0 with h | h | h
  · have := wavePropagator_neg c (-t) f x
    rw [neg_neg] at this
    rw [this, wavePropagator_eq_zero_of_near_of_pos hc (neg_pos.mpr h) hf
      (by rwa [abs_of_neg h] at hx), neg_zero]
  · subst h; exact wavePropagator_zero c f x
  · exact wavePropagator_eq_zero_of_near_of_pos hc h hf (by rwa [abs_of_pos h] at hx)

/-- The Fourier multiplier of the wave propagator for both signs of time. -/
lemma wavePropagator_fourier (f : 𝓢(Space 3, ℂ)) {c t : ℝ} (hc : 0 < c) {ξ : Space 3}
    (hξ : ξ ≠ 0) :
    ∫ x : Space 3, phase (inner ℝ x ξ) * wavePropagator c t f x =
      ((Real.sin (2 * Real.pi * c * ‖ξ‖ * t) / (2 * Real.pi * c * ‖ξ‖) : ℝ) : ℂ) *
        ∫ x : Space 3, phase (inner ℝ x ξ) * f x := by
  rcases lt_trichotomy t 0 with h | h | h
  · have h1 := wavePropagator_fourier_of_pos f hc (neg_pos.mpr h) hξ
    have e : ∀ x, wavePropagator c t f x = -wavePropagator c (-t) f x := fun x => by
      rw [wavePropagator_neg, neg_neg]
    simp_rw [e, mul_neg]
    rw [integral_neg, h1]
    have : 2 * Real.pi * c * ‖ξ‖ * -t = -(2 * Real.pi * c * ‖ξ‖ * t) := by ring
    rw [this, Real.sin_neg, neg_div]
    push_cast
    ring
  · subst h
    simp [wavePropagator_zero]
  · exact wavePropagator_fourier_of_pos f hc h hξ

/-! ## D. The free three-dimensional propagator -/

/-- **Kirchhoff's formula.** For `c > 0` and every real `t` the wave propagator has the Fourier
multiplier `sin(ω t) / ω`, propagates at speed at most `c` and satisfies the strong Huygens
principle. -/
lemma wavePropagator_isWavePropagator {c : ℝ} (hc : 0 < c) (t : ℝ) :
    IsWavePropagator c t (wavePropagator c t) :=
  { multiplier := fun f _ hξ => wavePropagator_fourier f hc hξ
    finiteSpeed := fun _ _ _ hf _ hx => wavePropagator_eq_zero_of_far hc hf hx
    huygens := fun _ _ _ hf _ hx => wavePropagator_eq_zero_of_near hc hf hx }

/-- The wave propagator is `t M_{ct}` with the normalized sphere mean. -/
lemma wavePropagator_eq_time_sphericalMean (c t : ℝ) (f : Space 3 → ℂ) (x : Space 3) :
    wavePropagator c t f x = (t : ℂ) * sphericalMean (c * t) f x := by
  unfold wavePropagator sphericalMean
  push_cast
  ring

end WaveEquation.Kirchhoff
