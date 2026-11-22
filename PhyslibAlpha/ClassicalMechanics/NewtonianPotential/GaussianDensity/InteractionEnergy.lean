/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.ClassicalMechanics.NewtonianPotential.GaussianDensity.Basic
public import PhyslibAlpha.ClassicalMechanics.NewtonianPotential.InteractionEnergy

/-!
# The gravitational interaction energy of Gaussian mass densities

## i. Overview

The Newtonian gravitational interaction energy of two Gaussian mass densities of masses `m₁`,
`m₂` and widths `σ₁`, `σ₂` centred at `a` and `b` is
`W = -(2 G m₁ m₂ / √π) ∫₀^T exp (-‖a - b‖² t²) dt` with `T = 1 / √(2 (σ₁² + σ₂²))`.
Up to the notation this is the error-function formula `-G m₁ m₂ erf (‖a - b‖ T) / ‖a - b‖`.

Two consequences are the self-interaction energy `-G m² / (√π σ)` of a single Gaussian density
and the interaction energy of the difference of two copies of the same density at two places
with itself.

## ii. Key results

- `integral_rpow_mul_rpow_mul_exp` : the radial integral of the Gaussian superposition.
- `interactionEnergy_gaussianDensity` : the interaction energy of two Gaussian densities.
- `interactionEnergy_gaussianDensity_self` : the self-interaction energy of a Gaussian density.
- `interactionEnergy_sub_sub_gaussianDensity` : the interaction energy of the difference of two
  displaced copies with itself.

## iii. Table of contents

- A. The radial integral
- B. The interaction energy

## iv. References

- None.
-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.NewtonianPotential

open MeasureTheory Space Physlib Distribution Set
open scoped SchwartzMap

/-!

## A. The radial integral

-/

open Filter Topology in
/-- The radial integral of the Gaussian superposition in closed form. -/
lemma integral_rpow_mul_rpow_mul_exp {κ : ℝ} (hκ : 0 < κ) (d : ℝ) :
    ∫ s in Ioi (0 : ℝ), s ^ (-(1 / 2 : ℝ)) *
        ((1 / (1 + κ * s)) ^ (3 / 2 : ℝ) * Real.exp (-(s / (1 + κ * s) * d ^ 2))) =
      2 * ∫ t in (0 : ℝ)..(1 / Real.sqrt κ), Real.exp (-(d ^ 2 * t ^ 2)) := by
  let Φ : ℝ → ℝ := fun u => ∫ t in (0 : ℝ)..u, Real.exp (-(d ^ 2 * t ^ 2))
  let v : ℝ → ℝ := fun s => Real.sqrt (s / (1 + κ * s))
  have hfc : Continuous (fun t : ℝ => Real.exp (-(d ^ 2 * t ^ 2))) := by fun_prop
  have hΦ : ∀ u, HasDerivAt Φ (Real.exp (-(d ^ 2 * u ^ 2))) u := fun u =>
    (hfc.integral_hasStrictDerivAt 0 u).hasDerivAt
  have hA : ∀ s : ℝ, 0 ≤ s → 0 < 1 + κ * s := fun s hs => by positivity
  have hv : ∀ s : ℝ, 0 < s →
      HasDerivAt v (1 / (1 + κ * s) ^ 2 / (2 * Real.sqrt (s / (1 + κ * s)))) s := by
    intro s hs
    have hq : HasDerivAt (fun s : ℝ => s / (1 + κ * s)) (1 / (1 + κ * s) ^ 2) s := by
      have h1 : HasDerivAt (fun s : ℝ => 1 + κ * s) κ s := by
        simpa using ((hasDerivAt_id' s).const_mul κ).const_add 1
      have h2 := (hasDerivAt_id' s).div h1 (hA s hs.le).ne'
      convert h2 using 1
      field_simp
      ring
    exact hq.sqrt (div_pos hs (hA s hs.le)).ne'
  have hderiv : ∀ s ∈ Ioi (0 : ℝ), HasDerivAt (fun s => 2 * Φ (v s))
      (s ^ (-(1 / 2 : ℝ)) *
        ((1 / (1 + κ * s)) ^ (3 / 2 : ℝ) * Real.exp (-(s / (1 + κ * s) * d ^ 2)))) s := by
    intro s hs
    have hs' : 0 < s := hs
    have hApos := hA s hs'.le
    have h : HasDerivAt (fun s => 2 * Φ (v s)) (2 * (Real.exp (-(d ^ 2 * v s ^ 2)) *
        (1 / (1 + κ * s) ^ 2 / (2 * Real.sqrt (s / (1 + κ * s)))))) s :=
      ((hΦ (v s)).comp s (hv s hs')).const_mul 2
    convert h using 1
    have hv2 : v s ^ 2 = s / (1 + κ * s) := Real.sq_sqrt (div_pos hs' hApos).le
    have hs1 : s ^ (-(1 / 2 : ℝ)) = (Real.sqrt s)⁻¹ := by
      rw [Real.rpow_neg hs'.le, ← Real.sqrt_eq_rpow]
    have hA1 : (1 / (1 + κ * s)) ^ (3 / 2 : ℝ) =
        1 / (1 + κ * s) * (Real.sqrt (1 + κ * s))⁻¹ := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by positivity), Real.rpow_one,
        ← Real.sqrt_eq_rpow, one_div, Real.sqrt_inv]
    have hq : Real.sqrt (s / (1 + κ * s)) = Real.sqrt s / Real.sqrt (1 + κ * s) :=
      Real.sqrt_div hs'.le _
    rw [hv2, hs1, hA1, hq, mul_comm (d ^ 2)]
    have ha : 0 < Real.sqrt s := Real.sqrt_pos.2 hs'
    have hb : 0 < Real.sqrt (1 + κ * s) := Real.sqrt_pos.2 hApos
    have hA' : 1 + κ * s = Real.sqrt (1 + κ * s) ^ 2 := (Real.sq_sqrt hApos.le).symm
    generalize Real.sqrt (1 + κ * s) = b at *
    generalize Real.sqrt s = a at *
    rw [hA']
    field_simp
  have hv0 : v 0 = 0 := by simp [v]
  have hcont : ContinuousWithinAt (fun s => 2 * Φ (v s)) (Ici 0) 0 := by
    have hvc : ContinuousAt v 0 := by
      have : ContinuousAt (fun s : ℝ => s / (1 + κ * s)) 0 :=
        continuousAt_id.div (by fun_prop) (by simp)
      exact this.sqrt
    have hΦc : ContinuousAt Φ (v 0) := (hΦ (v 0)).continuousAt
    exact ((hΦc.comp hvc).const_mul 2).continuousWithinAt
  have hlim : Tendsto (fun s => 2 * Φ (v s)) atTop (𝓝 (2 * Φ (1 / Real.sqrt κ))) := by
    have hq : Tendsto (fun s : ℝ => s / (1 + κ * s)) atTop (𝓝 (1 / κ)) := by
      have h0 : Tendsto (fun s : ℝ => (s⁻¹ + κ)⁻¹) atTop (𝓝 ((0 + κ)⁻¹)) :=
        ((tendsto_inv_atTop_zero.add_const κ).inv₀ (by simpa using hκ.ne'))
      rw [zero_add, ← one_div] at h0
      refine h0.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with s hs
      field_simp
    have hvl : Tendsto v atTop (𝓝 (1 / Real.sqrt κ)) := by
      have := (Real.continuous_sqrt.tendsto (1 / κ)).comp hq
      rwa [one_div, Real.sqrt_inv, ← one_div] at this
    exact ((hΦ _).continuousAt.tendsto.comp hvl).const_mul 2
  have hmain := integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv
    (fun s hs => by
      have hs' : (0 : ℝ) < s := hs
      have := hA s hs'.le
      positivity) hlim
  rw [hmain, hv0]
  simp [Φ]

/-!

## B. The interaction energy

-/

/-- The gravitational interaction energy of two Gaussian mass densities. -/
lemma interactionEnergy_gaussianDensity (G m₁ m₂ : ℝ) {σ₁ σ₂ : ℝ} (h₁ : 0 < σ₁) (h₂ : 0 < σ₂)
    (a b : Space 3) :
    interactionEnergy G (gaussianDensity m₁ h₁ a) (gaussianDensity m₂ h₂ b) =
      -(2 * G * m₁ * m₂ / Real.sqrt Real.pi) *
        ∫ t in (0 : ℝ)..(1 / Real.sqrt (2 * (σ₁ ^ 2 + σ₂ ^ 2))),
          Real.exp (-(‖a - b‖ ^ 2 * t ^ 2)) := by
  set ρ₁ := gaussianDensity m₁ h₁ a with hρ₁
  set ρ₂ := gaussianDensity m₂ h₂ b with hρ₂
  have hκ : 0 < 2 * (σ₁ ^ 2 + σ₂ ^ 2) := by positivity
  have hπ : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  rw [interactionEnergy_eq_integral_integral]
  have hint := integrable_prod_mul_mul_inv_norm_sub ρ₁ ρ₂
  have h := integral_prod (fun p : Space 3 × Space 3 => ρ₁ p.1 * (ρ₂ p.2 * ‖p.1 - p.2‖⁻¹)) hint
  have e : ∫ x, ∫ y, ρ₁ x * (ρ₂ y * ‖x - y‖⁻¹) =
      ∫ p : Space 3 × Space 3, ρ₁ p.1 * ρ₂ p.2 * ‖p.1 - p.2‖⁻¹ := by
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only
    ring
  have hrep := sqrt_pi_mul_integral_mul_mul_inv_norm_sub ρ₁ ρ₂
  have hs : ∫ s in Ioi (0 : ℝ), s ^ (-(1 / 2 : ℝ)) *
      ∫ p : Space 3 × Space 3, ρ₁ p.1 * ρ₂ p.2 * Real.exp (-(s * ‖p.1 - p.2‖ ^ 2)) =
      m₁ * m₂ * (2 * ∫ t in (0 : ℝ)..(1 / Real.sqrt (2 * (σ₁ ^ 2 + σ₂ ^ 2))),
        Real.exp (-(‖a - b‖ ^ 2 * t ^ 2))) := by
    rw [← integral_rpow_mul_rpow_mul_exp hκ ‖a - b‖, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    rw [hρ₁, hρ₂, integral_gaussianDensity_mul_gaussianDensity_mul_exp m₁ m₂ h₁ h₂ a b hs]
    ring
  rw [hs] at hrep
  have hD : ∫ p : Space 3 × Space 3, ρ₁ p.1 * ρ₂ p.2 * ‖p.1 - p.2‖⁻¹ =
      (Real.sqrt Real.pi)⁻¹ * (m₁ * m₂ *
        (2 * ∫ t in (0 : ℝ)..(1 / Real.sqrt (2 * (σ₁ ^ 2 + σ₂ ^ 2))),
          Real.exp (-(‖a - b‖ ^ 2 * t ^ 2)))) := by
    rw [← hrep, inv_mul_cancel_left₀ hπ.ne']
  rw [e, hD]
  field_simp

/-- The gravitational self-interaction energy of a Gaussian mass density of mass `m` and
width `σ` is `-G m² / (√π σ)`. -/
lemma interactionEnergy_gaussianDensity_self (G m : ℝ) {σ : ℝ} (hσ : 0 < σ) (a : Space 3) :
    interactionEnergy G (gaussianDensity m hσ a) (gaussianDensity m hσ a) =
      -(G * m ^ 2 / (Real.sqrt Real.pi * σ)) := by
  rw [interactionEnergy_gaussianDensity]
  have hT : Real.sqrt (2 * (σ ^ 2 + σ ^ 2)) = 2 * σ := by
    rw [show 2 * (σ ^ 2 + σ ^ 2) = (2 * σ) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hπ : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    zero_mul, neg_zero, Real.exp_zero, intervalIntegral.integral_const, sub_zero, smul_eq_mul,
    mul_one, hT]
  field_simp

/-- The interaction energy of the difference of two copies of a Gaussian mass density, centred
at `a` and at `b`, with itself. -/
lemma interactionEnergy_sub_sub_gaussianDensity (G m : ℝ) {σ : ℝ} (hσ : 0 < σ) (a b : Space 3) :
    interactionEnergy G (gaussianDensity m hσ a - gaussianDensity m hσ b)
        (gaussianDensity m hσ a - gaussianDensity m hσ b) =
      -(4 * G * m ^ 2 / Real.sqrt Real.pi) *
        ∫ t in (0 : ℝ)..(1 / (2 * σ)), (1 - Real.exp (-(‖a - b‖ ^ 2 * t ^ 2))) := by
  have hT : Real.sqrt (2 * (σ ^ 2 + σ ^ 2)) = 2 * σ := by
    rw [show 2 * (σ ^ 2 + σ ^ 2) = (2 * σ) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hπ : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hc : Continuous (fun t : ℝ => Real.exp (-(‖a - b‖ ^ 2 * t ^ 2))) := by fun_prop
  rw [interactionEnergy_sub_sub, interactionEnergy_gaussianDensity_self,
    interactionEnergy_gaussianDensity_self, interactionEnergy_gaussianDensity, hT,
    intervalIntegral.integral_sub (intervalIntegrable_const) (hc.intervalIntegrable _ _),
    intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul, mul_one]
  field_simp
  ring

end PhyslibAlpha.NewtonianPotential
