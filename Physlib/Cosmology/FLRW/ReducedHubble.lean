/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philippe Kevorkian, Jinzheng Li
-/
module

public import Physlib.Cosmology.FLRW.DensityParameters
/-!

# The reduced Hubble function of the standard cosmological model

## i. Overview

For a universe made of matter (`ρ ∝ a⁻³`) and radiation (`ρ ∝ a⁻⁴`), with a cosmological constant
and spatial curvature, the Hubble parameter at any time is `H = H₀ E(a / a₀)` with the reduced
Hubble function `E(x)² = Ω_Λ + Ω_m x⁻³ + Ω_r x⁻⁴ + Ω_K x⁻²` of the standard cosmological model.
The density parameters, defined in `Physlib.Cosmology.FLRW.DensityParameters`, are evaluated at
the reference time `t₀`: each term is the share of one component at the reference time, diluted
by its own power of the scale factor.

The equality scale factors are the values of `x = a / a₀` at which two terms of `E²` are equal:
radiation and matter at `a_eq = Ω_r / Ω_m`, matter and cosmological constant at
`a_Λ = (Ω_m / Ω_Λ)^(1/3)`.

## ii. Key results

- `reducedHubble`: the reduced Hubble function of the standard model.
- `sq_hubbleConstant_eq_mul_densityParameters`: the normalised Friedmann equation
  `H² = H₀² (Ω_Λ + Ω_m x⁻³ + Ω_r x⁻⁴ + Ω_K x⁻²)` with `x = a / a₀`.
- `sq_hubbleConstant_eq_reducedHubble`, `hubbleConstant_eq_reducedHubble`: `H = H₀ E(a / a₀)`
  for matter and radiation obeying their scaling laws.
- `equalityScaleFactorRadiationMatter`, `equalityScaleFactorMatterLambda` and the equalities
  they realise.

## iii. Table of contents

- A. The reduced Hubble function
- B. The equality scale factors

## iv. References

* None.

-/

@[expose] public section

namespace Cosmology.FLRW.FriedmannEquation

open Real Time

/-!

## A. The reduced Hubble function

-/

/-- The reduced Hubble function `E(x) = √(Ω_Λ + Ω_m x⁻³ + Ω_r x⁻⁴ + Ω_K x⁻²)` of the standard
  cosmological model: the Hubble parameter in units of its value `H₀` at the reference time,
  as a function of the scale factor `x = a / a₀` in units of its reference value. The four
  terms are the shares of the cosmological constant, matter, radiation and curvature at the
  reference time, each diluted by its own power of `x`. -/
noncomputable def reducedHubble (ΩΛ Ωm Ωr ΩK x : ℝ) : ℝ :=
  √(ΩΛ + Ωm * x ^ (-3 : ℝ) + Ωr * x ^ (-4 : ℝ) + ΩK * x ^ (-2 : ℝ))

/-- The normalised Friedmann equation `H² = H₀² (Ω_Λ + Ω_m x⁻³ + Ω_r x⁻⁴ + Ω_K x⁻²)` with
  `x = a / a₀`, for a universe of matter and radiation obeying their scaling laws. The sum on
  the right-hand side is the argument of the square root in `reducedHubble`. -/
lemma sq_hubbleConstant_eq_mul_densityParameters {a ρm ρr : Time → ℝ} {k Λ G c : ℝ}
    {t t₀ : Time} (hapos : ∀ s, 0 < a s) (hH₀ : hubbleConstant a t₀ ≠ 0)
    (hm : ρm t = ρm t₀ * (a t₀ / a t) ^ 3) (hr : ρr t = ρr t₀ * (a t₀ / a t) ^ 4)
    (hF1 : FirstOrderFriedmann a (fun s => ρm s + ρr s) k Λ G c t) :
    hubbleConstant a t ^ 2 = hubbleConstant a t₀ ^ 2
      * (lambdaDensityParameter a Λ c t₀ + densityParameter a ρm G t₀ * (a t / a t₀) ^ (-3 : ℝ)
        + densityParameter a ρr G t₀ * (a t / a t₀) ^ (-4 : ℝ)
        + curvatureDensityParameter a k c t₀ * (a t / a t₀) ^ (-2 : ℝ)) := by
  have hx : 0 < a t / a t₀ := div_pos (hapos t) (hapos t₀)
  have hpow : ∀ j : ℕ, (a t / a t₀) ^ (-(j : ℝ)) = ((a t / a t₀) ^ j)⁻¹ := fun j => by
    rw [Real.rpow_neg hx.le, Real.rpow_natCast]
  rw [show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num,
    show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, hpow,
    hpow, hpow]
  unfold FirstOrderFriedmann at hF1
  dsimp only at hF1
  rw [hm, hr] at hF1
  unfold lambdaDensityParameter densityParameter criticalDensity curvatureDensityParameter
  unfold hubbleConstant at hH₀ ⊢
  rw [hF1]
  have hπ := Real.pi_ne_zero
  have ha := (hapos t).ne'
  have ha₀ := (hapos t₀).ne'
  have hd₀ : ∂ₜ a t₀ ≠ 0 := (div_ne_zero_iff.mp hH₀).1
  field_simp
  ring

/-- `H² = H₀² E(a / a₀)²` for a universe of matter and radiation obeying their scaling laws
  (`Physlib.Cosmology.FLRW.MatterContent`), with cosmological constant and curvature. -/
lemma sq_hubbleConstant_eq_reducedHubble {a ρm ρr : Time → ℝ} {k Λ G c : ℝ} {t t₀ : Time}
    (hapos : ∀ s, 0 < a s) (hH₀ : hubbleConstant a t₀ ≠ 0)
    (hm : ρm t = ρm t₀ * (a t₀ / a t) ^ 3) (hr : ρr t = ρr t₀ * (a t₀ / a t) ^ 4)
    (hF1 : FirstOrderFriedmann a (fun s => ρm s + ρr s) k Λ G c t) :
    hubbleConstant a t ^ 2 = hubbleConstant a t₀ ^ 2
      * reducedHubble (lambdaDensityParameter a Λ c t₀) (densityParameter a ρm G t₀)
        (densityParameter a ρr G t₀) (curvatureDensityParameter a k c t₀) (a t / a t₀) ^ 2 := by
  have key := sq_hubbleConstant_eq_mul_densityParameters hapos hH₀ hm hr hF1
  have hnn : 0 ≤ lambdaDensityParameter a Λ c t₀
      + densityParameter a ρm G t₀ * (a t / a t₀) ^ (-3 : ℝ)
      + densityParameter a ρr G t₀ * (a t / a t₀) ^ (-4 : ℝ)
      + curvatureDensityParameter a k c t₀ * (a t / a t₀) ^ (-2 : ℝ) := by
    have h2 : 0 < hubbleConstant a t₀ ^ 2 := by positivity
    have : 0 ≤ hubbleConstant a t ^ 2 := sq_nonneg _
    rw [key] at this
    exact nonneg_of_mul_nonneg_right (by linarith) h2
  unfold reducedHubble
  rw [Real.sq_sqrt hnn]
  exact key

/-- `H = H₀ E(a / a₀)` for `H ≥ 0` and `H₀ > 0`. -/
lemma hubbleConstant_eq_reducedHubble {a ρm ρr : Time → ℝ} {k Λ G c : ℝ} {t t₀ : Time}
    (hapos : ∀ s, 0 < a s) (hH₀ : 0 < hubbleConstant a t₀)
    (hH : 0 ≤ hubbleConstant a t)
    (hm : ρm t = ρm t₀ * (a t₀ / a t) ^ 3) (hr : ρr t = ρr t₀ * (a t₀ / a t) ^ 4)
    (hF1 : FirstOrderFriedmann a (fun s => ρm s + ρr s) k Λ G c t) :
    hubbleConstant a t = hubbleConstant a t₀
      * reducedHubble (lambdaDensityParameter a Λ c t₀) (densityParameter a ρm G t₀)
        (densityParameter a ρr G t₀) (curvatureDensityParameter a k c t₀) (a t / a t₀) := by
  have key := sq_hubbleConstant_eq_reducedHubble hapos hH₀.ne' hm hr hF1
  rw [← mul_pow] at key
  have hE : 0 ≤ reducedHubble (lambdaDensityParameter a Λ c t₀) (densityParameter a ρm G t₀)
      (densityParameter a ρr G t₀) (curvatureDensityParameter a k c t₀) (a t / a t₀) :=
    Real.sqrt_nonneg _
  exact (pow_left_inj₀ hH (mul_nonneg hH₀.le hE) two_ne_zero).mp key

/-!

## B. The equality scale factors

-/

/-- The radiation-matter equality scale factor `a_eq = Ω_r / Ω_m`: the value of `x = a / a₀`
  at which the matter and radiation terms of `E²` are equal; radiation dominates before it. -/
noncomputable def equalityScaleFactorRadiationMatter (Ωr Ωm : ℝ) : ℝ := Ωr / Ωm

/-- The matter-Λ equality scale factor `a_Λ = (Ω_m / Ω_Λ)^(1/3)`: the value of `x = a / a₀`
  at which the matter term of `E²` equals `Ω_Λ`; the cosmological constant dominates after
  it. -/
noncomputable def equalityScaleFactorMatterLambda (Ωm ΩΛ : ℝ) : ℝ := (Ωm / ΩΛ) ^ (1 / 3 : ℝ)

/-- At `a_eq`, the matter and radiation terms of `E²` are equal. -/
lemma equalityScaleFactorRadiationMatter_spec {Ωr Ωm : ℝ} (hr : 0 < Ωr) (hm : 0 < Ωm) :
    Ωm * equalityScaleFactorRadiationMatter Ωr Ωm ^ (-3 : ℝ)
      = Ωr * equalityScaleFactorRadiationMatter Ωr Ωm ^ (-4 : ℝ) := by
  unfold equalityScaleFactorRadiationMatter
  have hx : 0 < Ωr / Ωm := div_pos hr hm
  have hpow : ∀ j : ℕ, (Ωr / Ωm) ^ (-(j : ℝ)) = ((Ωr / Ωm) ^ j)⁻¹ := fun j => by
    rw [Real.rpow_neg hx.le, Real.rpow_natCast]
  rw [show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num,
    hpow, hpow]
  field_simp

/-- At `a_Λ`, the matter term of `E²` equals `Ω_Λ`. -/
lemma equalityScaleFactorMatterLambda_spec {Ωm ΩΛ : ℝ} (hm : 0 < Ωm) (hL : 0 < ΩΛ) :
    Ωm * equalityScaleFactorMatterLambda Ωm ΩΛ ^ (-3 : ℝ) = ΩΛ := by
  unfold equalityScaleFactorMatterLambda
  have hy : 0 < Ωm / ΩΛ := div_pos hm hL
  rw [← Real.rpow_mul hy.le, show (1 / 3 : ℝ) * -3 = -1 by norm_num, Real.rpow_neg_one]
  field_simp

end Cosmology.FLRW.FriedmannEquation
