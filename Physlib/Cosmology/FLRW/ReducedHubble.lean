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

The reduced Hubble function of the standard cosmological model is
`E(x) = √(Ω_Λ + Ω_m x⁻³ + Ω_r x⁻⁴ + Ω_K x⁻²)`, with the density parameters of
`Physlib.Cosmology.FLRW.DensityParameters` taken at a reference time `t₀`. For an FLRW model
filled with matter (`ρ ∝ a⁻³`) and radiation (`ρ ∝ a⁻⁴`) that solves the Friedmann equations, the
Hubble parameter is `H = H₀ E(a / a₀)` with `H₀ = H(t₀) > 0` and `H ≥ 0`. The scaling laws of the
densities between `t₀` and `t` are hypotheses, not derived here.

The equality scale factors are the values of `x = a / a₀` at which two terms of `E²` are equal:
radiation and matter at `a_eq = Ω_r / Ω_m`, matter and cosmological constant at
`a_Λ = (Ω_m / Ω_Λ)^(1/3)`.

## ii. Key results

- `reducedHubble`: the reduced Hubble function of the standard model.
- `FLRW.FriedmannSolution.sq_hubbleConstant_eq_mul_densityParameters`: the normalised Friedmann
  equation `H² = H₀² (Ω_Λ + Ω_m x⁻³ + Ω_r x⁻⁴ + Ω_K x⁻²)` with `x = a / a₀`.
- `FLRW.FriedmannSolution.sq_hubbleConstant_eq_reducedHubble`,
  `FLRW.FriedmannSolution.hubbleConstant_eq_reducedHubble`: `H² = H₀² E(a / a₀)²` and
  `H = H₀ E(a / a₀)`.
- `equalityScaleFactorRadiationMatter`, `equalityScaleFactorMatterLambda` and the equalities
  they realise.

## iii. Table of contents

- A. The reduced Hubble function
- B. The equality scale factors
- C. The Hubble parameter of a solution of the Friedmann equations

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

/-!

## C. The Hubble parameter of a solution of the Friedmann equations

-/

namespace Cosmology.FLRW.FriedmannSolution

open Real Time FriedmannEquation

variable {U : FLRW} {F Fm Fr : CosmicFluid} {Λ G c : ℝ}

/-- For a solution of the Friedmann equations whose density is that of matter plus that of
  radiation, take two times `t` and `t₀` of the interval of the model with `H(t₀) ≠ 0` at which
  `ρ_m(t) = ρ_m(t₀) (a(t₀) / a(t))³` and `ρ_r(t) = ρ_r(t₀) (a(t₀) / a(t))⁴`. Then
  `H² = H₀² (Ω_Λ + Ω_m x⁻³ + Ω_r x⁻⁴ + Ω_K x⁻²)` with `x = a(t) / a(t₀)` and the density
  parameters taken at `t₀`. -/
lemma sq_hubbleConstant_eq_mul_densityParameters (h : U.FriedmannSolution F Λ G c)
    (hρ : ∀ s, F.ρ s = Fm.ρ s + Fr.ρ s) {t t₀ : Time} (ht : t ∈ U.I) (ht₀ : t₀ ∈ U.I)
    (hH₀ : hubbleConstant U.a t₀ ≠ 0)
    (hm : Fm.ρ t = Fm.ρ t₀ * (U.a t₀ / U.a t) ^ 3) (hr : Fr.ρ t = Fr.ρ t₀ * (U.a t₀ / U.a t) ^ 4) :
    hubbleConstant U.a t ^ 2 = hubbleConstant U.a t₀ ^ 2
      * (U.lambdaDensityParameter Λ c t₀ + U.densityParameter Fm G t₀ * (U.a t / U.a t₀) ^ (-3 : ℝ)
        + U.densityParameter Fr G t₀ * (U.a t / U.a t₀) ^ (-4 : ℝ)
        + U.curvatureDensityParameter c t₀ * (U.a t / U.a t₀) ^ (-2 : ℝ)) := by
  have hF1 := h.firstOrder t ht
  have hx : 0 < U.a t / U.a t₀ := div_pos (U.a_pos t ht) (U.a_pos t₀ ht₀)
  have hpow : ∀ j : ℕ, (U.a t / U.a t₀) ^ (-(j : ℝ)) = ((U.a t / U.a t₀) ^ j)⁻¹ := fun j => by
    rw [Real.rpow_neg hx.le, Real.rpow_natCast]
  rw [show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num,
    show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, hpow,
    hpow, hpow]
  unfold FirstOrderFriedmann at hF1
  rw [hρ t, hm, hr] at hF1
  unfold FLRW.lambdaDensityParameter FLRW.densityParameter FLRW.criticalDensity
    FLRW.curvatureDensityParameter
  unfold hubbleConstant at hH₀ ⊢
  rw [hF1]
  have hπ := Real.pi_ne_zero
  have ha := U.a_ne_zero ht
  have ha₀ := U.a_ne_zero ht₀
  have hd₀ : ∂ₜ U.a t₀ ≠ 0 := (div_ne_zero_iff.mp hH₀).1
  field_simp
  ring

/-- `H² = H₀² E(a / a₀)²`, under the hypotheses of
  `sq_hubbleConstant_eq_mul_densityParameters`. -/
lemma sq_hubbleConstant_eq_reducedHubble (h : U.FriedmannSolution F Λ G c)
    (hρ : ∀ s, F.ρ s = Fm.ρ s + Fr.ρ s) {t t₀ : Time} (ht : t ∈ U.I) (ht₀ : t₀ ∈ U.I)
    (hH₀ : hubbleConstant U.a t₀ ≠ 0)
    (hm : Fm.ρ t = Fm.ρ t₀ * (U.a t₀ / U.a t) ^ 3) (hr : Fr.ρ t = Fr.ρ t₀ * (U.a t₀ / U.a t) ^ 4) :
    hubbleConstant U.a t ^ 2 = hubbleConstant U.a t₀ ^ 2
      * reducedHubble (U.lambdaDensityParameter Λ c t₀) (U.densityParameter Fm G t₀)
        (U.densityParameter Fr G t₀) (U.curvatureDensityParameter c t₀) (U.a t / U.a t₀) ^ 2 := by
  have key := h.sq_hubbleConstant_eq_mul_densityParameters hρ ht ht₀ hH₀ hm hr
  have hnn : 0 ≤ U.lambdaDensityParameter Λ c t₀
      + U.densityParameter Fm G t₀ * (U.a t / U.a t₀) ^ (-3 : ℝ)
      + U.densityParameter Fr G t₀ * (U.a t / U.a t₀) ^ (-4 : ℝ)
      + U.curvatureDensityParameter c t₀ * (U.a t / U.a t₀) ^ (-2 : ℝ) := by
    have h2 : 0 < hubbleConstant U.a t₀ ^ 2 := by positivity
    have : 0 ≤ hubbleConstant U.a t ^ 2 := sq_nonneg _
    rw [key] at this
    exact nonneg_of_mul_nonneg_right (by linarith) h2
  unfold reducedHubble
  rw [Real.sq_sqrt hnn]
  exact key

/-- `H = H₀ E(a / a₀)` for `0 < H₀` and `0 ≤ H`, under the hypotheses of
  `sq_hubbleConstant_eq_reducedHubble`. -/
lemma hubbleConstant_eq_reducedHubble (h : U.FriedmannSolution F Λ G c)
    (hρ : ∀ s, F.ρ s = Fm.ρ s + Fr.ρ s) {t t₀ : Time} (ht : t ∈ U.I) (ht₀ : t₀ ∈ U.I)
    (hH₀ : 0 < hubbleConstant U.a t₀) (hH : 0 ≤ hubbleConstant U.a t)
    (hm : Fm.ρ t = Fm.ρ t₀ * (U.a t₀ / U.a t) ^ 3) (hr : Fr.ρ t = Fr.ρ t₀ * (U.a t₀ / U.a t) ^ 4) :
    hubbleConstant U.a t = hubbleConstant U.a t₀
      * reducedHubble (U.lambdaDensityParameter Λ c t₀) (U.densityParameter Fm G t₀)
        (U.densityParameter Fr G t₀) (U.curvatureDensityParameter c t₀) (U.a t / U.a t₀) := by
  have key := h.sq_hubbleConstant_eq_reducedHubble hρ ht ht₀ hH₀.ne' hm hr
  rw [← mul_pow] at key
  have hE : 0 ≤ reducedHubble (U.lambdaDensityParameter Λ c t₀) (U.densityParameter Fm G t₀)
      (U.densityParameter Fr G t₀) (U.curvatureDensityParameter c t₀) (U.a t / U.a t₀) :=
    Real.sqrt_nonneg _
  exact (pow_left_inj₀ hH (mul_nonneg hH₀.le hE) two_ne_zero).mp key

end Cosmology.FLRW.FriedmannSolution
