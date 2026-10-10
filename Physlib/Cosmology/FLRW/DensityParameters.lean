/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philippe Kevorkian, Jinzheng Li
-/
module

public import Physlib.Cosmology.FLRW.MatterContent
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
/-!

# Density parameters and the standard cosmological model

## i. Overview

The first-order Friedmann equation of `Physlib.Cosmology.FLRW.Basic`,
`H² = (8 π G / 3) ρ - k c² / a² + Λ c² / 3`, can be read as a budget for the expansion rate `H`.

The reference quantity is the critical density `ρ_cr = 3 H² / (8 π G)`. It is the mass density
for which this equation holds with `k = 0` and `Λ = 0`: the density of a spatially flat universe
without cosmological constant expanding at the rate `H`. It is called critical because, when
`Λ = 0`, a universe denser than `ρ_cr` is spatially closed (`k > 0`), a less dense one is open
(`k < 0`), and a universe at exactly `ρ_cr` is flat. It depends on time through `H`.

Each term of the equation is then measured in units of `ρ_cr`, which gives dimensionless
quantities:
- the density parameter `Ω = ρ / ρ_cr` of a component of mass density `ρ`;
- the cosmological-constant density parameter `Ω_Λ = Λ c² / (3 H²)`, which is the density
  parameter of the uniform density `ρ_Λ = Λ c² / (8 π G)` equivalent to `Λ`;
- the curvature density parameter `Ω_K = - k c² / (H² a²)`, which is not the density of a fluid
  but the share of the budget carried by spatial curvature.

Dividing the Friedmann equation by `H²` gives the closure relation `Ω + Ω_Λ + Ω_K = 1`.

For a universe made of matter (`ρ ∝ a⁻³`) and radiation (`ρ ∝ a⁻⁴`), the Hubble parameter at
any time is `H = H₀ E(a / a₀)` with the reduced Hubble function
`E(x)² = Ω_Λ + Ω_m x⁻³ + Ω_r x⁻⁴ + Ω_K x⁻²` of the standard cosmological model, the density
parameters being evaluated at the reference time `t₀`: each term is the share of one component
at the reference time, diluted by its own power of the scale factor. The age of the universe is
`t₀ = H₀⁻¹ ∫₀¹ dx / (x E(x))`, proportional to `1 / H₀`.

## ii. Key results

- `criticalDensity`, `densityParameter`, `curvatureDensityParameter`, `lambdaDensityParameter`.
- `densityParameter_add_lambda_add_curvature`: the closure relation `Ω + Ω_Λ + Ω_K = 1`;
  `densityParameter_add_curvature`: `Ω + Ω_K = 1` when `Λ = 0`.
- `reducedHubble`: the reduced Hubble function of the standard model;
  `sq_hubbleConstant_eq_reducedHubble`, `hubbleConstant_eq_reducedHubble`: `H = H₀ E(a / a₀)`
  for matter and radiation obeying their scaling laws.
- `age`: `t₀ = H₀⁻¹ ∫₀¹ dx / (x E(x))`; `age_eq`: `t₀ ∝ 1 / H₀`.
- `equalityScaleFactorRadiationMatter`, `equalityScaleFactorMatterLambda` and the equalities
  they realise.

## iii. Table of contents

- A. The critical density and the density parameters
- B. The closure relation
- C. The reduced Hubble function of the standard model
- D. The age of the universe
- E. The equality scale factors

-/

@[expose] public section

namespace Cosmology.FLRW.FriedmannEquation

open Real Time

/-!

## A. The critical density and the density parameters

-/

/-- The critical density `ρ_cr = 3 H² / (8 π G)`: the mass density for which the first-order
  Friedmann equation holds with `k = 0` and `Λ = 0` at the expansion rate `H`, that is, the
  density of a spatially flat universe without cosmological constant. It is the unit in which
  the density parameters are measured, and it depends on time through `H`. -/
noncomputable def criticalDensity (a : Time → ℝ) (G : ℝ) (t : Time) : ℝ :=
  3 * hubbleConstant a t ^ 2 / (8 * π * G)

/-- The density parameter `Ω = ρ / ρ_cr`: the mass density `ρ` of a component in units of the
  critical density. It is dimensionless; without cosmological constant, a total density
  parameter equal to `1` corresponds to a spatially flat universe
  (see `densityParameter_add_curvature`). -/
noncomputable def densityParameter (a ρ : Time → ℝ) (G : ℝ) (t : Time) : ℝ :=
  ρ t / criticalDensity a G t

/-- The curvature density parameter `Ω_K = - k c² / (H² a²)`: the share of the first-order
  Friedmann equation carried by the spatial curvature `k`, in the same units as the density
  parameters. It is not the density of a fluid; it is positive for `k < 0`, negative for
  `k > 0` and zero for a spatially flat universe. -/
noncomputable def curvatureDensityParameter (a : Time → ℝ) (k c : ℝ) (t : Time) : ℝ :=
  -k * c ^ 2 / (hubbleConstant a t ^ 2 * a t ^ 2)

/-- The cosmological-constant density parameter `Ω_Λ = Λ c² / (3 H²)`: the share of the
  first-order Friedmann equation carried by the cosmological constant. It is the density
  parameter of the uniform density `ρ_Λ = Λ c² / (8 π G)` (see `lambdaDensityParameter_eq`). -/
noncomputable def lambdaDensityParameter (a : Time → ℝ) (Λ c : ℝ) (t : Time) : ℝ :=
  Λ * c ^ 2 / (3 * hubbleConstant a t ^ 2)

/-- `Ω_Λ` is the density parameter of the fluid `ρ_Λ = Λ c² / (8 π G)`. -/
lemma lambdaDensityParameter_eq {a : Time → ℝ} {Λ G c : ℝ} {t : Time} (hG : G ≠ 0) :
    lambdaDensityParameter a Λ c t
      = densityParameter a (fun _ => cosmologicalConstantDensity Λ G c) G t := by
  unfold lambdaDensityParameter densityParameter criticalDensity cosmologicalConstantDensity
  have hπ := Real.pi_ne_zero
  field_simp

/-!

## B. The closure relation

-/

/-- The closure relation `Ω + Ω_Λ + Ω_K = 1`, a rearrangement of the first-order Friedmann
  equation, for `H ≠ 0`. -/
lemma densityParameter_add_lambda_add_curvature {a ρ : Time → ℝ} {k Λ G c : ℝ} {t : Time}
    (ha : a t ≠ 0) (hH : hubbleConstant a t ≠ 0)
    (hF1 : FirstOrderFriedmann a ρ k Λ G c t) :
    densityParameter a ρ G t + lambdaDensityParameter a Λ c t
      + curvatureDensityParameter a k c t = 1 := by
  unfold densityParameter lambdaDensityParameter curvatureDensityParameter criticalDensity
  unfold FirstOrderFriedmann at hF1
  unfold hubbleConstant at hH ⊢
  have hπ := Real.pi_ne_zero
  have key : ρ t / (3 * (∂ₜ a t / a t) ^ 2 / (8 * π * G)) + Λ * c ^ 2 / (3 * (∂ₜ a t / a t) ^ 2)
      + -k * c ^ 2 / ((∂ₜ a t / a t) ^ 2 * a t ^ 2)
      = (8 * π * G / 3 * ρ t - k * c ^ 2 / a t ^ 2 + Λ * c ^ 2 / 3) / (∂ₜ a t / a t) ^ 2 := by
    field_simp
    ring
  rw [key, ← hF1, div_self (pow_ne_zero 2 hH)]

/-- The closure relation `Ω + Ω_K = 1` without cosmological constant. -/
lemma densityParameter_add_curvature {a ρ : Time → ℝ} {k G c : ℝ} {t : Time} (ha : a t ≠ 0)
    (hH : hubbleConstant a t ≠ 0) (hF1 : FirstOrderFriedmann a ρ k 0 G c t) :
    densityParameter a ρ G t + curvatureDensityParameter a k c t = 1 := by
  have h := densityParameter_add_lambda_add_curvature ha hH hF1
  have h0 : lambdaDensityParameter a 0 c t = 0 := by
    unfold lambdaDensityParameter
    ring
  rw [h0, add_zero] at h
  exact h

/-!

## C. The reduced Hubble function of the standard model

-/

/-- The reduced Hubble function `E(x) = √(Ω_Λ + Ω_m x⁻³ + Ω_r x⁻⁴ + Ω_K x⁻²)` of the standard
  cosmological model: the Hubble parameter in units of its value `H₀` at the reference time,
  as a function of the scale factor `x = a / a₀` in units of its reference value. The four
  terms are the shares of the cosmological constant, matter, radiation and curvature at the
  reference time, each diluted by its own power of `x`. -/
noncomputable def reducedHubble (ΩΛ Ωm Ωr ΩK x : ℝ) : ℝ :=
  √(ΩΛ + Ωm * x ^ (-3 : ℝ) + Ωr * x ^ (-4 : ℝ) + ΩK * x ^ (-2 : ℝ))

/-- The argument of the square root in `reducedHubble`, for a universe of matter and radiation
  obeying their scaling laws, equals `H² / H₀²`: the normalised Friedmann equation. -/
lemma sq_hubbleConstant_eq_mul_reducedHubbleSq {a ρm ρr : Time → ℝ} {k Λ G c : ℝ}
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
  have key := sq_hubbleConstant_eq_mul_reducedHubbleSq hapos hH₀ hm hr hF1
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

## D. The age of the universe

-/

/-- The age of the universe `t₀ = H₀⁻¹ ∫₀¹ dx / (x E(x))` for a reduced Hubble function `E`:
  the time elapsed since `a = 0`, obtained by integrating `dt = da / (a H)` with
  `H = H₀ E(a / a₀)` (interval integral; no convergence is asserted here). -/
noncomputable def age (H₀ : ℝ) (E : ℝ → ℝ) : ℝ :=
  (1 / H₀) * ∫ x in (0 : ℝ)..1, 1 / (x * E x)

/-- The age is proportional to `1 / H₀`. -/
lemma age_eq (H₀ : ℝ) (E : ℝ → ℝ) : age H₀ E = (1 / H₀) * age 1 E := by
  unfold age
  ring

/-!

## E. The equality scale factors

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
