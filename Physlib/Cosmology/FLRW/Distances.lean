/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philippe Kevorkian, Jinzheng Li
-/
module

public import Physlib.Meta.TODO.Basic
public import Physlib.Cosmology.FLRW.SpecificCases.EinsteinDeSitter
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
/-!

# Distances and redshift in FLRW cosmology

## i. Overview

The distances of this file are defined for an FLRW model. They have their meaning at the times
of the interval of the model.

The comoving distance of a source emitting at the time `t` and observed at `t₀` is
`χ = c ∫_t^{t₀} dτ / a(τ)`, so that `∂ₜ χ = - c / a`. The redshift is `1 + z = a(t₀) / a(t)`,
with `∂ₜ z = -(1 + z) H`. Combining the two gives `∂ₜ χ = (c / (a(t₀) H)) ∂ₜ z`. For
`a(t₀) = 1`, this is the change of variables `dχ = c dz / H` behind the distance integrals in the
redshift.

The proper distance `D = a χ` obeys the Hubble-Lemaître law `∂ₜ D = H D`. The recession velocity
equals `c` exactly at the Hubble radius `R_H = c / H`.

The transverse comoving distance `r(χ)` is the function `S` of the spatial geometry of the model.
Its closed forms are written in the curvature parameter `K` of that geometry, with curvature
radius `1 / √|K|`.

The particle and event horizons at `t` integrate `c / a` over the times of the interval of the
model before and after `t`. The particle horizon of the Einstein-de Sitter model
`FLRW.einsteinDeSitter` is computed.

## ii. Key results

- `FLRW.comovingDistance`, `FLRW.deriv_comovingDistance`: `∂ₜ χ = - c / a`.
- `FLRW.redshift`, `FLRW.deriv_redshift`: `∂ₜ z = -(1 + z) H`.
- `FLRW.deriv_comovingDistance_eq_mul_deriv_redshift`: `∂ₜ χ = (c / (a(t₀) H)) ∂ₜ z`.
- `FLRW.properDistance`, `FLRW.deriv_properDistance`: the Hubble-Lemaître law.
- `FLRW.hubbleRadius`, `FLRW.deriv_properDistance_eq_iff`: the recession velocity at the Hubble
  radius.
- `FLRW.transverseComovingDistance` and its three closed forms.
- `FLRW.particleHorizon`, `FLRW.eventHorizon`, `FLRW.particleHorizon_einsteinDeSitter`.

## iii. Table of contents

- A. The comoving distance
- B. The redshift and the change of variables
- C. The proper distance and the Hubble radius
- D. The transverse comoving distance
- E. The horizons

-/

@[expose] public section

namespace Cosmology.FLRW

open Real Time FriedmannEquation

variable (U : FLRW)

/-!

## A. The comoving distance

-/

/-- The line-of-sight comoving distance `χ = c ∫_t^{t₀} dτ / a(τ)` of a source emitting at `t`
  and observed at `t₀`. -/
noncomputable def comovingDistance (c : ℝ) (t t₀ : Time) : ℝ :=
  c * ∫ τ in t.val..t₀.val, 1 / U.a ⟨τ⟩

/-- For `t` and `t₀` in the interval of the model, `∂ₜ χ = - c / a`. -/
lemma deriv_comovingDistance {c : ℝ} {t₀ t : Time} (ht₀ : t₀ ∈ U.I) (ht : t ∈ U.I) :
    ∂ₜ (fun s => U.comovingDistance c s t₀) t = -c / U.a t := by
  obtain ⟨τ⟩ := t
  have hS : IsOpen {σ : ℝ | (⟨σ⟩ : Time) ∈ U.I} := U.isOpen_I.preimage toRealCLE.symm.continuous
  have hf : ContinuousOn (fun σ : ℝ => 1 / U.a ⟨σ⟩) {σ : ℝ | (⟨σ⟩ : Time) ∈ U.I} :=
    continuousOn_const.div (U.differentiableOn_a.continuousOn.comp
      toRealCLE.symm.continuous.continuousOn fun _ h => h) fun _ h => U.a_ne_zero h
  have hsub : Set.uIcc τ t₀.val ⊆ {σ : ℝ | (⟨σ⟩ : Time) ∈ U.I} :=
    Set.OrdConnected.uIcc_subset (s := {σ : ℝ | (⟨σ⟩ : Time) ∈ U.I})
      ⟨fun _ hx _ hy _ hz => U.mk_mem_I_of_mem_Icc hx hy hz⟩ ht ht₀
  have h : HasDerivAt (fun σ : ℝ => ∫ x in σ..t₀.val, 1 / U.a ⟨x⟩) (-(1 / U.a ⟨τ⟩)) τ :=
    intervalIntegral.integral_hasDerivAt_left ((hf.mono hsub).intervalIntegrable)
      (hf.stronglyMeasurableAtFilter hS τ ht) (hf.continuousAt (hS.mem_nhds ht))
  refine deriv_eq_of_hasDerivAt ((h.const_mul c).congr_deriv ?_)
  ring

/-!

## B. The redshift and the change of variables

-/

/-- The redshift `z` of a source emitting at `t` and observed at `t₀`, with
  `1 + z = a(t₀) / a(t)`. -/
noncomputable def redshift (t₀ t : Time) : ℝ := U.a t₀ / U.a t - 1

lemma one_add_redshift (t₀ t : Time) : 1 + U.redshift t₀ t = U.a t₀ / U.a t := by
  unfold redshift
  ring

/-- For `t` in the interval of the model, `∂ₜ z = -(1 + z) H`. -/
lemma deriv_redshift {t₀ t : Time} (ht : t ∈ U.I) :
    ∂ₜ (U.redshift t₀) t = -(1 + U.redshift t₀ t) * hubbleConstant U.a t := by
  obtain ⟨τ⟩ := t
  have ha := U.a_ne_zero ht
  have hA := hasDerivAt_mk_of_differentiableAt (U.differentiableAt_a ht)
  have h := ((hasDerivAt_const τ (U.a t₀)).div hA ha).sub_const 1
  refine (deriv_eq_of_hasDerivAt (f := U.redshift t₀) h).trans ?_
  unfold redshift hubbleConstant
  field_simp
  ring

/-- For `t` in the interval of the model, `∂ₜ a = a H`. -/
lemma deriv_scaleFactor_eq_mul_hubbleConstant {t : Time} (ht : t ∈ U.I) :
    ∂ₜ U.a t = U.a t * hubbleConstant U.a t := by
  have ha := U.a_ne_zero ht
  unfold hubbleConstant
  field_simp

/-- For `t` and `t₀` in the interval of the model with `H(t) ≠ 0`,
  `∂ₜ χ = (c / (a(t₀) H)) ∂ₜ z`. For `a(t₀) = 1`, this is the change of variables
  `dχ = c dz / H`. -/
lemma deriv_comovingDistance_eq_mul_deriv_redshift {c : ℝ} {t₀ t : Time} (ht₀ : t₀ ∈ U.I)
    (ht : t ∈ U.I) (hH : hubbleConstant U.a t ≠ 0) :
    ∂ₜ (fun s => U.comovingDistance c s t₀) t
      = c / (U.a t₀ * hubbleConstant U.a t) * ∂ₜ (U.redshift t₀) t := by
  rw [U.deriv_comovingDistance ht₀ ht, U.deriv_redshift ht, one_add_redshift]
  have ha := U.a_ne_zero ht
  have ha₀ := U.a_ne_zero ht₀
  field_simp

/-!

## C. The proper distance and the Hubble radius

-/

/-- The proper distance `D = a χ` at fixed comoving distance `χ`. -/
noncomputable def properDistance (χ : ℝ) (t : Time) : ℝ := U.a t * χ

/-- The Hubble-Lemaître law `∂ₜ D = H D`, for `t` in the interval of the model. -/
lemma deriv_properDistance {χ : ℝ} {t : Time} (ht : t ∈ U.I) :
    ∂ₜ (U.properDistance χ) t = hubbleConstant U.a t * U.properDistance χ t := by
  obtain ⟨τ⟩ := t
  have ha := U.a_ne_zero ht
  have hA := hasDerivAt_mk_of_differentiableAt (U.differentiableAt_a ht)
  refine (deriv_eq_of_hasDerivAt (f := U.properDistance χ) (hA.mul_const χ)).trans ?_
  unfold hubbleConstant properDistance
  field_simp

/-- The Hubble radius `R_H = c / H`. -/
noncomputable def hubbleRadius (c : ℝ) (t : Time) : ℝ := c / hubbleConstant U.a t

/-- For `t` in the interval of the model with `H(t) ≠ 0`, the recession velocity `∂ₜ D` equals
  `c` exactly at the Hubble radius. -/
lemma deriv_properDistance_eq_iff {χ c : ℝ} {t : Time} (ht : t ∈ U.I)
    (hH : hubbleConstant U.a t ≠ 0) :
    ∂ₜ (U.properDistance χ) t = c ↔ U.properDistance χ t = U.hubbleRadius c t := by
  rw [U.deriv_properDistance ht, hubbleRadius, eq_div_iff hH]
  constructor <;> intro h <;> linarith [h]

/-!

## D. The transverse comoving distance

-/

/-- The transverse comoving distance `r(χ) = S(χ)` for the spatial geometry of an FLRW model. -/
noncomputable def transverseComovingDistance (χ : ℝ) : ℝ := U.geometry.S χ

/-- For a positive curvature parameter `K`, `r(χ) = (1 / √K) sin (√K χ)`. -/
lemma transverseComovingDistance_of_curvature_pos (hK : 0 < U.geometry.curvature) (χ : ℝ) :
    U.transverseComovingDistance χ
      = 1 / √U.geometry.curvature * Real.sin (√U.geometry.curvature * χ) := by
  unfold transverseComovingDistance
  generalize U.geometry = s at hK ⊢
  cases s with
  | Spherical k hk =>
    have hs : √(SpatialGeometry.Spherical k hk).curvature = -1 / k := by
      show √(1 / k ^ 2) = -1 / k
      rw [show (1 : ℝ) / k ^ 2 = (-1 / k) ^ 2 by ring]
      exact Real.sqrt_sq (div_nonneg_of_nonpos (by norm_num) hk.le)
    rw [hs]
    show k * Real.sin (χ / k) = 1 / (-1 / k) * Real.sin (-1 / k * χ)
    rw [show -1 / k * χ = -(χ / k) by ring, Real.sin_neg, one_div_div]
    ring
  | Flat => simp at hK
  | Saddle k hk => linarith [SpatialGeometry.curvature_saddle_neg k hk]

/-- For a zero curvature parameter, `r(χ) = χ`. -/
lemma transverseComovingDistance_of_curvature_eq_zero (hK : U.geometry.curvature = 0) (χ : ℝ) :
    U.transverseComovingDistance χ = χ := by
  unfold transverseComovingDistance
  generalize U.geometry = s at hK ⊢
  cases s with
  | Spherical k hk => exact absurd hK (SpatialGeometry.curvature_spherical_pos k hk).ne'
  | Flat => rfl
  | Saddle k hk => exact absurd hK (SpatialGeometry.curvature_saddle_neg k hk).ne

/-- For a negative curvature parameter `K`, `r(χ) = (1 / √(-K)) sinh (√(-K) χ)`. -/
lemma transverseComovingDistance_of_curvature_neg (hK : U.geometry.curvature < 0) (χ : ℝ) :
    U.transverseComovingDistance χ
      = 1 / √(-U.geometry.curvature) * Real.sinh (√(-U.geometry.curvature) * χ) := by
  unfold transverseComovingDistance
  generalize U.geometry = s at hK ⊢
  cases s with
  | Spherical k hk => linarith [SpatialGeometry.curvature_spherical_pos k hk]
  | Flat => simp at hK
  | Saddle k hk =>
    have hs : √(-(SpatialGeometry.Saddle k hk).curvature) = 1 / k := by
      show √(-(-1 / k ^ 2)) = 1 / k
      rw [show -(-1 / k ^ 2) = (1 / k) ^ 2 by ring]
      exact Real.sqrt_sq (one_div_pos.mpr hk).le
    rw [hs]
    show k * Real.sinh (χ / k) = 1 / (1 / k) * Real.sinh (1 / k * χ)
    rw [one_div_one_div, show 1 / k * χ = χ / k by ring]

/-!

## E. The horizons

-/

/-- The particle horizon at `t`, the integral of `c / a` over the times of the interval of the
  model before `t`. It is a Lebesgue integral, equal to `0` when the integrand is not
  integrable. -/
noncomputable def particleHorizon (c : ℝ) (t : Time) : ℝ :=
  c * ∫ τ in {τ : ℝ | (⟨τ⟩ : Time) ∈ U.I ∧ τ < t.val}, 1 / U.a ⟨τ⟩

/-- The event horizon at `t`, the integral of `c / a` over the times of the interval of the
  model after `t`. It is a Lebesgue integral, equal to `0` when the integrand is not
  integrable. -/
noncomputable def eventHorizon (c : ℝ) (t : Time) : ℝ :=
  c * ∫ τ in {τ : ℝ | (⟨τ⟩ : Time) ∈ U.I ∧ t.val < τ}, 1 / U.a ⟨τ⟩

/-- The particle horizon of the Einstein-de Sitter model at `t > 0` is `3 c t₀^(2/3) t^(1/3)`. -/
lemma particleHorizon_einsteinDeSitter {t₀ : Time} {c : ℝ} (ht₀ : 0 < t₀.val) {t : Time}
    (ht : 0 < t.val) :
    (einsteinDeSitter t₀ ht₀).particleHorizon c t
      = 3 * c * t₀.val ^ (2 / 3 : ℝ) * t.val ^ (1 / 3 : ℝ) := by
  have hset : {τ : ℝ | (⟨τ⟩ : Time) ∈ (einsteinDeSitter t₀ ht₀).I ∧ τ < t.val}
      = Set.Ioo 0 t.val := rfl
  rw [particleHorizon, hset, ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le ht.le]
  show c * ∫ τ in (0 : ℝ)..t.val, 1 / (τ / t₀.val) ^ (2 / 3 : ℝ) = _
  have hcongr : Set.EqOn (fun τ : ℝ => 1 / (τ / t₀.val) ^ (2 / 3 : ℝ))
      (fun τ : ℝ => t₀.val ^ (2 / 3 : ℝ) * τ ^ (-(2 / 3) : ℝ)) (Set.uIcc 0 t.val) := by
    intro τ hτ
    rw [Set.uIcc_of_le ht.le] at hτ
    have h0 : 0 ≤ τ := hτ.1
    simp only
    rw [Real.div_rpow h0 ht₀.le, one_div, inv_div, Real.rpow_neg h0, div_eq_mul_inv]
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by norm_num)), Real.zero_rpow (by norm_num)]
  norm_num
  ring

end Cosmology.FLRW

TODO "Define the lookback time `t₀ - t` and prove its model-independent expansion
  `t₀ - t = H₀⁻¹ [z - ½(2 + q₀) z² + …]` in powers of the redshift."

TODO "Define the luminosity distance `d_L = (1 + z) r(χ)` and the angular-diameter
  distance `d_A = r(χ) / (1 + z)`."

TODO "Prove Etherington's distance-duality relation `d_L = (1 + z)² d_A`."

TODO "Prove the low-redshift expansions of `χ`, `d_L` and `d_A` in powers of `z`
  in terms of the deceleration parameter `q₀`."
