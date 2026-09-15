/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philippe Kevorkian, Jinzheng Li
-/
module

public import Physlib.Meta.TODO.Basic
public import Physlib.Cosmology.FLRW.Dynamics
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
/-!

# Distances and redshift in FLRW cosmology

## i. Overview

The comoving distance of a source emitting at the time `t` and observed at `t₀` is
`χ = c ∫_t^{t₀} dτ / a(τ)`, so that `∂ₜ χ = - c / a`. The redshift is `1 + z = a(t₀) / a(t)`,
with `∂ₜ z = -(1 + z) H`; combining the two, `∂ₜ χ = (c / (a(t₀) H)) ∂ₜ z`, which is the
change of variables `dχ = c dz / H` (for `a(t₀) = 1`) behind the distance integrals written in
the redshift. The proper distance `D = a χ` obeys the Hubble-Lemaître law `∂ₜ D = H D`, and the
recession velocity equals `c` exactly at the Hubble radius `R_H = c / H`. The transverse comoving
distance `r(χ)` is the function `S` of `Cosmology.SpatialGeometry` for the geometry of curvature
`K`, with curvature radius `1 / √|K|`. The particle and event horizons are the comoving distances
to the initial time and to the infinite future; the particle horizon of the Einstein-de Sitter
universe is computed.

What is not stated here: the cosmological redshift law `E ∝ 1 / a` of a photon (it needs the
metric and the null geodesics, not yet objects of Physlib), and the comoving distance as an
integral in `z` (it needs `H` as a function of `z`); the differential relation above is what is
proved.

## ii. Key results

- `comovingDistance`, `deriv_comovingDistance`: `∂ₜ χ = - c / a`.
- `redshift`, `deriv_redshift`: `∂ₜ z = -(1 + z) H`; `deriv_comovingDistance_eq_mul_deriv_redshift`:
  `∂ₜ χ = (c / (a(t₀) H)) ∂ₜ z`.
- `properDistance`, `deriv_properDistance`: the Hubble-Lemaître law; `hubbleRadius`,
  `deriv_properDistance_eq_iff`.
- `spatialGeometryOfCurvature`, `transverseComovingDistance` and its three closed forms.
- `particleHorizon`, `eventHorizon`, `particleHorizon_einsteinDeSitter`.

## iii. Table of contents

- A. The comoving distance
- B. The redshift and the change of variables
- C. The proper distance and the Hubble radius
- D. The transverse comoving distance
- E. The horizons

-/

@[expose] public section

namespace Cosmology.FLRW.FriedmannEquation

open Real Time

/-!

## A. The comoving distance

-/

/-- The line-of-sight comoving distance `χ = c ∫_t^{t₀} dτ / a(τ)` of a source emitting at `t`
  and observed at `t₀`. -/
noncomputable def comovingDistance (a : Time → ℝ) (c : ℝ) (t t₀ : Time) : ℝ :=
  c * ∫ τ in t.val..t₀.val, 1 / a ⟨τ⟩

/-- For `a` continuous and positive, `∂ₜ χ = - c / a` (fundamental theorem of calculus). -/
lemma deriv_comovingDistance {a : Time → ℝ} {c : ℝ} (hcont : Continuous a) (hapos : ∀ s, 0 < a s)
    (t₀ t : Time) : ∂ₜ (fun s => comovingDistance a c s t₀) t = -c / a t := by
  obtain ⟨τ⟩ := t
  have hf : Continuous (fun τ : ℝ => 1 / a ⟨τ⟩) :=
    continuous_const.div (hcont.comp toRealCLE.symm.continuous) fun τ => (hapos ⟨τ⟩).ne'
  have h : HasDerivAt (fun σ : ℝ => ∫ x in σ..t₀.val, 1 / a ⟨x⟩) (-(1 / a ⟨τ⟩)) τ :=
    intervalIntegral.integral_hasDerivAt_left (hf.intervalIntegrable _ _)
      (hf.stronglyMeasurableAtFilter _ _) hf.continuousAt
  refine deriv_eq_of_hasDerivAt ((h.const_mul c).congr_deriv ?_)
  ring

/-!

## B. The redshift and the change of variables

-/

/-- The redshift of a source emitting at `t` and observed at `t₀`: `1 + z = a(t₀) / a(t)`. -/
noncomputable def redshift (a : Time → ℝ) (t₀ t : Time) : ℝ := a t₀ / a t - 1

lemma one_add_redshift {a : Time → ℝ} (t₀ t : Time) : 1 + redshift a t₀ t = a t₀ / a t := by
  unfold redshift
  ring

/-- `∂ₜ z = -(1 + z) H`: the change of variables `dt = - dz / ((1 + z) H)`. -/
lemma deriv_redshift {a : Time → ℝ} {t₀ t : Time} (hd : DifferentiableAt ℝ a t) (ha : a t ≠ 0) :
    ∂ₜ (redshift a t₀) t = -(1 + redshift a t₀ t) * hubbleConstant a t := by
  obtain ⟨τ⟩ := t
  have hA := hasDerivAt_mk_of_differentiableAt hd
  have h := ((hasDerivAt_const τ (a t₀)).div hA ha).sub_const 1
  refine (deriv_eq_of_hasDerivAt (f := redshift a t₀) h).trans ?_
  unfold redshift hubbleConstant
  field_simp
  ring

/-- `∂ₜ a = a H`. -/
lemma deriv_eq_mul_hubbleConstant {a : Time → ℝ} {t : Time} (ha : a t ≠ 0) :
    ∂ₜ a t = a t * hubbleConstant a t := by
  unfold hubbleConstant
  field_simp

/-- `∂ₜ χ = (c / (a(t₀) H)) ∂ₜ z`: with `a(t₀) = 1`, this is the change of variables
  `dχ = c dz / H` (both derivatives are negative: `χ` and `z` decrease with the emission time). -/
lemma deriv_comovingDistance_eq_mul_deriv_redshift {a : Time → ℝ} {c : ℝ} (hcont : Continuous a)
    (hapos : ∀ s, 0 < a s) {t₀ t : Time} (hd : DifferentiableAt ℝ a t)
    (hH : hubbleConstant a t ≠ 0) :
    ∂ₜ (fun s => comovingDistance a c s t₀) t
      = c / (a t₀ * hubbleConstant a t) * ∂ₜ (redshift a t₀) t := by
  rw [deriv_comovingDistance hcont hapos, deriv_redshift hd (hapos t).ne', one_add_redshift]
  have ha := (hapos t).ne'
  have ha₀ := (hapos t₀).ne'
  field_simp

/-!

## C. The proper distance and the Hubble radius

-/

/-- The proper distance `D = a χ` at fixed comoving distance `χ`. -/
noncomputable def properDistance (a : Time → ℝ) (χ : ℝ) (t : Time) : ℝ := a t * χ

/-- The Hubble-Lemaître law `∂ₜ D = H D`. -/
lemma deriv_properDistance {a : Time → ℝ} {χ : ℝ} {t : Time} (hd : DifferentiableAt ℝ a t)
    (ha : a t ≠ 0) : ∂ₜ (properDistance a χ) t = hubbleConstant a t * properDistance a χ t := by
  obtain ⟨τ⟩ := t
  have hA := hasDerivAt_mk_of_differentiableAt hd
  refine (deriv_eq_of_hasDerivAt (f := properDistance a χ) (hA.mul_const χ)).trans ?_
  unfold hubbleConstant properDistance
  field_simp

/-- The Hubble radius `R_H = c / H`. -/
noncomputable def hubbleRadius (a : Time → ℝ) (c : ℝ) (t : Time) : ℝ := c / hubbleConstant a t

/-- The recession velocity `∂ₜ D` equals `c` exactly at the Hubble radius. -/
lemma deriv_properDistance_eq_iff {a : Time → ℝ} {χ c : ℝ} {t : Time} (hd : DifferentiableAt ℝ a t)
    (ha : a t ≠ 0) (hH : hubbleConstant a t ≠ 0) :
    ∂ₜ (properDistance a χ) t = c ↔ properDistance a χ t = hubbleRadius a c t := by
  rw [deriv_properDistance hd ha, hubbleRadius, eq_div_iff hH]
  constructor <;> intro h <;> linarith [h]

/-!

## D. The transverse comoving distance

-/

/-- The spatial geometry of curvature parameter `K`, in the conventions of `SpatialGeometry`
  (`Spherical k` with `k < 0`, `Saddle k` with `k > 0`; the function `S` is even in `k`), with
  curvature radius `1 / √|K|`. -/
noncomputable def spatialGeometryOfCurvature (K : ℝ) : SpatialGeometry :=
  if hK : 0 < K then
    .Spherical (-(1 / √K)) (neg_neg_of_pos (one_div_pos.mpr (Real.sqrt_pos.mpr hK)))
  else if hK' : K < 0 then
    .Saddle (1 / √(-K)) (one_div_pos.mpr (Real.sqrt_pos.mpr (neg_pos.mpr hK')))
  else .Flat

/-- The transverse comoving distance `r(χ) = S(χ)` for the geometry of curvature `K`. -/
noncomputable def transverseComovingDistance (K χ : ℝ) : ℝ :=
  SpatialGeometry.S (spatialGeometryOfCurvature K) χ

/-- For `K > 0`, `r(χ) = (1 / √K) sin (√K χ)`. -/
lemma transverseComovingDistance_of_pos {K : ℝ} (hK : 0 < K) (χ : ℝ) :
    transverseComovingDistance K χ = 1 / √K * Real.sin (√K * χ) := by
  unfold transverseComovingDistance spatialGeometryOfCurvature
  rw [dif_pos hK]
  simp only [SpatialGeometry.S]
  have hs : √K ≠ 0 := (Real.sqrt_pos.mpr hK).ne'
  rw [show χ / -(1 / √K) = -(√K * χ) by field_simp, Real.sin_neg]
  ring

/-- For `K = 0`, `r(χ) = χ`. -/
lemma transverseComovingDistance_zero (χ : ℝ) : transverseComovingDistance 0 χ = χ := by
  unfold transverseComovingDistance spatialGeometryOfCurvature
  rw [dif_neg (lt_irrefl 0), dif_neg (lt_irrefl 0)]
  simp only [SpatialGeometry.S]

/-- For `K < 0`, `r(χ) = (1 / √(-K)) sinh (√(-K) χ)`. -/
lemma transverseComovingDistance_of_neg {K : ℝ} (hK : K < 0) (χ : ℝ) :
    transverseComovingDistance K χ = 1 / √(-K) * Real.sinh (√(-K) * χ) := by
  unfold transverseComovingDistance spatialGeometryOfCurvature
  rw [dif_neg (not_lt.mpr hK.le), dif_pos hK]
  simp only [SpatialGeometry.S]
  have hs : √(-K) ≠ 0 := (Real.sqrt_pos.mpr (neg_pos.mpr hK)).ne'
  rw [show χ / (1 / √(-K)) = √(-K) * χ by field_simp]

/-!

## E. The horizons

-/

/-- The particle horizon at `t`: the comoving distance to the initial time `tᵢ`. -/
noncomputable def particleHorizon (a : Time → ℝ) (c : ℝ) (tᵢ t : Time) : ℝ :=
  comovingDistance a c tᵢ t

/-- The event horizon at `t`: `c ∫_t^∞ dτ / a(τ)` (Lebesgue integral over `(t, ∞)`, equal to
  `0` when not integrable). -/
noncomputable def eventHorizon (a : Time → ℝ) (c : ℝ) (t : Time) : ℝ :=
  c * ∫ τ in Set.Ioi t.val, 1 / a ⟨τ⟩

/-- The particle horizon of the Einstein-de Sitter universe from `t = 0` is finite,
  `3 c t₀^(2/3) t^(1/3)`. -/
lemma particleHorizon_einsteinDeSitter {t₀ : Time} {c : ℝ} (ht₀ : 0 < t₀.val) {t : Time}
    (ht : 0 < t.val) :
    particleHorizon (einsteinDeSitterScaleFactor t₀) c ⟨0⟩ t
      = 3 * c * t₀.val ^ (2 / 3 : ℝ) * t.val ^ (1 / 3 : ℝ) := by
  unfold particleHorizon comovingDistance einsteinDeSitterScaleFactor
  dsimp only
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

end Cosmology.FLRW.FriedmannEquation
