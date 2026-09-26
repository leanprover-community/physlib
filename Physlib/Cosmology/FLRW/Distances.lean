/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philippe Kevorkian, Jinzheng Li
-/
module

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
universe is computed. The luminosity distance `d_L = (1 + z) r(χ)` and the angular-diameter
distance `d_A = r(χ) / (1 + z)` satisfy Etherington's relation `d_L = (1 + z)² d_A`. The
low-redshift expansions of the lookback time and of the distances are given through their
coefficients: the first and second derivatives of `z` and `χ` at the observation time, and the
resulting `dχ/dz = c / (a₀ H₀)`, `d²χ/dz² = - c (1 + q₀) / (a₀ H₀)` at `z = 0`.

What is not stated here: the cosmological redshift law `E ∝ 1 / a` of a photon (it needs the
metric and the null geodesics, not yet objects of Physlib), and the comoving distance as an
integral in `z` (it needs `H` as a function of `z`); the differential relation above is what is
proved. The Taylor expansions themselves (with remainder, through the inverse of `t ↦ z(t)`) are
not stated: only their coefficients are.

## ii. Key results

- `comovingDistance`, `deriv_comovingDistance`: `∂ₜ χ = - c / a`.
- `redshift`, `deriv_redshift`: `∂ₜ z = -(1 + z) H`; `deriv_comovingDistance_eq_mul_deriv_redshift`:
  `∂ₜ χ = (c / (a(t₀) H)) ∂ₜ z`.
- `properDistance`, `deriv_properDistance`: the Hubble-Lemaître law; `hubbleRadius`,
  `deriv_properDistance_eq_iff`.
- `spatialGeometryOfCurvature`, `transverseComovingDistance` and its three closed forms.
- `particleHorizon`, `eventHorizon`, `particleHorizon_einsteinDeSitter`.
- `lookbackTime`; `deriv_redshift_self`, `deriv_deriv_redshift_self`: `∂ₜ z = - H₀` and
  `∂ₜ ∂ₜ z = H₀² (2 + q₀)` at `t₀`, the coefficients of `t₀ - t = H₀⁻¹ [z - ½ (2 + q₀) z² + …]`.
- `luminosityDistance`, `angularDiameterDistance`, `luminosityDistance_eq`: Etherington.
- `deriv_deriv_comovingDistance_self`, `comovingDistance_coeff_one`, `comovingDistance_coeff_two`:
  `dχ/dz = c / (a₀ H₀)` and `d²χ/dz² = - c (1 + q₀) / (a₀ H₀)` at `z = 0`;
  `luminosityDistance_coeff_two`, `angularDiameterDistance_coeff_two`: the second-order
  coefficients `c (1 - q₀) / (a₀ H₀)` and `- c (3 + q₀) / (a₀ H₀)` of `d_L` and `d_A` (flat case).

## iii. Table of contents

- A. The comoving distance
- B. The redshift and the change of variables
- C. The proper distance and the Hubble radius
- D. The transverse comoving distance
- E. The horizons
- F. The lookback time and its expansion
- G. The luminosity and angular-diameter distances
- H. The low-redshift expansions of the distances

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

/-!

## F. The lookback time and its expansion

-/

/-- The lookback time `t₀ - t`. -/
def lookbackTime (t₀ t : Time) : ℝ := t₀.val - t.val

/-- At the observation time, `∂ₜ z = - H₀`: the first-order coefficient `dt/dz = - 1 / H₀`. -/
lemma deriv_redshift_self {a : Time → ℝ} {t₀ : Time} (hd : DifferentiableAt ℝ a t₀)
    (ha : a t₀ ≠ 0) : ∂ₜ (redshift a t₀) t₀ = -hubbleConstant a t₀ := by
  rw [deriv_redshift hd ha, one_add_redshift, div_self ha]
  ring

/-- `∂ₜ z = - a(t₀) ∂ₜ a / a²` at all times, for `a` differentiable and nonzero. -/
lemma deriv_redshift_eq {a : Time → ℝ} {t₀ : Time} (hd : Differentiable ℝ a) (hapos : ∀ s, a s ≠ 0)
    (s : Time) : ∂ₜ (redshift a t₀) s = -(a t₀ * ∂ₜ a s) / a s ^ 2 := by
  rw [deriv_redshift (hd s) (hapos s), one_add_redshift]
  unfold hubbleConstant
  have := hapos s
  field_simp

/-- At the observation time, `∂ₜ ∂ₜ z = H₀² (2 + q₀)`: the second-order coefficient
  `d²t/dz² = (2 + q₀) / H₀` of the lookback time `t₀ - t = H₀⁻¹ [z - ½ (2 + q₀) z² + …]`. -/
lemma deriv_deriv_redshift_self {a : Time → ℝ} {t₀ : Time} (hd : Differentiable ℝ a)
    (hdd : DifferentiableAt ℝ (∂ₜ a) t₀) (hapos : ∀ s, a s ≠ 0) (hd0 : ∂ₜ a t₀ ≠ 0) :
    ∂ₜ (∂ₜ (redshift a t₀)) t₀ = hubbleConstant a t₀ ^ 2 * (2 + decelerationParameter a t₀) := by
  have hz := deriv_redshift_eq (t₀ := t₀) hd hapos
  obtain ⟨τ₀⟩ := t₀
  have hA := hasDerivAt_mk_of_differentiableAt (hd ⟨τ₀⟩)
  have hA' := hasDerivAt_mk_of_differentiableAt hdd
  have h := ((hA'.const_mul (a ⟨τ₀⟩)).div (hA.pow 2) (pow_ne_zero 2 (hapos ⟨τ₀⟩))).neg
  refine (deriv_eq_of_hasDerivAt (f := ∂ₜ (redshift a ⟨τ₀⟩))
    (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun σ => ?_))).trans ?_
  · simp only [Pi.neg_apply, Pi.div_apply, Pi.pow_apply]
    rw [hz ⟨σ⟩]
    ring
  · simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    unfold hubbleConstant decelerationParameter
    have := hapos ⟨τ₀⟩
    field_simp
    ring

/-!

## G. The luminosity and angular-diameter distances

-/

/-- The luminosity distance `d_L = (1 + z) r(χ)`. -/
noncomputable def luminosityDistance (K : ℝ) (a : Time → ℝ) (c : ℝ) (t₀ t : Time) : ℝ :=
  (1 + redshift a t₀ t) * transverseComovingDistance K (comovingDistance a c t t₀)

/-- The angular-diameter distance `d_A = r(χ) / (1 + z)`. -/
noncomputable def angularDiameterDistance (K : ℝ) (a : Time → ℝ) (c : ℝ) (t₀ t : Time) : ℝ :=
  transverseComovingDistance K (comovingDistance a c t t₀) / (1 + redshift a t₀ t)

/-- Etherington's distance-duality relation `d_L = (1 + z)² d_A`. -/
lemma luminosityDistance_eq {K : ℝ} {a : Time → ℝ} {c : ℝ} {t₀ t : Time} (ha₀ : a t₀ ≠ 0)
    (ha : a t ≠ 0) :
    luminosityDistance K a c t₀ t
      = (1 + redshift a t₀ t) ^ 2 * angularDiameterDistance K a c t₀ t := by
  have hz : 1 + redshift a t₀ t ≠ 0 := by
    rw [one_add_redshift]
    exact div_ne_zero ha₀ ha
  unfold luminosityDistance angularDiameterDistance
  field_simp

/-!

## H. The low-redshift expansions of the distances

The comoving distance as a function of the redshift has, at `z = 0`, the derivatives
`dχ/dz = χ' / z'` and `d²χ/dz² = (χ'' z' - χ' z'') / z'³` (primes are time derivatives at `t₀`);
they are computed here, giving `χ = (c / (a₀ H₀)) [z - ½ (1 + q₀) z² + …]`, and, in the flat
case `r(χ) = χ`, `d_L = (c / (a₀ H₀)) [z + ½ (1 - q₀) z² + …]` and
`d_A = (c / (a₀ H₀)) [z - ½ (3 + q₀) z² + …]`.

-/

/-- At the observation time, `∂ₜ ∂ₜ χ = c H₀ / a₀`. -/
lemma deriv_deriv_comovingDistance_self {a : Time → ℝ} {c : ℝ} (hcont : Continuous a)
    (hapos : ∀ s, 0 < a s) {t₀ : Time} (hd : DifferentiableAt ℝ a t₀) :
    ∂ₜ (∂ₜ (fun s => comovingDistance a c s t₀)) t₀ = c * hubbleConstant a t₀ / a t₀ := by
  have hχ := deriv_comovingDistance (c := c) hcont hapos t₀
  obtain ⟨τ₀⟩ := t₀
  have hA := hasDerivAt_mk_of_differentiableAt hd
  have h := (hasDerivAt_const τ₀ (-c)).div hA (hapos ⟨τ₀⟩).ne'
  refine (deriv_eq_of_hasDerivAt (f := ∂ₜ (fun s => comovingDistance a c s ⟨τ₀⟩))
    (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun σ => hχ ⟨σ⟩))).trans ?_
  unfold hubbleConstant
  have := (hapos ⟨τ₀⟩).ne'
  field_simp
  ring

/-- `dχ/dz = χ' / z' = c / (a₀ H₀)` at `z = 0`. -/
lemma comovingDistance_coeff_one {a : Time → ℝ} {c : ℝ} (hcont : Continuous a)
    (hapos : ∀ s, 0 < a s) {t₀ : Time} (hd : DifferentiableAt ℝ a t₀)
    (hH : hubbleConstant a t₀ ≠ 0) :
    ∂ₜ (fun s => comovingDistance a c s t₀) t₀ / ∂ₜ (redshift a t₀) t₀
      = c / (a t₀ * hubbleConstant a t₀) := by
  rw [deriv_comovingDistance hcont hapos, deriv_redshift_self hd (hapos t₀).ne']
  have := (hapos t₀).ne'
  field_simp

/-- `d²χ/dz² = (χ'' z' - χ' z'') / z'³ = - c (1 + q₀) / (a₀ H₀)` at `z = 0`. -/
lemma comovingDistance_coeff_two {a : Time → ℝ} {c : ℝ} (hcont : Continuous a)
    (hapos : ∀ s, 0 < a s) {t₀ : Time} (hd : Differentiable ℝ a)
    (hdd : DifferentiableAt ℝ (∂ₜ a) t₀) (hd0 : ∂ₜ a t₀ ≠ 0) :
    (∂ₜ (∂ₜ (fun s => comovingDistance a c s t₀)) t₀ * ∂ₜ (redshift a t₀) t₀
      - ∂ₜ (fun s => comovingDistance a c s t₀) t₀ * ∂ₜ (∂ₜ (redshift a t₀)) t₀)
      / ∂ₜ (redshift a t₀) t₀ ^ 3
      = -(c * (1 + decelerationParameter a t₀) / (a t₀ * hubbleConstant a t₀)) := by
  have hne : ∀ s, a s ≠ 0 := fun s => (hapos s).ne'
  rw [deriv_deriv_comovingDistance_self hcont hapos (hd t₀), deriv_comovingDistance hcont hapos,
    deriv_redshift_self (hd t₀) (hne t₀), deriv_deriv_redshift_self hd hdd hne hd0]
  unfold hubbleConstant decelerationParameter
  have := hne t₀
  field_simp
  ring

/-- Flat case: the second-order coefficient of `d_L = (1 + z) χ(z)` is `2 χ₁ + χ₂`, which with
  `χ₁ = c / (a₀ H₀)` and `χ₂ = - c (1 + q₀) / (a₀ H₀)` is `c (1 - q₀) / (a₀ H₀)`. -/
lemma luminosityDistance_coeff_two (c a₀ H₀ q₀ : ℝ) (hH : H₀ ≠ 0) (ha : a₀ ≠ 0) :
    2 * (c / (a₀ * H₀)) + -(c * (1 + q₀) / (a₀ * H₀)) = c * (1 - q₀) / (a₀ * H₀) := by
  field_simp
  ring

/-- Flat case: the second-order coefficient of `d_A = χ(z) / (1 + z)` is `χ₂ - 2 χ₁`, which is
  `- c (3 + q₀) / (a₀ H₀)`. -/
lemma angularDiameterDistance_coeff_two (c a₀ H₀ q₀ : ℝ) (hH : H₀ ≠ 0) (ha : a₀ ≠ 0) :
    -(c * (1 + q₀) / (a₀ * H₀)) - 2 * (c / (a₀ * H₀)) = -(c * (3 + q₀) / (a₀ * H₀)) := by
  field_simp
  ring

end Cosmology.FLRW.FriedmannEquation
