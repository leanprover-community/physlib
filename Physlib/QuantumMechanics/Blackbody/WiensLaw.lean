/-
Copyright (c) 2026 Dwanith C. Jayanth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dwanith C. Jayanth
-/
module

public import Physlib.QuantumMechanics.Blackbody.PlancksLaw
public import Physlib.QuantumMechanics.Blackbody.WienEquation

/-!

# Wien's displacement law, derived from Planck's law

The peak of the blackbody spectrum shifts inversely with temperature: the
wavelength and frequency maxima of Planck's spectral radiance at different
temperatures are related by universal constants. This file builds the physical
layer on top of the dimensionless analysis in the `WienEquation` module.

## i. Overview

Wien's displacement law states that the peak of the blackbody spectrum shifts
inversely with temperature. In wavelength form: if `lam₁` maximizes
`B(lam, T₁)` and `lam₂` maximizes `B(lam, T₂)`, then

    `lam₁ T₁ = lam₂ T₂ = h c / (kB x₅)`,

where `x₅ ≈ 4.96511` is the unique positive solution of the transcendental
equation `x = 5 (1 - e⁻ˣ)`. In frequency form:

    `ν₁ / T₁ = ν₂ / T₂ = kB x₃ / h`,

where `x₃ ≈ 2.82144` is the unique positive solution of `x = 3 (1 - e⁻ˣ)`.
The two constants differ because the "peak" depends on the parametrization.

The proof factors each Planck curve into a temperature-dependent dimensional
prefactor and the universal dimensionless profile `xⁿ / (eˣ - 1)`. The profile
has a global maximum at the Wien root, and the chain rule transfers
that maximum, together with continuity and vanishing endpoints, back to the
spectral radiance.

## ii. Key results

- `wavePrefactor` / `freqPrefactor`: the physical prefactors `2 (kB T)⁵ / (h⁴ c³)` and
  `2 (kB T)³ / (h² c²)`.
- `waveVar` / `freqVar`: the dimensionless variables `h c / (lam kB T)` and `h ν / (kB T)`.
- `spectralRadianceWave_eq_profile` / `spectralRadiance_eq_profile`: the physical curves factor as
  prefactor times the dimensionless Planck profile.
- `hasDerivAt_wave` / `hasDerivAt_freq`: derivatives of the physical curves by the chain rule.
- `wave_crit_iff` / `freq_crit_iff`: critical points of the physical Planck curves.
- `spectralRadianceWave_continuousOn` / `spectralRadiance_continuousOn`: continuity of physical
  curves.
- `spectralRadianceWave_tendsto_zero_atTop` / `spectralRadiance_tendsto_zero_atTop`: the curves
  vanish at high wavelength and high frequency.
- `spectralRadianceWave_tendsto_nhdsWithin_zero` / `spectralRadiance_tendsto_nhdsWithin_zero`:
  the curves vanish at the origin.
- `spectralRadianceWave_isMaxOn` / `spectralRadiance_isMaxOn`: physical radiation maxima.
- `wien_displacement_wave` / `wien_displacement_freq`: the displacement laws
  `lam₁ T₁ = lam₂ T₂` and `ν₁ / T₁ = ν₂ / T₂`.
- `wien_peak_product` / `wien_peak_ratio`: constant peak values `lam T = h c / (kB x₅)` and
  `ν / T = kB x₃ / h`.

## iii. Table of contents

- A. Reduction of Planck's law to dimensionless form
- B. The physical Planck curves
- C. Wien's displacement laws

## iv. References

* https://en.wikipedia.org/wiki/Wien%27s_displacement_law
* W. Wien, "Eine neue Beziehung der Strahlung schwarzer Körper zum zweiten
  Hauptsatz der Wärmetheorie", Sitzungsber. Preuss. Akad. Wiss. (1893).
-/

@[expose] public section
noncomputable section

namespace BlackBody

open Constants

open Set Filter Topology

/-!

## A. Reduction of Planck's law to dimensionless form

Planck's spectral radiance curves in wavelength and frequency form decompose
into temperature-dependent dimensional prefactors and a universal dimensionless
Planck profile `xⁿ / (eˣ - 1)` (with `n = 5` for wavelength and `n = 3` for frequency)
expressed in terms of dimensionless variables `x = h c / (lam kB T)` and `x = h ν / (kB T)`.
-/

/-- Wavelength prefactor `C(T) = 2 (kB T)⁵ / (h⁴ c³)`. -/
noncomputable def wavePrefactor (B : BlackBody) (c : SpeedOfLight) : ℝ :=
  2 * (kB * (B.T : ℝ)) ^ 5 / ((h : ℝ) ^ 4 * (c : ℝ) ^ 3)


/-- Frequency prefactor `D(T) = 2 (kB T)³ / (h² c²)`. -/
noncomputable def freqPrefactor (B : BlackBody) (c : SpeedOfLight) : ℝ :=
  2 * (kB * (B.T : ℝ)) ^ 3 / ((h : ℝ) ^ 2 * (c : ℝ) ^ 2)


/-- Dimensionless wavelength variable `x = h c / (λ kB T)`. -/
noncomputable def waveVar (B : BlackBody) (c : SpeedOfLight) (lam : ℝ) : ℝ :=
  (h : ℝ) * (c : ℝ) / (lam * kB * (B.T : ℝ))


/-- Dimensionless frequency variable `x = h ν / (kB T)`. -/
noncomputable def freqVar (B : BlackBody) (ν : ℝ) : ℝ :=
  (h : ℝ) * ν / (kB * (B.T : ℝ))


/-- The wavelength prefactor is positive for positive temperature. -/
lemma wavePrefactor_pos (B : BlackBody) (c : SpeedOfLight)
    (hT : 0 < (B.T : ℝ)) : 0 < B.wavePrefactor c := by
  unfold wavePrefactor
  apply div_pos
  · exact mul_pos zero_lt_two (pow_pos (mul_pos kB_pos hT) 5)
  · exact mul_pos (pow_pos h_pos 4) (pow_pos c.val_pos 3)


/-- The frequency prefactor is positive for positive temperature. -/
lemma freqPrefactor_pos (B : BlackBody) (c : SpeedOfLight)
    (hT : 0 < (B.T : ℝ)) : 0 < B.freqPrefactor c := by
  unfold freqPrefactor
  apply div_pos
  · exact mul_pos zero_lt_two (pow_pos (mul_pos kB_pos hT) 3)
  · exact mul_pos (pow_pos h_pos 2) (pow_pos c.val_pos 2)


/-- The dimensionless wavelength variable is positive for positive wavelength and temperature. -/
lemma waveVar_pos (B : BlackBody) (c : SpeedOfLight) (lam : ℝ)
    (hT : 0 < (B.T : ℝ)) (hlam : 0 < lam) : 0 < B.waveVar c lam := by
  unfold waveVar
  exact div_pos (mul_pos h_pos c.val_pos) (mul_pos (mul_pos hlam kB_pos) hT)


/-- The dimensionless frequency variable is positive for positive frequency and temperature. -/
lemma freqVar_pos (B : BlackBody) (ν : ℝ)
    (hT : 0 < (B.T : ℝ)) (hν : 0 < ν) : 0 < B.freqVar ν := by
  unfold freqVar
  exact div_pos (mul_pos h_pos hν) (mul_pos kB_pos hT)


/-- The wavelength curve factors through the `n = 5` profile on `λ > 0`. -/
lemma spectralRadianceWave_eq_profile (B : BlackBody) (c : SpeedOfLight) (lam : ℝ)
    (hT : 0 < (B.T : ℝ)) (hlam : 0 < lam) :
    B.spectralRadianceWave c lam
      = B.wavePrefactor c * wienProfile 5 (B.waveVar c lam) := by
  unfold spectralRadianceWave wavePrefactor wienProfile waveVar
  rw [ite_eq_left hlam]
  have hlam' : lam ≠ 0 := ne_of_gt hlam
  have hh' : (h : ℝ) ≠ 0 := ne_of_gt h_pos
  have hc' : (c : ℝ) ≠ 0 := ne_of_gt c.val_pos
  have hk' : kB ≠ 0 := ne_of_gt kB_pos
  have hT' : (B.T : ℝ) ≠ 0 := ne_of_gt hT
  have hE : Real.exp ((h : ℝ) * (c : ℝ) / (lam * kB * (B.T : ℝ))) - 1 ≠ 0 := by
    have harg : 0 < (h : ℝ) * (c : ℝ) / (lam * kB * (B.T : ℝ)) :=
      div_pos (mul_pos h_pos c.val_pos) (mul_pos (mul_pos hlam kB_pos) hT)
    have h1e : 1 < Real.exp ((h : ℝ) * (c : ℝ) / (lam * kB * (B.T : ℝ))) :=
      Real.one_lt_exp_iff.mpr harg
    exact ne_of_gt (sub_pos.mpr h1e)
  field_simp


/-- The frequency curve factors through the `n = 3` profile on `ν > 0`. -/
lemma spectralRadiance_eq_profile (B : BlackBody) (c : SpeedOfLight) (ν : ℝ)
    (hT : 0 < (B.T : ℝ)) (hν : 0 < ν) :
    B.spectralRadiance c ν = B.freqPrefactor c * wienProfile 3 (B.freqVar ν) := by
  unfold spectralRadiance freqPrefactor wienProfile freqVar
  rw [ite_eq_left hν]
  have hν' : ν ≠ 0 := ne_of_gt hν
  have hh' : (h : ℝ) ≠ 0 := ne_of_gt h_pos
  have hc' : (c : ℝ) ≠ 0 := ne_of_gt c.val_pos
  have hk' : kB ≠ 0 := ne_of_gt kB_pos
  have hT' : (B.T : ℝ) ≠ 0 := ne_of_gt hT
  have hE : Real.exp ((h : ℝ) * ν / (kB * (B.T : ℝ))) - 1 ≠ 0 := by
    have harg : 0 < (h : ℝ) * ν / (kB * (B.T : ℝ)) :=
      div_pos (mul_pos h_pos hν) (mul_pos kB_pos hT)
    have h1e : 1 < Real.exp ((h : ℝ) * ν / (kB * (B.T : ℝ))) :=
      Real.one_lt_exp_iff.mpr harg
    exact ne_of_gt (sub_pos.mpr h1e)
  field_simp


/-!

## B. The physical Planck curves

For fixed temperature, the wavelength curve is a positive constant multiple of
the profile `f₅(x)` composed with `x = h c / (lam kB T)`, and the frequency curve
is a positive constant multiple of `f₃(x)` composed with `x = h ν / (kB T)`.
Critical points of the physical curves correspond exactly to solutions of the
Wien equation. The global maximum of the profile transfers to a global maximum
of the spectral radiance, and the curves are continuous and vanish at both ends.
-/

/-- Derivative of the wavelength curve at `λ > 0`, via the chain rule. -/
lemma hasDerivAt_wave (B : BlackBody) (c : SpeedOfLight) (lam : ℝ)
    (hT : 0 < (B.T : ℝ)) (hlam : 0 < lam) :
    HasDerivAt (fun lam => B.spectralRadianceWave c lam)
      (B.wavePrefactor c
        * (deriv (wienProfile 5) (B.waveVar c lam)
          * (-((h : ℝ) * (c : ℝ) / (kB * (B.T : ℝ))) / lam ^ 2))) lam := by
  have hx : 0 < B.waveVar c lam := waveVar_pos B c lam hT hlam
  have he : Real.exp (B.waveVar c lam) - 1 ≠ 0 :=
    ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr hx))
  have hvar : HasDerivAt (fun lam => B.waveVar c lam)
      (-((h : ℝ) * (c : ℝ) / (kB * (B.T : ℝ))) / lam ^ 2) lam := by
    unfold waveVar
    have h1 : HasDerivAt (fun l : ℝ => l * kB * (B.T : ℝ)) (kB * (B.T : ℝ)) lam := by
      simpa using ((hasDerivAt_id' lam).mul_const kB).mul_const (B.T : ℝ)
    have hden : lam * kB * (B.T : ℝ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (ne_of_gt hlam) (ne_of_gt kB_pos)) (ne_of_gt hT)
    convert (hasDerivAt_const lam ((h : ℝ) * (c : ℝ))).div h1 hden using 1
    field_simp
    ring
  have hcomp := (hasDerivAt_wienProfile 5 (B.waveVar c lam) he).comp lam hvar
  rw [← (hasDerivAt_wienProfile 5 (B.waveVar c lam) he).deriv] at hcomp
  have heq : (fun l => B.spectralRadianceWave c l) =ᶠ[𝓝 lam]
      (fun l => B.wavePrefactor c * wienProfile 5 (B.waveVar c l)) := by
    filter_upwards [Ioi_mem_nhds hlam] with y hy
    exact spectralRadianceWave_eq_profile B c y hT (mem_Ioi.mp hy)
  exact (hcomp.const_mul (B.wavePrefactor c)).congr_of_eventuallyEq heq


/-- Critical-point equation for the wavelength curve: `deriv = 0` iff the
  dimensionless variable satisfies the `n = 5` Wien equation. -/
lemma wave_crit_iff (B : BlackBody) (c : SpeedOfLight) (lam : ℝ)
    (hT : 0 < (B.T : ℝ)) (hlam : 0 < lam) :
    deriv (fun lam => B.spectralRadianceWave c lam) lam = 0
      ↔ B.waveVar c lam = 5 * (1 - Real.exp (-(B.waveVar c lam))) := by
  have hC0 : B.wavePrefactor c ≠ 0 :=
    ne_of_gt (wavePrefactor_pos B c hT)
  have hK0 : (-((h : ℝ) * (c : ℝ) / (kB * (B.T : ℝ))) / lam ^ 2) ≠ 0 := by
    apply div_ne_zero
    · exact neg_ne_zero.mpr (ne_of_gt (div_pos (mul_pos h_pos c.val_pos)
        (mul_pos kB_pos hT)))
    · exact pow_ne_zero 2 (ne_of_gt hlam)
  have hx : 0 < B.waveVar c lam := waveVar_pos B c lam hT hlam
  rw [(hasDerivAt_wave B c lam hT hlam).deriv]
  constructor
  · intro hzero
    have hmul := (mul_eq_zero.mp hzero).resolve_left hC0
    have hderiv := (mul_eq_zero.mp hmul).resolve_right hK0
    have hcrit := (wienProfile_crit_iff 5 (by norm_num)
      (B.waveVar c lam) hx).mp hderiv
    simpa using hcrit
  · intro hsol
    have hderiv : deriv (wienProfile 5) (B.waveVar c lam) = 0 :=
      (wienProfile_crit_iff 5 (by norm_num) (B.waveVar c lam) hx).mpr
        (by simpa using hsol)
    rw [hderiv, zero_mul, mul_zero]


/-- Derivative of the frequency curve at `ν > 0`, via the chain rule. -/
lemma hasDerivAt_freq (B : BlackBody) (c : SpeedOfLight) (ν : ℝ)
    (hT : 0 < (B.T : ℝ)) (hν : 0 < ν) :
    HasDerivAt (fun ν => B.spectralRadiance c ν)
      (B.freqPrefactor c
        * (deriv (wienProfile 3) (B.freqVar ν)
          * ((h : ℝ) / (kB * (B.T : ℝ))))) ν := by
  have hx : 0 < B.freqVar ν := freqVar_pos B ν hT hν
  have he : Real.exp (B.freqVar ν) - 1 ≠ 0 :=
    ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr hx))
  have hvar : HasDerivAt (fun ν => B.freqVar ν) ((h : ℝ) / (kB * (B.T : ℝ))) ν := by
    have hfun : (fun ν : ℝ => B.freqVar ν)
        = fun y => ((h : ℝ) / (kB * (B.T : ℝ))) * y := by
      ext y
      unfold freqVar
      ring
    rw [hfun]
    simpa using (hasDerivAt_id' ν).const_mul ((h : ℝ) / (kB * (B.T : ℝ)))
  have hcomp := (hasDerivAt_wienProfile 3 (B.freqVar ν) he).comp ν hvar
  rw [← (hasDerivAt_wienProfile 3 (B.freqVar ν) he).deriv] at hcomp
  have heq : (fun l => B.spectralRadiance c l) =ᶠ[𝓝 ν]
      (fun l => B.freqPrefactor c * wienProfile 3 (B.freqVar l)) := by
    filter_upwards [Ioi_mem_nhds hν] with y hy
    exact spectralRadiance_eq_profile B c y hT (mem_Ioi.mp hy)
  exact (hcomp.const_mul (B.freqPrefactor c)).congr_of_eventuallyEq heq


/-- Critical-point equation for the frequency curve: `deriv = 0` iff the
  dimensionless variable satisfies the `n = 3` Wien equation. -/
lemma freq_crit_iff (B : BlackBody) (c : SpeedOfLight) (ν : ℝ)
    (hT : 0 < (B.T : ℝ)) (hν : 0 < ν) :
    deriv (fun ν => B.spectralRadiance c ν) ν = 0
      ↔ B.freqVar ν = 3 * (1 - Real.exp (-(B.freqVar ν))) := by
  have hC0 : B.freqPrefactor c ≠ 0 :=
    ne_of_gt (freqPrefactor_pos B c hT)
  have hK0 : ((h : ℝ) / (kB * (B.T : ℝ))) ≠ 0 :=
    div_ne_zero (ne_of_gt h_pos)
      (mul_ne_zero (ne_of_gt kB_pos) (ne_of_gt hT))
  have hx : 0 < B.freqVar ν := freqVar_pos B ν hT hν
  rw [(hasDerivAt_freq B c ν hT hν).deriv]
  constructor
  · intro hzero
    have hmul := (mul_eq_zero.mp hzero).resolve_left hC0
    have hderiv := (mul_eq_zero.mp hmul).resolve_right hK0
    have hcrit := (wienProfile_crit_iff 3 (by norm_num)
      (B.freqVar ν) hx).mp hderiv
    simpa using hcrit
  · intro hsol
    have hderiv : deriv (wienProfile 3) (B.freqVar ν) = 0 :=
      (wienProfile_crit_iff 3 (by norm_num) (B.freqVar ν) hx).mpr
        (by simpa using hsol)
    rw [hderiv, zero_mul, mul_zero]


/-- The wavelength curve is continuous on `(0, ∞)`. -/
lemma spectralRadianceWave_continuousOn (B : BlackBody) (c : SpeedOfLight)
    (hT : 0 < (B.T : ℝ)) :
    ContinuousOn (fun lam => B.spectralRadianceWave c lam) (Ioi 0) := by
  have hcont : ContinuousOn
      (fun lam => B.wavePrefactor c * wienProfile 5 (B.waveVar c lam)) (Ioi 0) := by
    apply ContinuousOn.mul continuousOn_const _
    apply (wienProfile_continuousOn 5).comp _ _
    · unfold waveVar
      apply ContinuousOn.div continuousOn_const _ _
      · apply ContinuousOn.mul _ continuousOn_const
        apply ContinuousOn.mul _ continuousOn_const
        exact continuousOn_id
      · intro lam hlam
        exact mul_ne_zero (mul_ne_zero (ne_of_gt hlam) (ne_of_gt kB_pos))
          (ne_of_gt hT)
    · intro lam hlam
      exact waveVar_pos B c lam hT hlam
  exact hcont.congr fun lam hlam => spectralRadianceWave_eq_profile B c lam hT hlam


/-- The frequency curve is continuous on `(0, ∞)`. -/
lemma spectralRadiance_continuousOn (B : BlackBody) (c : SpeedOfLight)
    (hT : 0 < (B.T : ℝ)) :
    ContinuousOn (fun ν => B.spectralRadiance c ν) (Ioi 0) := by
  have hcont : ContinuousOn
      (fun ν => B.freqPrefactor c * wienProfile 3 (B.freqVar ν)) (Ioi 0) := by
    apply ContinuousOn.mul continuousOn_const _
    apply (wienProfile_continuousOn 3).comp _ _
    · unfold freqVar
      apply ContinuousOn.div _ continuousOn_const _
      · apply ContinuousOn.mul continuousOn_const continuousOn_id
      · intro ν hν
        exact mul_ne_zero (ne_of_gt kB_pos) (ne_of_gt hT)
    · intro ν hν
      exact freqVar_pos B ν hT hν
  exact hcont.congr fun ν hν => spectralRadiance_eq_profile B c ν hT hν


/-- The wavelength curve vanishes at infinity: `B(λ, T) → 0` as `λ → ∞`. -/
lemma spectralRadianceWave_tendsto_zero_atTop (B : BlackBody) (c : SpeedOfLight)
    (hT : 0 < (B.T : ℝ)) :
    Tendsto (fun lam => B.spectralRadianceWave c lam) atTop (𝓝 0) := by
  have hxlim : Tendsto (fun lam => B.waveVar c lam) atTop (𝓝[>] (0 : ℝ)) := by
    have hK : (0 : ℝ) < (h : ℝ) * (c : ℝ) / (kB * (B.T : ℝ)) :=
      div_pos (mul_pos h_pos c.val_pos) (mul_pos kB_pos hT)
    have hfun : ∀ lam : ℝ,
        B.waveVar c lam = ((h : ℝ) * (c : ℝ) / (kB * (B.T : ℝ))) * lam⁻¹ := by
      intro lam
      unfold waveVar
      rcases eq_or_ne lam 0 with rfl | hne
      · simp
      · have hk' : kB ≠ 0 := ne_of_gt kB_pos
        have hT' : (B.T : ℝ) ≠ 0 := ne_of_gt hT
        field_simp
    have hbase : Tendsto
        (fun lam : ℝ => ((h : ℝ) * (c : ℝ) / (kB * (B.T : ℝ))) * lam⁻¹)
          atTop (𝓝 0) := by
      have h := tendsto_inv_atTop_zero.const_mul
        ((h : ℝ) * (c : ℝ) / (kB * (B.T : ℝ)))
      simpa using h
    have hpos : ∀ᶠ lam : ℝ in atTop,
        ((h : ℝ) * (c : ℝ) / (kB * (B.T : ℝ))) * lam⁻¹ ∈ Ioi (0 : ℝ) := by
      filter_upwards [eventually_gt_atTop 0] with lam hlam
      exact mem_Ioi.mpr (mul_pos hK (inv_pos.mpr hlam))
    have hlim := tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      _ hbase hpos
    exact hlim.congr (fun lam => (hfun lam).symm)
  have hflim : Tendsto (fun lam : ℝ => wienProfile 5 (B.waveVar c lam)) atTop (𝓝 0) :=
    (wienProfile_tendsto_nhdsWithin_zero 5 (by decide)).comp hxlim
  have heq : (fun lam => B.spectralRadianceWave c lam) =ᶠ[atTop]
      (fun lam => B.wavePrefactor c * wienProfile 5 (B.waveVar c lam)) := by
    filter_upwards [eventually_gt_atTop 0] with lam hlam
    exact spectralRadianceWave_eq_profile B c lam hT hlam
  have hC := hflim.const_mul (B.wavePrefactor c)
  rw [mul_zero] at hC
  exact hC.congr' heq.symm


/-- The wavelength curve vanishes at the origin: `B(λ, T) → 0` as `λ → 0⁺`. -/
lemma spectralRadianceWave_tendsto_nhdsWithin_zero (B : BlackBody) (c : SpeedOfLight)
    (hT : 0 < (B.T : ℝ)) :
    Tendsto (fun lam => B.spectralRadianceWave c lam) (𝓝[>] 0) (𝓝 0) := by
  have hxlim : Tendsto (fun lam => B.waveVar c lam) (𝓝[>] (0 : ℝ)) atTop := by
    have hK : (0 : ℝ) < (h : ℝ) * (c : ℝ) / (kB * (B.T : ℝ)) :=
      div_pos (mul_pos h_pos c.val_pos) (mul_pos kB_pos hT)
    have hfun : ∀ lam : ℝ,
        B.waveVar c lam = lam⁻¹ * ((h : ℝ) * (c : ℝ) / (kB * (B.T : ℝ))) := by
      intro lam
      unfold waveVar
      rcases eq_or_ne lam 0 with rfl | hne
      · simp
      · have hk' : kB ≠ 0 := ne_of_gt kB_pos
        have hT' : (B.T : ℝ) ≠ 0 := ne_of_gt hT
        field_simp
    have hlim : Tendsto
        (fun lam : ℝ => lam⁻¹ * ((h : ℝ) * (c : ℝ) / (kB * (B.T : ℝ))))
          (𝓝[>] 0) atTop :=
      tendsto_inv_nhdsGT_zero.atTop_mul_const hK
    exact hlim.congr (fun lam => (hfun lam).symm)
  have hflim : Tendsto (fun lam : ℝ => wienProfile 5 (B.waveVar c lam)) (𝓝[>] 0) (𝓝 0) :=
    (wienProfile_tendsto_zero_atTop 5).comp hxlim
  have heq : (fun lam => B.spectralRadianceWave c lam) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun lam => B.wavePrefactor c * wienProfile 5 (B.waveVar c lam)) := by
    filter_upwards [self_mem_nhdsWithin] with lam hlam
    exact spectralRadianceWave_eq_profile B c lam hT hlam
  have hC := hflim.const_mul (B.wavePrefactor c)
  rw [mul_zero] at hC
  exact hC.congr' heq.symm


/-- The frequency curve vanishes at infinity: `B(ν, T) → 0` as `ν → ∞`. -/
lemma spectralRadiance_tendsto_zero_atTop (B : BlackBody) (c : SpeedOfLight)
    (hT : 0 < (B.T : ℝ)) :
    Tendsto (fun ν => B.spectralRadiance c ν) atTop (𝓝 0) := by
  have hxlim : Tendsto (fun ν => B.freqVar ν) atTop atTop := by
    have hK : (0 : ℝ) < (h : ℝ) / (kB * (B.T : ℝ)) :=
      div_pos h_pos (mul_pos kB_pos hT)
    have hfun : ∀ ν : ℝ, B.freqVar ν = ν * ((h : ℝ) / (kB * (B.T : ℝ))) := by
      intro ν
      unfold freqVar
      ring
    have hlim : Tendsto (fun ν : ℝ => ν * ((h : ℝ) / (kB * (B.T : ℝ)))) atTop atTop :=
      tendsto_id.atTop_mul_const hK
    exact hlim.congr (fun ν => (hfun ν).symm)
  have hflim : Tendsto (fun ν : ℝ => wienProfile 3 (B.freqVar ν)) atTop (𝓝 0) :=
    (wienProfile_tendsto_zero_atTop 3).comp hxlim
  have heq : (fun ν => B.spectralRadiance c ν) =ᶠ[atTop]
      (fun ν => B.freqPrefactor c * wienProfile 3 (B.freqVar ν)) := by
    filter_upwards [eventually_gt_atTop 0] with ν hν
    exact spectralRadiance_eq_profile B c ν hT hν
  have hC := hflim.const_mul (B.freqPrefactor c)
  rw [mul_zero] at hC
  exact hC.congr' heq.symm


/-- The frequency curve vanishes at the origin: `B(ν, T) → 0` as `ν → 0⁺`. -/
lemma spectralRadiance_tendsto_nhdsWithin_zero (B : BlackBody) (c : SpeedOfLight)
    (hT : 0 < (B.T : ℝ)) :
    Tendsto (fun ν => B.spectralRadiance c ν) (𝓝[>] 0) (𝓝 0) := by
  have hxlim : Tendsto (fun ν => B.freqVar ν) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    have hK : (0 : ℝ) < (h : ℝ) / (kB * (B.T : ℝ)) :=
      div_pos h_pos (mul_pos kB_pos hT)
    have hfun : ∀ ν : ℝ, B.freqVar ν = ((h : ℝ) / (kB * (B.T : ℝ))) * ν := by
      intro ν
      unfold freqVar
      ring
    have hbase : Tendsto (fun ν : ℝ => ((h : ℝ) / (kB * (B.T : ℝ))) * ν)
        (𝓝[>] 0) (𝓝 0) := by
      have hid : Tendsto id (𝓝[>] (0 : ℝ)) (𝓝 0) :=
        tendsto_id.mono_right nhdsWithin_le_nhds
      have h := hid.const_mul ((h : ℝ) / (kB * (B.T : ℝ)))
      simpa using h
    have hlim := tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      _ hbase (a := (0 : ℝ)) (s := Ioi 0) (l := 𝓝[>] (0 : ℝ)) ?_
    · exact hlim.congr (fun ν => (hfun ν).symm)
    · filter_upwards [self_mem_nhdsWithin] with ν hν
      exact mem_Ioi.mpr (mul_pos hK hν)
  have hflim : Tendsto (fun ν : ℝ => wienProfile 3 (B.freqVar ν)) (𝓝[>] 0) (𝓝 0) :=
    (wienProfile_tendsto_nhdsWithin_zero 3 (by decide)).comp hxlim
  have heq : (fun ν => B.spectralRadiance c ν) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ν => B.freqPrefactor c * wienProfile 3 (B.freqVar ν)) := by
    filter_upwards [self_mem_nhdsWithin] with ν hν
    exact spectralRadiance_eq_profile B c ν hT hν
  have hC := hflim.const_mul (B.freqPrefactor c)
  rw [mul_zero] at hC
  exact hC.congr' heq.symm


/-- The wavelength curve attains its global maximum on `(0, ∞)` at
  `λ* = h c / (kB T x₅)`: the peak of the blackbody spectrum. -/
lemma spectralRadianceWave_isMaxOn (B : BlackBody) (c : SpeedOfLight)
    (hT : 0 < (B.T : ℝ)) :
    IsMaxOn (fun lam => B.spectralRadianceWave c lam) (Ioi 0)
      ((h : ℝ) * (c : ℝ) / (kB * (B.T : ℝ) * wienConstant5)) := by
  have hrpos : 0 < wienConstant5 := wienConstant5_pos
  have hlamstar : 0 < (h : ℝ) * (c : ℝ) / (kB * (B.T : ℝ) * wienConstant5) :=
    div_pos (mul_pos h_pos c.val_pos) (mul_pos (mul_pos kB_pos hT) hrpos)
  have hstar : B.waveVar c ((h : ℝ) * (c : ℝ) / (kB * (B.T : ℝ) * wienConstant5))
      = wienConstant5 := by
    unfold waveVar
    have hk' : kB ≠ 0 := ne_of_gt kB_pos
    have hT' : (B.T : ℝ) ≠ 0 := ne_of_gt hT
    have hx5 : wienConstant5 ≠ 0 := ne_of_gt hrpos
    have hden : kB * (B.T : ℝ) * wienConstant5 ≠ 0 :=
      mul_ne_zero (mul_ne_zero hk' hT') hx5
    field_simp
  have hC : 0 ≤ B.wavePrefactor c :=
    le_of_lt (wavePrefactor_pos B c hT)
  intro lam hlam
  change B.spectralRadianceWave c lam
    ≤ B.spectralRadianceWave c
      ((h : ℝ) * (c : ℝ) / (kB * (B.T : ℝ) * wienConstant5))
  have hx : 0 < B.waveVar c lam :=
    waveVar_pos B c lam hT hlam
  have hprof := (isMaxOn_iff.mp (wienProfile_isMaxOn 5 (by decide))) _ hx
  have hprof' : wienProfile 5 (B.waveVar c lam)
      ≤ wienProfile 5 wienConstant5 := hprof
  have e1 : B.spectralRadianceWave c lam = B.wavePrefactor c * wienProfile 5 (B.waveVar c lam) :=
    spectralRadianceWave_eq_profile B c lam hT hlam
  have e2 : B.spectralRadianceWave c
      ((h : ℝ) * (c : ℝ) / (kB * (B.T : ℝ) * wienConstant5))
      = B.wavePrefactor c * wienProfile 5 (B.waveVar c
        ((h : ℝ) * (c : ℝ) / (kB * (B.T : ℝ) * wienConstant5))) :=
    spectralRadianceWave_eq_profile B c
      ((h : ℝ) * (c : ℝ) / (kB * (B.T : ℝ) * wienConstant5)) hT hlamstar
  rw [e1, e2, hstar]
  exact mul_le_mul_of_nonneg_left hprof' hC

/-- The frequency curve attains its global maximum on `(0, ∞)` at
  `ν* = kB T x₃ / h`. -/
lemma spectralRadiance_isMaxOn (B : BlackBody) (c : SpeedOfLight)
    (hT : 0 < (B.T : ℝ)) :
    IsMaxOn (fun ν => B.spectralRadiance c ν) (Ioi 0)
      (kB * (B.T : ℝ) * wienConstant3 / (h : ℝ)) := by
  have hrpos : 0 < wienConstant3 := wienConstant3_pos
  have hnustar : 0 < kB * (B.T : ℝ) * wienConstant3 / (h : ℝ) :=
    div_pos (mul_pos (mul_pos kB_pos hT) hrpos) h_pos
  have hstar : B.freqVar (kB * (B.T : ℝ) * wienConstant3 / (h : ℝ))
      = wienConstant3 := by
    unfold freqVar
    have hh' : (h : ℝ) ≠ 0 := ne_of_gt h_pos
    have hk' : kB ≠ 0 := ne_of_gt kB_pos
    have hT' : (B.T : ℝ) ≠ 0 := ne_of_gt hT
    field_simp
  have hC : 0 ≤ B.freqPrefactor c :=
    le_of_lt (freqPrefactor_pos B c hT)
  intro ν hν
  change B.spectralRadiance c ν
    ≤ B.spectralRadiance c (kB * (B.T : ℝ) * wienConstant3 / (h : ℝ))
  have hx : 0 < B.freqVar ν := freqVar_pos B ν hT hν
  have hprof := (isMaxOn_iff.mp (wienProfile_isMaxOn 3 (by decide))) _ hx
  have hprof' : wienProfile 3 (B.freqVar ν)
      ≤ wienProfile 3 wienConstant3 := hprof
  have e1 : B.spectralRadiance c ν = B.freqPrefactor c * wienProfile 3 (B.freqVar ν) :=
    spectralRadiance_eq_profile B c ν hT hν
  have e2 : B.spectralRadiance c
      (kB * (B.T : ℝ) * wienConstant3 / (h : ℝ))
      = B.freqPrefactor c * wienProfile 3
        (B.freqVar (kB * (B.T : ℝ) * wienConstant3 / (h : ℝ))) :=
    spectralRadiance_eq_profile B c
      (kB * (B.T : ℝ) * wienConstant3 / (h : ℝ)) hT hnustar
  rw [e1, e2, hstar]
  exact mul_le_mul_of_nonneg_left hprof' hC


/-!

## C. Wien's displacement laws

The main physical laws:
1. `wien_displacement_wave`: if `lam₁` maximizes `B(lam, T₁)` and `lam₂` maximizes
   `B(lam, T₂)`, then `lam₁ T₁ = lam₂ T₂`.
2. `wien_displacement_freq`: if `ν₁` maximizes `B(ν, T₁)` and `ν₂` maximizes
   `B(ν, T₂)`, then `ν₁ / T₁ = ν₂ / T₂`.
3. `wien_peak_product`: `lam T = h c / (kB x₅)`.
4. `wien_peak_ratio`: `ν / T = kB x₃ / h`.
-/

/-- Wien's displacement law (wavelength form): critical wavelengths at different
  temperatures satisfy `λ₁ T₁ = λ₂ T₂`. -/
lemma wien_displacement_wave (B₁ B₂ : BlackBody) (c : SpeedOfLight) (lam₁ lam₂ : ℝ)
    (hT₁ : 0 < (B₁.T : ℝ)) (hT₂ : 0 < (B₂.T : ℝ))
    (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂)
    (hcrit₁ : deriv (fun lam => B₁.spectralRadianceWave c lam) lam₁ = 0)
    (hcrit₂ : deriv (fun lam => B₂.spectralRadianceWave c lam) lam₂ = 0) :
    lam₁ * (B₁.T : ℝ) = lam₂ * (B₂.T : ℝ) := by
  have hx₁ : 0 < B₁.waveVar c lam₁ := waveVar_pos B₁ c lam₁ hT₁ hlam₁
  have hx₂ : 0 < B₂.waveVar c lam₂ := waveVar_pos B₂ c lam₂ hT₂ hlam₂
  have e₁ := (wave_crit_iff B₁ c lam₁ hT₁ hlam₁).mp hcrit₁
  have e₂ := (wave_crit_iff B₂ c lam₂ hT₂ hlam₂).mp hcrit₂
  have hx₁' : wienH 5 (B₁.waveVar c lam₁) = 0 := by
    unfold wienH
    linarith [e₁]
  have hx₂' : wienH 5 (B₂.waveVar c lam₂) = 0 := by
    unfold wienH
    linarith [e₂]
  -- uniqueness forces the dimensionless variables to agree
  have huniq₁ := wienRoot_unique 5 (by norm_num) _ hx₁ hx₁'
  have huniq₂ := wienRoot_unique 5 (by norm_num) _ hx₂ hx₂'
  have hxx : B₁.waveVar c lam₁ = B₂.waveVar c lam₂ := by
    rw [huniq₁, huniq₂]
  -- hence `lam₁ T₁ = lam₂ T₂`
  have hh' : (h : ℝ) ≠ 0 := ne_of_gt h_pos
  have hc' : (c : ℝ) ≠ 0 := ne_of_gt c.val_pos
  have hk' : kB ≠ 0 := ne_of_gt kB_pos
  unfold waveVar at hxx
  field_simp at hxx ⊢
  linarith [hxx]


/-- Wien's displacement law (frequency form): critical frequencies at different
  temperatures satisfy `ν₁ / T₁ = ν₂ / T₂`. -/
lemma wien_displacement_freq (B₁ B₂ : BlackBody) (c : SpeedOfLight) (ν₁ ν₂ : ℝ)
    (hT₁ : 0 < (B₁.T : ℝ)) (hT₂ : 0 < (B₂.T : ℝ))
    (hν₁ : 0 < ν₁) (hν₂ : 0 < ν₂)
    (hcrit₁ : deriv (fun ν => B₁.spectralRadiance c ν) ν₁ = 0)
    (hcrit₂ : deriv (fun ν => B₂.spectralRadiance c ν) ν₂ = 0) :
    ν₁ / (B₁.T : ℝ) = ν₂ / (B₂.T : ℝ) := by
  have hx₁ : 0 < B₁.freqVar ν₁ := freqVar_pos B₁ ν₁ hT₁ hν₁
  have hx₂ : 0 < B₂.freqVar ν₂ := freqVar_pos B₂ ν₂ hT₂ hν₂
  have e₁ := (freq_crit_iff B₁ c ν₁ hT₁ hν₁).mp hcrit₁
  have e₂ := (freq_crit_iff B₂ c ν₂ hT₂ hν₂).mp hcrit₂
  have hx₁' : wienH 3 (B₁.freqVar ν₁) = 0 := by
    unfold wienH
    linarith [e₁]
  have hx₂' : wienH 3 (B₂.freqVar ν₂) = 0 := by
    unfold wienH
    linarith [e₂]
  have huniq₁ := wienRoot_unique 3 (by norm_num) _ hx₁ hx₁'
  have huniq₂ := wienRoot_unique 3 (by norm_num) _ hx₂ hx₂'
  have hxx : B₁.freqVar ν₁ = B₂.freqVar ν₂ := by
    rw [huniq₁, huniq₂]
  have hh' : (h : ℝ) ≠ 0 := ne_of_gt h_pos
  have hk' : kB ≠ 0 := ne_of_gt kB_pos
  have hT₁' : (B₁.T : ℝ) ≠ 0 := ne_of_gt hT₁
  have hT₂' : (B₂.T : ℝ) ≠ 0 := ne_of_gt hT₂
  unfold freqVar at hxx
  field_simp at hxx ⊢
  linarith [hxx]


/-- The peak product `lam T` equals `h c / (kB x₅)` (wavelength Wien constant). -/
lemma wien_peak_product (B : BlackBody) (c : SpeedOfLight) (lam : ℝ)
    (hT : 0 < (B.T : ℝ)) (hlam : 0 < lam)
    (hcrit : deriv (fun lam => B.spectralRadianceWave c lam) lam = 0) :
    lam * (B.T : ℝ) = (h : ℝ) * (c : ℝ) / (kB * wienConstant5) := by
  have hx : 0 < B.waveVar c lam := waveVar_pos B c lam hT hlam
  have e := (wave_crit_iff B c lam hT hlam).mp hcrit
  have hx' : wienH 5 (B.waveVar c lam) = 0 := by
    unfold wienH
    linarith [e]
  have huniq := wienRoot_unique 5 (by norm_num) _ hx hx'
  have hrpos := wienConstant5_pos
  have hh' : (h : ℝ) ≠ 0 := ne_of_gt h_pos
  have hc' : (c : ℝ) ≠ 0 := ne_of_gt c.val_pos
  have hk' : kB ≠ 0 := ne_of_gt kB_pos
  have hT' : (B.T : ℝ) ≠ 0 := ne_of_gt hT
  have hlam' : lam ≠ 0 := ne_of_gt hlam
  have hr' : wienConstant5 ≠ 0 := ne_of_gt hrpos
  unfold waveVar at huniq
  unfold wienConstant5 at hr' hrpos ⊢
  field_simp at huniq ⊢
  linarith [huniq]


/-- The peak ratio `ν / T` equals `kB x₃ / h` (frequency Wien constant). -/
lemma wien_peak_ratio (B : BlackBody) (c : SpeedOfLight) (ν : ℝ)
    (hT : 0 < (B.T : ℝ)) (hν : 0 < ν)
    (hcrit : deriv (fun ν => B.spectralRadiance c ν) ν = 0) :
    ν / (B.T : ℝ) = kB * wienConstant3 / (h : ℝ) := by
  have hx : 0 < B.freqVar ν := freqVar_pos B ν hT hν
  have e := (freq_crit_iff B c ν hT hν).mp hcrit
  have hx' : wienH 3 (B.freqVar ν) = 0 := by
    unfold wienH
    linarith [e]
  have huniq := wienRoot_unique 3 (by norm_num) _ hx hx'
  have hh' : (h : ℝ) ≠ 0 := ne_of_gt h_pos
  have hk' : kB ≠ 0 := ne_of_gt kB_pos
  have hT' : (B.T : ℝ) ≠ 0 := ne_of_gt hT
  unfold freqVar at huniq
  unfold wienConstant3 at ⊢
  have h1 : (h : ℝ) * ν = kB * (B.T : ℝ) * wienRoot 3 (by norm_num) := by
    field_simp at huniq; exact huniq
  field_simp
  linarith

end BlackBody
