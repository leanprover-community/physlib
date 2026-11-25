/-
Copyright (c) 2026 AMPS formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AMPS formalization contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The leading Hawking packet envelope

The leading flat-band envelope.

## i. Overview

Hawking, *Particle creation by black holes* (1975), Eqs. (2.22)–(2.25),
bins the outgoing Killing frequency. In the leading approximation that fixes
the slowly varying coefficient over a bin, the variable part of the precursor
coefficient is the Fourier integral of a flat band. Its argument is the affine
log-frequency coordinate `z = log(ω′)/κ - u₀`. We calculate the integral and bound
its squared spectral tail in that coordinate. The bound does not estimate the
error from taking the radial scattering coefficient constant over the bin.

## ii. Key results

* `envelope_eq`
* `envelope_sq_le`

## iii. Table of contents

- A. The leading flat-band envelope

## iv. References

* [ref: Almheiri2013]
* [ref: Hawking1975ParticleCreation]

## A. The leading flat-band envelope
-/

@[expose] public section

noncomputable section

namespace AMPS.PacketSpectrum

open MeasureTheory Set Complex

/-- Fourier envelope from a flat outgoing frequency bin. The log-frequency
argument in the collapse approximation is supplied separately. -/
def envelope (lo hi z : ℝ) : ℂ :=
  ∫ ω in lo..hi, Complex.exp (((z : ℂ) * Complex.I) * (ω : ℂ))

/-- Exact flat-band packet integral appearing in Hawking Eq. (2.25). -/
lemma envelope_eq {lo hi z : ℝ} (hz : z ≠ 0) :
    envelope lo hi z =
      (Complex.exp ((z : ℂ) * Complex.I * (hi : ℂ)) -
        Complex.exp ((z : ℂ) * Complex.I * (lo : ℂ))) / ((z : ℂ) * Complex.I) := by
  exact integral_exp_mul_complex (mul_ne_zero (by exact_mod_cast hz) Complex.I_ne_zero)

/-- The square of the flat-band envelope decays quadratically in log frequency,
with a bound independent of the center and width of the outgoing bin. -/
lemma envelope_sq_le {lo hi z : ℝ} (hz : z ≠ 0) :
    ‖envelope lo hi z‖ ^ 2 ≤ 4 * z ^ (-2 : ℝ) := by
  have hunit (x : ℝ) : ‖Complex.exp ((z : ℂ) * I * (x : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re]
  rw [envelope_eq hz, norm_div, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]
  have hsub := norm_sub_le (Complex.exp ((z : ℂ) * I * (hi : ℂ)))
    (Complex.exp ((z : ℂ) * I * (lo : ℂ)))
  rw [hunit, hunit] at hsub
  have hd := abs_pos.mpr hz
  have hbound := div_le_div_of_nonneg_right hsub hd.le
  refine (pow_le_pow_left₀ (div_nonneg (norm_nonneg _) hd.le) hbound 2).trans ?_
  rw [div_pow, sq_abs, show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
  norm_num [zpow_neg, div_eq_mul_inv]

/-- The high log-frequency tail of the squared envelope beyond `w` is at most
`4/w`. In the precursor density the logarithmic coordinate absorbs the
`dω′/ω′` factor. This statement uses unnormalized Fourier weight. -/
lemma upper_log_frequency_tail {lo hi w : ℝ} (hw : 0 < w) :
    (∫ z in Ioi w, ‖envelope lo hi z‖ ^ 2) ≤ 4 / w := by
  let bound := fun z : ℝ => 4 * z ^ (-2 : ℝ)
  have hb : IntegrableOn bound (Ioi w) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hw).const_mul 4
  have hcomp : (fun z => ‖envelope lo hi z‖ ^ 2) ≤ᵐ[volume.restrict (Ioi w)] bound := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    exact envelope_sq_le (hw.trans hz).ne'
  let closed := fun z : ℝ =>
    ‖(Complex.exp ((z : ℂ) * I * (hi : ℂ)) -
      Complex.exp ((z : ℂ) * I * (lo : ℂ))) / ((z : ℂ) * I)‖ ^ 2
  have hclosed : Measurable closed := by dsimp [closed]; fun_prop
  have heq : closed =ᵐ[volume.restrict (Ioi w)] fun z => ‖envelope lo hi z‖ ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    rw [envelope_eq (hw.trans hz).ne']
  have hf : IntegrableOn (fun z => ‖envelope lo hi z‖ ^ 2) (Ioi w) :=
    hb.mono' (hclosed.aestronglyMeasurable.congr heq) (by
      filter_upwards [hcomp] with z hz
      simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖envelope lo hi z‖)] using hz)
  calc
    _ ≤ ∫ z in Ioi w, bound z := integral_mono_ae hf hb hcomp
    _ = _ := by
      rw [show bound = fun z => 4 * z ^ (-2 : ℝ) from rfl, integral_const_mul,
        integral_Ioi_rpow_of_lt (by norm_num) hw]
      norm_num [show (-2 : ℝ) + 1 = (-1 : ℝ) by norm_num, Real.rpow_neg_one, div_eq_mul_inv]

/-- Exact sinc envelope in coordinates centered on the Killing-frequency bin.
The scale records its nonzero width and the formula extends through the center
of the precursor spectrum. -/
lemma centered_envelope (width z : ℝ) :
    envelope (-width) width z = ((2 * width * Real.sinc (width * z) : ℝ) : ℂ) := by
  by_cases hz : z = 0
  · subst z
    simp [envelope, Real.sinc_zero]
    ring
  let f := fun x : ℝ => Complex.exp ((x : ℂ) * I)
  have hs := intervalIntegral.smul_integral_comp_mul_left f (a := -width) (b := width) z
  change z • (∫ ω in -width..width, f (z * ω)) = ∫ ω in z * -width..z * width, f ω at hs
  simp only [f, Complex.ofReal_mul] at hs
  have hid :
      (fun ω : ℝ => Complex.exp (((z : ℂ) * (ω : ℂ)) * I)) =
        fun ω : ℝ => Complex.exp (((z : ℂ) * I) * (ω : ℂ)) := by
    funext ω
    congr 1
    ring
  rw [mul_neg, hid] at hs
  change z • envelope (-width) width z =
    ∫ ω in -(z * width)..z * width, Complex.exp ((ω : ℂ) * I) at hs
  rw [integral_exp_mul_I_eq_sinc, Complex.real_smul] at hs
  apply mul_left_cancel₀ (show (z : ℂ) ≠ 0 by exact_mod_cast hz)
  rw [hs, mul_comm width z]
  push_cast
  ring

/-- Every nontrivial flat bin has a strictly positive logarithmic-frequency
density on an interval about its precursor-frequency center. -/
lemma centered_envelope_positive_interval {width : ℝ} (hw : 0 < width) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ Ioo (-δ) δ, width ≤ ‖envelope (-width) width z‖ := by
  have hc : Continuous (fun z : ℝ => envelope (-width) width z) := by
    simp_rw [centered_envelope]
    exact Complex.continuous_ofReal.comp (continuous_const.mul
      (Real.continuous_sinc.comp (continuous_const.mul continuous_id)))
  have hzero : ‖envelope (-width) width 0‖ = 2 * width := by
    rw [centered_envelope]
    simp [Real.norm_of_nonneg hw.le]
  obtain ⟨δ, hd, hδ⟩ := Metric.continuousAt_iff.mp (hc.norm.continuousAt (x := 0)) width hw
  refine ⟨δ, hd, fun z hz => ?_⟩
  have hz' : dist z 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_lt]
    exact hz
  have h := hδ hz'
  rw [Real.dist_eq, hzero] at h
  linarith [(abs_lt.mp h).1]

end AMPS.PacketSpectrum
