/-
Copyright (c) 2026 Qianli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qianli Ma
-/
module

public import Physlib.QuantumMechanics.RectangularBarrier.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!

# Stationary probability current at a rectangular barrier

Conservation of the one-dimensional current across both barrier interfaces.

## i. Overview

A stationary wave is represented by a function of the real spatial coordinate.
For a real potential, the Schrödinger equation makes the derivative of the
probability current vanish within each region. Continuity of the wave and its
first derivative gives the same current on both sides of each interface.
For a wave incident from the left, the common exterior wave number lets us
express this conservation as a balance of the squared amplitudes.

## ii. Key results

- `RectangularBarrier.probabilityCurrent_eq` gives equality of the current at any
  two positions for a classical stationary wave of the barrier.
- `RectangularBarrier.reflection_add_transmission_eq_one` gives the normalized
  flux balance for a stationary wave with the stated exterior plane-wave forms.

## iii. Table of contents

- A. Probability current and stationary waves
- B. Conservation across the interfaces
- C. Exterior plane waves and flux balance

## iv. References

* None.

-/

@[expose] public section

noncomputable section

namespace QuantumMechanics.RectangularBarrier

open Set Constants
open scoped ComplexConjugate Topology

/-! ## A. Probability current and stationary waves -/

/-- The probability current along the real spatial coordinate, with the
particle mass of the rectangular barrier and the reduced Planck constant. -/
def probabilityCurrent (Q : RectangularBarrier) (ψ : ℝ → ℂ) (x : ℝ) : ℝ :=
  ((ℏ : ℝ) / Q.m) * (conj (ψ x) * deriv ψ x).im

/-- A globally continuously differentiable stationary wave of energy `E`.
The second derivative obeys the Schrödinger equation on each open region
delimited by the two edges of the barrier. -/
structure IsStationaryWave (Q : RectangularBarrier) (E : ℝ) (ψ : ℝ → ℂ) : Prop where
  contDiff : ContDiff ℝ 1 ψ
  equation : ∀ x : ℝ, x ≠ Q.lower → x ≠ Q.upper →
    HasDerivAt (deriv ψ)
      ((2 * Q.m * (Q.potentialFunction ⟨fun _ => x⟩ - E) / (ℏ : ℝ) ^ 2) • ψ x) x

/-! ## B. Conservation across the interfaces -/

private lemma hasDerivAt_current (Q : RectangularBarrier) {ψ v : ℝ → ℂ} {x c : ℝ}
    (hψ : HasDerivAt ψ (v x) x) (hv : HasDerivAt v (c • ψ x) x) :
    HasDerivAt (fun t => ((ℏ : ℝ) / Q.m) * (conj (ψ t) * v t).im) 0 x := by
  have hconj := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x hψ
  have hprod := hconj.mul hv
  have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hprod
  convert him.const_mul ((ℏ : ℝ) / Q.m) using 1
  · rfl
  · simp [Complex.real_smul, Complex.mul_re, Complex.mul_im]
    ring

private lemma eq_on_closure_of_deriv_zero {f : ℝ → ℝ} {s : Set ℝ}
    (hf : Continuous f) (hs : IsOpen s) (hc : Convex ℝ s) (hne : s.Nonempty)
    (hd : ∀ x ∈ s, HasDerivAt f 0 x) {x y : ℝ}
    (hx : x ∈ closure s) (hy : y ∈ closure s) : f x = f y := by
  obtain ⟨z, hz⟩ := hne
  have hsub : closure s ⊆ {t | f t = f z} :=
    (isClosed_eq hf continuous_const).closure_subset_iff.mpr fun t ht =>
      hs.is_const_of_deriv_eq_zero hc.isPreconnected
        (fun w hw => (hd w hw).differentiableAt.differentiableWithinAt)
        (fun w hw => (hd w hw).deriv) ht hz
  exact (hsub hx).trans (hsub hy).symm

/-- For a stationary wave of a rectangular barrier, the probability current
is independent of position, including at both interfaces. -/
lemma probabilityCurrent_eq {Q : RectangularBarrier} {E : ℝ} {ψ : ℝ → ℂ}
    (hψ : Q.IsStationaryWave E ψ) (x y : ℝ) :
    Q.probabilityCurrent ψ x = Q.probabilityCurrent ψ y := by
  obtain ⟨h₁, h₂⟩ := contDiff_one_iff_deriv.mp hψ.contDiff
  have hj : Continuous (Q.probabilityCurrent ψ) := by
    unfold probabilityCurrent
    exact continuous_const.mul
      (Complex.continuous_im.comp ((Complex.continuous_conj.comp h₁.continuous).mul h₂))
  have hd (t : ℝ) (hl : t ≠ Q.lower) (hr : t ≠ Q.upper) :
      HasDerivAt (Q.probabilityCurrent ψ) 0 t :=
    hasDerivAt_current Q (h₁ t).hasDerivAt (hψ.equation t hl hr)
  have hmid : ∀ t ∈ Icc Q.lower Q.upper,
      Q.probabilityCurrent ψ t = Q.probabilityCurrent ψ Q.lower := by
    intro t ht
    rw [← closure_Ioo Q.h_bounds.ne] at ht
    exact eq_on_closure_of_deriv_zero hj isOpen_Ioo (convex_Ioo _ _)
      (nonempty_Ioo.mpr Q.h_bounds)
      (fun w hw => hd w hw.1.ne' hw.2.ne) ht
      (by rw [closure_Ioo Q.h_bounds.ne]; exact ⟨le_rfl, Q.h_bounds.le⟩)
  have hAll (t : ℝ) : Q.probabilityCurrent ψ t = Q.probabilityCurrent ψ Q.lower := by
    by_cases hl : t ≤ Q.lower
    · exact eq_on_closure_of_deriv_zero hj isOpen_Iio (convex_Iio _) nonempty_Iio
        (fun w (hw : w < Q.lower) => hd w hw.ne (hw.trans Q.h_bounds).ne)
        (by rwa [closure_Iio]) (by rw [closure_Iio]; exact le_rfl)
    by_cases hu : t ≤ Q.upper
    · exact hmid t ⟨(le_of_not_ge hl), hu⟩
    have hr : Q.probabilityCurrent ψ t = Q.probabilityCurrent ψ Q.upper :=
      eq_on_closure_of_deriv_zero hj isOpen_Ioi (convex_Ioi _) nonempty_Ioi
        (fun w (hw : Q.upper < w) => hd w (Q.h_bounds.trans hw).ne' hw.ne')
        (by rw [closure_Ioi]; exact le_of_not_ge hu) (by rw [closure_Ioi]; exact le_rfl)
    exact hr.trans (hmid Q.upper ⟨Q.h_bounds.le, le_rfl⟩)
  exact (hAll x).trans (hAll y).symm

/-! ## C. Exterior plane waves and flux balance -/

/-- The plane wave with wave number `k` at position `x`. -/
def planeWave (k x : ℝ) : ℂ :=
  Complex.exp ((k : ℂ) * (x : ℂ) * Complex.I)

private lemma hasDerivAt_planeWave (k x : ℝ) :
    HasDerivAt (planeWave k) ((k : ℂ) * Complex.I * planeWave k x) x := by
  have h : HasDerivAt (planeWave k) (planeWave k x * ((k : ℂ) * 1 * Complex.I)) x :=
    ((((hasDerivAt_id x).ofReal_comp).const_mul (k : ℂ)).mul_const Complex.I).cexp
  exact h.congr_deriv (by ring)

private lemma norm_planeWave (k x : ℝ) : ‖planeWave k x‖ = 1 := by
  rw [planeWave, ← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I]

private lemma planeWave_flux_algebra (u v : ℂ) (k : ℝ) :
    (conj (u + v) * ((k : ℂ) * Complex.I * (u - v))).im =
      k * (‖u‖ ^ 2 - ‖v‖ ^ 2) := by
  simp [Complex.sq_norm, Complex.normSq_apply, Complex.mul_im, Complex.mul_re,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  ring

/-- The current of two counterpropagating plane waves is the difference of their currents. -/
lemma probabilityCurrent_two_plane_waves (Q : RectangularBarrier) (k : ℝ) (A B : ℂ) (x : ℝ) :
    Q.probabilityCurrent (fun y => A * planeWave k y + B * planeWave (-k) y) x =
      ((ℏ : ℝ) / Q.m * k) * (‖A‖ ^ 2 - ‖B‖ ^ 2) := by
  have h := ((hasDerivAt_planeWave k x).const_mul A).add
    ((hasDerivAt_planeWave (-k) x).const_mul B)
  have hderiv : HasDerivAt (fun y => A * planeWave k y + B * planeWave (-k) y)
      ((k : ℂ) * Complex.I * (A * planeWave k x - B * planeWave (-k) x)) x := by
    refine h.congr_deriv ?_
    push_cast
    ring
  rw [probabilityCurrent, hderiv.deriv, planeWave_flux_algebra, ← mul_assoc]
  simp only [norm_mul, norm_planeWave, mul_one]

private lemma probabilityCurrent_congr (Q : RectangularBarrier) {ψ φ : ℝ → ℂ} {x : ℝ}
    (h : ψ =ᶠ[𝓝 x] φ) : Q.probabilityCurrent ψ x = Q.probabilityCurrent φ x := by
  simp only [probabilityCurrent, h.eq_of_nhds, h.deriv_eq]

variable {Q : RectangularBarrier} {E k : ℝ} {ψ : ℝ → ℂ} {A B C : ℂ}

/-- For a stationary wave with a left incident wave and no right incident wave, the incident
squared amplitude equals the sum of the reflected and transmitted squared amplitudes. -/
lemma incident_norm_sq_eq (hψ : Q.IsStationaryWave E ψ) (hk : 0 < k)
    (hLeft : EqOn ψ (fun x => A * planeWave k x + B * planeWave (-k) x) (Iio Q.lower))
    (hRight : EqOn ψ (fun x => C * planeWave k x) (Ioi Q.upper)) :
    ‖A‖ ^ 2 = ‖B‖ ^ 2 + ‖C‖ ^ 2 := by
  let xL := Q.lower - 1
  let xR := Q.upper + 1
  have hL : ψ =ᶠ[𝓝 xL] fun x => A * planeWave k x + B * planeWave (-k) x := by
    filter_upwards [Iio_mem_nhds (sub_lt_self Q.lower zero_lt_one)] with x hx using hLeft hx
  have hR : ψ =ᶠ[𝓝 xR] fun x => C * planeWave k x + 0 * planeWave (-k) x := by
    filter_upwards [Ioi_mem_nhds (lt_add_of_pos_right Q.upper zero_lt_one)] with x hx
    simpa only [zero_mul, add_zero] using hRight hx
  have hj := probabilityCurrent_eq hψ xL xR
  rw [probabilityCurrent_congr Q hL, probabilityCurrent_congr Q hR,
    probabilityCurrent_two_plane_waves, probabilityCurrent_two_plane_waves] at hj
  have hc : ((ℏ : ℝ) / Q.m * k) ≠ 0 :=
    mul_ne_zero (div_ne_zero ℏ_ne_zero Q.m_ne_zero) hk.ne'
  have h : ‖A‖ ^ 2 - ‖B‖ ^ 2 = ‖C‖ ^ 2 := by
    simpa using mul_left_cancel₀ hc hj
  simpa only [add_comm] using sub_eq_iff_eq_add.mp h

/-- The reflection and transmission coefficients for a nonzero incident wave sum to one. -/
lemma reflection_add_transmission_eq_one (hψ : Q.IsStationaryWave E ψ) (hk : 0 < k) (hA : A ≠ 0)
    (hLeft : EqOn ψ (fun x => A * planeWave k x + B * planeWave (-k) x) (Iio Q.lower))
    (hRight : EqOn ψ (fun x => C * planeWave k x) (Ioi Q.upper)) :
    ‖B‖ ^ 2 / ‖A‖ ^ 2 + ‖C‖ ^ 2 / ‖A‖ ^ 2 = 1 := by
  rw [← add_div, ← incident_norm_sq_eq hψ hk hLeft hRight,
    div_self (pow_ne_zero 2 (norm_ne_zero_iff.mpr hA))]

end QuantumMechanics.RectangularBarrier
