/-
Copyright (c) 2026 Qianli Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qianli Ma
-/
module

public import Physlib.QuantumMechanics.RectangularBarrier.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.RealDeriv

/-!

# Stationary probability current at a rectangular barrier

Conservation of the one-dimensional current across both barrier interfaces.

## i. Overview

A stationary wave is represented by a function of the real spatial coordinate.
For a real potential, the Schrödinger equation makes the derivative of the
probability current vanish within each region. Continuity of the wave and its
first derivative gives the same current on both sides of each interface.

## ii. Key results

- `RectangularBarrier.probabilityCurrent_eq` gives equality of the current at any
  two positions for a classical stationary wave of the barrier.

## iii. Table of contents

- A. Probability current and stationary waves
- B. Conservation across the interfaces

## iv. References

* None.

-/

@[expose] public section

noncomputable section

namespace QuantumMechanics.RectangularBarrier

open Set Constants
open scoped ComplexConjugate

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

end QuantumMechanics.RectangularBarrier
