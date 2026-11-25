/-
Copyright (c) 2026 AMPS formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AMPS formalization contributors
-/
module

public import PhyslibAlpha.Relativity.BlackHole.AMPS.Packet
public import PhyslibAlpha.Relativity.BlackHole.AMPS.Blueshift
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.Ring

/-!
# A predicted outgoing packet at the horizon

The number-sharp branch at the stretched horizon.

## i. Overview

In AMPS §2 and Fig. 1 a measurement on the early radiation predicts the number of
the outgoing packet that is propagated backwards outside the stretched horizon.
An independent early operation acts on neither of the two oscillator coordinates.
This makes it commute with the infalling annihilator. Thus a merely *possible*
early readout already constrains the original state.

The two-mode results here use a canonical inverse Bogoliubov pair for the chosen
packet and the radial Schwarzschild geometric-optics propagation in `Blueshift`.
The energy is the single-packet excitation energy above vacuum in units with ℏ = 1.
The stretched surface can be fixed by the proper radial distance on a static
Schwarzschild slice. The carrier frequency is measured by the radial observer
falling from rest at infinity at that event.

## ii. Key results

* `infalling_earlyAction`
* `predicted_number_excludes_vacuum`

## iii. Table of contents

- A. The number-sharp branch at the stretched horizon

## iv. References

* [ref: Almheiri2013]

## A. The number-sharp branch at the stretched horizon
-/

@[expose] public section

noncomputable section

namespace AMPS.Horizon

open Packet
variable {E : Type*} [Fintype E]

/-- Apply an early-radiation operation on its own tensor factor.
Its matrix is independent of both oscillator indices. -/
def earlyAction (P : Matrix E E ℂ) (ψ : Amplitude E) : Amplitude E :=
  fun p => ∑ j, P p.2.2 j * ψ (p.1, p.2.1, j)

/-- Locality in the independent-factor representation. The early operation is a general
linear filter; the argument does not require that the filter actually be applied. -/
lemma infalling_earlyAction (P : Matrix E E ℂ) (α β : ℂ) (ψ : Amplitude E) :
    infalling α β (earlyAction P ψ) = earlyAction P (infalling α β ψ) := by
  funext ⟨k, m, e⟩
  cases m with
  | zero =>
    simp only [infalling, earlyAction, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  | succ m =>
    simp only [infalling, earlyAction, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring

/-- If the early filter can reproduce a nonzero number branch, the unmeasured state
cannot be the infalling vacuum for this packet. -/
lemma predicted_number_excludes_vacuum {ψ : Amplitude E} (P : Matrix E E ℂ)
    (n : ℕ) (α β : ℂ) (hβ : β ≠ 0)
    (hread : earlyAction P ψ = projectNumber n ψ) (hlive : projectNumber n ψ ≠ 0) :
    infalling α β ψ ≠ 0 := by
  intro hvac
  apply numberSharp_not_vacuum (α := α) (numberSharp_projectNumber n ψ) hβ hlive
  rw [← hread, infalling_earlyAction, hvac]
  funext p
  simp [earlyAction]

/-- Pointwise amplitude error between the early operation and the ideal outgoing
number projector on the *same* state. Any upper bound on the ℓ² norm of the
difference also bounds each of these coordinates. -/
def PredictsWithin (P : Matrix E E ℂ) (ψ : Amplitude E) (n : ℕ) (ε : ℝ) : Prop :=
  ∀ p, ‖earlyAction P ψ p - projectNumber n ψ p‖ ≤ ε

/-- Stability of the original-state obstruction. The two ladder coefficients at
one output coordinate give an explicit budget for disagreement with a sharp late
number. It remains meaningful for an approximate early filter and approximate vacuum. -/
lemma prediction_vacuum_tradeoff {ψ : Amplitude E} {P : Matrix E E ℂ} {n : ℕ}
    {ε : ℝ} (h : PredictsWithin P ψ n ε) (α β : ℂ) (m : ℕ) (e : E) :
    ‖β * (Real.sqrt (m + 1) : ℂ)‖ * ‖ψ (n,m,e)‖ ≤
      ‖earlyAction P (infalling α β ψ) (n,m+1,e)‖ +
      (‖α * (Real.sqrt (n + 1) : ℂ)‖ + ‖β * (Real.sqrt (m + 1) : ℂ)‖) * ε := by
  let u : ℂ := α * (Real.sqrt (n + 1) : ℂ)
  let v : ℂ := β * (Real.sqrt (m + 1) : ℂ)
  let x := ψ (n,m,e)
  let y := earlyAction P ψ (n,m,e)
  let z := earlyAction P ψ (n+1,m+1,e)
  have hy : ‖y - x‖ ≤ ε := by simpa [x, y, projectNumber] using h (n,m,e)
  have hz : ‖z‖ ≤ ε := by simpa [z, projectNumber] using h (n+1,m+1,e)
  have ident : v * x = (u * z + v * y) - u * z - v * (y - x) := by ring
  have houtput : earlyAction P (infalling α β ψ) (n,m+1,e) = u * z + v * y := by
    rw [← infalling_earlyAction]
    rfl
  rw [houtput]
  change ‖v‖ * ‖x‖ ≤ ‖u * z + v * y‖ + (‖u‖ + ‖v‖) * ε
  calc
    ‖v‖ * ‖x‖ = ‖v * x‖ := (norm_mul _ _).symm
    _ ≤ ‖u * z + v * y‖ + ‖u * z‖ + ‖v * (y - x)‖ := by
      calc
        _ = ‖(u * z + v * y) - u * z - v * (y - x)‖ := congrArg norm ident
        _ ≤ ‖(u * z + v * y) - u * z‖ + ‖v * (y - x)‖ := norm_sub_le _ _
        _ ≤ _ := by linarith [norm_sub_le (u * z + v * y) (u * z)]
    _ ≤ _ := by
      rw [norm_mul u, norm_mul v, add_mul]
      linarith [mul_le_mul_of_nonneg_left hz (norm_nonneg u),
        mul_le_mul_of_nonneg_left hy (norm_nonneg v)]

/-- A normalized exact predicted branch has a minimum mean packet energy in the local
infalling frame. Normalization is expressed by its Born weight before conditioning.
The central frequency is the measured frequency of the same outgoing radial carrier.
The separate non-vacuum conclusion applies to the premeasurement state. -/
lemma amps_packet {ψ : Amplitude E} (P : Matrix E E ℂ) (n : ℕ) (α β : ℂ)
    (_hcanonical : α.normSq - β.normSq = 1) (hβ : β ≠ 0)
    (hread : earlyAction P ψ = projectNumber n ψ)
    (hlive : projectNumber n ψ ≠ 0)
    (c : ℂ) (hnorm : HasSum (fun p => (c * projectNumber n ψ p).normSq) 1)
    (hdom : Summable (fun p => (infalling α β (fun i => c * projectNumber n ψ i) p).normSq))
    {rs ωinf ωstar cutoff K margin : ℝ} (hrs : 0 < rs) (hω : 0 < ωinf)
    (hhigh : ωinf < ωstar) (hcut : ωstar < cutoff) (hscale : K / rs < ωstar)
    (hmargin : margin ≤ rs * (ωinf / ωstar)) :
    infalling α β ψ ≠ 0 ∧
    ∃ r, rs < r ∧ rs + margin < r ∧ Blueshift.infallFrequency rs r ωinf = ωstar ∧
      K < rs * Blueshift.infallFrequency rs r ωinf ∧ ωstar < cutoff ∧
      0 < ωstar * β.normSq ∧ ωstar * β.normSq ≤
        Blueshift.infallFrequency rs r ωinf *
          ∑' p, (infalling α β (fun i => c * projectNumber n ψ i) p).normSq := by
  have hsharp : NumberSharp (fun p => c * projectNumber n ψ p) n := by
    intro k m e hk
    simp [projectNumber, hk]
  have hw := hω.trans hhigh
  obtain ⟨hr, heq⟩ := Blueshift.radiusForFrequency_spec hrs hω hhigh
  refine ⟨predicted_number_excludes_vacuum P n α β hβ hread hlive,
    Blueshift.radiusForFrequency rs ωinf ωstar, hr, ?_, heq, ?_, hcut, ?_, ?_⟩
  · have hm := Blueshift.radiusForFrequency_radial_margin hrs hω hhigh
    linarith
  · rw [heq, mul_comm rs]
    exact (div_lt_iff₀ hrs).mp hscale
  · exact mul_pos hw (Complex.normSq_pos.mpr hβ)
  · rw [heq]
    exact numberSharp_energy_ge hsharp hnorm hdom hw.le

/-- The chosen packet reaches its prescribed sub-cutoff carrier frequency
beyond a stretched horizon of proper thickness `ℓ`. The selected radius
`r` lies on the outgoing radial null branch, and the frequency uses the
unit-energy radial geodesic falling from rest at infinity. The stretched
radius `s` is measured on a static Schwarzschild slice and is unique by
`Blueshift.existsUnique_stretched_radius`. The energy bound is conditional
on the normalized predicted branch, while the vacuum exclusion concerns the
original state. The energy describes one packet in the two-mode model. -/
lemma amps_packet_outside_stretched_horizon {ψ : Amplitude E} (P : Matrix E E ℂ)
    (n : ℕ) (α β : ℂ) (hcanonical : α.normSq - β.normSq = 1) (hβ : β ≠ 0)
    (hread : earlyAction P ψ = projectNumber n ψ) (hlive : projectNumber n ψ ≠ 0)
    (c : ℂ) (hnorm : HasSum (fun p => (c * projectNumber n ψ p).normSq) 1)
    (hdom : Summable (fun p => (infalling α β (fun i => c * projectNumber n ψ i) p).normSq))
    {rs ωinf ωstar cutoff K ℓ : ℝ} (hrs : 0 < rs) (hω : 0 < ωinf)
    (hhigh : ωinf < ωstar) (hcut : ωstar < cutoff) (hscale : K / rs < ωstar)
    (hℓ : 0 < ℓ) (hthickness : ℓ ≤ 2 * rs * Real.sqrt (ωinf / ωstar)) :
    infalling α β ψ ≠ 0 ∧ ∃ s r, rs < s ∧ s < r ∧ Blueshift.staticProperDistance rs s = ℓ ∧
      ℓ < Blueshift.staticProperDistance rs r ∧ Blueshift.infallFrequency rs r ωinf = ωstar ∧
      K < rs * Blueshift.infallFrequency rs r ωinf ∧ ωstar < cutoff ∧
      0 < ωstar * β.normSq ∧ ωstar * β.normSq ≤ Blueshift.infallFrequency rs r ωinf *
        ∑' p, (infalling α β (fun i => c * projectNumber n ψ i) p).normSq := by
  obtain ⟨hpre, r, hr, hgap, hfreq, hK, hsub, hpos, henergy⟩ :=
    amps_packet P n α β hcanonical hβ hread hlive c hnorm hdom hrs hω hhigh hcut hscale le_rfl
  have hproper := hthickness.trans_lt (Blueshift.staticProperDistance_of_radial_margin hrs
    (div_pos hω (hω.trans hhigh)) (by linarith : rs * (ωinf / ωstar) < r - rs))
  obtain ⟨s, ⟨horder, hdist⟩, _⟩ := Blueshift.existsUnique_stretched_radius hrs hr hℓ hproper
  exact ⟨hpre, s, r, horder.1, horder.2, hdist, hproper, hfreq, hK, hsub, hpos, henergy⟩

end AMPS.Horizon
