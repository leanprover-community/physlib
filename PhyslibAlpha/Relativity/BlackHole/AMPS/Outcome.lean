/-
Copyright (c) 2026 AMPS formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AMPS formalization contributors
-/
module

public import PhyslibAlpha.Relativity.BlackHole.AMPS.Readout
public import PhyslibAlpha.Relativity.BlackHole.AMPS.Operational
public import PhyslibAlpha.Relativity.BlackHole.AMPS.Blueshift
public import PhyslibAlpha.Relativity.BlackHole.AMPS.VacuumTest

/-!
# From an early number prediction to infalling oscillator outcomes

Infalling counters and excitation energy.

## i. Overview

AMPS §2 and Appendix A compare an early measurement predicting an outgoing
number with the vacuum seen by an infalling observer. Here one normalized
state provides the early marginal, its joint distribution with the outgoing
number, and the two infalling occupation distributions. The first result uses
the Appendix A rank-one estimator for finitely many exterior amplitudes. The
second uses an arbitrary early yes/no projector and permits an infinite
occupation tail in both exterior and infalling coordinates.

The change to infalling coordinates is a supplied unitary that carries the
specified squeezed vacuum to the joint oscillator ground. This property
suffices for the bounds on the two individual number counters and their
combined excitation energy. A specific Bogoliubov implementation, propagation of
both wavepackets, and a local detector interaction require additional data.
`Blueshift.packet_frequency_band` transports an outgoing radial band at one
exterior event. Using its lower edge for the energy estimate here requires
a frequency lower bound for each infalling oscillator at that event.

## ii. Key results

* `amps_infalling_outcomes`
* `amps_full_support_outcomes`

## iii. Table of contents

- A. Infalling counters and excitation energy

## iv. References

* [ref: Almheiri2013]

## A. Infalling counters and excitation energy
-/

@[expose] public section

noncomputable section

namespace AMPS.Outcome

open Prediction Readout VacuumTest

variable {I R : Type*} [Fintype R]

/-- Observable consequences of a lower bound on the probability of leaving
the joint infalling ground. Counter probabilities require only a normalized
state. The free Hamiltonian's mean energy above vacuum uses the finite energy form domain. -/
structure InfallingOutcomeBounds (L : ℝ) (φ : R → InfallingPair) : Prop where
  /-- Born probability of a nonzero occupation in the pair. -/
  joint : L ≤ 1 - jointGroundProbability φ
  /-- At least one of the two single-oscillator counters has this click probability. -/
  counter : L / 2 ≤ firstClickProbability φ ∨ L / 2 ≤ secondClickProbability φ
  /-- Mean excitation energy above the joint ground for two oscillators with a common gap. -/
  energy : ∀ ωmin ω₁ ω₂ : ℝ, 0 ≤ ωmin → ωmin ≤ ω₁ → ωmin ≤ ω₂ →
    FiniteExcitationEnergy ω₁ ω₂ φ → ωmin * L ≤ meanExcitationEnergy ω₁ ω₂ φ

private lemma of_squeezed_test (x : R → Pair) (hnorm : ∑ t, ‖x t‖ ^ 2 = 1)
    {q : ℂ} (hq : q.normSq < 1) (U : Pair ≃ₗᵢ[ℂ] InfallingPair)
    (hground : U (vacuum q hq) = infallingGround) (a d : ℝ)
    (htest : 0 ≤ d → a * d ^ 2 ≤ 1 - pairProbability (vacuum q hq) x) :
    InfallingOutcomeBounds (a * (max 0 d) ^ 2) (fun t => U (x t)) := by
  let φ := fun t => U (x t)
  have hur : ∑ t, ‖φ t‖ ^ 2 = 1 := by simp only [φ, U.norm_map, hnorm]
  have heq : jointGroundProbability φ = pairProbability (vacuum q hq) x :=
    jointGroundProbability_map U.toLinearIsometry hq hground x
  have hbound : a * (max 0 d) ^ 2 ≤ 1 - jointGroundProbability φ := by
    by_cases h : 0 ≤ d
    · rw [max_eq_right h, heq]
      exact htest h
    · simpa only [max_eq_left (le_of_not_ge h), zero_pow (by decide : 2 ≠ 0), mul_zero]
        using sub_nonneg.mpr (jointGroundProbability_le_one φ hur)
  refine ⟨hbound, (one_counter_clicks φ hur).imp ?_ ?_, ?_⟩
  · exact fun h => (div_le_div_of_nonneg_right hbound (by norm_num)).trans h
  · exact fun h => (div_le_div_of_nonneg_right hbound (by norm_num)).trans h
  · intro ωmin ω₁ ω₂ hmin h₁ h₂ hfinite
    exact (mul_le_mul_of_nonneg_left hbound hmin).trans
      (mean_energy_ge_joint_rejection φ hmin h₁ h₂ hur hfinite)

/-- Let `a` be the probability of early yes, `g` the Appendix A relative
squared error on the selected branch, and `h` its thermal number probability.
Then `a (max(0, 1-g-h))²` bounds the probability of exciting the infalling
pair. On the original state at least one ideal number counter has at least
half that probability to register a nonzero occupation. For packet
frequencies with a common lower bound, finite mean energy also has the
corresponding spectral-gap bound. All probabilities include the early
register without conditioning on the early measurement being performed. -/
lemma amps_infalling_outcomes [Fintype I] [DecidableEq I] [DecidableEq R]
    (label : I ↪ ℕ × ℕ × Unit) (ψ : Wave I (EuclideanSpace ℂ R)) (i : I) (r : R) (hlive : ψ i ≠ 0)
    (halign : ℂ ∙ ψ i = ℂ ∙ EuclideanSpace.single r (1 : ℂ)) (hnorm : ‖ψ‖ = 1)
    {q : ℂ} (hq : q.normSq < 1) (U : Pair ≃ₗᵢ[ℂ] InfallingPair)
    (hground : U (vacuum q hq) = infallingGround) :
    let a := ‖earlyProjector (ψ i) ψ‖ ^ 2
    let g := ‖lateBranch i ψ - earlyBranch i ψ‖ ^ 2 / ‖lateBranch i ψ‖ ^ 2
    let L := a * (max 0 (1 - g - thermalNumberWeight q (label i).1)) ^ 2
    InfallingOutcomeBounds L (fun t => U (rows label ψ t)) := by
  dsimp only
  rw [relative_prediction_error i ψ hlive]
  apply of_squeezed_test (rows label ψ) (by rw [row_mass, hnorm, one_pow]) hq U hground
  intro hgap
  rw [← marked_eq_ray label ψ i r halign]
  exact amps_embedded_readout label ψ i r hlive halign hnorm hq hgap

/-- A scaled early binary projector can predict the whole, possibly
degenerate outgoing occupation event on a state with arbitrary infinite
occupation tails. If its squared vector error is at most `g` times the
late-yes probability, the excess over the squeezed-vacuum prior gives
the same infalling counter and energy bounds on the original state. -/
lemma amps_full_support_outcomes (x : R → Pair) (yes : R → Bool) (n : ℕ) (s g : ℝ)
    (hnorm : ∑ t, ‖x t‖ ^ 2 = 1) (hp : 0 < outgoingProbability x n)
    (ha : 0 < markedProbability yes x)
    (herr : Operational.errorWeight x yes n s ≤ g * outgoingProbability x n)
    {q : ℂ} (hq : q.normSq < 1) (U : Pair ≃ₗᵢ[ℂ] InfallingPair)
    (hground : U (vacuum q hq) = infallingGround) :
    let L := markedProbability yes x * (max 0 (1 - g - thermalNumberWeight q n)) ^ 2
    InfallingOutcomeBounds L (fun t => U (x t)) := by
  apply of_squeezed_test x hnorm hq U hground
  exact Operational.amps_full_support x yes n s g hnorm hp ha herr hq

/-- A high-probability occupation can contain many fine-grained late states. In the
eigenbasis of an early Hermitian estimator, thresholding at one half gives a physical
binary measurement. The error here concerns the entire occupation, without selecting
a rare basis state. -/
lemma amps_coarse_outcomes (x : R → Pair) (eigenvalue : R → ℝ) (n : ℕ)
    (hnorm : ∑ r, ‖x r‖ ^ 2 = 1)
    {q : ℂ} (hq : q.normSq < 1) (U : Pair ≃ₗᵢ[ℂ] InfallingPair)
    (hground : U (vacuum q hq) = infallingGround) :
    let strength := outgoingProbability x n * (1 - thermalNumberWeight q n) -
      4 * Operational.spectralError x eigenvalue n
    InfallingOutcomeBounds ((max 0 strength) ^ 2) (fun r => U (x r)) := by
  dsimp only
  let d := outgoingProbability x n * (1 - thermalNumberWeight q n) -
    4 * Operational.spectralError x eigenvalue n
  have htest : 0 ≤ d → 1 * d ^ 2 ≤ 1 - pairProbability (vacuum q hq) x := by
    intro hd
    have h := Operational.coarse_estimator_pair_test x eigenvalue n hnorm hq
    change (max 0 d) ^ 2 ≤ _ at h
    simpa only [one_mul, max_eq_right hd] using h
  simpa only [one_mul] using of_squeezed_test x hnorm hq U hground 1 d htest

end AMPS.Outcome
