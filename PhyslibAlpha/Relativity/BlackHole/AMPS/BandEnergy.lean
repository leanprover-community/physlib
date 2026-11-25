/-
Copyright (c) 2026 AMPS formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AMPS formalization contributors
-/
module

public import PhyslibAlpha.Relativity.BlackHole.AMPS.Blueshift
public import PhyslibAlpha.Relativity.BlackHole.AMPS.Outcome

/-!
# Excitation energy for a band of Schwarzschild frequencies

Frequency bands and the infalling energy bound.

## i. Overview

The radial geometric-optics map rescales the entire frequency band at a single
exterior event. For two orthogonal infalling packet modes, take their normalized
one-particle frequency distributions in that band. The integral of the local
frequency against each distribution gives its energy per excitation in the
two-mode compression of the free Hamiltonian. We combine the resulting energy
floor with the coarse early-radiation prediction bound on the original state.

This uses the radial geometric-optics model and the specified band support.
The reduction to two modes and the Bogoliubov identification of their ground state
remain physical hypotheses. The squeezed vacuum probability follows from the two
Bogoliubov ladder equations and their unique normalized solution up to a phase. The norms of a
collapse-spacetime scattering kernel are
not calculated by this argument.

## ii. Key results

* `frequency_at_hawking_radius`
* `packetEnergy_bounds`

## iii. Table of contents

- A. Frequency bands and the infalling energy bound

## iv. References

* [ref: Almheiri2013]

## A. Frequency bands and the infalling energy bound
-/

@[expose] public section

noncomputable section

namespace AMPS.BandEnergy

open MeasureTheory VacuumTest

/-- The Killing frequencies of a band centered at the Hawking scale, with dimensionless
endpoints. Finite width is allowed. -/
abbrev Band (rs lo hi : ℝ) := Set.Icc (lo / rs) (hi / rs)

/-- Mean local one-particle energy of a normalized packet, in units with ℏ = 1. -/
def packetEnergy (rs r lo hi : ℝ) (μ : Measure (Band rs lo hi)) : ℝ :=
  ∫ ν, Blueshift.infallFrequency rs r ν.val ∂μ

/-- The same radial frequency map applies across the whole band. -/
lemma frequency_at_hawking_radius {rs lo hi target : ℝ}
    (hrs : 0 < rs) (hhigh : 1 / rs < target) (ν : Band rs lo hi) :
    lo * target ≤ Blueshift.infallFrequency rs
      (Blueshift.radiusForFrequency rs (1 / rs) target) ν.val ∧
    Blueshift.infallFrequency rs (Blueshift.radiusForFrequency rs (1 / rs) target) ν.val ≤
      hi * target := by
  have hω : 0 < 1 / rs := one_div_pos.mpr hrs
  obtain ⟨hr, hcarrier⟩ := Blueshift.radiusForFrequency_spec hrs hω hhigh
  let r := Blueshift.radiusForFrequency rs (1 / rs) target
  let d := 1 - Real.sqrt (rs / r)
  have hratio : (1 / rs) / d = target :=
    (Blueshift.infallFrequency_eq hrs hr _).symm.trans hcarrier
  have hb := Blueshift.packet_frequency_band hrs hr ν.property.1 ν.property.2
  have scaled (c : ℝ) : (c / rs) / d = c * target := by
    rw [← hratio]
    ring
  change (lo / rs) / d ≤ _ ∧ _ ≤ (hi / rs) / d at hb
  rwa [scaled lo, scaled hi] at hb

/-- A band-limited one-particle distribution gives an energy between the local
band edges. The measure is the normalized spectral weight of the packet. -/
lemma packetEnergy_bounds {rs lo hi target : ℝ} (hrs : 0 < rs)
    (hhigh : 1 / rs < target) (μ : Measure (Band rs lo hi)) [IsProbabilityMeasure μ]
    (hint : Integrable (fun ν : Band rs lo hi => Blueshift.infallFrequency rs
      (Blueshift.radiusForFrequency rs (1 / rs) target) ν.val) μ) :
    let r := Blueshift.radiusForFrequency rs (1 / rs) target
    lo * target ≤ packetEnergy rs r lo hi μ ∧ packetEnergy rs r lo hi μ ≤ hi * target := by
  dsimp only
  constructor
  · simpa [packetEnergy] using integral_mono_ae (integrable_const (lo * target)) hint
      (Filter.Eventually.of_forall fun ν => (frequency_at_hawking_radius hrs hhigh ν).1)
  · simpa [packetEnergy] using integral_mono_ae hint (integrable_const (hi * target))
      (Filter.Eventually.of_forall fun ν => (frequency_at_hawking_radius hrs hhigh ν).2)

/-- Allow frequency tails outside the indicated band. With a positive-frequency
profile the mass in the band alone contributes its lower band edge to the energy.
This version uses the Killing-frequency distribution on the whole real axis. -/
lemma packetEnergy_ge_of_band_mass {rs lo hi target mass : ℝ} (hrs : 0 < rs)
    (hhigh : 1 / rs < target) (hfloor : 0 ≤ lo * target) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hpositive : ∀ᵐ ν ∂μ, 0 ≤ ν)
    (hmass : mass ≤ μ.real (Band rs lo hi))
    (hint : Integrable (Blueshift.infallFrequency rs
      (Blueshift.radiusForFrequency rs (1 / rs) target)) μ) :
    lo * target * mass ≤ ∫ ν, Blueshift.infallFrequency rs
      (Blueshift.radiusForFrequency rs (1 / rs) target) ν ∂μ := by
  let r := Blueshift.radiusForFrequency rs (1 / rs) target
  let b : Set ℝ := Band rs lo hi
  have hb : MeasurableSet b := measurableSet_Icc
  have hcompare : b.indicator (fun _ => lo * target) ≤ᵐ[μ]
      Blueshift.infallFrequency rs r := by
    filter_upwards [hpositive] with ν hν
    by_cases hmem : ν ∈ b
    · rw [Set.indicator_of_mem hmem]
      exact (frequency_at_hawking_radius hrs hhigh ⟨ν, hmem⟩).1
    · rw [Set.indicator_of_notMem hmem]
      have hr := (Blueshift.radiusForFrequency_spec hrs (one_div_pos.mpr hrs) hhigh).1
      have hden : 0 ≤ 1 - Real.sqrt (rs / r) :=
        sub_nonneg.mpr (Real.sqrt_le_one.mpr ((div_le_one (hrs.trans hr)).mpr hr.le))
      rw [Blueshift.infallFrequency_eq hrs hr]
      exact div_nonneg hν hden
  have h := integral_mono_ae ((integrable_const (lo * target)).indicator hb) hint hcompare
  rw [integral_indicator_const _ hb, smul_eq_mul, mul_comm] at h
  exact (mul_le_mul_of_nonneg_left hmass hfloor).trans h

/-- A fixed, nonzero fractional bandwidth fits between the Hawking and Planck
scales for arbitrarily large black holes. The entire band, from half to twice
the Hawking carrier frequency at infinity, is boosted by the same factor. -/
lemma fixed_band_window {rs K : ℝ} (hrs : 4 < rs)
    (hK : 2 * K < Real.sqrt rs) :
    let target := 1 / Real.sqrt rs
    1 / rs < target ∧ (2 : ℝ) * target < 1 ∧ K / rs < (1 / 2 : ℝ) * target := by
  dsimp only
  have hsp : 0 < Real.sqrt rs := Real.sqrt_pos.2 (by linarith)
  have hsq : Real.sqrt rs ^ 2 = rs := Real.sq_sqrt (by linarith)
  have htwo : 2 < Real.sqrt rs := by
    nlinarith [sq_nonneg (Real.sqrt rs), hsp]
  have hrs' : 0 < rs := by linarith
  refine ⟨(one_div_lt_one_div_of_lt hsp (by nlinarith)), ?_, ?_⟩
  · rw [← mul_div_assoc, mul_one, div_lt_one hsp]
    exact htwo
  · apply (div_lt_iff₀ hrs').2
    have heq : (1 / 2 : ℝ) * (1 / Real.sqrt rs) * rs = Real.sqrt rs / 2 := by
      calc
        _ = (1 / 2 : ℝ) * (1 / Real.sqrt rs) * (Real.sqrt rs * Real.sqrt rs) :=
          congrArg (fun t => (1 / 2 : ℝ) * (1 / Real.sqrt rs) * t) (by nlinarith [hsq])
        _ = _ := by field_simp
    rw [heq]
    linarith

variable {R : Type*} [Fintype R]

/-- Provided the two infalling modes are represented by the supplied spectral
profiles, the prediction of the outgoing occupation forces a lower bound on the
original state's mean energy outside the stretched horizon. Both profiles lie
below the Planck scale and their lower edge can exceed the Hawking scale by a
prescribed factor. The normalized spectral measures specify the two orthogonal
one-particle modes of the compressed Hamiltonian. -/
lemma amps_band_energy (x : R → Pair) (eigenvalue : R → ℝ) (n : ℕ)
    (hnorm : ∑ t, ‖x t‖ ^ 2 = 1) {q : ℂ} (hq : q.normSq < 1)
    (U : Pair ≃ₗᵢ[ℂ] InfallingPair) {α β : ℂ} (hCCR : α.normSq - β.normSq = 1)
    (hcoef : α * q + β = 0)
    (ha : Packet.infalling α β (fun p => U.symm infallingGround p) = 0)
    (hb : Packet.partnerInfalling α β (fun p => U.symm infallingGround p) = 0)
    {rs lo hi target K : ℝ} (hsize : 1 ≤ rs)
    (hhigh : 1 / rs < target) (hsub : target < 1)
    (hfloor : 0 ≤ lo * target) (hscale : K / rs < lo * target)
    (hcap : hi * target < 1)
    (μ₁ μ₂ : Measure (Band rs lo hi)) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (hint₁ : Integrable (fun ν : Band rs lo hi => Blueshift.infallFrequency rs
      (Blueshift.radiusForFrequency rs (1 / rs) target) ν.val) μ₁)
    (hint₂ : Integrable (fun ν : Band rs lo hi => Blueshift.infallFrequency rs
      (Blueshift.radiusForFrequency rs (1 / rs) target) ν.val) μ₂) :
    let r := Blueshift.radiusForFrequency rs (1 / rs) target
    let ω₁ := packetEnergy rs r lo hi μ₁
    let ω₂ := packetEnergy rs r lo hi μ₂
    let strength := outgoingProbability x n * (1 - thermalNumberWeight q n) -
      4 * Operational.spectralError x eigenvalue n
    (∃ stretched, rs < stretched ∧ stretched < r ∧
      Blueshift.staticProperDistance rs stretched = 1) ∧
    (∀ ν : Band rs lo hi, K / rs < Blueshift.infallFrequency rs r ν.val ∧
      Blueshift.infallFrequency rs r ν.val < 1) ∧
    (FiniteExcitationEnergy ω₁ ω₂ (fun t => U (x t)) →
      lo * target * (max 0 strength) ^ 2 ≤
        meanExcitationEnergy ω₁ ω₂ (fun t => U (x t))) := by
  dsimp only
  have hrs : 0 < rs := zero_lt_one.trans_le hsize
  obtain ⟨stretched, hs, hr, hdist, _, _⟩ :=
    Blueshift.hawking_carrier_outside_planck_surface hsize hhigh hsub
  refine ⟨⟨stretched, hs, hr, hdist⟩, ?_, ?_⟩
  · intro ν
    obtain ⟨hlo, hhi⟩ := frequency_at_hawking_radius hrs hhigh ν
    exact ⟨hscale.trans_le hlo, hhi.trans_lt hcap⟩
  · intro hfinite
    have hα : α ≠ 0 := by
      intro hz
      rw [hz, Complex.normSq_zero] at hCCR
      linarith [Complex.normSq_nonneg β]
    have hmatch := jointGroundProbability_of_pullback_vacuum U hq hα hcoef ha hb x
    have htest := Operational.coarse_estimator_pair_test x eigenvalue n hnorm hq
    rw [← hmatch] at htest
    have hunit : ∑ t, ‖U (x t)‖ ^ 2 = 1 := by simp only [U.norm_map, hnorm]
    exact (mul_le_mul_of_nonneg_left htest hfloor).trans
      (mean_energy_ge_joint_rejection _ hfloor (packetEnergy_bounds hrs hhigh μ₁ hint₁).1
        (packetEnergy_bounds hrs hhigh μ₂ hint₂).1 hunit hfinite)

end AMPS.BandEnergy
