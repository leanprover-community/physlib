/-
Copyright (c) 2026 Philippe Kevorkian. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philippe Kevorkian
-/
module

public import Mathlib.MeasureTheory.Measure.Support
public import Physlib.QuantumMechanics.Operators.SpaceD.Multiplication
public import Physlib.QuantumMechanics.Operators.SpectralTheory.Basic
/-!

# Spectrum of multiplication operators

## i. Overview

In this module we compute the spectrum of the multiplication operators `𝓜 μ f` of
`Operators/Multiplication.lean`. If `ε ≤ ‖f x‖` for `μ`-a.e. `x`, with `ε > 0`, then `𝓜 μ f` is
bounded below by `ε`. Applied to `f - z`, this shows that the spectrum of `𝓜 μ f` is contained in
the essential range of `f`, the support of the pushforward measure `μ.map f`. For a σ-finite
measure the two sets are equal, and for a continuous `f` and a measure which is positive on
non-empty open sets they are the closure of the range of `f`.

## ii. Key results

- `mulOperator_isLowerBound` : If `ε ≤ ‖f x‖` for `μ`-a.e. `x`, with `ε > 0`, then `ε` is a
    lower bound for `𝓜 μ f`.
- `mulOperator_spectrum_eq_support_map` : For a σ-finite measure `μ` and a `μ`-a.e. strongly
    measurable `f`, the spectrum of `𝓜 μ f` is the essential range of `f`, the support of the
    pushforward measure `μ.map f`.
- `mulOperator_spectrum_eq_closure_range` : For a σ-finite measure `μ` which is positive on
    non-empty open sets and a continuous `f`, the spectrum of `𝓜 μ f` is the closure of the
    range of `f`.

## iii. Table of contents

- A. Lower bound
- B. Spectrum

## iv. References

* None.
-/

@[expose] public section

namespace QuantumMechanics
namespace SpaceDHilbertSpace
noncomputable section

open LinearPMap
open MeasureTheory
open Filter

variable {d : ℕ}

/-!
## A. Lower bound
-/

/-- If `ε ≤ ‖f x‖` for `μ`-a.e. `x`, with `ε > 0`, then `ε` is a lower bound for `𝓜 μ f`, that is
  `ε * ‖ψ‖ ≤ ‖𝓜 μ f ψ‖` for every `ψ` in its domain. -/
lemma mulOperator_isLowerBound {μ : Measure (Space d)} {f : Space d → ℂ} {ε : ℝ} (hε : 0 < ε)
    (h : ∀ᵐ x ∂μ, ε ≤ ‖f x‖) : IsLowerBound (𝓜 μ f) 0 ε := by
  intro ψ
  rw [zero_smul, sub_zero]
  refine (le_inv_mul_iff₀ hε).mp (Lp.norm_le_mul_norm_of_ae_le_mul ?_)
  filter_upwards [h, mulOperator_apply_ae ψ] with x hx h₁
  rw [h₁, Pi.smul_apply', norm_smul, ← mul_assoc]
  exact le_mul_of_one_le_left (norm_nonneg _) ((one_le_inv_mul₀ hε).mpr hx)

/-!
## B. Spectrum

For an almost everywhere strongly measurable `f`, the essential range of `f` is the support
`(μ.map f).support` of the pushforward of `μ` by `f`.
-/

/-- The spectrum of `𝓜 μ f` is contained in the essential range `(μ.map f).support` of `f`,
  for any measure `μ` and any `μ`-a.e. strongly measurable `f`. -/
lemma mulOperator_spectrum_subset_support_map {μ : Measure (Space d)} {f : Space d → ℂ}
    (hf : AEStronglyMeasurable f μ) : σ (𝓜 μ f) ⊆ (μ.map f).support := by
  intro z hz
  by_contra hz'
  obtain ⟨ε, hε, hμ⟩ := Metric.nhds_basis_ball.notMem_measureSupport.mp hz'
  have h : ∀ᵐ x ∂μ, ε ≤ ‖(f - z • 1) x‖ := by
    filter_upwards [ae_of_ae_map hf.aemeasurable (measure_eq_zero_iff_ae_notMem.mp hμ)] with x hx
    simpa [dist_eq_norm] using hx
  have hlb := mulOperator_isLowerBound hε h
  rw [mulOperator_sub_smul_one] at hlb
  obtain ⟨h_ker, h_cont⟩ := mem_regularityDomain_iff.mp
    ⟨ε, hε, fun ψ ↦ by simpa [LinearPMap.sub_apply] using hlb ⟨ψ.1, ψ.2, by simp⟩⟩
  refine hz ⟨h_ker, ?_, h_cont⟩
  rw [← mulOperator_sub_smul_one]
  exact mulOperator_range_eq_top (hf.sub (by fun_prop)) hε h

/-- For a σ-finite measure `μ` and a `μ`-a.e. strongly measurable `f`, the spectrum of `𝓜 μ f`
  is the essential range of `f`, the support of the pushforward measure `μ.map f`. -/
lemma mulOperator_spectrum_eq_support_map {μ : Measure (Space d)} [SigmaFinite μ]
    {f : Space d → ℂ} (hf : AEStronglyMeasurable f μ) :
    σ (𝓜 μ f) = (μ.map f).support := by
  refine subset_antisymm (mulOperator_spectrum_subset_support_map hf) fun z hz hρ ↦ ?_
  obtain ⟨c, hc, hlb⟩ := resolventSet_subset_regularityDomain _ hρ
  -- `f` is within `c / 2` of `z` on a measurable set `t` of finite, positive measure.
  have hg := hf.aemeasurable.measurable_mk
  have hpos := Metric.nhds_basis_ball.mem_measureSupport.mp hz (c / 2) (by positivity)
  rw [Measure.map_congr hf.aemeasurable.ae_eq_mk, Measure.map_apply hg measurableSet_ball] at hpos
  obtain ⟨t, ht, hts, htpos, htop⟩ :=
    Measure.exists_subset_measure_lt_top (measurableSet_ball.preimage hg) hpos
  have htf : ∀ᵐ x ∂μ, x ∈ t → ‖f x - z‖ < c / 2 := by
    filter_upwards [hf.aemeasurable.ae_eq_mk] with x hx hxt
    simpa [hx, dist_eq_norm] using hts hxt
  -- The lower bound `c` fails on a preimage `ψ` of the indicator `φ` of `t` under `𝓜 μ f - z • 1`.
  have hE := (mulOperator_sub_smul_one μ f z).symm
  let φ : SpaceDHilbertSpace d μ := indicatorConstLp 2 ht htop.ne 1
  obtain ⟨ψ, hψ⟩ := LinearMap.range_eq_top.mp hρ.2.1 φ
  rw [toFun_eq_coe] at hψ
  have hψd : ψ.1 ∈ (𝓜 μ (f - z • 1)).domain := by
    rw [← hE]
    exact ψ.2
  have hψ' : 𝓜 μ (f - z • 1) ⟨ψ.1, hψd⟩ = φ := by
    rw [← hψ]
    exact ((LinearPMap.ext_iff.mp hE).2 (hf := ψ.2) (hg := hψd)).symm
  have h₁ : ‖φ‖ ≤ c / 2 * ‖ψ.1‖ := by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [hψ' ▸ mulOperator_apply_ae ⟨ψ.1, hψd⟩,
      indicatorConstLp_coeFn (p := 2) (hs := ht) (hμs := htop.ne) (c := (1 : ℂ)), htf]
      with x h₁ h₂ h₃
    by_cases hx : x ∈ t
    · rw [h₁, Pi.smul_apply', norm_smul]
      exact mul_le_mul_of_nonneg_right (by simpa using (h₃ hx).le) (norm_nonneg _)
    · rw [h₂, Set.indicator_of_notMem hx, norm_zero]
      positivity
  have h₂ : c * ‖ψ.1‖ ≤ ‖φ‖ := by
    simpa [← hψ, LinearPMap.sub_apply] using hlb ⟨ψ, ψ.2.1⟩
  have h₃ : 0 < ‖φ‖ := by
    rw [norm_indicatorConstLp two_ne_zero ENNReal.ofNat_ne_top, norm_one, one_mul]
    exact Real.rpow_pos_of_pos (ENNReal.toReal_pos htpos.ne' htop.ne) _
  nlinarith [norm_nonneg ψ.1]

/-- For a continuous `f` and a σ-finite measure `μ` which is positive on non-empty open sets,
  the spectrum of `𝓜 μ f` is the closure of the range of `f`. -/
lemma mulOperator_spectrum_eq_closure_range (μ : Measure (Space d)) [SigmaFinite μ]
    [μ.IsOpenPosMeasure] {f : Space d → ℂ} (hf : Continuous f) :
    σ (𝓜 μ f) = _root_.closure (Set.range f) := by
  rw [mulOperator_spectrum_eq_support_map hf.aestronglyMeasurable]
  ext z
  rw [Metric.nhds_basis_ball.mem_measureSupport, Metric.mem_closure_iff]
  refine forall₂_congr fun ε _ ↦ ?_
  rw [Measure.map_apply hf.measurable measurableSet_ball]
  refine ⟨fun h ↦ ?_, fun ⟨_, ⟨x, hx⟩, hxz⟩ ↦ ?_⟩
  · obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero h.ne'
    exact ⟨f x, ⟨x, rfl⟩, by rwa [dist_comm]⟩
  · refine (Metric.isOpen_ball.preimage hf).measure_pos μ ⟨x, ?_⟩
    rwa [Set.mem_preimage, hx, Metric.mem_ball, dist_comm]

end
end SpaceDHilbertSpace
end QuantumMechanics
