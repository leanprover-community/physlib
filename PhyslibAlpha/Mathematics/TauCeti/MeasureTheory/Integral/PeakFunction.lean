/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Integrals against `L¹` peak functions concentrating at a point

Let `f i` be a net of `L¹` classes of unit integral, `∫ f i = 1`, with uniformly bounded `L¹` norms,
which concentrate at a point `x₀`: for every neighbourhood `U` of `x₀`, eventually each `f i`
vanishes almost everywhere outside `U`.

## i. Overview

Let `f i` be a net of `L¹` classes of unit integral, `∫ f i = 1`, with uniformly bounded `L¹` norms,
which concentrate at a point `x₀`: for every neighbourhood `U` of `x₀`, eventually each `f i`
vanishes almost everywhere outside `U`. Then `∫ x, f i x • φ x ∂μ` tends to `a` for every `φ`
with limit `a` at `x₀` whose products `f i • φ` with the weights are almost everywhere strongly
measurable. This is the approximate-identity argument in its pointwise form: since `∫ f i = 1`,
the difference is `∫ x, f i x • (φ x - a) ∂μ`, and `φ x` stays close to `a` on the set where
`f i` lives.

Only the integrands `f i • φ` are asked to be almost everywhere strongly measurable, not `φ`
itself. This holds when `φ` is, but also for a continuous `φ` and a measure that is inner regular
for compact sets but not σ-finite, such as the Haar measure `MeasureTheory.Measure.addHaar` of a
locally compact group that is not σ-compact
(`MeasureTheory.AEFinStronglyMeasurable.aestronglyMeasurable_smul`).

On a measure that charges every open set and is finite on some neighbourhood of each point, such
peak functions exist inside every neighbourhood of every point (normalized indicators), so the
statement is never vacuous.

The weights here are `L¹` classes with values in an `RCLike` field, as consumed by integrated forms
of representations. Mathlib's peak-function results
(`tendsto_integral_peak_smul_of_integrable_of_tendsto` in
`Mathlib/MeasureTheory/Integral/PeakFunction.lean`) do not apply in that situation: they ask for
nonnegative real weights, defined pointwise, and for `φ` to be integrable. The latter fails for the
orbits `g ↦ π g v` of a unitary representation of a non-compact group, which have constant norm.
Similarly, `tendsto_integral_smul_of_tendsto_average_norm_sub` asks for pointwise bounds
`|g i| ≤ K / μ (a i)` on the weights. Here, instead, `φ` only has to be bounded near `x₀`, which
its limit at `x₀` provides.

## ii. Key results

* `TauCeti.norm_integral_smul_sub_le`: the approximate-identity estimate
  `‖∫ x, f x • φ x ∂μ - y‖ ≤ ε * ‖f‖` when `∫ f = 1`, `f` vanishes off `U`, and `φ` stays within `ε`
  of `y` on `U`.
* `TauCeti.tendsto_integral_smul_of_tendsto`: a net of `L¹` peak functions concentrating at
  `x₀` integrates `φ` to its limit at `x₀`.
* `TauCeti.exists_integral_eq_one_norm_eq_one`: peak functions of unit integral and unit
  `L¹` norm exist inside every neighbourhood of a point.

## iii. Table of contents

- A. Development

## iv. References

* G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., CRC Press (2016), §2.5.
-/

public section

/-! ## A. Development -/

open Filter MeasureTheory Metric Set
open scoped Topology

namespace TauCeti

variable {α 𝕜 E : Type*} [MeasurableSpace α] [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E] [CompleteSpace E] {μ : Measure α}

/-- **The approximate-identity estimate.** If an `L¹` class `f` has unit integral and vanishes
almost everywhere outside `U`, and `φ` stays within `ε` of `y` on `U`, then the integral of `φ`
against `f` is within `ε * ‖f‖` of `y`. The integrand `f • φ` is assumed almost everywhere
strongly measurable. -/
lemma norm_integral_smul_sub_le {f : α →₁[μ] 𝕜} (hf : ∫ x, f x ∂μ = 1) {U : Set α}
    (hfU : ∀ᵐ x ∂μ, x ∉ U → f x = 0) {φ : α → E}
    (hφ : AEStronglyMeasurable (fun x ↦ f x • φ x) μ) {y : E}
    {ε : ℝ} (hφU : ∀ x ∈ U, ‖φ x - y‖ ≤ ε) :
    ‖(∫ x, f x • φ x ∂μ) - y‖ ≤ ε * ‖f‖ := by
  have hfi : Integrable (fun x ↦ f x) μ := L1.integrable_coeFn f
  -- Pointwise, `‖f x • (φ x - y)‖ ≤ ‖f x‖ * ε`, since `f x = 0` off `U`.
  have hbound : ∀ᵐ x ∂μ, ‖f x • (φ x - y)‖ ≤ ‖f x‖ * ε := by
    filter_upwards [hfU] with x hx
    rw [norm_smul]
    by_cases hxU : x ∈ U
    · exact mul_le_mul_of_nonneg_left (hφU x hxU) (norm_nonneg _)
    · simp [hx hxU]
  have hint : Integrable (fun x ↦ f x • (φ x - y)) μ :=
    (hfi.norm.mul_const ε).mono'
      ((hφ.sub (hfi.aestronglyMeasurable.smul_const y)).congr
        (.of_forall fun x ↦ (smul_sub _ _ _).symm)) hbound
  -- Since `∫ f = 1`, subtracting `y` is integrating `f • (φ - y)`.
  have hsplit : ∫ x, f x • φ x ∂μ = (∫ x, f x • (φ x - y) ∂μ) + ∫ x, f x • y ∂μ := by
    rw [← integral_add hint (hfi.smul_const y)]
    simp_rw [smul_sub, sub_add_cancel]
  rw [hsplit, integral_smul_const, hf, one_smul, add_sub_cancel_right, L1.norm_eq_integral_norm,
    mul_comm, ← integral_mul_const]
  exact norm_integral_le_of_norm_le (hfi.norm.mul_const ε) hbound

/-- **`L¹` peak functions integrate a function to its limit at the peak.** Let `f i` be `L¹`
classes which eventually have unit integral and `L¹` norm at most `C`, and which concentrate at
`x₀`: for every neighbourhood `U` of `x₀`, eventually `f i` vanishes almost everywhere outside `U`.
Then `∫ x, f i x • φ x ∂μ` tends to `a` for every `φ` tending to `a` at `x₀` whose products
`f i • φ` are eventually almost everywhere strongly measurable. -/
lemma tendsto_integral_smul_of_tendsto {ι : Type*} {l : Filter ι} {f : ι → α →₁[μ] 𝕜}
    {C : ℝ} {x₀ : α} [TopologicalSpace α] (hf : ∀ᶠ i in l, ∫ x, f i x ∂μ = 1)
    (hfC : ∀ᶠ i in l, ‖f i‖ ≤ C) (hfx₀ : ∀ U ∈ 𝓝 x₀, ∀ᶠ i in l, ∀ᵐ x ∂μ, x ∉ U → f i x = 0)
    {φ : α → E} (hφ : ∀ᶠ i in l, AEStronglyMeasurable (fun x ↦ f i x • φ x) μ) {a : E}
    (hφa : Tendsto φ (𝓝 x₀) (𝓝 a)) :
    Tendsto (fun i ↦ ∫ x, f i x • φ x ∂μ) l (𝓝 a) := by
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  -- Ask `φ` to stay within `δ` of `a`, where `δ * |C| < ε`.
  set δ : ℝ := ε / (|C| + 1) with hδ
  have hδpos : 0 < δ := div_pos hε (by positivity)
  have hδC : δ * |C| < ε := by
    rw [hδ, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    exact mul_lt_mul_of_pos_left (lt_add_one _) hε
  filter_upwards [hf, hfC, hfx₀ _ (hφa (closedBall_mem_nhds a hδpos)), hφ] with i hi hiC hiU hiφ
  rw [dist_eq_norm]
  calc ‖(∫ x, f i x • φ x ∂μ) - a‖ ≤ δ * ‖f i‖ :=
        norm_integral_smul_sub_le hi hiU hiφ fun x hx ↦ by simpa [dist_eq_norm] using hx
    _ ≤ δ * |C| := mul_le_mul_of_nonneg_left (hiC.trans (le_abs_self C)) hδpos.le
    _ < ε := hδC

variable (𝕜 μ) in
/-- **`L¹` peak functions exist.** For a measure positive on nonempty open sets and finite on some
neighbourhood of each point, every neighbourhood `U` of a point carries an `L¹` class of unit
integral and unit `L¹` norm vanishing almost everywhere outside `U`: the indicator of a
neighbourhood of finite measure inside `U`, normalized by that measure. -/
lemma exists_integral_eq_one_norm_eq_one [TopologicalSpace α] [OpensMeasurableSpace α]
    [μ.IsOpenPosMeasure] [IsLocallyFiniteMeasure μ] {x₀ : α} {U : Set α} (hU : U ∈ 𝓝 x₀) :
    ∃ f : α →₁[μ] 𝕜, ∫ x, f x ∂μ = 1 ∧ ‖f‖ = 1 ∧ ∀ᵐ x ∂μ, x ∉ U → f x = 0 := by
  -- An open neighbourhood `V ⊆ U` of `x₀` of positive, finite measure.
  obtain ⟨W, hW, hWμ⟩ := μ.finiteAt_nhds x₀
  set V := interior (U ∩ W)
  have hVμ : μ V ≠ ⊤ :=
    ((measure_mono (interior_subset.trans inter_subset_right)).trans_lt hWμ).ne
  have hVpos : 0 < μ.real V :=
    ENNReal.toReal_pos (isOpen_interior.measure_ne_zero μ
      ⟨x₀, mem_interior_iff_mem_nhds.2 (inter_mem hU hW)⟩) hVμ
  refine ⟨indicatorConstLp 1 isOpen_interior.measurableSet hVμ ((μ.real V)⁻¹ : 𝕜), ?_, ?_, ?_⟩
  · rw [integral_indicatorConstLp, RCLike.real_smul_eq_coe_mul, ← RCLike.ofReal_inv,
      ← RCLike.ofReal_mul, mul_inv_cancel₀ hVpos.ne', RCLike.ofReal_one]
  · rw [norm_indicatorConstLp one_ne_zero ENNReal.one_ne_top, ENNReal.toReal_one, div_one,
      Real.rpow_one, ← RCLike.ofReal_inv, RCLike.norm_ofReal, abs_of_pos (inv_pos.2 hVpos),
      inv_mul_cancel₀ hVpos.ne']
  · filter_upwards [indicatorConstLp_coeFn_notMem (p := 1) (hs := isOpen_interior.measurableSet)
      (hμs := hVμ) (c := ((μ.real V)⁻¹ : 𝕜))] with x hx hxU
    exact hx fun hxV ↦ hxU (interior_subset hxV).1

end TauCeti
