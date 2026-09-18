/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philippe Kevorkian, Jinzheng Li
-/
module

public import Physlib.Cosmology.FLRW.DensityParameters
public import Physlib.Cosmology.FLRW.Solutions
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.IntermediateValue
/-!

# Dynamical criteria for FLRW cosmology

## i. Overview

Qualitative consequences of the Friedmann equations of `Physlib.Cosmology.FLRW.Basic`:
the energy conditions of the cosmic fluid; the expansion accelerates if and only if the fluid
(with the cosmological constant folded in as a `w = -1` component) violates the strong energy
condition; the deceleration parameter is `q = ½ Σ_x Ω_x (1 + 3 w_x)` for a finite family of
barotropic fluids, `q = ½ (Ω_m + 2 Ω_r - 2 Ω_Λ)` for ΛCDM; a universe with `k ≤ 0`, positive
density and `Λ ≥ 0` has `∂ₜ a ≠ 0` at all times, so that an expanding universe expands forever;
and a decelerating universe expanding at `t₀` has `a ≤ 0` at every time earlier than
`t₀ - a(t₀) / ∂ₜ a(t₀) = t₀ - 1 / H₀`, so that its scale factor vanishes at a finite time in the
past if it is continuous, whereas the de Sitter scale factor is positive at all times.

## ii. Key results

- `NullEnergyCondition`, `WeakEnergyCondition`, `StrongEnergyCondition`,
  `DominantEnergyCondition` and the implications between them.
- `deriv_deriv_pos_iff`: `∂ₜ ∂ₜ a > 0 ↔ ρ + 3 p / c² < 0` (`Λ = 0`);
  `deriv_deriv_pos_iff_lambda`: the same for the total fluid with `Λ` folded in.
- `decelerationParameter_eq_sum`: `q = ½ Σ_i Ω_i (1 + 3 w_i)`;
  `decelerationParameter_lambdaCDM`: `q = ½ (Ω_m + 2 Ω_r - 2 Ω_Λ)`.
- `deriv_ne_zero_of_friedmann`, `deriv_pos_of_friedmann`: eternal expansion for `k ≤ 0`.
- `deriv_deriv_nonpos_of_friedmann`, `scaleFactor_nonpos_of_decelerating`,
  `exists_scaleFactor_eq_zero`: the Big-Bang bound and the existence of a zero of `a`;
  `deSitterScaleFactor_pos`: no such zero for de Sitter.

## iii. Table of contents

- A. The energy conditions
- B. Accelerated expansion and the strong energy condition
- C. The deceleration parameter in terms of the density parameters
- D. Eternal expansion
- E. The Big-Bang singularity
  - E.1. Deceleration from the second-order Friedmann equation
  - E.2. The bound on the scale factor
  - E.3. The de Sitter contrast

-/

@[expose] public section

namespace Cosmology.FLRW.FriedmannEquation

open Real Time

/-!

## A. The energy conditions

-/

/-- The null energy condition `ρ + p / c² ≥ 0`. -/
def NullEnergyCondition (ρ p : Time → ℝ) (c : ℝ) (t : Time) : Prop := 0 ≤ ρ t + p t / c ^ 2

/-- The weak energy condition `ρ ≥ 0 ∧ ρ + p / c² ≥ 0`. -/
def WeakEnergyCondition (ρ p : Time → ℝ) (c : ℝ) (t : Time) : Prop :=
  0 ≤ ρ t ∧ 0 ≤ ρ t + p t / c ^ 2

/-- The strong energy condition `ρ + p / c² ≥ 0 ∧ ρ + 3 p / c² ≥ 0`. -/
def StrongEnergyCondition (ρ p : Time → ℝ) (c : ℝ) (t : Time) : Prop :=
  0 ≤ ρ t + p t / c ^ 2 ∧ 0 ≤ ρ t + 3 * p t / c ^ 2

/-- The dominant energy condition `ρ ≥ 0 ∧ |p| ≤ ρ c²`. -/
def DominantEnergyCondition (ρ p : Time → ℝ) (c : ℝ) (t : Time) : Prop :=
  0 ≤ ρ t ∧ |p t| ≤ ρ t * c ^ 2

lemma WeakEnergyCondition.of_dominant {ρ p : Time → ℝ} {c : ℝ} {t : Time} (hc : c ≠ 0)
    (h : DominantEnergyCondition ρ p c t) : WeakEnergyCondition ρ p c t := by
  obtain ⟨h0, h1⟩ := h
  have hc2 : 0 < c ^ 2 := by positivity
  have h2 : -(ρ t * c ^ 2) ≤ p t := (abs_le.mp h1).1
  refine ⟨h0, ?_⟩
  have : -(ρ t) ≤ p t / c ^ 2 := by
    rw [le_div_iff₀ hc2]
    linarith
  linarith

lemma NullEnergyCondition.of_weak {ρ p : Time → ℝ} {c : ℝ} {t : Time}
    (h : WeakEnergyCondition ρ p c t) : NullEnergyCondition ρ p c t := h.2

lemma NullEnergyCondition.of_strong {ρ p : Time → ℝ} {c : ℝ} {t : Time}
    (h : StrongEnergyCondition ρ p c t) : NullEnergyCondition ρ p c t := h.1

/-!

## B. Accelerated expansion and the strong energy condition

-/

/-- Without cosmological constant, the expansion accelerates if and only if
  `ρ + 3 p / c² < 0`, that is, if and only if the strong energy condition fails through its
  second inequality. -/
lemma deriv_deriv_pos_iff {a ρ p : Time → ℝ} {G c : ℝ} {t : Time} (hG : 0 < G) (ha : 0 < a t)
    (hF2 : SecondOrderFriedmann a ρ p 0 G c t) :
    0 < ∂ₜ (∂ₜ a) t ↔ ρ t + 3 * p t / c ^ 2 < 0 := by
  unfold SecondOrderFriedmann at hF2
  rw [← div_pos_iff_of_pos_right ha, hF2]
  have hk : 0 < 4 * π * G / 3 := by positivity
  simp only [zero_mul, zero_div, add_zero]
  constructor
  · intro h
    by_contra hX
    have hX' := not_lt.mp hX
    have := mul_nonneg hk.le hX'
    linarith
  · intro h
    have := mul_pos hk (neg_pos.mpr h)
    linarith

/-- With cosmological constant, the expansion accelerates if and only if the total fluid,
  `Λ` folded in as the `w = -1` component, violates `ρ + 3 p / c² ≥ 0`. -/
lemma deriv_deriv_pos_iff_lambda {a ρ p : Time → ℝ} {Λ G c : ℝ} {t : Time} (hG : 0 < G)
    (hc : c ≠ 0) (ha : 0 < a t) (hF2 : SecondOrderFriedmann a ρ p Λ G c t) :
    0 < ∂ₜ (∂ₜ a) t ↔
      (ρ t + cosmologicalConstantDensity Λ G c)
        + 3 * (p t + cosmologicalConstantPressure Λ G c) / c ^ 2 < 0 :=
  deriv_deriv_pos_iff hG ha ((secondOrderFriedmann_iff_lambdaFluid hG.ne' hc).mp hF2)

/-!

## C. The deceleration parameter in terms of the density parameters

-/

/-- For a finite family of barotropic fluids `ρ_i` with `p_i = w_i ρ_i c²`, without
  cosmological constant, `q = ½ Σ_i Ω_i (1 + 3 w_i)`. -/
lemma decelerationParameter_eq_sum {n : ℕ} {a : Time → ℝ} {ρi : Fin n → Time → ℝ}
    {w : Fin n → ℝ} {G c : ℝ} {t : Time} (hG : G ≠ 0) (hc : c ≠ 0) (ha : a t ≠ 0)
    (hH : hubbleConstant a t ≠ 0)
    (hF2 : SecondOrderFriedmann a (fun s => ∑ i, ρi i s) (fun s => ∑ i, w i * ρi i s * c ^ 2)
      0 G c t) :
    decelerationParameter a t = 1 / 2 * ∑ i, densityParameter a (ρi i) G t * (1 + 3 * w i) := by
  unfold SecondOrderFriedmann at hF2
  dsimp only at hF2
  have hsum1 : (∑ i, ρi i t) + 3 * (∑ i, w i * ρi i t * c ^ 2) / c ^ 2
      = ∑ i, ρi i t * (1 + 3 * w i) := by
    rw [mul_div_assoc, Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  rw [hsum1] at hF2
  have ha'' := (div_eq_iff ha).mp hF2
  have hsum2 : ∑ i, densityParameter a (ρi i) G t * (1 + 3 * w i)
      = 8 * π * G / (3 * hubbleConstant a t ^ 2) * ∑ i, ρi i t * (1 + 3 * w i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold densityParameter criticalDensity
    have hπ := Real.pi_ne_zero
    field_simp
  rw [hsum2]
  unfold decelerationParameter
  unfold hubbleConstant at hH ⊢
  rw [ha'']
  have hπ := Real.pi_ne_zero
  field_simp
  ring

/-- ΛCDM: matter (`w = 0`), radiation (`w = 1/3`) and the cosmological constant give
  `q = ½ (Ω_m + 2 Ω_r - 2 Ω_Λ)`. -/
lemma decelerationParameter_lambdaCDM {a ρm ρr : Time → ℝ} {Λ G c : ℝ} {t : Time}
    (hc : c ≠ 0) (ha : a t ≠ 0)
    (hF2 : SecondOrderFriedmann a (fun s => ρm s + ρr s) (fun s => ρr s * c ^ 2 / 3) Λ G c t) :
    decelerationParameter a t = 1 / 2 * (densityParameter a ρm G t
      + 2 * densityParameter a ρr G t - 2 * lambdaDensityParameter a Λ c t) := by
  unfold SecondOrderFriedmann at hF2
  dsimp only at hF2
  have ha'' := (div_eq_iff ha).mp hF2
  unfold decelerationParameter densityParameter lambdaDensityParameter criticalDensity
  unfold hubbleConstant
  rw [ha'']
  have hπ := Real.pi_ne_zero
  field_simp
  ring

/-!

## D. Eternal expansion

-/

/-- For `k ≤ 0`, `Λ ≥ 0` and positive density, the first-order Friedmann equation forces
  `H² > 0`, hence `∂ₜ a ≠ 0` at every time. -/
lemma deriv_ne_zero_of_friedmann {a ρ : Time → ℝ} {k Λ G c : ℝ} (hk : k ≤ 0) (hΛ : 0 ≤ Λ)
    (hρ : ∀ s, 0 < ρ s) (hapos : ∀ s, 0 < a s) (hG : 0 < G)
    (hF1 : ∀ s, FirstOrderFriedmann a ρ k Λ G c s) (s : Time) : ∂ₜ a s ≠ 0 := by
  have h := hF1 s
  unfold FirstOrderFriedmann at h
  have h1 : 0 ≤ -(k * c ^ 2 / a s ^ 2) := by
    have ha2 : 0 < a s ^ 2 := by
      have := hapos s
      positivity
    have hkc : k * c ^ 2 ≤ 0 := by nlinarith [sq_nonneg c, hk]
    have : k * c ^ 2 / a s ^ 2 ≤ 0 := (div_le_iff₀ ha2).mpr (by linarith)
    linarith
  have h2 : 0 < 8 * π * G / 3 * ρ s := by
    have := hρ s
    positivity
  have h3 : 0 ≤ Λ * c ^ 2 / 3 := by positivity
  have hsq : 0 < (∂ₜ a s / a s) ^ 2 := by
    rw [h]
    linarith
  have hne : ∂ₜ a s / a s ≠ 0 := by
    intro h0
    rw [h0] at hsq
    simp at hsq
  exact (div_ne_zero_iff.mp hne).1

/-- If moreover `∂ₜ a` is continuous and positive at one time, it is positive at all times:
  an expanding universe with `k ≤ 0`, `Λ ≥ 0` and positive density expands forever. -/
lemma deriv_pos_of_friedmann {a ρ : Time → ℝ} {k Λ G c : ℝ} (hk : k ≤ 0) (hΛ : 0 ≤ Λ)
    (hρ : ∀ s, 0 < ρ s) (hapos : ∀ s, 0 < a s) (hG : 0 < G)
    (hF1 : ∀ s, FirstOrderFriedmann a ρ k Λ G c s) (hcont : Continuous (∂ₜ a)) {t₀ : Time}
    (h0 : 0 < ∂ₜ a t₀) (s : Time) : 0 < ∂ₜ a s := by
  have hne := deriv_ne_zero_of_friedmann hk hΛ hρ hapos hG hF1
  have hf : Continuous (fun σ : ℝ => ∂ₜ a ⟨σ⟩) := hcont.comp toRealCLE.symm.continuous
  obtain ⟨τ₀⟩ := t₀
  obtain ⟨σ⟩ := s
  by_contra hle
  have hle' := not_lt.mp hle
  have hlt : ∂ₜ a ⟨σ⟩ < 0 := lt_of_le_of_ne hle' (hne ⟨σ⟩)
  rcases le_or_gt σ τ₀ with hστ | hστ
  · have hmem : (0 : ℝ) ∈ Set.Icc (∂ₜ a ⟨σ⟩) (∂ₜ a ⟨τ₀⟩) := ⟨hlt.le, h0.le⟩
    obtain ⟨x, _, hx⟩ := intermediate_value_Icc hστ hf.continuousOn hmem
    exact hne ⟨x⟩ hx
  · have hmem : (0 : ℝ) ∈ Set.Icc (∂ₜ a ⟨σ⟩) (∂ₜ a ⟨τ₀⟩) := ⟨hlt.le, h0.le⟩
    obtain ⟨x, _, hx⟩ := intermediate_value_Icc' hστ.le hf.continuousOn hmem
    exact hne ⟨x⟩ hx

/-!

## E. The Big-Bang singularity

-/

/-!

### E.1. Deceleration from the second-order Friedmann equation

-/

/-- With `ρ ≥ 0`, `p ≥ 0`, `Λ = 0` and `a > 0`, the second-order Friedmann equation gives
  `∂ₜ ∂ₜ a ≤ 0`. -/
lemma deriv_deriv_nonpos_of_friedmann {a ρ p : Time → ℝ} {G c : ℝ} {t : Time} (hρ : 0 ≤ ρ t)
    (hp : 0 ≤ p t) (ha : 0 < a t) (hG : 0 < G) (hc : c ≠ 0)
    (hF2 : SecondOrderFriedmann a ρ p 0 G c t) : ∂ₜ (∂ₜ a) t ≤ 0 := by
  unfold SecondOrderFriedmann at hF2
  have ha'' := (div_eq_iff ha.ne').mp hF2
  rw [ha'']
  have hc2 : 0 < c ^ 2 := by positivity
  have hX : 0 ≤ ρ t + 3 * p t / c ^ 2 := by positivity
  have hk : 0 ≤ 4 * π * G / 3 := by positivity
  have := mul_nonneg (mul_nonneg hk hX) ha.le
  linarith

/-!

### E.2. The bound on the scale factor

-/

/-- If `a` is twice differentiable with `∂ₜ ∂ₜ a ≤ 0` at all times and `∂ₜ a t₀ > 0`, then
  `a t ≤ 0` for every `t` with `t ≤ t₀ - a t₀ / ∂ₜ a t₀`: a decelerating universe expanding
  at `t₀` cannot have a positive scale factor earlier than `t₀ - 1 / H₀`. The proof is the
  tangent-line bound `a t ≤ a t₀ + ∂ₜ a t₀ (t - t₀)` of a function with non-increasing
  derivative. -/
lemma scaleFactor_nonpos_of_decelerating {a : Time → ℝ} (hd1 : Differentiable ℝ a)
    (hd2 : Differentiable ℝ (∂ₜ a)) (hdec : ∀ s, ∂ₜ (∂ₜ a) s ≤ 0) {t₀ : Time}
    (h0 : 0 < ∂ₜ a t₀) {t : Time} (ht : t.val ≤ t₀.val - a t₀ / ∂ₜ a t₀) : a t ≤ 0 := by
  obtain ⟨τ₀⟩ := t₀
  obtain ⟨σ⟩ := t
  dsimp only at ht
  have hf : Differentiable ℝ (fun σ : ℝ => a ⟨σ⟩) :=
    hd1.comp toRealCLE.symm.differentiable
  have hf' : Differentiable ℝ (fun σ : ℝ => ∂ₜ a ⟨σ⟩) :=
    hd2.comp toRealCLE.symm.differentiable
  have hanti : Antitone (fun σ : ℝ => ∂ₜ a ⟨σ⟩) :=
    antitone_of_deriv_nonpos hf' fun x => by
      rw [(hasDerivAt_mk_of_differentiableAt (hd2 ⟨x⟩)).deriv]
      exact hdec ⟨x⟩
  have htan : a ⟨σ⟩ ≤ a ⟨τ₀⟩ + ∂ₜ a ⟨τ₀⟩ * (σ - τ₀) := by
    rcases le_or_gt σ τ₀ with h | h
    · have := Convex.mul_sub_le_image_sub_of_le_deriv (convex_Iic τ₀)
        hf.continuous.continuousOn hf.differentiableOn (C := ∂ₜ a ⟨τ₀⟩)
        (fun x hx => by
          rw [(hasDerivAt_mk_of_differentiableAt (hd1 ⟨x⟩)).deriv]
          rw [interior_Iic] at hx
          exact hanti (le_of_lt hx))
        σ (Set.mem_Iic.mpr h) τ₀ (Set.mem_Iic.mpr le_rfl) h
      linarith
    · have := Convex.image_sub_le_mul_sub_of_deriv_le (convex_Ici τ₀)
        hf.continuous.continuousOn hf.differentiableOn (C := ∂ₜ a ⟨τ₀⟩)
        (fun x hx => by
          rw [(hasDerivAt_mk_of_differentiableAt (hd1 ⟨x⟩)).deriv]
          rw [interior_Ici] at hx
          exact hanti (le_of_lt hx))
        τ₀ (Set.mem_Ici.mpr le_rfl) σ (Set.mem_Ici.mpr h.le) h.le
      linarith
  have hσ : ∂ₜ a ⟨τ₀⟩ * σ ≤ ∂ₜ a ⟨τ₀⟩ * τ₀ - a ⟨τ₀⟩ := by
    have := mul_le_mul_of_nonneg_left ht h0.le
    rw [mul_sub, mul_div_cancel₀ _ h0.ne'] at this
    exact this
  linarith

/-- A decelerating universe expanding at `t₀` with `a t₀ > 0` has a zero of its scale factor
  at some time (earlier than `t₀`), by the intermediate value theorem: the Big-Bang
  singularity, at most `1 / H₀` in the past. -/
lemma exists_scaleFactor_eq_zero {a : Time → ℝ} (hd1 : Differentiable ℝ a)
    (hd2 : Differentiable ℝ (∂ₜ a)) (hdec : ∀ s, ∂ₜ (∂ₜ a) s ≤ 0) {t₀ : Time}
    (h0 : 0 < ∂ₜ a t₀) (ha0 : 0 < a t₀) : ∃ t : Time, a t = 0 := by
  obtain ⟨τ₀⟩ := t₀
  obtain ⟨τ₁, hτ₁⟩ : ∃ τ₁ : ℝ, τ₁ = τ₀ - a ⟨τ₀⟩ / ∂ₜ a ⟨τ₀⟩ := ⟨_, rfl⟩
  have hle : τ₁ ≤ τ₀ := by
    have : 0 < a ⟨τ₀⟩ / ∂ₜ a ⟨τ₀⟩ := div_pos ha0 h0
    linarith
  have h1 : a ⟨τ₁⟩ ≤ 0 :=
    scaleFactor_nonpos_of_decelerating hd1 hd2 hdec h0 (t := ⟨τ₁⟩) (by dsimp only; rw [hτ₁])
  have hf : Continuous (fun σ : ℝ => a ⟨σ⟩) := hd1.continuous.comp toRealCLE.symm.continuous
  have hmem : (0 : ℝ) ∈ Set.Icc (a ⟨τ₁⟩) (a ⟨τ₀⟩) := ⟨h1, ha0.le⟩
  obtain ⟨x, _, hx⟩ := intermediate_value_Icc hle hf.continuousOn hmem
  exact ⟨⟨x⟩, hx⟩

/-!

### E.3. The de Sitter contrast

-/

/-- The de Sitter scale factor is positive at all times: no Big-Bang singularity. -/
lemma deSitterScaleFactor_pos {a₀ σ Λ c : ℝ} (ha₀ : 0 < a₀) (t : Time) :
    0 < deSitterScaleFactor a₀ σ Λ c t := by
  unfold deSitterScaleFactor
  positivity

end Cosmology.FLRW.FriedmannEquation
