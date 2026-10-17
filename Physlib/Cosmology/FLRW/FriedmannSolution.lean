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

# Solutions of the Friedmann equations: dynamical criteria

## i. Overview

Qualitative consequences of the Friedmann equations for an FLRW model `U : FLRW` filled with a
cosmic fluid `F : CosmicFluid` that solves them, `U.FriedmannSolution F Λ G c`. The proposition
`FLRW.FriedmannSolution` itself is defined in `Physlib.Cosmology.FLRW.Basic`: the continuity
equation (`Physlib.Cosmology.FLRW.MatterContent`), the density parameters and the exact solutions,
which are used here, are stated about it. The energy conditions of the cosmic fluid are in
`Physlib.Cosmology.FLRW.EnergyConditions`. On the interval `U.I` of the model: the expansion
accelerates if and only if the fluid, with the cosmological constant folded in as a `w = -1`
component, violates the strong energy condition; the deceleration parameter is
`q = ½ Σ_x Ω_x (1 + 3 w_x)` for a finite family of barotropic fluids, and
`q = ½ (Ω_m + 2 Ω_r - 2 Ω_Λ)` for ΛCDM; with a spatial geometry of non-positive curvature,
positive density and `0 ≤ Λ`, the derivative `∂ₜ a` of the scale factor does not vanish, so that
a model expanding at one time of `U.I` expands at all times of `U.I`. Finally, a model whose scale
factor decelerates on `U.I` and expands at `t₀ ∈ U.I` lies below its tangent line at `t₀`, so that
it cannot be defined at any time earlier than `t₀ - a(t₀) / ∂ₜ a(t₀) = t₀ - 1 / H(t₀)`: its
interval of time is bounded below, the Big Bang being at most `1 / H(t₀)` in the past. This holds
for `0 ≤ ρ`, `0 ≤ p` and `Λ = 0`; the de Sitter model, with `0 < Λ`, is defined at all times.

## ii. Key results

- `FLRW.FriedmannSolution.deriv_deriv_scaleFactor_pos_iff`: `0 < ∂ₜ ∂ₜ a ↔ ρ + 3 p / c² < 0`
  (`Λ = 0`); `FLRW.FriedmannSolution.deriv_deriv_scaleFactor_pos_iff_lambda`: the same for the
  total fluid with `Λ` folded in.
- `FLRW.FriedmannSolution.decelerationParameter_eq_sum`: `q = ½ Σ_i Ω_i (1 + 3 w_i)`;
  `FLRW.FriedmannSolution.decelerationParameter_lambdaCDM`: `q = ½ (Ω_m + 2 Ω_r - 2 Ω_Λ)`.
- `FLRW.FriedmannSolution.deriv_scaleFactor_ne_zero`,
  `FLRW.FriedmannSolution.deriv_scaleFactor_pos`: eternal expansion for a non-positive curvature.
- `FLRW.scaleFactor_le_tangent`, `FLRW.lt_of_mem_I_of_decelerating`,
  `FLRW.FriedmannSolution.lt_of_mem_I`, `FLRW.FriedmannSolution.bddBelow_I`: the Big-Bang bound;
  `FLRW.not_bddBelow_deSitter_I`: the de Sitter model is defined at all times.

## iii. Table of contents

- A. The interval and the tangent-line bound for a decelerating model
- B. Accelerated expansion and the strong energy condition
- C. The deceleration parameter in terms of the density parameters
- D. Eternal expansion
- E. The Big-Bang bound for a solution of the Friedmann equations
- F. The de Sitter contrast

## iv. References

* None.

-/

@[expose] public section

namespace Cosmology

open Real Time FLRW.FriedmannEquation

namespace FLRW

/-!

## A. The interval and the tangent-line bound for a decelerating model

These statements hold for any FLRW model; they do not use the Friedmann equations.

-/

/-- The times between two times of the interval `U.I` of an FLRW model are in `U.I`. -/
lemma mk_mem_I_of_mem_Icc (U : FLRW) {σ τ x : ℝ} (hσ : (⟨σ⟩ : Time) ∈ U.I)
    (hτ : (⟨τ⟩ : Time) ∈ U.I) (hx : x ∈ Set.Icc σ τ) : (⟨x⟩ : Time) ∈ U.I :=
  U.ordConnected_I.out hσ hτ ⟨(Time.le_def _ _).mpr hx.1, (Time.le_def _ _).mpr hx.2⟩

/-- Along the time coordinate, the derivative of the scale factor is continuous on any segment
  of the interval `U.I`. -/
lemma continuousOn_deriv_scaleFactor_mk (U : FLRW) {σ τ : ℝ} (hσ : (⟨σ⟩ : Time) ∈ U.I)
    (hτ : (⟨τ⟩ : Time) ∈ U.I) : ContinuousOn (fun x : ℝ => ∂ₜ U.a ⟨x⟩) (Set.Icc σ τ) :=
  U.differentiableOn_deriv_a.continuousOn.comp toRealCLE.symm.continuous.continuousOn
    fun _ hx => U.mk_mem_I_of_mem_Icc hσ hτ hx

/-- If the scale factor decelerates on the interval (`∂ₜ ∂ₜ a ≤ 0` on `U.I`), it lies below its
  tangent line at any time `t₀` of `U.I`: `a t ≤ a t₀ + ∂ₜ a t₀ (t - t₀)` for `t ∈ U.I`. The
  derivative is antitone on the segment between `t` and `t₀`, which lies in `U.I`, and the mean
  value inequality concludes. -/
lemma scaleFactor_le_tangent (U : FLRW) (hdec : ∀ s ∈ U.I, ∂ₜ (∂ₜ U.a) s ≤ 0) {t₀ t : Time}
    (ht₀ : t₀ ∈ U.I) (ht : t ∈ U.I) : U.a t ≤ U.a t₀ + ∂ₜ U.a t₀ * (t.val - t₀.val) := by
  obtain ⟨τ₀⟩ := t₀
  obtain ⟨σ⟩ := t
  dsimp only
  -- on a segment of `U.I`, the scale factor and its derivative have derivatives along the
  -- time coordinate, and the derivative of the scale factor is antitone
  have key : ∀ {lo hi : ℝ}, (⟨lo⟩ : Time) ∈ U.I → (⟨hi⟩ : Time) ∈ U.I →
      (∀ x ∈ Set.Icc lo hi, HasDerivAt (fun y : ℝ => U.a ⟨y⟩) (∂ₜ U.a ⟨x⟩) x) ∧
      AntitoneOn (fun x : ℝ => ∂ₜ U.a ⟨x⟩) (Set.Icc lo hi) := by
    intro lo hi hlo hhi
    have hA : ∀ x ∈ Set.Icc lo hi, HasDerivAt (fun y : ℝ => U.a ⟨y⟩) (∂ₜ U.a ⟨x⟩) x :=
      fun x hx => hasDerivAt_mk_of_differentiableAt
        (U.differentiableAt_a (U.mk_mem_I_of_mem_Icc hlo hhi hx))
    have hA' : ∀ x ∈ Set.Icc lo hi,
        HasDerivAt (fun y : ℝ => ∂ₜ U.a ⟨y⟩) (∂ₜ (∂ₜ U.a) ⟨x⟩) x :=
      fun x hx => hasDerivAt_mk_of_differentiableAt
        (U.differentiableAt_deriv_a (U.mk_mem_I_of_mem_Icc hlo hhi hx))
    refine ⟨hA, antitoneOn_of_deriv_nonpos (convex_Icc lo hi)
      (U.continuousOn_deriv_scaleFactor_mk hlo hhi)
      (fun x hx => (hA' x (interior_subset hx)).differentiableAt.differentiableWithinAt)
      (fun x hx => ?_)⟩
    rw [(hA' x (interior_subset hx)).deriv]
    exact hdec _ (U.mk_mem_I_of_mem_Icc hlo hhi (interior_subset hx))
  rcases le_total σ τ₀ with h | h
  · obtain ⟨hA, hanti⟩ := key ht ht₀
    have hmv := Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc σ τ₀)
      (fun x hx => (hA x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hA x (interior_subset hx)).differentiableAt.differentiableWithinAt)
      (C := ∂ₜ U.a ⟨τ₀⟩) (fun x hx => by
        rw [(hA x (interior_subset hx)).deriv]
        exact hanti (interior_subset hx) ⟨h, le_rfl⟩ (interior_subset hx).2)
      σ ⟨le_rfl, h⟩ τ₀ ⟨h, le_rfl⟩ h
    linarith
  · obtain ⟨hA, hanti⟩ := key ht₀ ht
    have hmv := Convex.image_sub_le_mul_sub_of_deriv_le (convex_Icc τ₀ σ)
      (fun x hx => (hA x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hA x (interior_subset hx)).differentiableAt.differentiableWithinAt)
      (C := ∂ₜ U.a ⟨τ₀⟩) (fun x hx => by
        rw [(hA x (interior_subset hx)).deriv]
        exact hanti ⟨le_rfl, h⟩ (interior_subset hx) (interior_subset hx).1)
      τ₀ ⟨le_rfl, h⟩ σ ⟨h, le_rfl⟩ h
    linarith

/-- The Big-Bang bound for an FLRW model: if the scale factor decelerates on `U.I` and the model
  expands at `t₀ ∈ U.I`, every time of `U.I` is later than `t₀ - a t₀ / ∂ₜ a t₀`. Earlier, the
  tangent line, and hence the scale factor, would be non-positive. -/
lemma lt_of_mem_I_of_decelerating (U : FLRW) (hdec : ∀ s ∈ U.I, ∂ₜ (∂ₜ U.a) s ≤ 0)
    {t₀ : Time} (ht₀ : t₀ ∈ U.I) (h0 : 0 < ∂ₜ U.a t₀) {t : Time} (ht : t ∈ U.I) :
    t₀.val - U.a t₀ / ∂ₜ U.a t₀ < t.val := by
  by_contra hle
  have hle' := not_lt.mp hle
  have htan := U.scaleFactor_le_tangent hdec ht₀ ht
  have hpos := U.a_pos t ht
  have hq : ∂ₜ U.a t₀ * (U.a t₀ / ∂ₜ U.a t₀) = U.a t₀ := by field_simp
  have h1 : t.val - t₀.val ≤ -(U.a t₀ / ∂ₜ U.a t₀) := by linarith
  have h2 := mul_le_mul_of_nonneg_left h1 h0.le
  rw [mul_neg, hq] at h2
  linarith

/-- Hence the interval of an FLRW model that decelerates on `U.I` and expands at one of its
  times is bounded below. -/
lemma bddBelow_I_of_decelerating (U : FLRW) (hdec : ∀ s ∈ U.I, ∂ₜ (∂ₜ U.a) s ≤ 0) {t₀ : Time}
    (ht₀ : t₀ ∈ U.I) (h0 : 0 < ∂ₜ U.a t₀) : BddBelow U.I :=
  ⟨⟨t₀.val - U.a t₀ / ∂ₜ U.a t₀⟩, fun _ ht =>
    (Time.le_def _ _).mpr (U.lt_of_mem_I_of_decelerating hdec ht₀ h0 ht).le⟩

namespace FriedmannSolution

variable {U : FLRW} {F : CosmicFluid} {Λ G c : ℝ}

/-!

## B. Accelerated expansion and the strong energy condition

-/

/-- On the interval of a solution without cosmological constant, the second derivative
  `∂ₜ ∂ₜ a` of the scale factor is positive (the expansion accelerates) if and only if
  `ρ + 3 p / c² < 0`, that is, if and only if the strong energy condition of the cosmic fluid
  fails through its second inequality. -/
lemma deriv_deriv_scaleFactor_pos_iff (h : U.FriedmannSolution F 0 G c) (hG : 0 < G) {t : Time}
    (ht : t ∈ U.I) : 0 < ∂ₜ (∂ₜ U.a) t ↔ F.ρ t + 3 * F.p t / c ^ 2 < 0 := by
  have hF2 := h.secondOrder t ht
  unfold SecondOrderFriedmann at hF2
  rw [← div_pos_iff_of_pos_right (U.a_pos t ht), hF2]
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

/-- With cosmological constant `Λ`, on the interval of a solution, `∂ₜ ∂ₜ a` is positive if and
  only if the total fluid, `Λ` folded in as the `w = -1` component, violates
  `0 ≤ ρ + 3 p / c²`. -/
lemma deriv_deriv_scaleFactor_pos_iff_lambda (h : U.FriedmannSolution F Λ G c) (hG : 0 < G)
    (hc : c ≠ 0) {t : Time} (ht : t ∈ U.I) :
    0 < ∂ₜ (∂ₜ U.a) t ↔ (F.ρ t + cosmologicalConstantDensity Λ G c)
      + 3 * (F.p t + cosmologicalConstantPressure Λ G c) / c ^ 2 < 0 :=
  ((friedmannSolution_iff_addCosmologicalConstant hG.ne' hc).mp h).deriv_deriv_scaleFactor_pos_iff
    hG ht

/-!

## C. The deceleration parameter in terms of the density parameters

-/

/-- For a cosmic fluid made of a finite family of barotropic fluids `ρ_i` with
  `p_i = w_i ρ_i c²`, without cosmological constant, `q = ½ Σ_i Ω_i (1 + 3 w_i)` at every time
  of the interval at which `H ≠ 0`. -/
lemma decelerationParameter_eq_sum {n : ℕ} {ρi : Fin n → Time → ℝ} {w : Fin n → ℝ}
    (h : U.FriedmannSolution F 0 G c) (hG : G ≠ 0) (hc : c ≠ 0)
    (hρ : ∀ s, F.ρ s = ∑ i, ρi i s) (hp : ∀ s, F.p s = ∑ i, w i * ρi i s * c ^ 2) {t : Time}
    (ht : t ∈ U.I) (hH : hubbleConstant U.a t ≠ 0) :
    decelerationParameter U.a t
      = 1 / 2 * ∑ i, densityParameter U.a (ρi i) G t * (1 + 3 * w i) := by
  have hF2 := h.secondOrder t ht
  have ha := U.a_ne_zero ht
  unfold SecondOrderFriedmann at hF2
  rw [hρ t, hp t] at hF2
  have hsum1 : (∑ i, ρi i t) + 3 * (∑ i, w i * ρi i t * c ^ 2) / c ^ 2
      = ∑ i, ρi i t * (1 + 3 * w i) := by
    rw [mul_div_assoc, Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  rw [hsum1] at hF2
  have ha'' := (div_eq_iff ha).mp hF2
  have hsum2 : ∑ i, densityParameter U.a (ρi i) G t * (1 + 3 * w i)
      = 8 * π * G / (3 * hubbleConstant U.a t ^ 2) * ∑ i, ρi i t * (1 + 3 * w i) := by
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

/-- ΛCDM: for a cosmic fluid made of matter (`w = 0`) and radiation (`w = 1/3`), with the
  cosmological constant, `q = ½ (Ω_m + 2 Ω_r - 2 Ω_Λ)` at every time of the interval. -/
lemma decelerationParameter_lambdaCDM {ρm ρr : Time → ℝ} (h : U.FriedmannSolution F Λ G c)
    (hc : c ≠ 0) (hρ : ∀ s, F.ρ s = ρm s + ρr s) (hp : ∀ s, F.p s = ρr s * c ^ 2 / 3)
    {t : Time} (ht : t ∈ U.I) :
    decelerationParameter U.a t = 1 / 2 * (densityParameter U.a ρm G t
      + 2 * densityParameter U.a ρr G t - 2 * lambdaDensityParameter U.a Λ c t) := by
  have hF2 := h.secondOrder t ht
  have ha := U.a_ne_zero ht
  unfold SecondOrderFriedmann at hF2
  rw [hρ t, hp t] at hF2
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

/-- For a spatial geometry of non-positive curvature parameter, `0 ≤ Λ` and a positive density
  at a time `t` of the interval, the first-order Friedmann equation forces `0 < H²` at `t`:
  the derivative `∂ₜ a` of the scale factor does not vanish at `t`. -/
lemma deriv_scaleFactor_ne_zero (h : U.FriedmannSolution F Λ G c)
    (hk : U.geometry.curvature ≤ 0) (hΛ : 0 ≤ Λ) (hG : 0 < G) {t : Time} (ht : t ∈ U.I)
    (hρ : 0 < F.ρ t) : ∂ₜ U.a t ≠ 0 := by
  have h1 := h.firstOrder t ht
  unfold FirstOrderFriedmann at h1
  have ha2 : 0 < U.a t ^ 2 := pow_pos (U.a_pos t ht) 2
  have hkc : U.geometry.curvature * c ^ 2 ≤ 0 := by nlinarith [sq_nonneg c, hk]
  have h2 : U.geometry.curvature * c ^ 2 / U.a t ^ 2 ≤ 0 :=
    (div_le_iff₀ ha2).mpr (by linarith)
  have h3 : 0 < 8 * π * G / 3 * F.ρ t := by positivity
  have h4 : 0 ≤ Λ * c ^ 2 / 3 := by positivity
  have hsq : 0 < (∂ₜ U.a t / U.a t) ^ 2 := by
    rw [h1]
    linarith
  intro h0
  rw [h0, zero_div] at hsq
  simp at hsq

/-- If moreover the density is positive on the interval and the model expands at one time `t₀`
  of `U.I`, it expands at all times of `U.I`: with a non-positive curvature parameter, `0 ≤ Λ`
  and a positive density, an expanding model expands forever. -/
lemma deriv_scaleFactor_pos (h : U.FriedmannSolution F Λ G c) (hk : U.geometry.curvature ≤ 0)
    (hΛ : 0 ≤ Λ) (hG : 0 < G) (hρ : ∀ s ∈ U.I, 0 < F.ρ s) {t₀ : Time} (ht₀ : t₀ ∈ U.I)
    (h0 : 0 < ∂ₜ U.a t₀) {t : Time} (ht : t ∈ U.I) : 0 < ∂ₜ U.a t := by
  have hne : ∀ s ∈ U.I, ∂ₜ U.a s ≠ 0 := fun s hs =>
    h.deriv_scaleFactor_ne_zero hk hΛ hG hs (hρ s hs)
  by_contra hle
  have hlt : ∂ₜ U.a t < 0 := lt_of_le_of_ne (not_lt.mp hle) (hne t ht)
  obtain ⟨τ₀⟩ := t₀
  obtain ⟨σ⟩ := t
  have hmem : (0 : ℝ) ∈ Set.Icc (∂ₜ U.a ⟨σ⟩) (∂ₜ U.a ⟨τ₀⟩) := ⟨hlt.le, h0.le⟩
  rcases le_total σ τ₀ with hστ | hστ
  · obtain ⟨x, hx, hx0⟩ :=
      intermediate_value_Icc hστ (U.continuousOn_deriv_scaleFactor_mk ht ht₀) hmem
    exact hne _ (U.mk_mem_I_of_mem_Icc ht ht₀ hx) hx0
  · obtain ⟨x, hx, hx0⟩ :=
      intermediate_value_Icc' hστ (U.continuousOn_deriv_scaleFactor_mk ht₀ ht) hmem
    exact hne _ (U.mk_mem_I_of_mem_Icc ht₀ ht hx) hx0

/-!

## E. The Big-Bang bound for a solution of the Friedmann equations

-/

/-- With `0 ≤ ρ`, `0 ≤ p` and `Λ = 0` at a time `t` of the interval, the second-order Friedmann
  equation gives `∂ₜ ∂ₜ a ≤ 0` at `t`: the expansion decelerates. -/
lemma deriv_deriv_scaleFactor_nonpos (h : U.FriedmannSolution F 0 G c) (hG : 0 < G)
    (hc : c ≠ 0) {t : Time} (ht : t ∈ U.I) (hρ : 0 ≤ F.ρ t) (hp : 0 ≤ F.p t) :
    ∂ₜ (∂ₜ U.a) t ≤ 0 := by
  have hF2 := h.secondOrder t ht
  have ha := U.a_pos t ht
  unfold SecondOrderFriedmann at hF2
  have ha'' := (div_eq_iff ha.ne').mp hF2
  rw [ha'']
  have hc2 : 0 < c ^ 2 := by positivity
  have hX : 0 ≤ F.ρ t + 3 * F.p t / c ^ 2 := by positivity
  have hk : 0 ≤ 4 * π * G / 3 := by positivity
  have := mul_nonneg (mul_nonneg hk hX) ha.le
  linarith

/-- The Big-Bang bound for a solution of the Friedmann equations with `0 ≤ ρ`, `0 ≤ p` and
  `Λ = 0` on its interval: if the model expands at `t₀ ∈ U.I`, every time of `U.I` is later than
  `t₀ - 1 / H(t₀)`, the Big Bang being at most `1 / H(t₀)` in the past. -/
lemma lt_of_mem_I (h : U.FriedmannSolution F 0 G c) (hG : 0 < G) (hc : c ≠ 0)
    (hρ : ∀ s ∈ U.I, 0 ≤ F.ρ s) (hp : ∀ s ∈ U.I, 0 ≤ F.p s) {t₀ : Time} (ht₀ : t₀ ∈ U.I)
    (h0 : 0 < ∂ₜ U.a t₀) {t : Time} (ht : t ∈ U.I) :
    t₀.val - 1 / hubbleConstant U.a t₀ < t.val := by
  have hdec : ∀ s ∈ U.I, ∂ₜ (∂ₜ U.a) s ≤ 0 := fun s hs =>
    h.deriv_deriv_scaleFactor_nonpos hG hc hs (hρ s hs) (hp s hs)
  have := U.lt_of_mem_I_of_decelerating hdec ht₀ h0 ht
  unfold hubbleConstant
  rwa [one_div_div]

/-- Under the same assumptions, the interval of the model is bounded below. -/
lemma bddBelow_I (h : U.FriedmannSolution F 0 G c) (hG : 0 < G) (hc : c ≠ 0)
    (hρ : ∀ s ∈ U.I, 0 ≤ F.ρ s) (hp : ∀ s ∈ U.I, 0 ≤ F.p s) {t₀ : Time} (ht₀ : t₀ ∈ U.I)
    (h0 : 0 < ∂ₜ U.a t₀) : BddBelow U.I :=
  U.bddBelow_I_of_decelerating
    (fun s hs => h.deriv_deriv_scaleFactor_nonpos hG hc hs (hρ s hs) (hp s hs)) ht₀ h0

end FriedmannSolution

/-!

## F. The de Sitter contrast

-/

/-- The de Sitter model, which solves the Friedmann equations with `0 < Λ`
  (`FLRW.friedmannSolution_deSitter`), is defined at all times: its interval is not bounded
  below. -/
lemma not_bddBelow_deSitter_I (a₀ σ Λ c : ℝ) (ha₀ : 0 < a₀) :
    ¬ BddBelow (FLRW.deSitter a₀ σ Λ c ha₀).I := by
  rintro ⟨b, hb⟩
  have h1 := (Time.le_def _ _).mp
    (hb (show (⟨b.val - 1⟩ : Time) ∈ (FLRW.deSitter a₀ σ Λ c ha₀).I from Set.mem_univ _))
  dsimp only at h1
  linarith

end FLRW

end Cosmology
