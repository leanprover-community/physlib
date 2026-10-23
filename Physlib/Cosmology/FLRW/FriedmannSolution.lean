/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philippe Kevorkian, Jinzheng Li
-/
module

public import Physlib.Cosmology.FLRW.DensityParameters
public import Mathlib.Topology.Order.IntermediateValue
/-!

# Solutions of the Friedmann equations: dynamical criteria

## i. Overview

Qualitative consequences of the Friedmann equations for an FLRW model `U : FLRW` filled with a
cosmic fluid `F : CosmicFluid` that solves them, `U.FriedmannSolution F Λ G c`. The proposition
`FLRW.FriedmannSolution` itself is defined in `Physlib.Cosmology.FLRW.Basic`, together with the
tangent-line bound for a decelerating FLRW model, which does not use the Friedmann equations; the
continuity equation (`Physlib.Cosmology.FLRW.MatterContent`) and the density parameters, which
are used here, are stated about it. The energy conditions of the cosmic fluid are in
`Physlib.Cosmology.FLRW.EnergyConditions`. On the interval `U.I` of the model: a solution with
cosmological constant `Λ` is a solution without it for the fluid with `Λ` folded in; the
expansion accelerates if and only if the fluid, with the cosmological constant folded in as a
`w = -1` component, violates the strong energy condition; the deceleration parameter is
`q = ½ Σ_x Ω_x (1 + 3 w_x)` for a finite family of barotropic fluids, and
`q = ½ (Ω_m + 2 Ω_r - 2 Ω_Λ)` for ΛCDM; with a spatial geometry of non-positive curvature,
positive density and `0 ≤ Λ`, the derivative `∂ₜ a` of the scale factor does not vanish, so that
a model expanding at one time of `U.I` expands at all times of `U.I`. Finally, with `0 ≤ ρ`,
`0 ≤ p` and `Λ = 0` the scale factor decelerates on `U.I`, so that a model expanding at
`t₀ ∈ U.I` cannot be defined at any time earlier than `t₀ - 1 / H(t₀)`: its interval of time is
bounded below, the Big Bang being at most `1 / H(t₀)` in the past. The de Sitter model of
`Physlib.Cosmology.FLRW.DeSitter`, with `0 < Λ`, is defined at all times.

## ii. Key results

- `FLRW.friedmannSolution_iff_addCosmologicalConstant`: a solution with `Λ` is a solution
  without `Λ` for the fluid `F.addCosmologicalConstant Λ G c`.
- `FLRW.FriedmannSolution.deriv_deriv_scaleFactor_pos_iff`: `0 < ∂ₜ ∂ₜ a ↔ ρ + 3 p / c² < 0`
  (`Λ = 0`); `FLRW.FriedmannSolution.deriv_deriv_scaleFactor_pos_iff_lambda`: the same for the
  total fluid with `Λ` folded in.
- `FLRW.FriedmannSolution.decelerationParameter_eq_sum`: `q = ½ Σ_i Ω_i (1 + 3 w_i)`;
  `FLRW.FriedmannSolution.decelerationParameter_lambdaCDM`: `q = ½ (Ω_m + 2 Ω_r - 2 Ω_Λ)`.
- `FLRW.FriedmannSolution.deriv_scaleFactor_ne_zero`,
  `FLRW.FriedmannSolution.deriv_scaleFactor_pos`: eternal expansion for a non-positive curvature.
- `FLRW.FriedmannSolution.deriv_deriv_scaleFactor_nonpos`,
  `FLRW.FriedmannSolution.lt_of_mem_I`, `FLRW.FriedmannSolution.bddBelow_I`: the Big-Bang bound.

## iii. Table of contents

- A. The cosmological constant folded into the cosmic fluid
- B. Accelerated expansion and the strong energy condition
- C. The deceleration parameter in terms of the density parameters
- D. Eternal expansion
- E. The Big-Bang bound for a solution of the Friedmann equations

## iv. References

* None.

-/

@[expose] public section

namespace Cosmology.FLRW.FriedmannSolution

open Real Time Cosmology.FLRW.FriedmannEquation

/-!

## A. The cosmological constant folded into the cosmic fluid

-/

/-- An FLRW model filled with the cosmic fluid `F` solves the Friedmann equations with the
  cosmological constant `Λ` if and only if it solves them without cosmological constant for the
  fluid `F` with `Λ` folded in. -/
lemma _root_.Cosmology.FLRW.friedmannSolution_iff_addCosmologicalConstant {U : FLRW}
    {F : CosmicFluid} {Λ G c : ℝ} (hG : G ≠ 0) (hc : c ≠ 0) :
    U.FriedmannSolution F Λ G c ↔ U.FriedmannSolution (F.addCosmologicalConstant Λ G c) 0 G c :=
  ⟨fun h => ⟨fun t ht => (firstOrderFriedmann_iff_lambdaFluid hG).mp (h.firstOrder t ht),
      fun t ht => (secondOrderFriedmann_iff_lambdaFluid hG hc).mp (h.secondOrder t ht)⟩,
    fun h => ⟨fun t ht => (firstOrderFriedmann_iff_lambdaFluid hG).mpr (h.firstOrder t ht),
      fun t ht => (secondOrderFriedmann_iff_lambdaFluid hG hc).mpr (h.secondOrder t ht)⟩⟩

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

/-- For a solution of the Friedmann equations without cosmological constant whose cosmic fluid is
  a sum of barotropic components of pressure `w_i ρ_i c²`, the deceleration parameter is
  `q = ½ Σ_i Ω_i (1 + 3 w_i)` at the times of the interval of the model at which `H ≠ 0`, for
  `G ≠ 0` and `c ≠ 0`. -/
lemma decelerationParameter_eq_sum {n : ℕ} {Fi : Fin n → CosmicFluid} {w : Fin n → ℝ}
    (h : U.FriedmannSolution F 0 G c) (hG : G ≠ 0) (hc : c ≠ 0)
    (hρ : ∀ s, F.ρ s = ∑ i, (Fi i).ρ s) (hp : ∀ s, F.p s = ∑ i, (Fi i).p s)
    (hw : ∀ i, (Fi i).p = barotropicPressure (w i) (Fi i).ρ c) {t : Time} (ht : t ∈ U.I)
    (hH : hubbleConstant U.a t ≠ 0) :
    decelerationParameter U.a t
      = 1 / 2 * ∑ i, U.densityParameter (Fi i) G t * (1 + 3 * w i) := by
  have hp' : ∀ s, F.p s = ∑ i, w i * (Fi i).ρ s * c ^ 2 := fun s => by
    simp only [hp s, hw, barotropicPressure]
  have hF2 := h.secondOrder t ht
  have ha := U.a_ne_zero ht
  unfold SecondOrderFriedmann at hF2
  rw [hρ t, hp' t] at hF2
  have hsum1 : (∑ i, (Fi i).ρ t) + 3 * (∑ i, w i * (Fi i).ρ t * c ^ 2) / c ^ 2
      = ∑ i, (Fi i).ρ t * (1 + 3 * w i) := by
    rw [mul_div_assoc, Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  rw [hsum1] at hF2
  have ha'' := (div_eq_iff ha).mp hF2
  have hsum2 : ∑ i, U.densityParameter (Fi i) G t * (1 + 3 * w i)
      = 8 * π * G / (3 * hubbleConstant U.a t ^ 2) * ∑ i, (Fi i).ρ t * (1 + 3 * w i) := by
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

/-- For a solution of the Friedmann equations whose cosmic fluid is the sum of matter (zero
  pressure) and radiation (pressure `ρ_r c² / 3`), the deceleration parameter is
  `q = ½ (Ω_m + 2 Ω_r - 2 Ω_Λ)` at the times of the interval of the model, for `c ≠ 0` (the ΛCDM
  case). -/
lemma decelerationParameter_lambdaCDM {Fm Fr : CosmicFluid} (h : U.FriedmannSolution F Λ G c)
    (hc : c ≠ 0) (hρ : ∀ s, F.ρ s = Fm.ρ s + Fr.ρ s) (hp : ∀ s, F.p s = Fm.p s + Fr.p s)
    (hm : Fm.p = barotropicPressure 0 Fm.ρ c) (hr : Fr.p = barotropicPressure (1 / 3) Fr.ρ c)
    {t : Time} (ht : t ∈ U.I) :
    decelerationParameter U.a t = 1 / 2 * (U.densityParameter Fm G t
      + 2 * U.densityParameter Fr G t - 2 * U.lambdaDensityParameter Λ c t) := by
  have hp' : ∀ s, F.p s = Fr.ρ s * c ^ 2 / 3 := fun s => by
    rw [hp s, hm, hr]
    simp only [barotropicPressure]
    ring
  have hF2 := h.secondOrder t ht
  have ha := U.a_ne_zero ht
  unfold SecondOrderFriedmann at hF2
  rw [hρ t, hp' t] at hF2
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

end Cosmology.FLRW.FriedmannSolution
