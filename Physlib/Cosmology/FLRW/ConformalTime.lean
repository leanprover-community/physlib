/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philippe Kevorkian, Jinzheng Li
-/
module

public import Physlib.Meta.TODO.Basic
public import Physlib.Cosmology.FLRW.Distances
/-!

# Conformal time in FLRW cosmology

## i. Overview

The conformal time of an FLRW model is defined by `a dη = dt`. Counted from a time `t₁`, it is
`η = ∫_{t₁}^{t} dτ / a(τ)`. For `t₁` and `t` in the interval of the model, `∂ₜ η = 1 / a`. For
the Einstein-de Sitter model, counted from the Big Bang `t = 0`, it is `η = 3 t₀^(2/3) t^(1/3)`.

Physlib has no inverse function `t(η)`. The derivative with respect to `η` of a function of
cosmic time is therefore defined through the chain rule, `f' = a ∂ₜ f`. It is consistent with
`∂ₜ f = f' ∂ₜ η`.

The conformal Hubble factor `ℋ = a' / a` equals `a H`. For an FLRW model filled with a cosmic
fluid, the Friedmann equations in conformal time are `ℋ² = (8πG/3) ρ a² + (Λc²/3) a² - k c²` and
`a'' / a = (4πG/3) (ρ - 3 p / c²) a² + (2Λc²/3) a² - k c²`, with `k` the curvature parameter of
the spatial geometry of the model. At a time of the interval, the first one is equivalent to the
first-order Friedmann equation. At a time of the interval where the first-order equation holds,
the second one is equivalent to the second-order Friedmann equation.

## ii. Key results

- `FLRW.conformalTime`, `FLRW.deriv_conformalTime`: `∂ₜ η = 1 / a`.
- `FLRW.conformalTime_einsteinDeSitter`: the conformal time of the Einstein-de Sitter model.
- `FLRW.conformalDeriv`, `FLRW.deriv_eq_conformalDeriv_mul`: `f' = a ∂ₜ f` and
  `∂ₜ f = f' ∂ₜ η`.
- `FLRW.conformalHubble`, `FLRW.conformalHubble_eq`: `ℋ = a H`.
- `FLRW.ConformalFirstOrderFriedmann`, `FLRW.conformalFirstOrderFriedmann_iff`: the first-order
  Friedmann equation in conformal time.
- `FLRW.ConformalSecondOrderFriedmann`, `FLRW.conformalDeriv_conformalDeriv`,
  `FLRW.conformalSecondOrderFriedmann_iff`: the acceleration equation in conformal time.

## iii. Table of contents

- A. The conformal time
- B. The conformal derivative
- C. The conformal Hubble factor
- D. The Friedmann equations in conformal time

## iv. References

* None.

-/

@[expose] public section

namespace Cosmology.FLRW

open Real Time FriedmannEquation

variable (U : FLRW)

/-!

## A. The conformal time

-/

/-- The conformal time `η = ∫_{t₁}^{t} dτ / a(τ)` of an FLRW model, counted from the time
  `t₁`. A light ray emitted at `t₁` has travelled the comoving distance `c η` at `t`. -/
noncomputable def conformalTime (t₁ t : Time) : ℝ :=
  ∫ τ in t₁.val..t.val, 1 / U.a ⟨τ⟩

/-- For `t₁` and `t` in the interval of the model, `∂ₜ η = 1 / a`, that is `a dη = dt`. -/
lemma deriv_conformalTime {t₁ t : Time} (ht₁ : t₁ ∈ U.I) (ht : t ∈ U.I) :
    ∂ₜ (U.conformalTime t₁) t = 1 / U.a t := by
  have h : U.conformalTime t₁ = -fun s => U.comovingDistance 1 s t₁ := by
    funext s
    show ∫ τ in t₁.val..s.val, 1 / U.a ⟨τ⟩ = -(1 * ∫ τ in s.val..t₁.val, 1 / U.a ⟨τ⟩)
    rw [one_mul, intervalIntegral.integral_symm]
  rw [h, Time.deriv_neg, U.deriv_comovingDistance ht₁ ht]
  ring

/-- The conformal time of the Einstein-de Sitter model, counted from the Big Bang `t = 0`, is
  `η = 3 t₀^(2/3) t^(1/3)` for `t > 0`. -/
lemma conformalTime_einsteinDeSitter {t₀ : Time} (ht₀ : 0 < t₀.val) {t : Time}
    (ht : 0 < t.val) :
    (einsteinDeSitter t₀ ht₀).conformalTime ⟨0⟩ t
      = 3 * t₀.val ^ (2 / 3 : ℝ) * t.val ^ (1 / 3 : ℝ) := by
  have hset : {τ : ℝ | (⟨τ⟩ : Time) ∈ (einsteinDeSitter t₀ ht₀).I ∧ τ < t.val}
      = Set.Ioo 0 t.val := rfl
  have h := particleHorizon_einsteinDeSitter (c := 1) ht₀ ht
  rw [particleHorizon, hset, ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le ht.le, one_mul, mul_one] at h
  exact h

/-!

## B. The conformal derivative

-/

/-- The derivative with respect to the conformal time of a function of cosmic time, defined
  through the chain rule `f' = a ∂ₜ f` (from `dt = a dη`). -/
noncomputable def conformalDeriv (f : Time → ℝ) (t : Time) : ℝ := U.a t * ∂ₜ f t

/-- For `t₁` and `t` in the interval of the model, the conformal derivative satisfies the chain
  rule `∂ₜ f = f' ∂ₜ η`. -/
lemma deriv_eq_conformalDeriv_mul {f : Time → ℝ} {t₁ t : Time} (ht₁ : t₁ ∈ U.I)
    (ht : t ∈ U.I) : ∂ₜ f t = U.conformalDeriv f t * ∂ₜ (U.conformalTime t₁) t := by
  rw [U.deriv_conformalTime ht₁ ht, conformalDeriv, mul_right_comm,
    mul_one_div_cancel (U.a_ne_zero ht), one_mul]

/-- At a time of the interval of the model, the second conformal derivative of its scale factor
  is `a'' = a ((∂ₜ a)² + a ∂ₜ ∂ₜ a)`, by the product rule. -/
lemma conformalDeriv_conformalDeriv {t : Time} (ht : t ∈ U.I) :
    U.conformalDeriv (U.conformalDeriv U.a) t
      = U.a t * (∂ₜ U.a t ^ 2 + U.a t * ∂ₜ (∂ₜ U.a) t) := by
  obtain ⟨τ⟩ := t
  have hA := hasDerivAt_mk_of_differentiableAt (U.differentiableAt_a ht)
  have hA' := hasDerivAt_mk_of_differentiableAt (U.differentiableAt_deriv_a ht)
  rw [conformalDeriv, deriv_eq_of_hasDerivAt (f := U.conformalDeriv U.a) (hA.mul hA')]
  ring

/-!

## C. The conformal Hubble factor

-/

/-- The conformal Hubble factor `ℋ = a' / a`, the expansion rate per unit of conformal time. -/
noncomputable def conformalHubble (t : Time) : ℝ := U.conformalDeriv U.a t / U.a t

/-- The conformal Hubble factor is `ℋ = a H`. -/
lemma conformalHubble_eq (t : Time) :
    U.conformalHubble t = U.a t * hubbleConstant U.a t := by
  rw [conformalHubble, conformalDeriv, hubbleConstant, mul_div_assoc]

/-!

## D. The Friedmann equations in conformal time

-/

/-- The first-order Friedmann equation in conformal time for an FLRW model filled with a cosmic
  fluid, `ℋ² = (8πG/3) ρ a² + (Λc²/3) a² - k c²`, with `k` the curvature parameter of the spatial
  geometry of the model. -/
def ConformalFirstOrderFriedmann (F : CosmicFluid) (Λ G c : ℝ) (t : Time) : Prop :=
  U.conformalHubble t ^ 2
    = 8 * π * G / 3 * F.ρ t * U.a t ^ 2 + Λ * c ^ 2 / 3 * U.a t ^ 2
      - U.geometry.curvature * c ^ 2

/-- The acceleration equation in conformal time for an FLRW model filled with a cosmic fluid,
  `a'' / a = (4πG/3) (ρ - 3 p / c²) a² + (2Λc²/3) a² - k c²`, with `k` the curvature parameter
  of the spatial geometry of the model. -/
def ConformalSecondOrderFriedmann (F : CosmicFluid) (Λ G c : ℝ) (t : Time) : Prop :=
  U.conformalDeriv (U.conformalDeriv U.a) t / U.a t
    = 4 * π * G / 3 * (F.ρ t - 3 * F.p t / c ^ 2) * U.a t ^ 2 + 2 * Λ * c ^ 2 / 3 * U.a t ^ 2
      - U.geometry.curvature * c ^ 2

/-- At a time of the interval of the model, the first-order Friedmann equation is equivalent to
  its form in conformal time. -/
lemma conformalFirstOrderFriedmann_iff {F : CosmicFluid} {Λ G c : ℝ} {t : Time} (ht : t ∈ U.I) :
    FirstOrderFriedmann U.a F.ρ U.geometry.curvature Λ G c t
      ↔ U.ConformalFirstOrderFriedmann F Λ G c t := by
  have hA := pow_ne_zero 2 (U.a_ne_zero ht)
  have hk : U.geometry.curvature * c ^ 2 / U.a t ^ 2 * U.a t ^ 2
      = U.geometry.curvature * c ^ 2 := div_mul_cancel₀ _ hA
  rw [FirstOrderFriedmann, ConformalFirstOrderFriedmann, conformalHubble_eq, hubbleConstant]
  constructor
  · intro h
    linear_combination U.a t ^ 2 * h - hk
  · intro h
    refine mul_left_cancel₀ hA ?_
    linear_combination h + hk

/-- At a time of the interval of the model where the first-order Friedmann equation holds, the
  second-order Friedmann equation is equivalent to the acceleration equation in conformal
  time. -/
lemma conformalSecondOrderFriedmann_iff {F : CosmicFluid} {Λ G c : ℝ} {t : Time} (ht : t ∈ U.I)
    (hF1 : FirstOrderFriedmann U.a F.ρ U.geometry.curvature Λ G c t) :
    SecondOrderFriedmann U.a F.ρ F.p Λ G c t ↔ U.ConformalSecondOrderFriedmann F Λ G c t := by
  have ha := U.a_ne_zero ht
  have hA := pow_ne_zero 2 ha
  have hk : U.geometry.curvature * c ^ 2 / U.a t ^ 2 * U.a t ^ 2
      = U.geometry.curvature * c ^ 2 := div_mul_cancel₀ _ hA
  have hX : (∂ₜ U.a t / U.a t) ^ 2 * U.a t ^ 2 = ∂ₜ U.a t ^ 2 := by
    rw [div_pow, div_mul_cancel₀ _ hA]
  have hY : ∂ₜ (∂ₜ U.a) t / U.a t * U.a t = ∂ₜ (∂ₜ U.a) t := div_mul_cancel₀ _ ha
  have hZ : U.a t * (∂ₜ U.a t ^ 2 + U.a t * ∂ₜ (∂ₜ U.a) t) / U.a t
      = ∂ₜ U.a t ^ 2 + U.a t * ∂ₜ (∂ₜ U.a) t := mul_div_cancel_left₀ _ ha
  rw [FirstOrderFriedmann] at hF1
  rw [SecondOrderFriedmann, ConformalSecondOrderFriedmann, U.conformalDeriv_conformalDeriv ht]
  constructor
  · intro h
    linear_combination hZ + U.a t ^ 2 * hF1 - hX - hk + U.a t ^ 2 * h - U.a t * hY
  · intro h
    refine mul_left_cancel₀ hA ?_
    linear_combination U.a t * hY + h - hZ - U.a t ^ 2 * hF1 + hX + hk

end Cosmology.FLRW

TODO "State the FLRW metric in conformal time as `a(η)²` times a static metric,
  making its conformal flatness manifest."
