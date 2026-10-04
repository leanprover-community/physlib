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

The conformal time `η` is defined by `a dη = dt`, that is `η(t) = ∫ dτ / a(τ)`; its time
derivative is `1 / a`. Since Physlib has no inverse function `t(η)`, the derivative of a function
of time with respect to `η` is defined through the chain rule, `f' = a ∂ₜ f`, and shown to be
consistent with `∂ₜ f = f' ∂ₜ η`. The conformal Hubble factor `ℋ = a' / a` equals `a H`, and the
Friedmann and acceleration equations in conformal time,
`ℋ² = (8πG/3) ρ a² + (Λc²/3) a² − k c²` and
`a''/a = (4πG/3)(ρ − 3 p/c²) a² + (2Λc²/3) a² − k c²`, are derived from their cosmic-time forms.

Not stated here: the FLRW metric in conformal time and its conformal flatness, the metric not
being an object of Physlib yet.

## ii. Key results

- `conformalTime`, `deriv_conformalTime`: `∂ₜ η = 1 / a`; `conformalTime_einsteinDeSitter`.
- `conformalDeriv`, `deriv_eq_conformalDeriv_mul`: `f' = a ∂ₜ f` and `∂ₜ f = f' ∂ₜ η`.
- `conformalHubble`, `conformalHubble_eq`: `ℋ = a H`.
- `ConformalFirstOrderFriedmann`, `ConformalSecondOrderFriedmann`,
  `conformalFirstOrderFriedmann_iff`, `conformalDeriv_conformalDeriv`,
  `conformalSecondOrderFriedmann_of`.

## iii. Table of contents

- A. The conformal time
- B. The conformal derivative
- C. The conformal Hubble factor
- D. The Friedmann equations in conformal time
- E. Remaining TODO item

-/

@[expose] public section

namespace Cosmology.FLRW.FriedmannEquation

open Real Time

/-!

## A. The conformal time

-/

/-- The conformal time `η(t) = ∫_{t_ref}^{t} dτ / a(τ)`, counted from a reference time. -/
noncomputable def conformalTime (a : Time → ℝ) (tref t : Time) : ℝ :=
  ∫ τ in tref.val..t.val, 1 / a ⟨τ⟩

/-- `∂ₜ η = 1 / a`, that is `a dη = dt` (fundamental theorem of calculus). -/
lemma deriv_conformalTime {a : Time → ℝ} (hcont : Continuous a) (hapos : ∀ s, 0 < a s)
    (tref t : Time) : ∂ₜ (conformalTime a tref) t = 1 / a t := by
  obtain ⟨τ⟩ := t
  have hf : Continuous (fun τ : ℝ => 1 / a ⟨τ⟩) :=
    continuous_const.div (hcont.comp toRealCLE.symm.continuous) fun τ => (hapos ⟨τ⟩).ne'
  exact deriv_eq_of_hasDerivAt (f := conformalTime a tref)
    (intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
      (hf.stronglyMeasurableAtFilter _ _) hf.continuousAt)

/-- The conformal time of the Einstein-de Sitter universe from `t = 0`, `η = 3 t₀^(2/3) t^(1/3)`. -/
lemma conformalTime_einsteinDeSitter {t₀ : Time} (ht₀ : 0 < t₀.val) {t : Time}
    (ht : 0 < t.val) :
    conformalTime (einsteinDeSitterScaleFactor t₀) ⟨0⟩ t
      = 3 * t₀.val ^ (2 / 3 : ℝ) * t.val ^ (1 / 3 : ℝ) := by
  have h := particleHorizon_einsteinDeSitter (c := 1) ht₀ ht
  unfold particleHorizon comovingDistance at h
  unfold conformalTime
  linarith

/-!

## B. The conformal derivative

-/

/-- The derivative with respect to the conformal time of a function of the cosmic time, through
  the chain rule `f' = a ∂ₜ f` (from `dt = a dη`). -/
noncomputable def conformalDeriv (a f : Time → ℝ) (t : Time) : ℝ := a t * ∂ₜ f t

/-- Consistency of the conformal derivative: `∂ₜ f = f' ∂ₜ η`. -/
lemma deriv_eq_conformalDeriv_mul {a f : Time → ℝ} (hcont : Continuous a) (hapos : ∀ s, 0 < a s)
    (tref t : Time) : ∂ₜ f t = conformalDeriv a f t * ∂ₜ (conformalTime a tref) t := by
  rw [deriv_conformalTime hcont hapos, conformalDeriv]
  have := (hapos t).ne'
  field_simp

/-!

## C. The conformal Hubble factor

-/

/-- The conformal Hubble factor `ℋ = a' / a`. -/
noncomputable def conformalHubble (a : Time → ℝ) (t : Time) : ℝ := conformalDeriv a a t / a t

/-- `ℋ = a H`. -/
lemma conformalHubble_eq {a : Time → ℝ} {t : Time} (ha : a t ≠ 0) :
    conformalHubble a t = a t * hubbleConstant a t := by
  unfold conformalHubble conformalDeriv hubbleConstant
  field_simp

/-!

## D. The Friedmann equations in conformal time

-/

/-- The first-order Friedmann equation in conformal time,
  `ℋ² = (8πG/3) ρ a² + (Λc²/3) a² − k c²`. -/
def ConformalFirstOrderFriedmann (a ρ : Time → ℝ) (k Λ G c : ℝ) (t : Time) : Prop :=
  conformalHubble a t ^ 2 = 8 * π * G / 3 * ρ t * a t ^ 2 + Λ * c ^ 2 / 3 * a t ^ 2 - k * c ^ 2

/-- The acceleration equation in conformal time,
  `a''/a = (4πG/3)(ρ − 3 p/c²) a² + (2Λc²/3) a² − k c²`. -/
def ConformalSecondOrderFriedmann (a ρ p : Time → ℝ) (k Λ G c : ℝ) (t : Time) : Prop :=
  conformalDeriv a (conformalDeriv a a) t / a t
    = 4 * π * G / 3 * (ρ t - 3 * p t / c ^ 2) * a t ^ 2 + 2 * Λ * c ^ 2 / 3 * a t ^ 2 - k * c ^ 2

/-- The first-order Friedmann equation holds in cosmic time if and only if it holds in conformal
  time. -/
lemma conformalFirstOrderFriedmann_iff {a ρ : Time → ℝ} {k Λ G c : ℝ} {t : Time} (ha : a t ≠ 0) :
    FirstOrderFriedmann a ρ k Λ G c t ↔ ConformalFirstOrderFriedmann a ρ k Λ G c t := by
  unfold FirstOrderFriedmann ConformalFirstOrderFriedmann
  rw [conformalHubble_eq ha]
  unfold hubbleConstant
  have key : (a t * (∂ₜ a t / a t)) ^ 2 = (∂ₜ a t / a t) ^ 2 * a t ^ 2 := by
    field_simp
  rw [key]
  constructor
  · intro h
    rw [h]
    field_simp
    ring
  · intro h
    have h2 : 0 < a t ^ 2 := by positivity
    apply mul_right_cancel₀ (pow_ne_zero 2 ha)
    rw [h]
    field_simp
    ring

/-- The second conformal derivative of the scale factor, `a'' = a ((∂ₜ a)² + a ∂ₜ ∂ₜ a)`
  (product rule). -/
lemma conformalDeriv_conformalDeriv {a : Time → ℝ} {t : Time} (hd : DifferentiableAt ℝ a t)
    (hdd : DifferentiableAt ℝ (∂ₜ a) t) :
    conformalDeriv a (conformalDeriv a a) t = a t * (∂ₜ a t ^ 2 + a t * ∂ₜ (∂ₜ a) t) := by
  obtain ⟨τ⟩ := t
  have hA := hasDerivAt_mk_of_differentiableAt hd
  have hA' := hasDerivAt_mk_of_differentiableAt hdd
  have h := deriv_eq_of_hasDerivAt (f := conformalDeriv a a) (hA.mul hA')
  rw [show conformalDeriv a (conformalDeriv a a) ⟨τ⟩
    = a ⟨τ⟩ * ∂ₜ (conformalDeriv a a) ⟨τ⟩ from rfl, h]
  ring

/-- The acceleration equation in conformal time follows from the two Friedmann equations in
  cosmic time. -/
lemma conformalSecondOrderFriedmann_of {a ρ p : Time → ℝ} {k Λ G c : ℝ} {t : Time}
    (hd : DifferentiableAt ℝ a t) (hdd : DifferentiableAt ℝ (∂ₜ a) t) (ha : a t ≠ 0)
    (hF1 : FirstOrderFriedmann a ρ k Λ G c t) (hF2 : SecondOrderFriedmann a ρ p Λ G c t) :
    ConformalSecondOrderFriedmann a ρ p k Λ G c t := by
  unfold ConformalSecondOrderFriedmann
  rw [conformalDeriv_conformalDeriv hd hdd]
  unfold FirstOrderFriedmann at hF1
  unfold SecondOrderFriedmann at hF2
  have h2 := (div_eq_iff ha).mp hF2
  have h1 : ∂ₜ a t ^ 2 = (8 * π * G / 3 * ρ t - k * c ^ 2 / a t ^ 2 + Λ * c ^ 2 / 3) * a t ^ 2 := by
    rw [← hF1]
    field_simp
  have e : a t * (∂ₜ a t ^ 2 + a t * ∂ₜ (∂ₜ a) t) / a t = ∂ₜ a t ^ 2 + a t * ∂ₜ (∂ₜ a) t := by
    field_simp
  rw [e, h2, h1]
  field_simp
  ring

/-!

## E. Remaining TODO item

-/

TODO "State the FLRW metric in conformal time as `a(η)²` times a static metric,
  making its conformal flatness manifest."

end Cosmology.FLRW.FriedmannEquation
