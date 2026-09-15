/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philippe Kevorkian, Jinzheng Li
-/
module

public import Physlib.Meta.TODO.Basic
public import Physlib.Cosmology.FLRW.Basic
/-!

# Matter content of FLRW cosmology

## i. Overview

This file describes the matter content of a Friedmann-Lemaître-Robertson-Walker universe
through the continuity equation `∂ₜ ρ + 3 H (ρ + p / c²) = 0` of the cosmic fluid and its
relation to the two Friedmann equations of `Physlib.Cosmology.FLRW.Basic`: the continuity
equation follows from the first-order equation (holding at all times) and the second-order
equation, and conversely the second-order equation follows from the first-order equation and
the continuity equation whenever `∂ₜ a ≠ 0`. The three equations are therefore not
independent. The equation of state, the density scaling laws and the perfect-fluid
stress-energy tensor are still TODO items.

Time derivatives of curves `Time → ℝ` are computed through the bridge
`Time.hasDerivAt_comp_toRealCLE_symm` to Mathlib's `HasDerivAt` on `ℝ`.

## ii. Key results

- `ContinuityEquation`: the continuity equation at an instant `t`.
- `deriv_firstOrderFriedmann`: the time derivative of the first-order Friedmann equation,
  `2 H (a''/a - H²) = (8 π G / 3) ρ' + 2 k c² H / a²`.
- `continuityEquation_of_friedmann`: the continuity equation follows from the two Friedmann
  equations.
- `secondOrderFriedmann_of_continuityEquation`: the second-order Friedmann equation follows
  from the first-order equation and the continuity equation when `∂ₜ a ≠ 0`.

## iii. Table of contents

- A. The continuity equation
  - A.1. The definition
  - A.2. The derivative of the first-order Friedmann equation
  - A.3. Continuity from the Friedmann equations
  - A.4. The second-order Friedmann equation from continuity
- B. Remaining TODO items

-/

@[expose] public section

namespace Cosmology.FLRW.FriedmannEquation

open Real Time

/-!

## A. The continuity equation

-/

/-!

### A.1. The definition

-/

/-- The continuity equation of the cosmic fluid at the instant `t`:
  `∂ₜ ρ + 3 H (ρ + p / c²) = 0`, with `H = hubbleConstant a`. -/
def ContinuityEquation (a ρ p : Time → ℝ) (c : ℝ) (t : Time) : Prop :=
  ∂ₜ ρ t + 3 * hubbleConstant a t * (ρ t + p t / c ^ 2) = 0

/-!

### A.2. The derivative of the first-order Friedmann equation

-/

/-- Differentiating the first-order Friedmann equation, assumed at all times, at `⟨τ⟩`:
  `2 H (a''/a - H²) = (8 π G / 3) ρ' + 2 k c² H / a²`. -/
lemma deriv_firstOrderFriedmann {a ρ : Time → ℝ} {k Λ G c τ : ℝ} (ha : a ⟨τ⟩ ≠ 0)
    (hd1 : DifferentiableAt ℝ a ⟨τ⟩) (hd2 : DifferentiableAt ℝ (∂ₜ a) ⟨τ⟩)
    (hdρ : DifferentiableAt ℝ ρ ⟨τ⟩) (hF1 : ∀ s, FirstOrderFriedmann a ρ k Λ G c s) :
    2 * (∂ₜ a ⟨τ⟩ / a ⟨τ⟩) * (∂ₜ (∂ₜ a) ⟨τ⟩ / a ⟨τ⟩ - (∂ₜ a ⟨τ⟩ / a ⟨τ⟩) ^ 2)
      = 8 * π * G / 3 * ∂ₜ ρ ⟨τ⟩
        + 2 * k * c ^ 2 * (∂ₜ a ⟨τ⟩ / a ⟨τ⟩) / (a ⟨τ⟩) ^ 2 := by
  have hA := hasDerivAt_mk_of_differentiableAt hd1
  have hA' := hasDerivAt_mk_of_differentiableAt hd2
  have hR := hasDerivAt_mk_of_differentiableAt hdρ
  have hL := (hA'.div hA ha).pow 2
  have hRd := ((hR.const_mul (8 * π * G / 3)).sub
    ((hasDerivAt_const τ (k * c ^ 2)).div (hA.pow 2) (pow_ne_zero 2 ha))).add_const
    (Λ * c ^ 2 / 3)
  have hu := hL.unique
    (hRd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun σ => hF1 ⟨σ⟩))
  simp only [Pi.pow_apply, Pi.div_apply, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, zero_mul,
    zero_sub] at hu
  field_simp at hu ⊢
  linear_combination hu

/-!

### A.3. Continuity from the Friedmann equations

-/

/-- The continuity equation follows from the first-order Friedmann equation, assumed at all
  times, and the second-order Friedmann equation at `t`; `a` must be twice differentiable and
  `ρ` differentiable at `t`. -/
lemma continuityEquation_of_friedmann {a ρ p : Time → ℝ} {k Λ G c : ℝ} {t : Time}
    (hG : 0 < G) (ha : a t ≠ 0) (hd1 : DifferentiableAt ℝ a t)
    (hd2 : DifferentiableAt ℝ (∂ₜ a) t)
    (hdρ : DifferentiableAt ℝ ρ t) (hF1 : ∀ s, FirstOrderFriedmann a ρ k Λ G c s)
    (hF2 : SecondOrderFriedmann a ρ p Λ G c t) :
    ContinuityEquation a ρ p c t := by
  obtain ⟨τ⟩ := t
  have hd := deriv_firstOrderFriedmann ha hd1 hd2 hdρ hF1
  have h1 := hF1 ⟨τ⟩
  unfold FirstOrderFriedmann at h1
  unfold SecondOrderFriedmann at hF2
  unfold ContinuityEquation hubbleConstant
  have hπ := Real.pi_pos
  have hG3 : 8 * π * G / 3 ≠ 0 := by positivity
  apply mul_left_cancel₀ hG3
  linear_combination -hd + 2 * (∂ₜ a ⟨τ⟩ / a ⟨τ⟩) * hF2
    - 2 * (∂ₜ a ⟨τ⟩ / a ⟨τ⟩) * h1

/-!

### A.4. The second-order Friedmann equation from continuity

-/

/-- The second-order Friedmann equation at `t` follows from the first-order Friedmann
  equation, assumed at all times, and the continuity equation at `t`, provided `∂ₜ a t ≠ 0`.
  Together with `continuityEquation_of_friedmann`, the three equations are not independent. -/
lemma secondOrderFriedmann_of_continuityEquation {a ρ p : Time → ℝ} {k Λ G c : ℝ}
    {t : Time} (ha : a t ≠ 0) (hd1' : ∂ₜ a t ≠ 0) (hd1 : DifferentiableAt ℝ a t)
    (hd2 : DifferentiableAt ℝ (∂ₜ a) t) (hdρ : DifferentiableAt ℝ ρ t)
    (hF1 : ∀ s, FirstOrderFriedmann a ρ k Λ G c s) (hC : ContinuityEquation a ρ p c t) :
    SecondOrderFriedmann a ρ p Λ G c t := by
  obtain ⟨τ⟩ := t
  have hd := deriv_firstOrderFriedmann ha hd1 hd2 hdρ hF1
  have h1 := hF1 ⟨τ⟩
  unfold FirstOrderFriedmann at h1
  unfold ContinuityEquation hubbleConstant at hC
  unfold SecondOrderFriedmann
  have hH : 2 * (∂ₜ a ⟨τ⟩ / a ⟨τ⟩) ≠ 0 := by
    have : ∂ₜ a ⟨τ⟩ / a ⟨τ⟩ ≠ 0 := div_ne_zero hd1' ha
    positivity
  apply mul_left_cancel₀ hH
  linear_combination hd + 8 * π * G / 3 * hC + 2 * (∂ₜ a ⟨τ⟩ / a ⟨τ⟩) * h1

/-!

## B. Remaining TODO items

-/

TODO "Define the perfect-fluid stress-energy tensor
  `T_{μν} = (ρ + P/c²) u_μ u_ν + P g_{μν}` for the FLRW metric."

TODO "Define the linear (barotropic) equation of state `P = w ρ c²` and prove the
  density scaling law `ρ = ρ₀ a^(−3(1+w))` for constant `w`."

TODO "Specialize the density scaling law to dust (`w = 0`, `ρ ∝ a⁻³`), radiation
  (`w = 1/3`, `ρ ∝ a⁻⁴`) and vacuum energy (`w = −1`, `ρ` constant)."

TODO "Prove that the cosmological constant acts as a `w = −1` perfect fluid with
  `ρ_Λ = Λ c² / (8 π G)` and `P_Λ = −ρ_Λ c²`."

end Cosmology.FLRW.FriedmannEquation
