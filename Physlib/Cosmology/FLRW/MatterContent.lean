/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philippe Kevorkian, Jinzheng Li
-/
module

public import Physlib.Meta.TODO.Basic
public import Physlib.Cosmology.FLRW.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
/-!

# Matter content of FLRW cosmology

## i. Overview

This file describes the matter content of a Friedmann-Lemaître-Robertson-Walker universe
through the continuity equation `∂ₜ ρ + 3 H (ρ + p / c²) = 0` of the cosmic fluid and its
relation to the two Friedmann equations of `Physlib.Cosmology.FLRW.Basic`: the continuity
equation follows from the first-order equation (holding at all times) and the second-order
equation, and conversely the second-order equation follows from the first-order equation and
the continuity equation whenever `∂ₜ a ≠ 0`. The three equations are therefore not
independent. For a barotropic equation of state `p = w ρ c²` with constant `w`, the continuity
equation gives the density scaling law `ρ ∝ a^(-3(1+w))`, specialised to dust, radiation and
vacuum energy; and the cosmological constant is equivalent to a `w = -1` fluid of density
`ρ_Λ = Λ c² / (8 π G)`. The perfect-fluid stress-energy tensor is still a TODO item.

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
- `barotropicPressure`: `p = w ρ c²`; `density_scaling`: under the barotropic continuity
  equation at all times, `ρ t = ρ t₀ (a t / a t₀)^(-3(1+w))`; `continuityEquation_of_scaling`:
  the converse; `density_scaling_dust`, `density_scaling_radiation`,
  `density_scaling_vacuum`: `ρ ∝ a⁻³`, `ρ ∝ a⁻⁴`, `ρ` constant.
- `cosmologicalConstantDensity`, `cosmologicalConstantPressure`:
  `ρ_Λ = Λ c² / (8 π G)`, `p_Λ = - ρ_Λ c²`; `firstOrderFriedmann_iff_lambdaFluid`,
  `secondOrderFriedmann_iff_lambdaFluid`: the Friedmann equations with `Λ` are the Friedmann
  equations without `Λ` for the fluid `ρ + ρ_Λ`, `p + p_Λ`;
  `cosmologicalConstantPressure_eq_barotropic`: `p_Λ` is the `w = -1` barotropic pressure.

## iii. Table of contents

- A. The continuity equation
  - A.1. The definition
  - A.2. The derivative of the first-order Friedmann equation
  - A.3. Continuity from the Friedmann equations
  - A.4. The second-order Friedmann equation from continuity
- B. The barotropic equation of state and the density scaling law
  - B.1. The equation of state
  - B.2. The density scaling law
  - B.3. Dust, radiation and vacuum energy
- C. The cosmological constant as a fluid
- D. Remaining TODO items

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

## B. The barotropic equation of state and the density scaling law

-/

/-!

### B.1. The equation of state

-/

/-- The barotropic pressure `p = w ρ c²` with constant equation-of-state parameter `w`. -/
noncomputable def barotropicPressure (w : ℝ) (ρ : Time → ℝ) (c : ℝ) : Time → ℝ :=
  fun t => w * ρ t * c ^ 2

/-- Under the barotropic continuity equation, `∂ₜ ρ = -3 (1 + w) H ρ`. -/
lemma deriv_of_continuityEquation_barotropic {a ρ : Time → ℝ} {w c : ℝ} {t : Time} (hc : c ≠ 0)
    (hC : ContinuityEquation a ρ (barotropicPressure w ρ c) c t) :
    ∂ₜ ρ t = -3 * (1 + w) * hubbleConstant a t * ρ t := by
  unfold ContinuityEquation barotropicPressure at hC
  have h : w * ρ t * c ^ 2 / c ^ 2 = w * ρ t := by
    field_simp
  rw [h] at hC
  linear_combination hC

/-!

### B.2. The density scaling law

-/

/-- Under the barotropic continuity equation at all times, the curve `σ ↦ ρ ⟨σ⟩ a ⟨σ⟩^(3(1+w))`
  has zero derivative. -/
lemma hasDerivAt_mul_rpow_of_continuityEquation {a ρ : Time → ℝ} {w c : ℝ} (hc : c ≠ 0)
    (hd1 : Differentiable ℝ a) (hdρ : Differentiable ℝ ρ) (hapos : ∀ s, 0 < a s)
    (hC : ∀ s, ContinuityEquation a ρ (barotropicPressure w ρ c) c s) (τ : ℝ) :
    HasDerivAt (fun σ : ℝ => ρ ⟨σ⟩ * a ⟨σ⟩ ^ (3 * (1 + w))) 0 τ := by
  have hA := hasDerivAt_mk_of_differentiableAt (hd1 ⟨τ⟩)
  have hR := hasDerivAt_mk_of_differentiableAt (hdρ ⟨τ⟩)
  have hP := hA.rpow_const (p := 3 * (1 + w)) (Or.inl (hapos ⟨τ⟩).ne')
  refine (hR.mul hP).congr_deriv ?_
  rw [deriv_of_continuityEquation_barotropic hc (hC ⟨τ⟩), Real.rpow_sub_one (hapos ⟨τ⟩).ne']
  unfold hubbleConstant
  field_simp
  ring

/-- The density scaling law: under the barotropic continuity equation at all times, with `a`
  and `ρ` differentiable and `a > 0`, `ρ t = ρ t₀ (a t / a t₀)^(-3(1+w))`. -/
lemma density_scaling {a ρ : Time → ℝ} {w c : ℝ} (hc : c ≠ 0) (hd1 : Differentiable ℝ a)
    (hdρ : Differentiable ℝ ρ) (hapos : ∀ s, 0 < a s)
    (hC : ∀ s, ContinuityEquation a ρ (barotropicPressure w ρ c) c s) (t t₀ : Time) :
    ρ t = ρ t₀ * (a t / a t₀) ^ (-(3 * (1 + w))) := by
  have hconst := is_const_of_deriv_eq_zero
    (fun τ => (hasDerivAt_mul_rpow_of_continuityEquation hc hd1 hdρ hapos hC τ).differentiableAt)
    (fun τ => (hasDerivAt_mul_rpow_of_continuityEquation hc hd1 hdρ hapos hC τ).deriv)
  obtain ⟨τ⟩ := t
  obtain ⟨τ₀⟩ := t₀
  have h := hconst τ τ₀
  beta_reduce at h
  have h1 := Real.rpow_pos_of_pos (hapos ⟨τ⟩) (3 * (1 + w))
  have h0 := Real.rpow_pos_of_pos (hapos ⟨τ₀⟩) (3 * (1 + w))
  rw [Real.rpow_neg (div_pos (hapos ⟨τ⟩) (hapos ⟨τ₀⟩)).le,
    Real.div_rpow (hapos ⟨τ⟩).le (hapos ⟨τ₀⟩).le]
  field_simp
  linear_combination h

/-- Conversely, `ρ = ρ₀ (a / a₀)^(-3(1+w))` satisfies the barotropic continuity equation at
  all times, for `a` differentiable and positive. -/
lemma continuityEquation_of_scaling {a : Time → ℝ} {w c ρ₀ a₀ : ℝ} (hc : c ≠ 0) (ha₀ : a₀ ≠ 0)
    (hd1 : Differentiable ℝ a) (hapos : ∀ s, 0 < a s) (t : Time) :
    ContinuityEquation a (fun s => ρ₀ * (a s / a₀) ^ (-(3 * (1 + w))))
      (barotropicPressure w (fun s => ρ₀ * (a s / a₀) ^ (-(3 * (1 + w)))) c) c t := by
  obtain ⟨τ⟩ := t
  have hA := hasDerivAt_mk_of_differentiableAt (hd1 ⟨τ⟩)
  have hx : a ⟨τ⟩ / a₀ ≠ 0 := div_ne_zero (hapos ⟨τ⟩).ne' ha₀
  have hP := ((hA.div_const a₀).rpow_const (p := -(3 * (1 + w))) (Or.inl hx)).const_mul ρ₀
  have hd : ∂ₜ (fun s : Time => ρ₀ * (a s / a₀) ^ (-(3 * (1 + w)))) ⟨τ⟩
      = ρ₀ * (∂ₜ a ⟨τ⟩ / a₀ * -(3 * (1 + w)) * (a ⟨τ⟩ / a₀) ^ (-(3 * (1 + w)) - 1)) :=
    deriv_comp_toRealCLE_of_hasDerivAt (fun σ => ρ₀ * (a ⟨σ⟩ / a₀) ^ (-(3 * (1 + w)))) ⟨τ⟩ _ hP
  unfold ContinuityEquation barotropicPressure hubbleConstant
  rw [hd, Real.rpow_sub_one hx]
  have ha := (hapos ⟨τ⟩).ne'
  field_simp
  ring

/-!

### B.3. Dust, radiation and vacuum energy

-/

/-- Dust, `w = 0`: `ρ ∝ a⁻³`. -/
lemma density_scaling_dust {a ρ : Time → ℝ} {c : ℝ} (hc : c ≠ 0) (hd1 : Differentiable ℝ a)
    (hdρ : Differentiable ℝ ρ) (hapos : ∀ s, 0 < a s)
    (hC : ∀ s, ContinuityEquation a ρ (barotropicPressure 0 ρ c) c s) (t t₀ : Time) :
    ρ t = ρ t₀ * (a t₀ / a t) ^ 3 := by
  rw [density_scaling hc hd1 hdρ hapos hC t t₀]
  have hx : 0 < a t / a t₀ := div_pos (hapos t) (hapos t₀)
  rw [show -(3 * (1 + (0 : ℝ))) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hx.le,
    Real.rpow_natCast, ← inv_pow, inv_div]

/-- Radiation, `w = 1/3`: `ρ ∝ a⁻⁴`. -/
lemma density_scaling_radiation {a ρ : Time → ℝ} {c : ℝ} (hc : c ≠ 0) (hd1 : Differentiable ℝ a)
    (hdρ : Differentiable ℝ ρ) (hapos : ∀ s, 0 < a s)
    (hC : ∀ s, ContinuityEquation a ρ (barotropicPressure (1 / 3) ρ c) c s) (t t₀ : Time) :
    ρ t = ρ t₀ * (a t₀ / a t) ^ 4 := by
  rw [density_scaling hc hd1 hdρ hapos hC t t₀]
  have hx : 0 < a t / a t₀ := div_pos (hapos t) (hapos t₀)
  rw [show -(3 * (1 + (1 / 3 : ℝ))) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg hx.le,
    Real.rpow_natCast, ← inv_pow, inv_div]

/-- Vacuum energy, `w = -1`: `ρ` is constant. -/
lemma density_scaling_vacuum {a ρ : Time → ℝ} {c : ℝ} (hc : c ≠ 0) (hd1 : Differentiable ℝ a)
    (hdρ : Differentiable ℝ ρ) (hapos : ∀ s, 0 < a s)
    (hC : ∀ s, ContinuityEquation a ρ (barotropicPressure (-1) ρ c) c s) (t t₀ : Time) :
    ρ t = ρ t₀ := by
  rw [density_scaling hc hd1 hdρ hapos hC t t₀,
    show -(3 * (1 + (-1 : ℝ))) = 0 by norm_num, Real.rpow_zero, mul_one]

/-!

## C. The cosmological constant as a fluid

-/

/-- The density `ρ_Λ = Λ c² / (8 π G)` associated with the cosmological constant. -/
noncomputable def cosmologicalConstantDensity (Λ G c : ℝ) : ℝ :=
  Λ * c ^ 2 / (8 * π * G)

/-- The pressure `p_Λ = - ρ_Λ c²` associated with the cosmological constant. -/
noncomputable def cosmologicalConstantPressure (Λ G c : ℝ) : ℝ :=
  -(cosmologicalConstantDensity Λ G c) * c ^ 2

/-- The first-order Friedmann equation with `Λ` is the first-order Friedmann equation without
  `Λ` for the density `ρ + ρ_Λ`. -/
lemma firstOrderFriedmann_iff_lambdaFluid {a ρ : Time → ℝ} {k Λ G c : ℝ} {t : Time}
    (hG : G ≠ 0) :
    FirstOrderFriedmann a ρ k Λ G c t ↔
      FirstOrderFriedmann a (fun s => ρ s + cosmologicalConstantDensity Λ G c) k 0 G c t := by
  unfold FirstOrderFriedmann cosmologicalConstantDensity
  have hπ := Real.pi_ne_zero
  have key : 8 * π * G / 3 * ρ t - k * c ^ 2 / a t ^ 2 + Λ * c ^ 2 / 3
      = 8 * π * G / 3 * (ρ t + Λ * c ^ 2 / (8 * π * G)) - k * c ^ 2 / a t ^ 2 + 0 * c ^ 2 / 3 := by
    field_simp
    ring
  rw [key]

/-- The second-order Friedmann equation with `Λ` is the second-order Friedmann equation
  without `Λ` for the density `ρ + ρ_Λ` and the pressure `p + p_Λ`. -/
lemma secondOrderFriedmann_iff_lambdaFluid {a ρ p : Time → ℝ} {Λ G c : ℝ} {t : Time}
    (hG : G ≠ 0) (hc : c ≠ 0) :
    SecondOrderFriedmann a ρ p Λ G c t ↔
      SecondOrderFriedmann a (fun s => ρ s + cosmologicalConstantDensity Λ G c)
        (fun s => p s + cosmologicalConstantPressure Λ G c) 0 G c t := by
  unfold SecondOrderFriedmann cosmologicalConstantPressure cosmologicalConstantDensity
  have hπ := Real.pi_ne_zero
  have key : -(4 * π * G / 3) * (ρ t + 3 * p t / c ^ 2) + Λ * c ^ 2 / 3
      = -(4 * π * G / 3) * (ρ t + Λ * c ^ 2 / (8 * π * G)
        + 3 * (p t + -(Λ * c ^ 2 / (8 * π * G)) * c ^ 2) / c ^ 2) + 0 * c ^ 2 / 3 := by
    field_simp
    ring
  rw [key]

/-- `p_Λ` is the barotropic pressure of `ρ_Λ` with `w = -1`. -/
lemma cosmologicalConstantPressure_eq_barotropic (Λ G c : ℝ) (t : Time) :
    cosmologicalConstantPressure Λ G c
      = barotropicPressure (-1) (fun _ => cosmologicalConstantDensity Λ G c) c t := by
  unfold cosmologicalConstantPressure barotropicPressure
  ring

/-!

## D. Remaining TODO items

-/

TODO "Define the perfect-fluid stress-energy tensor
  `T_{μν} = (ρ + P/c²) u_μ u_ν + P g_{μν}` for the FLRW metric."

end Cosmology.FLRW.FriedmannEquation
