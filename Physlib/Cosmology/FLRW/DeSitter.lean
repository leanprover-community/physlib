/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philippe Kevorkian, Jinzheng Li
-/
module

public import Physlib.Cosmology.FLRW.Basic
/-!

# The de Sitter solution of the Friedmann equations

## i. Overview

The de Sitter solution of the Friedmann equations (`FirstOrderFriedmann` and
`SecondOrderFriedmann` of `Physlib.Cosmology.FLRW.Basic`): the scale factor
`a(t) = a₀ exp(σ √(Λ/3) c t)`, `σ = ±1`, solves both equations with `ρ = 0`, `p = 0`, flat
spatial slices and `Λ > 0`; its Hubble parameter is constant and its deceleration parameter is
`q = -1`. As an FLRW model filled with the empty cosmic fluid, `FLRW.deSitter`, it is defined at
all times: its interval of time is not bounded below, whereas a solution with `0 ≤ ρ`, `0 ≤ p`
and `Λ = 0` that expands at one time has a Big Bang
(`Physlib.Cosmology.FLRW.FriedmannSolution`).

## ii. Key results

- `deSitterScaleFactor`: `a(t) = a₀ exp(σ √(Λ/3) c t)` with `σ = ±1`.
- `deSitterScaleFactor_firstOrderFriedmann`, `deSitterScaleFactor_secondOrderFriedmann`:
  it solves both Friedmann equations with `ρ = 0`, `p = 0`, `k = 0` and `Λ > 0`.
- `hubbleConstant_deSitterScaleFactor`: its Hubble parameter is the constant `σ √(Λ/3) c`
  (for any `σ`, `Λ`, `c`).
- `decelerationParameter_deSitterScaleFactor`: its deceleration parameter is `q = -1`.
- `FLRW.deSitter`, `FLRW.friedmannSolution_deSitter`: the de Sitter model, defined at all
  times, filled with the empty cosmic fluid solves the Friedmann equations.
- `FLRW.not_bddBelow_deSitter_I`: the interval of the de Sitter model is not bounded below.

## iii. Table of contents

- A. The scale factor and its derivatives
- B. The Friedmann equations
- C. The Hubble and deceleration parameters
- D. The de Sitter model
- E. The de Sitter model is defined at all times

## iv. References

* None.

-/

@[expose] public section

namespace Cosmology.FLRW.FriedmannEquation

open Real Time

/-!

## A. The scale factor and its derivatives

-/

/-- The de Sitter scale factor `a(t) = a₀ exp(σ √(Λ/3) c t)`, for `σ = ±1`
  (the expanding branch is `σ = 1`). -/
noncomputable def deSitterScaleFactor (a₀ σ Λ c : ℝ) : Time → ℝ :=
  fun t => a₀ * Real.exp (σ * √(Λ / 3) * c * t.val)

lemma deriv_deSitterScaleFactor (a₀ σ Λ c : ℝ) :
    ∂ₜ (deSitterScaleFactor a₀ σ Λ c) =
      fun t => a₀ * (σ * √(Λ / 3) * c) * Real.exp (σ * √(Λ / 3) * c * t.val) := by
  funext t
  have h : HasDerivAt (fun y : ℝ => a₀ * Real.exp (σ * √(Λ / 3) * c * y))
      (a₀ * (σ * √(Λ / 3) * c) * Real.exp (σ * √(Λ / 3) * c * t.val)) t.val := by
    have h := (((hasDerivAt_id t.val).const_mul (σ * √(Λ / 3) * c)).exp).const_mul a₀
    refine h.congr_deriv ?_
    simp only [id_eq]
    ring
  exact deriv_eq_of_hasDerivAt h

lemma deriv_deriv_deSitterScaleFactor (a₀ σ Λ c : ℝ) :
    ∂ₜ (∂ₜ (deSitterScaleFactor a₀ σ Λ c)) =
      fun t => a₀ * (σ * √(Λ / 3) * c) * (σ * √(Λ / 3) * c) *
        Real.exp (σ * √(Λ / 3) * c * t.val) := by
  rw [deriv_deSitterScaleFactor]
  funext t
  have h : HasDerivAt (fun y : ℝ => a₀ * (σ * √(Λ / 3) * c) * Real.exp (σ * √(Λ / 3) * c * y))
      (a₀ * (σ * √(Λ / 3) * c) * (σ * √(Λ / 3) * c) * Real.exp (σ * √(Λ / 3) * c * t.val))
      t.val := by
    have h := (((hasDerivAt_id t.val).const_mul (σ * √(Λ / 3) * c)).exp).const_mul
      (a₀ * (σ * √(Λ / 3) * c))
    refine h.congr_deriv ?_
    simp only [id_eq]
    ring
  exact deriv_eq_of_hasDerivAt h

/-- `σ² (√(Λ/3))² c² = Λ c² / 3` for `σ = ±1` and `0 ≤ Λ`. -/
lemma sq_deSitterRate {σ Λ c : ℝ} (hΛ : 0 ≤ Λ) (hσ : σ = 1 ∨ σ = -1) :
    (σ * √(Λ / 3) * c) ^ 2 = Λ * c ^ 2 / 3 := by
  have hs : √(Λ / 3) ^ 2 = Λ / 3 := Real.sq_sqrt (by linarith)
  rcases hσ with rfl | rfl <;> linear_combination c ^ 2 * hs

/-!

## B. The Friedmann equations

-/

/-- The de Sitter scale factor solves the first-order Friedmann equation with `ρ = 0`,
  `k = 0` and `Λ > 0`. -/
lemma deSitterScaleFactor_firstOrderFriedmann {a₀ σ Λ G c : ℝ} (hΛ : 0 < Λ)
    (ha₀ : a₀ ≠ 0) (hσ : σ = 1 ∨ σ = -1) (t : Time) :
    FirstOrderFriedmann (deSitterScaleFactor a₀ σ Λ c) (fun _ => 0) 0 Λ G c t := by
  unfold FirstOrderFriedmann
  rw [deriv_deSitterScaleFactor]
  simp only [deSitterScaleFactor]
  have he := Real.exp_ne_zero (σ * √(Λ / 3) * c * t.val)
  rw [show a₀ * (σ * √(Λ / 3) * c) * Real.exp (σ * √(Λ / 3) * c * t.val) /
      (a₀ * Real.exp (σ * √(Λ / 3) * c * t.val)) = σ * √(Λ / 3) * c by field_simp,
    sq_deSitterRate hΛ.le hσ]
  ring

/-- The de Sitter scale factor solves the second-order Friedmann equation with `ρ = 0`,
  `p = 0` and `Λ > 0`. -/
lemma deSitterScaleFactor_secondOrderFriedmann {a₀ σ Λ G c : ℝ} (hΛ : 0 < Λ)
    (ha₀ : a₀ ≠ 0) (hσ : σ = 1 ∨ σ = -1) (t : Time) :
    SecondOrderFriedmann (deSitterScaleFactor a₀ σ Λ c) (fun _ => 0) (fun _ => 0) Λ G c t := by
  unfold SecondOrderFriedmann
  rw [deriv_deriv_deSitterScaleFactor]
  simp only [deSitterScaleFactor]
  have he := Real.exp_ne_zero (σ * √(Λ / 3) * c * t.val)
  rw [show a₀ * (σ * √(Λ / 3) * c) * (σ * √(Λ / 3) * c) *
      Real.exp (σ * √(Λ / 3) * c * t.val) / (a₀ * Real.exp (σ * √(Λ / 3) * c * t.val))
      = (σ * √(Λ / 3) * c) ^ 2 by field_simp,
    sq_deSitterRate hΛ.le hσ]
  ring

/-!

## C. The Hubble and deceleration parameters

-/

/-- The Hubble parameter of the de Sitter solution is the constant `σ √(Λ/3) c`. -/
lemma hubbleConstant_deSitterScaleFactor {a₀ σ Λ c : ℝ} (ha₀ : a₀ ≠ 0) (t : Time) :
    hubbleConstant (deSitterScaleFactor a₀ σ Λ c) t = σ * √(Λ / 3) * c := by
  unfold hubbleConstant
  rw [deriv_deSitterScaleFactor]
  simp only [deSitterScaleFactor]
  have he := Real.exp_ne_zero (σ * √(Λ / 3) * c * t.val)
  field_simp

/-- The deceleration parameter of the de Sitter solution is `q = -1`. -/
lemma decelerationParameter_deSitterScaleFactor {a₀ σ Λ c : ℝ} (hΛ : 0 < Λ) (hc : 0 < c)
    (ha₀ : a₀ ≠ 0) (hσ : σ = 1 ∨ σ = -1) (t : Time) :
    decelerationParameter (deSitterScaleFactor a₀ σ Λ c) t = -1 := by
  unfold decelerationParameter
  rw [deriv_deriv_deSitterScaleFactor, deriv_deSitterScaleFactor]
  simp only [deSitterScaleFactor]
  have he := Real.exp_ne_zero (σ * √(Λ / 3) * c * t.val)
  have hK : σ * √(Λ / 3) * c ≠ 0 := by
    have hs : 0 < √(Λ / 3) := Real.sqrt_pos.mpr (by linarith)
    rcases hσ with rfl | rfl
    · positivity
    · have : 0 < √(Λ / 3) * c := mul_pos hs hc
      linarith
  have hσ0 : σ ≠ 0 := by
    rcases hσ with rfl | rfl <;> norm_num
  field_simp

/-!

## D. The de Sitter model

-/

/-- The de Sitter model, defined at all times: the FLRW model with the scale factor
  `deSitterScaleFactor a₀ σ Λ c`, `a₀ > 0`, and the flat spatial geometry. -/
noncomputable def _root_.Cosmology.FLRW.deSitter (a₀ σ Λ c : ℝ) (ha₀ : 0 < a₀) : FLRW where
  I := Set.univ
  isOpen_I := isOpen_univ
  ordConnected_I := Set.ordConnected_univ
  a := deSitterScaleFactor a₀ σ Λ c
  a_pos _ _ := mul_pos ha₀ (Real.exp_pos _)
  differentiableOn_a := by
    unfold deSitterScaleFactor
    fun_prop
  differentiableOn_deriv_a := by
    rw [deriv_deSitterScaleFactor]
    fun_prop
  geometry := .Flat

/-- The de Sitter model filled with the empty cosmic fluid solves the Friedmann equations with
  cosmological constant `Λ > 0`, for `σ = ±1`. -/
lemma _root_.Cosmology.FLRW.friedmannSolution_deSitter {a₀ σ Λ : ℝ} (G c : ℝ) (hΛ : 0 < Λ)
    (ha₀ : 0 < a₀) (hσ : σ = 1 ∨ σ = -1) :
    (FLRW.deSitter a₀ σ Λ c ha₀).FriedmannSolution CosmicFluid.empty Λ G c :=
  ⟨fun t _ => deSitterScaleFactor_firstOrderFriedmann hΛ ha₀.ne' hσ t,
    fun t _ => deSitterScaleFactor_secondOrderFriedmann hΛ ha₀.ne' hσ t⟩

/-!

## E. The de Sitter model is defined at all times

-/

/-- The de Sitter model, which solves the Friedmann equations with `0 < Λ`
  (`FLRW.friedmannSolution_deSitter`), is defined at all times: its interval is not bounded
  below. -/
lemma _root_.Cosmology.FLRW.not_bddBelow_deSitter_I (a₀ σ Λ c : ℝ) (ha₀ : 0 < a₀) :
    ¬ BddBelow (FLRW.deSitter a₀ σ Λ c ha₀).I := by
  rintro ⟨b, hb⟩
  have h1 := (Time.le_def _ _).mp
    (hb (show (⟨b.val - 1⟩ : Time) ∈ (FLRW.deSitter a₀ σ Λ c ha₀).I from Set.mem_univ _))
  dsimp only at h1
  linarith

end Cosmology.FLRW.FriedmannEquation
