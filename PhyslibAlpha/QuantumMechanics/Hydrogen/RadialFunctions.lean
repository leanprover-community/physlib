/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.Mathematics.SpecialFunctions.Laguerre
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Physlib.QuantumMechanics.Hydrogen.Rydberg

/-!

# The radial functions of the hydrogen atom

The bound-state radial functions of the three-dimensional hydrogen atom, the radial
Schrödinger equation they solve, and the expectation values `⟨1/r⟩`, `⟨1/r²⟩`, `⟨1/r³⟩` and
`|R(0)|²` that enter the fine structure.

## i. Overview

In units of the Bohr radius, with principal quantum number `ν` and `l < ν`,

`u_{νl}(ρ) = ρ^(l+1) e^(-ρ/ν) L_{ν-l-1}^(2l+1)(2ρ/ν)`.

Writing `u = Q e^(-ρ/ν)` with the polynomial `Q`, the radial equation
`u'' = (l(l+1)/ρ² - 2/ρ + 1/ν²) u` becomes a polynomial identity that follows from the Laguerre
equation at `x = 2ρ/ν` together with `(ν - l - 1) + l + 1 = ν` (`radialU_ode`). In physical units
this is the radial Schrödinger equation with eigenvalue `-Ry/ν²`, which is physlib's Bohr level
`HydrogenAtom.energyLevel (ν - 1)` for `d = 3` (`radialFun_schrodinger`).

The substitution `x = 2ρ/ν` turns the moments `∫ u² ρ^(-k) dρ` into the Laguerre integrals of
`Laguerre.lean`, which gives

- `⟨1/ρ⟩ = 1/ν²`,
- `⟨1/ρ²⟩ = 1/(ν³ (l + 1/2))`,
- `⟨1/ρ³⟩ = 1/(ν³ l (l + 1/2)(l + 1))` for `l ≥ 1`,
- `|R_{ν0}(0)|²/‖u‖² = 4/ν³`.

The functions are not normalised; all expectation values are quotients by `‖u‖²`. The
separation of the three-dimensional Schrödinger equation into spherical harmonics is not part of
this module.

## ii. Key results

- `radialU`, `radialR`: the radial functions `u_{νl}` and `R_{νl} = u_{νl}/ρ`.
- `radialU_ode`: the radial equation in atomic units.
- `radialFun_schrodinger`: the radial Schrödinger equation in physical units.
- `radialMoment_zero`: `‖u_{νl}‖² = (ν/2)^(2l+3) (ν + l)!/(ν - l - 1)! · 2ν`.
- `radialMean_one`, `radialMean_two`, `radialMean_three`: the expectation values.
- `radialR_zero_sq_div`: the density at the origin for `s` states.

## iii. Table of contents

- A. Polynomial times exponential
- B. The radial functions and the radial equation
- C. Radial moments and expectation values
- D. The value at the origin
- E. Physical units

## iv. References

- H. A. Bethe and E. E. Salpeter, *Quantum Mechanics of One- and Two-Electron Atoms*, Springer
  (1957).
- J. J. Sakurai and J. Napolitano, *Modern Quantum Mechanics*, 3rd ed., Cambridge University
  Press (2020), section 3.7.

## A. Polynomial times exponential

-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Hydrogen

open Polynomial MeasureTheory Set

lemma hasDerivAt_eval_mul_exp (Q : ℝ[X]) (β ρ : ℝ) :
    HasDerivAt (fun ρ => Q.eval ρ * Real.exp (-(β * ρ)))
      ((derivative Q - C β * Q).eval ρ * Real.exp (-(β * ρ))) ρ := by
  have h2 : HasDerivAt (fun ρ => Real.exp (-(β * ρ))) (Real.exp (-(β * ρ)) * (-β)) ρ := by
    simpa using ((hasDerivAt_id ρ).const_mul β).neg.exp
  convert (Q.hasDerivAt ρ).mul h2 using 1
  simp only [eval_sub, eval_mul, eval_C]
  ring

lemma deriv_eval_mul_exp (Q : ℝ[X]) (β : ℝ) :
    deriv (fun ρ => Q.eval ρ * Real.exp (-(β * ρ))) =
      fun ρ => (derivative Q - C β * Q).eval ρ * Real.exp (-(β * ρ)) :=
  funext fun ρ => (hasDerivAt_eval_mul_exp Q β ρ).deriv

/-!

## B. The radial functions and the radial equation

-/

variable (ν l : ℕ)

/-- The polynomial `ρ^(l+1) L_{ν-l-1}^(2l+1)(2ρ/ν)`. -/
def radialPoly : ℝ[X] :=
  X ^ (l + 1) * (laguerre (ν - l - 1) (2 * l + 1)).comp (C (2 / (ν : ℝ)) * X)

/-- The reduced radial function `u_{νl}(ρ) = ρ^(l+1) e^(-ρ/ν) L_{ν-l-1}^(2l+1)(2ρ/ν)` of the
hydrogen atom, in units of the Bohr radius and not normalised; `ν` is the principal quantum
number. The radial wave function is `R_{νl}(ρ) = u_{νl}(ρ)/ρ`. -/
def radialU (ρ : ℝ) : ℝ := (radialPoly ν l).eval ρ * Real.exp (-(1 / (ν : ℝ) * ρ))

variable {ν l}

lemma eval_radialPoly (ρ : ℝ) :
    (radialPoly ν l).eval ρ =
      ρ ^ (l + 1) * (laguerre (ν - l - 1) (2 * l + 1)).eval (2 / (ν : ℝ) * ρ) := by
  simp [radialPoly, eval_comp]

lemma eval_derivative_radialPoly (ρ : ℝ) :
    (derivative (radialPoly ν l)).eval ρ =
      ((l : ℝ) + 1) * ρ ^ l * (laguerre (ν - l - 1) (2 * l + 1)).eval (2 / (ν : ℝ) * ρ) +
        2 / (ν : ℝ) * ρ ^ (l + 1) *
          (derivative (laguerre (ν - l - 1) (2 * l + 1))).eval (2 / (ν : ℝ) * ρ) := by
  simp [radialPoly, derivative_mul, derivative_comp, eval_comp]
  ring

lemma eval_derivative_derivative_radialPoly (ρ : ℝ) :
    (derivative (derivative (radialPoly ν l))).eval ρ =
      ((l : ℝ) + 1) * l * ρ ^ (l - 1) *
          (laguerre (ν - l - 1) (2 * l + 1)).eval (2 / (ν : ℝ) * ρ) +
        2 * ((l : ℝ) + 1) * (2 / (ν : ℝ)) * ρ ^ l *
          (derivative (laguerre (ν - l - 1) (2 * l + 1))).eval (2 / (ν : ℝ) * ρ) +
        (2 / (ν : ℝ)) ^ 2 * ρ ^ (l + 1) *
          (derivative (derivative (laguerre (ν - l - 1) (2 * l + 1)))).eval
            (2 / (ν : ℝ) * ρ) := by
  simp [radialPoly, derivative_mul, derivative_comp, eval_comp, derivative_X_pow]
  ring

/-- The polynomial identity behind the radial equation:
`ρ² (Q'' - 2Q'/ν + Q/ν²) = (l(l+1) - 2ρ + ρ²/ν²) Q` for `Q = radialPoly ν l`. -/
lemma radialPoly_identity (hl : l < ν) (ρ : ℝ) :
    ρ ^ 2 * ((derivative (derivative (radialPoly ν l))).eval ρ -
        2 * (1 / (ν : ℝ)) * (derivative (radialPoly ν l)).eval ρ +
          (1 / (ν : ℝ)) ^ 2 * (radialPoly ν l).eval ρ) =
      ((l : ℝ) * (l + 1) - 2 * ρ + (1 / (ν : ℝ)) ^ 2 * ρ ^ 2) * (radialPoly ν l).eval ρ := by
  obtain ⟨N, rfl⟩ : ∃ N, ν = l + 1 + N := ⟨ν - l - 1, by omega⟩
  have hN : l + 1 + N - l - 1 = N := by omega
  rw [eval_derivative_derivative_radialPoly, eval_derivative_radialPoly, eval_radialPoly]
  have hE := laguerre_ode (N := l + 1 + N - l - 1) (α := 2 * l + 1) (2 / ((l + 1 + N : ℕ) : ℝ) * ρ)
  rw [hN] at hE ⊢
  have hν : ((l + 1 + N : ℕ) : ℝ) ≠ 0 := by positivity
  have hβ : 1 / ((l + 1 + N : ℕ) : ℝ) * ((l + 1 + N : ℕ) : ℝ) = 1 := by field_simp
  set b := 1 / ((l + 1 + N : ℕ) : ℝ) with hb
  have hκ : 2 / ((l + 1 + N : ℕ) : ℝ) = 2 * b := by rw [hb]; ring
  rw [hκ] at hE ⊢
  set G := (laguerre N (2 * l + 1)).eval (2 * b * ρ)
  set G1 := (derivative (laguerre N (2 * l + 1))).eval (2 * b * ρ)
  set G2 := (derivative (derivative (laguerre N (2 * l + 1)))).eval (2 * b * ρ)
  push_cast at hE hβ ⊢
  rcases l with _ | l
  · simp only [pow_zero, Nat.cast_zero] at hE hβ ⊢
    linear_combination (2 * b * ρ ^ 2) * hE - 2 * ρ ^ 2 * G * hβ
  · rw [show l + 1 - 1 = l by omega]
    push_cast at hE hβ ⊢
    linear_combination (2 * b * ρ ^ (l + 3)) * hE - 2 * ρ ^ (l + 3) * G * hβ

lemma deriv_deriv_radialU (ρ : ℝ) :
    deriv (deriv (radialU ν l)) ρ =
      ((derivative (derivative (radialPoly ν l))).eval ρ -
        2 * (1 / (ν : ℝ)) * (derivative (radialPoly ν l)).eval ρ +
          (1 / (ν : ℝ)) ^ 2 * (radialPoly ν l).eval ρ) * Real.exp (-(1 / (ν : ℝ) * ρ)) := by
  rw [show radialU ν l = fun ρ => (radialPoly ν l).eval ρ * Real.exp (-(1 / (ν : ℝ) * ρ)) from rfl,
    deriv_eval_mul_exp, deriv_eval_mul_exp]
  simp only [derivative_sub, derivative_mul, derivative_C, zero_mul, zero_add, eval_sub, eval_mul,
    eval_C]
  ring

/-- **The radial Schrödinger equation of hydrogen.** In units of the Bohr radius and the
Rydberg energy, `u_{νl}'' = (l(l+1)/ρ² - 2/ρ + 1/ν²) u_{νl}`, i.e. `u_{νl}` is an eigenfunction
of `-d²/dρ² + l(l+1)/ρ² - 2/ρ` with eigenvalue `-1/ν²`. -/
lemma radialU_ode (hl : l < ν) {ρ : ℝ} (hρ : ρ ≠ 0) :
    deriv (deriv (radialU ν l)) ρ =
      ((l : ℝ) * (l + 1) / ρ ^ 2 - 2 / ρ + 1 / (ν : ℝ) ^ 2) * radialU ν l ρ := by
  have key := radialPoly_identity hl ρ
  have hρ2 : ρ ^ 2 ≠ 0 := pow_ne_zero 2 hρ
  rw [deriv_deriv_radialU, eq_div_of_mul_eq hρ2 ((mul_comm _ _).trans key), radialU]
  field_simp

/-!

## C. Radial moments and expectation values

-/

lemma integral_pow_mul_exp_mul_laguerre_sq_comp (e N α : ℕ) {b : ℝ} (hb : 0 < b) :
    ∫ ρ in Ioi (0 : ℝ), ρ ^ e * Real.exp (-(b * ρ)) * ((laguerre N α).eval (b * ρ)) ^ 2 =
      b⁻¹ * (b⁻¹ ^ e *
        ∫ x in Ioi (0 : ℝ), x ^ e * Real.exp (-x) * ((laguerre N α).eval x) ^ 2) := by
  have h := integral_comp_mul_left_Ioi
    (fun x : ℝ => ((b⁻¹ * x) ^ e * Real.exp (-x) * ((laguerre N α).eval x) ^ 2 : ℝ)) 0 hb
  simp only [mul_zero, inv_mul_cancel_left₀ hb.ne'] at h
  rw [h, smul_eq_mul]
  congr 1
  rw [← integral_const_mul]
  congr 1
  funext x
  simp only [mul_pow]
  ring

lemma radialU_sq_div_pow {k : ℕ} (hk : k ≤ 2 * l + 2) {ρ : ℝ} (hρ : 0 < ρ) :
    radialU ν l ρ ^ 2 / ρ ^ k = ρ ^ (2 * l + 2 - k) * Real.exp (-(2 / (ν : ℝ) * ρ)) *
      ((laguerre (ν - l - 1) (2 * l + 1)).eval (2 / (ν : ℝ) * ρ)) ^ 2 := by
  have hp : ρ ^ (2 * l + 2) = ρ ^ (2 * l + 2 - k) * ρ ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  have he : Real.exp (-(1 / (ν : ℝ) * ρ)) ^ 2 = Real.exp (-(2 / (ν : ℝ) * ρ)) := by
    rw [sq, ← Real.exp_add]
    ring_nf
  rw [div_eq_iff (pow_ne_zero _ hρ.ne'), radialU, eval_radialPoly, mul_pow, mul_pow, ← pow_mul, he,
    show (l + 1) * 2 = 2 * l + 2 by ring, hp]
  ring

/-- The radial moment `∫₀^∞ u_{νl}(ρ)² ρ^(-k) dρ`. For `k = 0` this is the squared norm. -/
def radialMoment (ν l k : ℕ) : ℝ := ∫ ρ in Ioi (0 : ℝ), radialU ν l ρ ^ 2 / ρ ^ k

/-- The expectation value `⟨ρ^(-k)⟩` in the state `u_{νl}`. -/
def radialMean (ν l k : ℕ) : ℝ := radialMoment ν l k / radialMoment ν l 0

lemma radialMoment_eq (hl : l < ν) {k : ℕ} (hk : k ≤ 2 * l + 2) :
    radialMoment ν l k = ((ν : ℝ) / 2) * (((ν : ℝ) / 2) ^ (2 * l + 2 - k) *
      ∫ x in Ioi (0 : ℝ), x ^ (2 * l + 2 - k) * Real.exp (-x) *
        ((laguerre (ν - l - 1) (2 * l + 1)).eval x) ^ 2) := by
  have hν : (0 : ℝ) < 2 / (ν : ℝ) := by
    have : (0 : ℝ) < ν := by exact_mod_cast (show 0 < ν by omega)
    positivity
  rw [radialMoment, setIntegral_congr_fun measurableSet_Ioi (fun ρ hρ => radialU_sq_div_pow hk hρ),
    integral_pow_mul_exp_mul_laguerre_sq_comp _ _ _ hν, inv_div]

/-- The squared norm `∫ u_{νl}² dρ = (ν/2)^(2l+3) (ν+l)!/(ν-l-1)! · 2ν`. -/
lemma radialMoment_zero (hl : l < ν) :
    radialMoment ν l 0 = ((ν : ℝ) / 2) ^ (2 * l + 3) *
      (((ν + l).factorial : ℝ) / (ν - l - 1).factorial * (2 * ν)) := by
  rw [radialMoment_eq hl (by omega), show 2 * l + 2 - 0 = 2 * l + 1 + 1 by omega,
    integral_laguerre_sq_alpha_add_one, show ν - l - 1 + (2 * l + 1) = ν + l by omega]
  obtain ⟨N, rfl⟩ : ∃ N, ν = l + 1 + N := ⟨ν - l - 1, by omega⟩
  rw [show l + 1 + N - l - 1 = N by omega]
  push_cast
  ring

lemma radialMoment_one (hl : l < ν) :
    radialMoment ν l 1 = ((ν : ℝ) / 2) ^ (2 * l + 2) *
      (((ν + l).factorial : ℝ) / (ν - l - 1).factorial) := by
  rw [radialMoment_eq hl (by omega), show 2 * l + 2 - 1 = 2 * l + 1 by omega,
    integral_laguerre_sq_alpha, show ν - l - 1 + (2 * l + 1) = ν + l by omega]
  ring

lemma radialMoment_two (hl : l < ν) :
    radialMoment ν l 2 = ((ν : ℝ) / 2) ^ (2 * l + 1) *
      (((ν + l).factorial : ℝ) / ((ν - l - 1).factorial * (2 * l + 1))) := by
  rw [radialMoment_eq hl (by omega), show 2 * l + 2 - 2 = 2 * l + 1 - 1 by omega,
    integral_laguerre_sq_alpha_sub_one (by omega), show ν - l - 1 + (2 * l + 1) = ν + l by omega,
    show 2 * l + 1 - 1 = 2 * l by omega]
  push_cast
  ring

lemma radialMoment_three (hl : l < ν) (hl1 : 1 ≤ l) :
    radialMoment ν l 3 = ((ν : ℝ) / 2) ^ (2 * l) *
      (((ν + l).factorial : ℝ) * (2 * ν) /
        ((ν - l - 1).factorial * (2 * l * (2 * l + 1) * (2 * l + 2)))) := by
  rw [radialMoment_eq hl (by omega), show 2 * l + 2 - 3 = 2 * l + 1 - 2 by omega,
    integral_laguerre_sq_alpha_sub_two (by omega), show ν - l - 1 + (2 * l + 1) = ν + l by omega,
    show 2 * l + 1 - 2 = 2 * l - 1 by omega]
  obtain ⟨N, rfl⟩ : ∃ N, ν = l + 1 + N := ⟨ν - l - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  rw [show m + 1 + 1 + N - (m + 1) - 1 = N by omega, show 2 * (m + 1) - 1 = 2 * m + 1 by omega]
  push_cast
  ring

/-- `⟨1/ρ⟩ = 1/ν²`, the virial theorem for hydrogen. -/
lemma radialMean_one (hl : l < ν) : radialMean ν l 1 = 1 / (ν : ℝ) ^ 2 := by
  have hν : (ν : ℝ) ≠ 0 := by exact_mod_cast (show ν ≠ 0 by omega)
  rw [radialMean, radialMoment_one hl, radialMoment_zero hl]
  field_simp
  ring

/-- `⟨1/ρ²⟩ = 1/(ν³ (l + 1/2))`. -/
lemma radialMean_two (hl : l < ν) :
    radialMean ν l 2 = 1 / ((ν : ℝ) ^ 3 * (l + 1 / 2)) := by
  have hν : (ν : ℝ) ≠ 0 := by exact_mod_cast (show ν ≠ 0 by omega)
  rw [radialMean, radialMoment_two hl, radialMoment_zero hl]
  field_simp
  ring

/-- `⟨1/ρ³⟩ = 1/(ν³ l (l + 1/2) (l + 1))` for `l ≥ 1`. -/
lemma radialMean_three (hl : l < ν) (hl1 : 1 ≤ l) :
    radialMean ν l 3 = 1 / ((ν : ℝ) ^ 3 * (l * (l + 1 / 2) * (l + 1))) := by
  have hν : (ν : ℝ) ≠ 0 := by exact_mod_cast (show ν ≠ 0 by omega)
  have hl0 : (l : ℝ) ≠ 0 := by exact_mod_cast (show l ≠ 0 by omega)
  rw [radialMean, radialMoment_three hl hl1, radialMoment_zero hl]
  field_simp
  ring

/-!

## D. The value at the origin

-/

/-- The radial wave function `R_{νl}(ρ) = u_{νl}(ρ)/ρ = ρ^l e^(-ρ/ν) L_{ν-l-1}^(2l+1)(2ρ/ν)`. -/
def radialR (ν l : ℕ) (ρ : ℝ) : ℝ :=
  ρ ^ l * Real.exp (-(1 / (ν : ℝ) * ρ)) * (laguerre (ν - l - 1) (2 * l + 1)).eval (2 / (ν : ℝ) * ρ)

lemma radialU_eq_mul_radialR (ρ : ℝ) : radialU ν l ρ = ρ * radialR ν l ρ := by
  rw [radialU, eval_radialPoly, radialR]
  ring

/-- For an `s` state the normalised density at the nucleus is `|R_{ν0}(0)|²/‖u‖² = 4/ν³`. -/
lemma radialR_zero_sq_div (hν : 0 < ν) :
    radialR ν 0 0 ^ 2 / radialMoment ν 0 0 = 4 / (ν : ℝ) ^ 3 := by
  have hν' : (ν : ℝ) ≠ 0 := by exact_mod_cast hν.ne'
  rw [radialMoment_zero hν]
  simp only [radialR, pow_zero, mul_zero, neg_zero, Real.exp_zero, mul_one, one_mul,
    eval_laguerre_zero]
  obtain ⟨N, rfl⟩ : ∃ N, ν = N + 1 := ⟨ν - 1, by omega⟩
  rw [show N + 1 - 0 - 1 = N by omega, show N + (2 * 0 + 1) = N + 1 by omega,
    Nat.choose_succ_self_right, show N + 1 + 0 = N + 1 by omega, Nat.factorial_succ]
  have hN : (N.factorial : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-!

## E. Physical units

-/

open QuantumMechanics Constants

variable {d : ℕ}

/-- The Bohr radius `a = ℏ²/(m k)` of a hydrogen atom. -/
def bohrRadius (H : HydrogenAtom d) : ℝ := (ℏ : ℝ) ^ 2 / (H.m * H.k)

lemma bohrRadius_pos (H : HydrogenAtom d) (hk : 0 < H.k) : 0 < bohrRadius H :=
  div_pos (pow_pos ℏ_pos 2) (mul_pos H.m_pos hk)

/-- The reduced radial function `u_{νl}(r/a)` in physical units. -/
def radialFun (H : HydrogenAtom d) (ν l : ℕ) (r : ℝ) : ℝ := radialU ν l ((bohrRadius H)⁻¹ * r)

/-- **The radial Schrödinger equation of hydrogen in physical units.** For `d = 3` and an
attractive potential, `u_{νl}(r/a)` solves
`-ℏ²/(2m) u'' + (ℏ² l(l+1)/(2m r²) - k/r) u = E u` with `E = -Ry/ν²`, the Bohr level
`H.energyLevel (ν - 1)` of physlib. -/
lemma radialFun_schrodinger (H : HydrogenAtom 3) (hk : 0 < H.k) (hl : l < ν)
    {r : ℝ} (hr : r ≠ 0) :
    -((ℏ : ℝ) ^ 2 / (2 * H.m)) * deriv (deriv (radialFun H ν l)) r +
        ((ℏ : ℝ) ^ 2 * ((l : ℝ) * (l + 1)) / (2 * H.m * r ^ 2) - H.k / r) * radialFun H ν l r =
      H.energyLevel (ν - 1) * radialFun H ν l r := by
  set c := (bohrRadius H)⁻¹ with hc
  have hc0 : c ≠ 0 := inv_ne_zero (bohrRadius_pos H hk).ne'
  have h1 : deriv (radialFun H ν l) = fun r => c * deriv (radialU ν l) (c * r) := by
    funext r
    rw [show radialFun H ν l = (radialU ν l <| c * ·) from rfl, deriv_comp_mul_left, smul_eq_mul]
  have h2 : deriv (deriv (radialFun H ν l)) r = c * (c * deriv (deriv (radialU ν l)) (c * r)) := by
    rw [h1, deriv_const_mul_field, show (fun r => deriv (radialU ν l) (c * r)) =
      (deriv (radialU ν l) <| c * ·) from rfl, deriv_comp_mul_left, smul_eq_mul]
  rw [h2, radialU_ode hl (mul_ne_zero hc0 hr),
    show radialFun H ν l r = radialU ν l (c * r) from rfl,
    HydrogenAtom.energyLevel_eq, HydrogenAtom.levelIndex_eq, HydrogenAtom.rydbergEnergy_eq,
    Nat.cast_sub (show 1 ≤ ν by omega), hc, bohrRadius]
  have hm := H.m_pos.ne'
  have hk0 := hk.ne'
  have hℏ := ℏ_ne_zero
  have hν : (ν : ℝ) ≠ 0 := by exact_mod_cast (show ν ≠ 0 by omega)
  have hνν : (ν : ℝ) ^ 2 * (ν : ℝ)⁻¹ ^ 2 = 1 := by field_simp
  push_cast
  field_simp
  linear_combination
    (H.m ^ 2 * H.k ^ 2 * r ^ 2 * radialU ν l (H.m * H.k * r / (ℏ : ℝ) ^ 2)) * hνν

end PhyslibAlpha.Hydrogen
