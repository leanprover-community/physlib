/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import PhyslibAlpha.Relativity.General.Minkowski
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!

# Schwarzschild curvature in the orthonormal frame

The Schwarzschild Weyl tensor, Ricci flatness, Kretschmann scalar, and Newtonian tidal potential
in the orthonormal frame `(t, r, θ, φ)`.

## i. Overview

In the orthonormal frame `(t, r, θ, φ)`, the Schwarzschild curvature is a purely electric Weyl
tensor determined by `E = diag(0, -2k, k, k)` with `k = M / r³`:

`R_{ijlm} = δ_{il} E_{jm} - δ_{im} E_{jl} - δ_{jl} E_{im} + δ_{jm} E_{il}`.

This module builds that tensor as a `RiemannTensor 4`, proves its Ricci flatness against
`minkowski` (via the general Ricci contraction), computes its sum of squares `48 k²` (yielding
the Kretschmann scalar `48 M² / r⁶`), proves it is purely electric, and verifies that the
static Newtonian potential `Φ = -M / r` read off `g_tt = -(1 + 2Φ)` has Hessian eigenvalues
`diag(0, -2M/r³, M/r³, M/r³)`.

## ii. Key results

- `electricPart` : trace-free static Weyl electric matrix `diag(0, -2k, k, k)`.
- `schwarzschild` : the Schwarzschild frame curvature as a `RiemannTensor 4`.
- `ricci_eq_zero` : Schwarzschild frame curvature is Ricci flat for all `k`.
- `frameSqSum_eq`, `kretschmann_scalar` : frame sum of squares `48 k²` and Kretschmann
  invariant `48 M² / r⁶`.
- `weyl_purely_electric` : every component with one temporal index vanishes.
- `tidalPart_eq_electricPart`, `tidal_trace_zero` : Hessian of `Φ = -M/r` matches
  `electricPart (M/r³)` and is harmonic.

## iii. Table of contents

- A. The electric Weyl tensor and frame curvature
- B. Ricci flatness, Kretschmann scalar, and purely electric property
- C. Tidal Hessian of the static potential

## iv. References

* None.

-/

@[expose] public section

namespace GeneralRelativity

namespace Schwarzschild

/-!

## A. The electric Weyl tensor and frame curvature

-/

/-- The electric part of a static Weyl tensor in the orthonormal frame `(t, r, θ, φ)`:
`diag(0, -2k, k, k)`, symmetric and trace free. -/
noncomputable def electricPart (k : ℝ) (i j : Fin 4) : ℝ :=
  if i = j then (if i = 0 then 0 else if i = 1 then -2 * k else k) else 0

/-- `electricPart k` is symmetric. -/
lemma electricPart_symm (k : ℝ) (i j : Fin 4) :
    electricPart k i j = electricPart k j i := by
  fin_cases i <;> fin_cases j <;> simp [electricPart]

/-- `electricPart k` is trace free. -/
lemma electricPart_trace (k : ℝ) : (∑ i, electricPart k i i) = 0 := by
  simp [electricPart, Fin.sum_univ_four]
  ring

/-- Sum of squares of the orthonormal-frame components of a curvature tensor. -/
noncomputable def frameSqSum (R : RiemannTensor 4) : ℝ :=
  ∑ i, ∑ j, ∑ l, ∑ m, R.comp i j l m * R.comp i j l m

/-- The Schwarzschild curvature in the orthonormal frame, with `k = M / r³` at a point: the
static Weyl tensor of electric part `E = diag(0, -2k, k, k)`. -/
noncomputable def schwarzschild (k : ℝ) : RiemannTensor 4 where
  comp := fun i j l m =>
    (if i = l then electricPart k j m else 0)
      - (if i = m then electricPart k j l else 0)
      - (if j = l then electricPart k i m else 0)
      + (if j = m then electricPart k i l else 0)
  skew_last := by
    intro i j l m
    show (if i = l then electricPart k j m else 0)
        - (if i = m then electricPart k j l else 0)
        - (if j = l then electricPart k i m else 0)
        + (if j = m then electricPart k i l else 0)
      = -((if i = m then electricPart k j l else 0)
        - (if i = l then electricPart k j m else 0)
        - (if j = m then electricPart k i l else 0)
        + (if j = l then electricPart k i m else 0))
    ring
  pair_symm := by
    intro i j l m
    fin_cases i <;> fin_cases j <;> fin_cases l <;> fin_cases m
    all_goals simp [electricPart, two_mul, add_assoc]
  bianchi := by
    intro i j l m
    fin_cases i <;> fin_cases j <;> fin_cases l <;> fin_cases m
    all_goals simp [electricPart, two_mul, add_assoc]

/-!

## B. Ricci flatness, Kretschmann scalar, and purely electric property

-/

/-- Schwarzschild frame curvature is Ricci flat for every mass-curvature parameter `k`. -/
lemma ricci_eq_zero (k : ℝ) : ricci minkowski (schwarzschild k) = 0 := by
  ext i j
  rw [ricci_of_diag minkowski (schwarzschild k) (fun _ _ h => minkowski_ginv_offdiag h) i j]
  fin_cases i <;> fin_cases j
  all_goals simp [minkowski, schwarzschild, electricPart, eta4, Fin.sum_univ_four,
    two_mul, add_assoc]

/-- The frame components of `schwarzschild k` satisfy `∑ R_{ijlm}² = 48 k²`. -/
lemma frameSqSum_eq (k : ℝ) : frameSqSum (schwarzschild k) = 48 * k ^ 2 := by
  simp [frameSqSum, schwarzschild, electricPart, Fin.sum_univ_four, two_mul, add_assoc]
  ring

/-- The Schwarzschild Kretschmann scalar `48 M² / r⁶`, obtained at `k = M / r³`. -/
lemma kretschmann_scalar (M r : ℝ) (hr : r ≠ 0) :
    frameSqSum (schwarzschild (M / r ^ 3)) = 48 * M ^ 2 / r ^ 6 := by
  rw [frameSqSum_eq]
  have hr3 : r ^ 3 ≠ 0 := pow_ne_zero 3 hr
  field_simp

/-- The Schwarzschild frame Weyl tensor is purely electric: for spatial `j, l, m`, every
component carrying exactly one temporal index vanishes. -/
lemma weyl_purely_electric (k : ℝ) (j l m : Fin 4) (hj : j ≠ 0) (hl : l ≠ 0)
    (hm : m ≠ 0) :
    (schwarzschild k).comp 0 j l m = 0 ∧ (schwarzschild k).comp j 0 l m = 0 ∧
      (schwarzschild k).comp j l 0 m = 0 ∧ (schwarzschild k).comp j l m 0 = 0 := by
  have h0j : (0 : Fin 4) ≠ j := fun h => hj h.symm
  have h0l : (0 : Fin 4) ≠ l := fun h => hl h.symm
  have h0m : (0 : Fin 4) ≠ m := fun h => hm h.symm
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp_all [schwarzschild, electricPart]

/-!

## C. Tidal Hessian of the static potential

-/

/-- The Schwarzschild metric in `(t, r, θ, φ)` coordinates with signature `(-, +, +, +)`. -/
noncomputable def schwarzschildMetric (M : ℝ) (x : Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ :=
  fun i j =>
    if i = j then
      if i = 0 then -(1 - 2 * M / x 1)
      else if i = 1 then (1 - 2 * M / x 1)⁻¹
      else if i = 2 then x 1 ^ 2
      else x 1 ^ 2 * Real.sin (x 2) ^ 2
    else 0

/-- The `tt` component of the Schwarzschild metric is `-(1 - 2M/r)`. -/
lemma schwarzschildMetric_tt (M : ℝ) (x : Fin 4 → ℝ) :
    schwarzschildMetric M x 0 0 = -(1 - 2 * M / x 1) := by
  simp [schwarzschildMetric]

/-- The static Newtonian potential is `Φ = -M / r`: `g_tt = -(1 + 2Φ)`. -/
lemma schwarzschildMetric_tt_potential (M : ℝ) (x : Fin 4 → ℝ) :
    schwarzschildMetric M x 0 0 = -(1 + 2 * (-M / x 1)) := by
  rw [schwarzschildMetric_tt]
  ring

/-- First radial derivative of the potential: `Φ' = M / r²`. -/
lemma potential_hasDerivAt (M r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun s : ℝ => -M / s) (M / r ^ 2) r := by
  have h : HasDerivAt (fun s : ℝ => s⁻¹) (-(r ^ 2)⁻¹) r := hasDerivAt_inv hr
  have h' := h.const_mul (-M)
  have hfun : (fun s : ℝ => -M / s) = fun s : ℝ => -M * s⁻¹ := by
    funext s
    simp [div_eq_mul_inv]
  have hval : -M * -(r ^ 2)⁻¹ = M / r ^ 2 := by ring
  rw [← hfun, hval] at h'
  exact h'

/-- Second radial derivative of the potential: `Φ'' = -2M / r³`. -/
lemma slope_hasDerivAt (M r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun s : ℝ => M / s ^ 2) (-2 * M / r ^ 3) r := by
  have hnum : HasDerivAt (fun _ : ℝ => M) 0 r := hasDerivAt_const r M
  have hden : HasDerivAt (fun s : ℝ => s ^ 2) (2 * r) r := by
    simpa using hasDerivAt_pow 2 r
  have h := hnum.div hden (pow_ne_zero 2 hr)
  have hfun : (fun s : ℝ => M / s ^ 2) = (fun _ : ℝ => M) / fun s : ℝ => s ^ 2 := rfl
  have hval : (0 * r ^ 2 - M * (2 * r)) / (r ^ 2) ^ 2 = -2 * M / r ^ 3 := by
    have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
    have hr4 : (r ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 hr2
    field_simp
    ring
  rw [← hfun, hval] at h
  exact h

/-- The tidal Hessian of a static radial potential in the orthonormal frame `(t, r, θ, φ)`:
eigenvalues `0`, `Φ''`, `Φ'/r`, `Φ'/r`. -/
noncomputable def tidalPart (phiRR phiOverR : ℝ) (i j : Fin 4) : ℝ :=
  if i = j then (if i = 0 then 0 else if i = 1 then phiRR else phiOverR) else 0

/-- With `Φ = -M / r`, the tidal tensor equals `electricPart (M / r³)`. -/
lemma tidalPart_eq_electricPart (M r : ℝ) :
    tidalPart (-2 * M / r ^ 3) (M / r ^ 3) = electricPart (M / r ^ 3) := by
  funext i j
  fin_cases i <;> fin_cases j
  all_goals first
    | (simp [tidalPart, electricPart]; ring)
    | simp [tidalPart, electricPart]

/-- The exterior potential is harmonic: `Φ'' + 2 Φ' / r = 0`. -/
lemma tidal_trace_zero (M r : ℝ) :
    (-2 * M / r ^ 3) + 2 * (M / r ^ 3) = 0 := by
  ring

end Schwarzschild

end GeneralRelativity
