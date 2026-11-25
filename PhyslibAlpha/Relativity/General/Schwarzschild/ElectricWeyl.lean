/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.Metrics.Minkowski
public import PhyslibAlpha.Relativity.Tensors.RicciTensor
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
- `tidalPart_eq_electricPart` : Hessian of `Φ = -M/r` matches `electricPart (M/r³)`.

## iii. Table of contents

- A. The electric Weyl tensor and frame curvature
- B. Ricci flatness, Kretschmann scalar, and purely electric property
- C. Tidal Hessian of the static potential

## iv. References

* R. M. Wald, *General Relativity* (1984). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973). [ref: mtw_1973_gravitation]

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

/-- Symmetry of the electric Weyl matrix `diag(0, -2k, k, k)` for any tidal scale parameter
`k`. -/
lemma electricPart_symm (k : ℝ) (i j : Fin 4) :
    electricPart k i j = electricPart k j i := by
  fin_cases i <;> fin_cases j <;> simp [electricPart]

/-- The electric Weyl matrix `diag(0, -2k, k, k)` is trace-free for every tidal scale `k`. -/
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
    rw [electricPart_symm k m j, electricPart_symm k m i,
      electricPart_symm k l j, electricPart_symm k l i]
    simp only [eq_comm (a := l) (b := i), eq_comm (a := l) (b := j),
      eq_comm (a := m) (b := i), eq_comm (a := m) (b := j)]
    ring
  bianchi := by
    intro i j l m
    rw [electricPart_symm k l j, electricPart_symm k l m,
      electricPart_symm k m j]
    simp only [eq_comm (a := l) (b := j), eq_comm (a := m) (b := j),
      eq_comm (a := m) (b := l)]
    ring

/-!

## B. Ricci flatness, Kretschmann scalar, and purely electric property

-/

/-- Schwarzschild frame curvature is Ricci flat for every mass-curvature parameter `k`. -/
lemma ricci_eq_zero (k : ℝ) : ricci minkowski (schwarzschild k) = 0 := by
  ext i j
  rw [ricci_of_diag minkowski (schwarzschild k) (fun _ _ h => minkowski_ginv_offdiag h) i j]
  fin_cases i <;> fin_cases j
  all_goals simp [minkowski, schwarzschild, electricPart, Fin.sum_univ_four,
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

end Schwarzschild

end GeneralRelativity
