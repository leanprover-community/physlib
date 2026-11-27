/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.General.Kerr.MetricDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

/-!

# Boyer–Lindquist Kerr Christoffel symbols

All 20 independent Christoffel connection coefficients `KerrSpacetime.christoffel`, their
agreement with `Pipeline.christoffel`, and the contracted trace `KerrSpacetime.christoffelTrace`.

## i. Overview

Using the coordinate partial derivatives `KerrSpacetime.metricCoordDeriv` from `Kerr.MetricDeriv`,
this module defines the analytical closed-form Christoffel symbol table `KerrSpacetime.christoffel`
(20 non-zero symmetric components) and its contracted trace `KerrSpacetime.christoffelTrace`
(`tr_r = 2 r / Σ`, `tr_θ = cot θ - 2 a² cos θ sin θ / Σ`), and establishes that
`Pipeline.christoffel K.metric K.metricInv` equals `K.christoffel` everywhere on regular
coordinates (`Σ ≠ 0`, `Δ ≠ 0`, `sin θ ≠ 0`) and on a neighborhood thereof.

## ii. Key results

- `KerrSpacetime.christoffel`, `KerrSpacetime.christoffel_symm` : explicit Christoffel symbols of
  Boyer–Lindquist Kerr spacetime and lower-index symmetry.
- `KerrSpacetime.christoffel_eq`, `KerrSpacetime.eventually_christoffel_eq` : agreement with
  `Pipeline.christoffel`.
- `KerrSpacetime.christoffelTrace`, `KerrSpacetime.sum_christoffel_trace` : contracted Christoffel
  trace `∑ ρ, Γ^ρ_{ρ μ}`.

## iii. Table of contents

- A. Explicit Boyer–Lindquist Christoffel symbols
- B. Agreement with the Levi-Civita formula and trace identity

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 12 (Sec. 12.3). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 33.
  [ref: mtw_1973_gravitation]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 7
  (https://arxiv.org/pdf/gr-qc/9712019#page=187). [ref: Carroll1997]
* S. Chandrasekhar, *The Mathematical Theory of Black Holes* (1983), Ch. 6. [ref: Chandrasekhar1983]
-/

@[expose] public section

namespace GeneralRelativity

namespace Kerr

open Pipeline

namespace KerrSpacetime

/-!

## A. Explicit Boyer–Lindquist Christoffel symbols

The Levi-Civita connection coefficients of a stationary axisymmetric black hole split cleanly into
non-vanishing symmetric pairs `(k, i, j)` determined by the metric polynomials `Σ` and `Δ`.

-/

/-- Closed-form Levi-Civita Christoffel symbols `Γ^k_{ij}` of the Boyer–Lindquist Kerr metric. -/
noncomputable def christoffel (K : KerrSpacetime) (x : Fin 4 → ℝ) (k i j : Fin 4) : ℝ :=
  let r := x 1
  let c := Real.cos (x 2)
  let s := Real.sin (x 2)
  let sig := K.sigma r (x 2)
  let del := K.delta r
  if k = 0 then
    if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then
      K.M * (K.a ^ 2 + r ^ 2) * (r ^ 2 - K.a ^ 2 * c ^ 2) / (sig ^ 2 * del)
    else if (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) then
      -2 * K.M * K.a ^ 2 * c * r * s / sig ^ 2
    else if (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) then
      -K.M * K.a * s ^ 2
          * (-K.a ^ 4 * c ^ 2 + K.a ^ 2 * c ^ 2 * r ^ 2 + K.a ^ 2 * r ^ 2 + 3 * r ^ 4)
        / (sig ^ 2 * del)
    else if (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) then
      2 * K.M * K.a ^ 3 * c * r * s ^ 3 / sig ^ 2
    else 0
  else if k = 1 then
    if i = 0 ∧ j = 0 then K.M * (r ^ 2 - K.a ^ 2 * c ^ 2) * del / sig ^ 3
    else if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then
      -K.M * K.a * s ^ 2 * (r ^ 2 - K.a ^ 2 * c ^ 2) * del / sig ^ 3
    else if i = 1 ∧ j = 1 then
      -(-K.M * K.a ^ 2 * c ^ 2 + K.M * r ^ 2 + K.a ^ 2 * c ^ 2 * r - K.a ^ 2 * r) / (sig * del)
    else if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then -K.a ^ 2 * c * s / sig
    else if i = 2 ∧ j = 2 then -r * del / sig
    else if i = 3 ∧ j = 3 then
      -s ^ 2 * del * (-K.M * K.a ^ 4 * c ^ 4 + K.M * K.a ^ 4 * c ^ 2
        + K.M * K.a ^ 2 * c ^ 2 * r ^ 2 - K.M * K.a ^ 2 * r ^ 2 + K.a ^ 4 * c ^ 4 * r
        + 2 * K.a ^ 2 * c ^ 2 * r ^ 3 + r ^ 5) / sig ^ 3
    else 0
  else if k = 2 then
    if i = 0 ∧ j = 0 then -2 * K.M * K.a ^ 2 * c * r * s / sig ^ 3
    else if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then
      2 * K.M * K.a * c * r * s * (K.a ^ 2 + r ^ 2) / sig ^ 3
    else if i = 1 ∧ j = 1 then K.a ^ 2 * c * s / (sig * del)
    else if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then r / sig
    else if i = 2 ∧ j = 2 then -K.a ^ 2 * c * s / sig
    else if i = 3 ∧ j = 3 then
      -c * s * (-2 * K.M * K.a ^ 4 * c ^ 4 * r + 2 * K.M * K.a ^ 4 * r
        - 4 * K.M * K.a ^ 2 * c ^ 2 * r ^ 3 + 4 * K.M * K.a ^ 2 * r ^ 3 + K.a ^ 6 * c ^ 4
        + K.a ^ 4 * c ^ 4 * r ^ 2 + 2 * K.a ^ 4 * c ^ 2 * r ^ 2 + 2 * K.a ^ 2 * c ^ 2 * r ^ 4
        + K.a ^ 2 * r ^ 4 + r ^ 6) / sig ^ 3
    else 0
  else
    if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then
      K.M * K.a * (r ^ 2 - K.a ^ 2 * c ^ 2) / (sig ^ 2 * del)
    else if (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) then -2 * K.M * K.a * c * r / (s * sig ^ 2)
    else if (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) then
      (-K.M * K.a ^ 4 * c ^ 4 + K.M * K.a ^ 4 * c ^ 2 - K.M * K.a ^ 2 * c ^ 2 * r ^ 2
        - K.M * K.a ^ 2 * r ^ 2 - 2 * K.M * r ^ 4 + K.a ^ 4 * c ^ 4 * r
        + 2 * K.a ^ 2 * c ^ 2 * r ^ 3 + r ^ 5) / (sig ^ 2 * del)
    else if (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) then
      c * (-2 * K.M * K.a ^ 2 * c ^ 2 * r + 2 * K.M * K.a ^ 2 * r + K.a ^ 4 * c ^ 4
        + 2 * K.a ^ 2 * c ^ 2 * r ^ 2 + r ^ 4) / (s * sig ^ 2)
    else 0

/-- Lower-index symmetry of `K.christoffel`. -/
lemma christoffel_symm (K : KerrSpacetime) (x : Fin 4 → ℝ) (k i j : Fin 4) :
    K.christoffel x k i j = K.christoffel x k j i := by
  simp only [christoffel]
  have hpair : ∀ a b : Fin 4,
      ((j = a ∧ i = b) ∨ (j = b ∧ i = a)) ↔ ((i = a ∧ j = b) ∨ (i = b ∧ j = a)) := by
    intro a b; tauto
  have hdiag : ∀ a : Fin 4, (j = a ∧ i = a) ↔ (i = a ∧ j = a) := fun a => and_comm
  simp only [hpair, hdiag]

/-- `K.christoffel` does not depend on the `t` (`μ = 0`) or `φ` (`μ = 3`) coordinates. -/
lemma pd_christoffel_const_03 (K : KerrSpacetime) (x : Fin 4 → ℝ) (μ : Fin 4) (hμ : μ = 0 ∨ μ = 3)
    (k i j : Fin 4) : coordDeriv μ (fun y => K.christoffel y k i j) x = 0 := by
  rcases hμ with rfl | rfl
  · exact coordDeriv_const_slice 0 (K.christoffel x k i j)
      (fun _ => by simp [christoffel, sigma, delta])
  · exact coordDeriv_const_slice 3 (K.christoffel x k i j)
      (fun _ => by simp [christoffel, sigma, delta])

/-!

## B. Agreement with the Levi-Civita formula and trace identity

Evaluating `Pipeline.christoffel` confirms the 20 closed-form Christoffel symbols across all 64
components and yields the logarithmic divergence formula `∑ ρ, Γ^ρ_{ρ μ} = ∂_μ ln(Σ sin θ)`.

-/

private lemma christoffel_0 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) (hdel : K.delta (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0)
    (i j : Fin 4) :
    Pipeline.christoffel K.metric K.metricInv x 0 i j = K.christoffel x 0 i j := by
  have hs2 : Real.sin (x 2) ^ 2 = 1 - Real.cos (x 2) ^ 2 := Real.sin_sq (x 2)
  simp only [Pipeline.christoffel, Fin.sum_univ_four, K.pd_metric_eq _ x hsig hdel]
  fin_cases i <;> fin_cases j <;>
    simp only [metricInv, metricCoordDeriv, christoffel, Matrix.of_apply] <;> norm_num
  all_goals
    field_simp [hsig, hdel, hs]
    simp -failIfUnchanged only [sigma, delta, axialFactor, hs2]
    ring

private lemma christoffel_1 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) (hdel : K.delta (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0)
    (i j : Fin 4) :
    Pipeline.christoffel K.metric K.metricInv x 1 i j = K.christoffel x 1 i j := by
  have hs2 : Real.sin (x 2) ^ 2 = 1 - Real.cos (x 2) ^ 2 := Real.sin_sq (x 2)
  simp only [Pipeline.christoffel, Fin.sum_univ_four, K.pd_metric_eq _ x hsig hdel]
  fin_cases i <;> fin_cases j <;>
    simp only [metricInv, metricCoordDeriv, christoffel, Matrix.of_apply] <;> norm_num
  all_goals field_simp [hsig, hdel, hs]
  all_goals simp -failIfUnchanged only [sigma, delta, axialFactor, hs2]
  all_goals ring

private lemma christoffel_2 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) (hdel : K.delta (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0)
    (i j : Fin 4) :
    Pipeline.christoffel K.metric K.metricInv x 2 i j = K.christoffel x 2 i j := by
  have hs2 : Real.sin (x 2) ^ 2 = 1 - Real.cos (x 2) ^ 2 := Real.sin_sq (x 2)
  simp only [Pipeline.christoffel, Fin.sum_univ_four, K.pd_metric_eq _ x hsig hdel]
  fin_cases i <;> fin_cases j <;>
    simp only [metricInv, metricCoordDeriv, christoffel, Matrix.of_apply] <;> norm_num
  all_goals field_simp [hsig, hdel, hs]
  all_goals simp -failIfUnchanged only [sigma, delta, axialFactor, hs2]
  all_goals ring

private lemma christoffel_3 (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) (hdel : K.delta (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0)
    (i j : Fin 4) :
    Pipeline.christoffel K.metric K.metricInv x 3 i j = K.christoffel x 3 i j := by
  have hs2 : Real.sin (x 2) ^ 2 = 1 - Real.cos (x 2) ^ 2 := Real.sin_sq (x 2)
  simp only [Pipeline.christoffel, Fin.sum_univ_four, K.pd_metric_eq _ x hsig hdel]
  fin_cases i <;> fin_cases j <;>
    simp only [metricInv, metricCoordDeriv, christoffel, Matrix.of_apply] <;> norm_num
  all_goals
    field_simp [hsig, hdel, hs]
    simp -failIfUnchanged only [sigma, delta, axialFactor, hs2]
    ring

/-- Every Christoffel symbol computed from the coordinate metric agrees with `K.christoffel` at
every regular coordinate point (`Σ ≠ 0`, `Δ ≠ 0`, `sin θ ≠ 0`). -/
lemma christoffel_eq (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) (hdel : K.delta (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0)
    (k i j : Fin 4) :
    Pipeline.christoffel K.metric K.metricInv x k i j = K.christoffel x k i j := by
  fin_cases k
  · exact christoffel_0 K x hsig hdel hs i j
  · exact christoffel_1 K x hsig hdel hs i j
  · exact christoffel_2 K x hsig hdel hs i j
  · exact christoffel_3 K x hsig hdel hs i j

/-- Continuity-neighborhood equality between `Pipeline.christoffel` and `K.christoffel`. -/
lemma eventually_christoffel_eq (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) (hdel : K.delta (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0)
    (k i j : Fin 4) :
    (fun y => Pipeline.christoffel K.metric K.metricInv y k i j)
      =ᶠ[nhds x] fun y => K.christoffel y k i j := by
  have hcSig : Continuous (fun y : Fin 4 → ℝ => K.sigma (y 1) (y 2)) := by
    simp only [sigma]; fun_prop
  have hcDel : Continuous (fun y : Fin 4 → ℝ => K.delta (y 1)) := by
    simp only [delta]; fun_prop
  have hcS : Continuous (fun y : Fin 4 → ℝ => Real.sin (y 2)) := by fun_prop
  have hmem := (hcSig.continuousAt.eventually_ne hsig).and
    ((hcDel.continuousAt.eventually_ne hdel).and (hcS.continuousAt.eventually_ne hs))
  filter_upwards [hmem] with y ⟨hySig, hyDel, hyS⟩
  exact K.christoffel_eq y hySig hyDel hyS k i j

/-- Contracted Boyer–Lindquist Kerr Christoffel trace `∑ ρ, Γ^ρ_{ρ μ} = ∂_μ ln(Σ sin θ)`. -/
noncomputable def christoffelTrace (K : KerrSpacetime) (x : Fin 4 → ℝ) (μ : Fin 4) : ℝ :=
  if μ = 1 then 2 * x 1 / K.sigma (x 1) (x 2)
  else if μ = 2 then
    Real.cos (x 2) / Real.sin (x 2)
      - 2 * K.a ^ 2 * Real.cos (x 2) * Real.sin (x 2) / K.sigma (x 1) (x 2)
  else 0

/-- Exact contraction identity `∑ ρ, K.christoffel x ρ ρ μ = K.christoffelTrace x μ`. -/
lemma sum_christoffel_trace (K : KerrSpacetime) (x : Fin 4 → ℝ)
    (hsig : K.sigma (x 1) (x 2) ≠ 0) (hdel : K.delta (x 1) ≠ 0) (hs : Real.sin (x 2) ≠ 0)
    (μ : Fin 4) :
    (∑ ρ : Fin 4, K.christoffel x ρ ρ μ) = K.christoffelTrace x μ := by
  have hs2 : Real.sin (x 2) ^ 2 = 1 - Real.cos (x 2) ^ 2 := Real.sin_sq (x 2)
  fin_cases μ
  · simp [Fin.sum_univ_four, christoffel, christoffelTrace]
  · simp only [Fin.sum_univ_four, christoffel, christoffelTrace]
    norm_num
    field_simp [hsig, hdel]
    simp only [sigma, delta]
    ring
  · simp only [Fin.sum_univ_four, christoffel, christoffelTrace]
    norm_num
    field_simp [hsig, hs]
    simp only [sigma]
    rw [hs2]
    ring
  · simp [Fin.sum_univ_four, christoffel, christoffelTrace]

end KerrSpacetime

end Kerr

end GeneralRelativity
