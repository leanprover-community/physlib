/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.General.Linearized.LorenzGauge
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!

# Weak-field Newtonian limit

Isotropic Newtonian perturbation `h_{ij} = -2 Φ δ_{ij}` and equivalence between the linearized
Einstein equation `G^{(1)}_{00} = 8 π ρ` and Poisson's equation `∇² Φ = 4 π ρ`.

## i. Overview

For a static Newtonian gravitational potential `Φ` (`∂_0 Φ = 0`), the weak-field
`MetricPerturbation` `newtonianPerturbation Φ` has components `-2 Φ δ_{ij}` (corresponding to
`ds² = -(1 + 2 Φ) dt² + (1 - 2 Φ) d𝐱²`). It satisfies the Lorenz gauge condition identically and
has trace-reversed perturbation supported purely in the `(0, 0)` component (`h̄_{00} = -4 Φ`).
Consequently, `linearizedEinstein (newtonianPerturbation Φ) x 0 0 = 2 ∇² Φ`, bridging linearized
general relativity directly to Newtonian gravity (`∇² Φ = 4 π ρ`).

## ii. Key results

- `newtonianPerturbation`, `traceReversed_newtonianPerturbation` : weak-field Newtonian metric
  perturbation and its trace reversal.
- `newtonianPerturbation_lorenz_gauge` : static Newtonian potentials satisfy Lorenz gauge.
- `newtonianPerturbation_linearizedEinstein_00`, `newtonianPerturbation_poisson_iff` : Newtonian
  Poisson limit `G^{(1)}_{00} = 8 π ρ ↔ ∇² Φ = 4 π ρ`.

## iii. Table of contents

- A. Weak-field Newtonian perturbation and Poisson limit

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 4 (Sec. 4.4). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 18.
  [ref: mtw_1973_gravitation]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 6
  (https://arxiv.org/pdf/gr-qc/9712019#page=144). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

namespace Linearized

open CoordinateCurvature

/-!

## A. Weak-field Newtonian perturbation and Poisson limit

For a static non-relativistic source generating the weak-field metric `diag(-(1+2Φ), 1-2Φ, ...)`,
the Lorenz gauge holds automatically and the time–time Einstein equation reduces to `2 ∇² Φ`.

-/

/-- Weak-field isotropic Newtonian metric perturbation `h_{ij} = -2 Φ δ_{ij}` corresponding to
`ds² = -(1 + 2 Φ) dt² + (1 - 2 Φ) d𝐱²` in `(-, +, +, +)` signature. -/
noncomputable def newtonianPerturbation (Φ : (Fin 4 → ℝ) → ℝ) : MetricPerturbation where
  h x i j := if i = j then -(2 * Φ x) else 0
  symm _ := Matrix.IsSymm.ext fun i j => by fin_cases i <;> fin_cases j <;> simp

/-- Trace reversal isolates the `(0, 0)` component: `h̄_{00} = -4 Φ`, all other entries `0`. -/
lemma traceReversed_newtonianPerturbation (Φ : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) (i j : Fin 4) :
    (newtonianPerturbation Φ).traceReversed.h x i j =
      if i = 0 ∧ j = 0 then -(4 * Φ x) else 0 := by
  have hT : perturbationTrace ((newtonianPerturbation Φ).h x) = -(4 * Φ x) := by
    simp [perturbationTrace, metricTrace, minkowski, newtonianPerturbation, Fin.sum_univ_four]
    ring
  simp only [MetricPerturbation.traceReversed, traceReversed, Matrix.of_apply, hT]
  fin_cases i <;> fin_cases j <;> simp [newtonianPerturbation] <;> ring

/-- Static Newtonian potentials (`∂_0 Φ = 0`) satisfy the Lorenz gauge identically. -/
lemma newtonianPerturbation_lorenz_gauge (Φ : (Fin 4 → ℝ) → ℝ) (y : Fin 4 → ℝ)
    (hstat : coordDeriv 0 Φ y = 0) (j : Fin 4) :
    IsLorenzGauge (newtonianPerturbation Φ) y j := by
  simp only [IsLorenzGauge, lorenzDivergence, Fin.sum_univ_four,
    traceReversed_newtonianPerturbation, minkowskiMetric4_apply]
  fin_cases j <;> norm_num
  · simp only [coordDeriv_const]
    have hneg : (fun z => -(4 * Φ z)) = fun z => (-4 : ℝ) * Φ z := funext fun _ => by ring
    rw [hneg, coordDeriv_const_mul, hstat]
    ring
  all_goals simp [coordDeriv_const]

/-- Weak-field Newtonian limit: for a static `C²` potential `Φ`, the `(0, 0)` linearized Einstein
tensor equals `2 ∇² Φ`, so `G^{(1)}_{00} = 8 π ρ ↔ ∇² Φ = 4 π ρ`. -/
lemma newtonianPerturbation_linearizedEinstein_00 (Φ : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ)
    (hΦ : ContDiffAt ℝ 2 Φ x) (hstat : ∀ y, coordDeriv 0 Φ y = 0) :
    linearizedEinstein (newtonianPerturbation Φ) x 0 0 = 2 * laplacian3 Φ x := by
  have hc : (newtonianPerturbation Φ).IsC2At x := fun a b => by
    fin_cases a <;> fin_cases b <;> simp only [newtonianPerturbation, ↓reduceIte]
    all_goals first | exact contDiffAt_const | exact (contDiffAt_const.mul hΦ).neg
  have hlz : ∀ᶠ y in nhds x, ∀ k, IsLorenzGauge (newtonianPerturbation Φ) y k :=
    Filter.Eventually.of_forall fun y k => newtonianPerturbation_lorenz_gauge Φ y (hstat y) k
  rw [linearizedEinstein_lorenz_gauge (newtonianPerturbation Φ) x hc hlz 0 0]
  have htr : (fun y => (newtonianPerturbation Φ).traceReversed.h y 0 0)
      = fun y => (-4 : ℝ) * Φ y := by
    funext y; simp only [traceReversed_newtonianPerturbation, and_self, ↓reduceIte]; ring
  rw [htr, minkowskiDalembertian_const_mul, minkowskiDalembertian_eq_laplacian3_of_static Φ x hstat]
  ring

/-- Equivalence between `G^{(1)}_{00} = 8 π ρ` and the Newtonian Poisson equation
`∇² Φ = 4 π ρ`. -/
lemma newtonianPerturbation_poisson_iff (Φ : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ)
    (hΦ : ContDiffAt ℝ 2 Φ x) (hstat : ∀ y, coordDeriv 0 Φ y = 0) (ρ : ℝ) :
    linearizedEinstein (newtonianPerturbation Φ) x 0 0 = 8 * Real.pi * ρ
      ↔ laplacian3 Φ x = 4 * Real.pi * ρ := by
  rw [newtonianPerturbation_linearizedEinstein_00 Φ x hΦ hstat]
  constructor <;> intro h <;> linarith

end Linearized

end GeneralRelativity
