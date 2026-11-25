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

For a static Newtonian gravitational potential `Φ` (`∂_0 Φ = 0`), the weak-field metric
perturbation `newtonianPerturb Φ = -2 Φ δ_{ij}` (corresponding to
`ds² = -(1 + 2 Φ) dt² + (1 - 2 Φ) d𝐱²`) satisfies the Lorenz gauge condition identically and has
trace-reversed perturbation supported purely in the `(0, 0)` component (`h̄_{00} = -4 Φ`).
Consequently, `linEinstein (newtonianPerturb Φ) x 0 0 = 2 ∇² Φ`, bridging linearized general
relativity directly to Newtonian gravity (`∇² Φ = 4 π ρ`).

## ii. Key results

- `newtonianPerturb`, `newtonianPerturb_symm`, `traceReversed_newtonianPerturb` : weak-field
  Newtonian metric perturbation and its trace reversal.
- `newtonianPerturb_lorenz_gauge` : static Newtonian potentials satisfy Lorenz gauge.
- `laplacian3`, `newtonianPerturb_linEinstein_00`, `newtonianPerturb_poisson_iff` : Newtonian
  Poisson limit `G^{(1)}_{00} = 8 π ρ ↔ ∇² Φ = 4 π ρ`.

## iii. Table of contents

- A. Weak-field Newtonian perturbation and Poisson limit

## iv. References

* R. M. Wald, *General Relativity* (1984). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973). [ref: mtw_1973_gravitation]

-/

@[expose] public section

namespace GeneralRelativity

namespace Linearized

open Pipeline

/-!

## A. Weak-field Newtonian perturbation and Poisson limit

-/

/-- Weak-field isotropic Newtonian metric perturbation `h_{ij} = -2 Φ δ_{ij}` corresponding to
`ds² = -(1 + 2 Φ) dt² + (1 - 2 Φ) d𝐱²` in `(-, +, +, +)` signature. -/
noncomputable def newtonianPerturb (Φ : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) : Tensor2 4 :=
  fun i j => if i = j then -(2 * Φ x) else 0

/-- Symmetry of `newtonianPerturb`. -/
lemma newtonianPerturb_symm (Φ : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) :
    IsSymm (newtonianPerturb Φ x) := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [newtonianPerturb]

/-- Trace reversal isolates the `(0, 0)` component: `h̄_{00} = -4 Φ`, all other entries `0`. -/
lemma traceReversed_newtonianPerturb (Φ : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) (i j : Fin 4) :
    traceReversed (newtonianPerturb Φ x) i j = if i = 0 ∧ j = 0 then -(4 * Φ x) else 0 := by
  have hT : hTrace (newtonianPerturb Φ x) = -(4 * Φ x) := by
    simp [hTrace, newtonianPerturb, Fin.sum_univ_four]; ring
  fin_cases i <;> fin_cases j <;> simp [traceReversed, hT, newtonianPerturb] <;> ring

/-- Static Newtonian potentials (`∂_0 Φ = 0`) satisfy the Lorenz gauge identically. -/
lemma newtonianPerturb_lorenz_gauge (Φ : (Fin 4 → ℝ) → ℝ) (y : Fin 4 → ℝ)
    (hstat : pd 0 Φ y = 0) (j : Fin 4) :
    lorenzGaugeCond (newtonianPerturb Φ) y j := by
  simp only [lorenzGaugeCond, lorenzDiv, Fin.sum_univ_four, traceReversed_newtonianPerturb,
    minkowskiMetric4_apply]
  fin_cases j <;> norm_num
  · simp only [pd_const]
    have hneg : (fun z => -(4 * Φ z)) = fun z => (-4 : ℝ) * Φ z := funext fun _ => by ring
    rw [hneg, pd_const_mul, hstat]
    ring
  all_goals simp [pd_const]

/-- Three-dimensional spatial Laplacian `∇² Φ = ∂₁² Φ + ∂₂² Φ + ∂₃² Φ`. -/
noncomputable def laplacian3 (Φ : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) : ℝ :=
  pd 1 (pd 1 Φ) x + pd 2 (pd 2 Φ) x + pd 3 (pd 3 Φ) x

/-- Weak-field Newtonian limit: for a static `C²` potential `Φ`, the `(0, 0)` linearized Einstein
tensor equals `2 ∇² Φ`, so `G^{(1)}_{00} = 8 π ρ ↔ ∇² Φ = 4 π ρ`. -/
lemma newtonianPerturb_linEinstein_00 (Φ : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ)
    (hΦ : ContDiffAt ℝ 2 Φ x) (hstat : ∀ y, pd 0 Φ y = 0) :
    linEinstein (newtonianPerturb Φ) x 0 0 = 2 * laplacian3 Φ x := by
  have hsym : ∀ z a b, newtonianPerturb Φ z a b = newtonianPerturb Φ z b a :=
    newtonianPerturb_symm Φ
  have hc : ∀ a b, ContDiffAt ℝ 2 (fun z => newtonianPerturb Φ z a b) x := fun a b => by
    fin_cases a <;> fin_cases b <;> simp only [newtonianPerturb, ↓reduceIte]
    all_goals first | exact contDiffAt_const | exact (contDiffAt_const.mul hΦ).neg
  have hlz : ∀ᶠ y in nhds x, ∀ k, lorenzGaugeCond (newtonianPerturb Φ) y k :=
    Filter.Eventually.of_forall fun y k => newtonianPerturb_lorenz_gauge Φ y (hstat y) k
  rw [linEinstein_lorenz_gauge (newtonianPerturb Φ) x hsym hc hlz 0 0]
  have htr : (fun y => traceReversed (newtonianPerturb Φ y) 0 0)
      = fun y => (-4 : ℝ) * Φ y := by
    funext y; simp only [traceReversed_newtonianPerturb, and_self, ↓reduceIte]; ring
  have h00 : pd 0 (pd 0 (fun y => (-4 : ℝ) * Φ y)) x = 0 := by
    have hev : pd 0 (fun y => (-4 : ℝ) * Φ y) = fun _ => 0 := funext fun z => by
      rw [pd_const_mul, hstat z, mul_zero]
    rw [hev]; exact pd_const 0 0 x
  have hk : ∀ k : Fin 4, pd k (pd k (fun y => (-4 : ℝ) * Φ y)) x
      = (-4 : ℝ) * pd k (pd k Φ) x := by
    intro k
    have hev : pd k (fun y => (-4 : ℝ) * Φ y) = fun z => (-4 : ℝ) * pd k Φ z :=
      funext fun z => pd_const_mul k (-4) z
    rw [hev, pd_const_mul]
  rw [htr]
  simp only [boxEta, Fin.sum_univ_four, minkowskiMetric4_apply, laplacian3]
  rw [h00, hk 1, hk 2, hk 3]
  norm_num
  ring

/-- Equivalence between `G^{(1)}_{00} = 8 π ρ` and the Newtonian Poisson equation
`∇² Φ = 4 π ρ`. -/
lemma newtonianPerturb_poisson_iff (Φ : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ)
    (hΦ : ContDiffAt ℝ 2 Φ x) (hstat : ∀ y, pd 0 Φ y = 0) (ρ : ℝ) :
    linEinstein (newtonianPerturb Φ) x 0 0 = 8 * Real.pi * ρ
      ↔ laplacian3 Φ x = 4 * Real.pi * ρ := by
  rw [newtonianPerturb_linEinstein_00 Φ x hΦ hstat]
  constructor <;> intro h <;> linarith

end Linearized

end GeneralRelativity
