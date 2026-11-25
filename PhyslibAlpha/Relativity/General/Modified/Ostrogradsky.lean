/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.Tensors.Tensor2
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!

# The Ostrogradsky instability

Degeneracy of the acceleration Hessian and unboundedness below of the canonical Hamiltonian for
non-degenerate higher-derivative Lagrangians.

## i. Overview

By Ostrogradsky's theorem, a non-degenerate Lagrangian depending on second time derivatives
`L(q, q̇, q̈)` introduces a second canonical pair `(q̇, p₁)` whose momentum `p₁` enters the
canonical Hamiltonian only linearly as `p₁ q̇`. Consequently, for any non-zero velocity `q̇ ≠ 0`,
the Hamiltonian is unbounded below — the Ostrogradsky ghost — explaining why viable modified
gravity theories must either reduce to healthy scalar–tensor theories (`f(R)`) or restrict to
second-order field equations (Horndeski / Galileons).

This module formalises the algebraic core for the model `L = (1/2) q̈² - (1/2) m² q²`,
contrasting it with a standard positive-definite quadratic kinetic term.

## ii. Key results

- `HigherDerivModel` : benchmark higher-derivative harmonic oscillator model with mass `m`.
- `kineticMatrix`, `kineticMatrix_degenerate` : singular Hessian `diag(0, 1)` in `(q̇, q̈)`.
- `hamiltonian`, `hamiltonian_add`, `ostrogradsky_unbounded_below` : linearity in `p₁` and
  unboundedness
  below whenever `v ≠ 0`.
- `kinetic_nonneg`, `kinetic_zero_iff` : positivity and non-degeneracy of a standard first-order
  quadratic kinetic term.

## iii. Table of contents

- A. Degenerate kinetic matrix and Ostrogradsky ghost
- B. Contrast with standard quadratic kinetic terms

## iv. References

* Mikhail Ostrogradsky, *Mémoires sur les équations différentielles, relatives au problème des
  isopérimètres*, *Mémoires de l'Académie Impériale des Sciences de Saint-Pétersbourg* (1850).
  [ref: Ostrogradsky1850]
* Richard P. Woodard, *The Theorem of Ostrogradsky*, *Scholarpedia* (2015)
  (https://arxiv.org/abs/1506.02210). [ref: Woodard2015]
* Alexander Ganz and Karim Noui, *Reconsidering the Ostrogradsky Theorem: Higher-Derivatives
  Lagrangians, Ghosts and Degeneracy*, *Classical and Quantum Gravity* (2021). [ref: GanzNoui2021]
* David Langlois and Karim Noui, *Degenerate Higher Derivative Theories beyond Horndeski: Evading
  the Ostrogradsky Instability*, *Journal of Cosmology and Astroparticle Physics* (2016). [ref:
  LangloisNoui2016]

-/

@[expose] public section

namespace GeneralRelativity

namespace Modified

namespace Ostrogradsky

/-!

## A. Degenerate kinetic matrix and Ostrogradsky ghost

-/

/-- Higher-derivative benchmark model `L = (1/2) q̈² - (1/2) m² q²` parameterized by mass `m`. -/
structure HigherDerivModel where
  /-- Oscillator mass parameter `m`. -/
  m : ℝ

/-- The kinetic Hessian matrix `diag(0, 1)` of `L = (1/2) q̈² + V(q)` in `(q̇, q̈)`. -/
def kineticMatrix : Tensor2 2 :=
  fun i j => if i = 1 ∧ j = 1 then 1 else 0

/-- The kinetic matrix of `L = (1/2) q̈² + V(q)` is degenerate (determinant zero). -/
lemma kineticMatrix_degenerate :
    kineticMatrix 0 0 * kineticMatrix 1 1 - kineticMatrix 0 1 * kineticMatrix 1 0 = 0 := by
  simp [kineticMatrix]

/-- Canonical Ostrogradsky Hamiltonian for the higher-derivative toy model
`L = (1/2) q̈² - (1/2) m² q²`, with `p₁` conjugate to `q̇` and `p₂ = q̈`. -/
noncomputable def hamiltonian (v a p₁ p₂ q m : ℝ) : ℝ :=
  p₁ * v + p₂ * a - a ^ 2 / 2 + m ^ 2 * q ^ 2 / 2

/-- Shifting `p₁` by `t` translates the Ostrogradsky Hamiltonian linearly by `t * v`. -/
lemma hamiltonian_add (v a p₁ p₂ q m t : ℝ) :
    hamiltonian v a (p₁ + t) p₂ q m = hamiltonian v a p₁ p₂ q m + t * v := by
  simp only [hamiltonian]
  ring

/-- The Ostrogradsky ghost: for any non-zero velocity `v ≠ 0`, the Hamiltonian is unbounded
below as a function of `p₁`. -/
lemma ostrogradsky_unbounded_below (v a p₂ q m : ℝ) (hv : v ≠ 0) :
    ∀ B : ℝ, ∃ p₁ : ℝ, hamiltonian v a p₁ p₂ q m < B := by
  intro B
  have h : (B - 1 - (p₂ * a - a ^ 2 / 2 + m ^ 2 * q ^ 2 / 2)) / v * v
      = B - 1 - (p₂ * a - a ^ 2 / 2 + m ^ 2 * q ^ 2 / 2) := by
    field_simp
  refine ⟨(B - 1 - (p₂ * a - a ^ 2 / 2 + m ^ 2 * q ^ 2 / 2)) / v, ?_⟩
  simp only [hamiltonian]
  linarith

/-!

## B. Contrast with standard quadratic kinetic terms

-/

/-- A standard first-order quadratic kinetic term `(1/2) m x²` is non-negative for `m > 0`. -/
lemma kinetic_nonneg (m x : ℝ) (hm : 0 < m) : 0 ≤ m * x ^ 2 / 2 := by
  positivity

/-- A standard quadratic kinetic term vanishes if and only if the velocity is zero. -/
lemma kinetic_zero_iff (m x : ℝ) (hm : 0 < m) : m * x ^ 2 / 2 = 0 ↔ x = 0 := by
  constructor
  · intro h
    have h2 : m * x ^ 2 = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h3 | h3
    · linarith
    · exact (pow_eq_zero_iff (n := 2) (by norm_num)).mp h3
  · rintro rfl
    ring

/-- Canonical Ostrogradsky Hamiltonian evaluated for a `HigherDerivModel`. -/
noncomputable def HigherDerivModel.hamiltonian (H : HigherDerivModel) (v a p₁ p₂ q : ℝ) : ℝ :=
  Ostrogradsky.hamiltonian v a p₁ p₂ q H.m

end Ostrogradsky

end Modified

end GeneralRelativity
