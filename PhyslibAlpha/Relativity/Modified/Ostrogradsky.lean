/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import PhyslibAlpha.Relativity.Tensors.Tensor2
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!

# The Ostrogradsky instability

Degeneracy of the higher-derivative kinetic Hessian and unboundedness below of the canonical
Hamiltonian for non-degenerate second-order Lagrangians.

## i. Overview

By Ostrogradsky's theorem, a non-degenerate Lagrangian depending on second time derivatives
`L(q, q̇, q̈)` has two canonical coordinate–momentum pairs `(Q₁, p₁) = (q, ∂L/∂q̇ - d/dt(∂L/∂q̈))`
and `(Q₂, p₂) = (q̇, ∂L/∂q̈)`. Because `p₁` enters the canonical Hamiltonian only linearly through
`p₁ q̇` for any non-degenerate second-order Lagrangian, the Hamiltonian is unbounded below whenever
`q̇ ≠ 0` — the Ostrogradsky ghost — explaining why viable modified gravity theories must either
reduce to healthy scalar–tensor theories (`f(R)`) or restrict to second-order field equations
(Horndeski / Galileons).

This module formalises `HigherDerivativeOscillator` and the algebraic core for `L = (1/2) q̈² -
(1/2) m² q²`, contrasting its linear ghost instability with a standard positive-definite quadratic
kinetic term.

## ii. Key results

- `HigherDerivativeOscillator` : benchmark higher-derivative harmonic oscillator model with
  mass `m`.
- `oscillatorKineticHessian`, `oscillatorKineticHessian_degenerate` : singular kinetic Hessian
  `diag(0, 1)` in `(q̇, q̈)` with `Matrix.det oscillatorKineticHessian = 0`.
- `HigherDerivativeOscillator.hamiltonian`, `HigherDerivativeOscillator.hamiltonian_add`,
  `HigherDerivativeOscillator.ostrogradsky_unbounded_below` : linearity in `p₁` and
  unboundedness below
  whenever `v ≠ 0`.
## iii. Table of contents

- A. Degenerate kinetic matrix and Ostrogradsky ghost

## iv. References

* Mikhail Ostrogradsky, *Mémoires sur les équations différentielles, relatives au problème des
  isopérimètres*, *Mémoires de l'Académie Impériale des Sciences de Saint-Pétersbourg* 6, pp.
  385-517 (1850). [ref: Ostrogradsky1850]
* Richard P. Woodard, *The Theorem of Ostrogradsky*, *Scholarpedia* (2015), Sec. 2
  (https://arxiv.org/pdf/1506.02210#page=3). [ref: Woodard2015]
* Alexander Ganz and Karim Noui, *Reconsidering the Ostrogradsky Theorem: Higher-Derivatives
  Lagrangians, Ghosts and Degeneracy*, *Classical and Quantum Gravity* 38, 075005 (2021), Sec. 2-3
  (https://arxiv.org/pdf/2007.01063#page=1). [ref: GanzNoui2021]
* David Langlois and Karim Noui, *Degenerate Higher Derivative Theories beyond Horndeski: Evading
  the Ostrogradsky Instability*, *Journal of Cosmology and Astroparticle Physics* (2016), Sec. 2-3
  (https://arxiv.org/pdf/1510.06930#page=1). [ref: LangloisNoui2016]
-/

@[expose] public section

namespace GeneralRelativity

namespace Modified

namespace Ostrogradsky

/-!

## A. Degenerate kinetic matrix and Ostrogradsky ghost

In Ostrogradsky's canonical formulation of `L = ½ q̈² - ½ m² q²`, the momentum `p₁` conjugate to
the position `q` appears only linearly as `p₁ q̇` in the Hamiltonian, making the energy unbounded
from below whenever `q̇ ≠ 0`.

-/

/-- Higher-derivative benchmark model `L = (1/2) q̈² - (1/2) m² q²` parameterized by mass `m`. -/
structure HigherDerivativeOscillator where
  /-- Oscillator mass parameter `m`. -/
  m : ℝ

/-- The kinetic Hessian matrix `diag(0, 1)` of `L = (1/2) q̈² + V(q)` with respect to `(q̇, q̈)`. -/
def oscillatorKineticHessian : Tensor2 2 :=
  fun i j => if i = 1 ∧ j = 1 then 1 else 0

/-- The kinetic Hessian matrix of `L = (1/2) q̈² + V(q)` is singular
(`det oscillatorKineticHessian = 0`). -/
lemma oscillatorKineticHessian_degenerate : Matrix.det oscillatorKineticHessian = 0 := by
  simp [oscillatorKineticHessian, Matrix.det_fin_two]

/-- Canonical Ostrogradsky Hamiltonian for `L = (1/2) q̈² - (1/2) m² q²`, with canonical pairs
`(q, p₁)` and `(q̇, p₂)` where `p₁` is conjugate to position `q` and `p₂ = q̈` is conjugate to
velocity `q̇`. -/
noncomputable def HigherDerivativeOscillator.hamiltonian (H : HigherDerivativeOscillator)
    (v a p₁ p₂ q : ℝ) : ℝ :=
  p₁ * v + p₂ * a - a ^ 2 / 2 + H.m ^ 2 * q ^ 2 / 2

/-- Shifting `p₁` by `t` translates the Ostrogradsky Hamiltonian linearly by `t * v`. -/
lemma HigherDerivativeOscillator.hamiltonian_add (H : HigherDerivativeOscillator)
    (v a p₁ p₂ q t : ℝ) :
    H.hamiltonian v a (p₁ + t) p₂ q = H.hamiltonian v a p₁ p₂ q + t * v := by
  simp only [HigherDerivativeOscillator.hamiltonian]
  ring

/-- The Ostrogradsky ghost: for any non-zero velocity `v ≠ 0`, the Hamiltonian of a
`HigherDerivativeOscillator` is unbounded below as a function of `p₁`. -/
lemma HigherDerivativeOscillator.ostrogradsky_unbounded_below (H : HigherDerivativeOscillator)
    (v a p₂ q : ℝ) (hv : v ≠ 0) :
    ∀ B : ℝ, ∃ p₁ : ℝ, H.hamiltonian v a p₁ p₂ q < B := by
  intro B
  have h : (B - 1 - (p₂ * a - a ^ 2 / 2 + H.m ^ 2 * q ^ 2 / 2)) / v * v
      = B - 1 - (p₂ * a - a ^ 2 / 2 + H.m ^ 2 * q ^ 2 / 2) := by
    field_simp
  refine ⟨(B - 1 - (p₂ * a - a ^ 2 / 2 + H.m ^ 2 * q ^ 2 / 2)) / v, ?_⟩
  simp only [HigherDerivativeOscillator.hamiltonian]
  linarith

end Ostrogradsky

end Modified

end GeneralRelativity
