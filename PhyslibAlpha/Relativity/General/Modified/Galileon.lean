/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Ring

/-!

# Galileon and Horndeski total-derivative structure

One-dimensional algebraic and derivative structure behind Galileon shift symmetry and second-order
equations of motion.

## i. Overview

Horndeski's theorem characterises the most general scalar–tensor theory yielding second-order
field equations. Its shift-symmetric subsector, the Galileon theories, remains second order
because higher-derivative interaction terms reduce to total derivatives under constant velocity
shifts `φ' ↦ φ' + c`, while exact Galileon shift symmetry forbids a scalar potential.

This module formalises the one-dimensional core of those two mechanisms:

- `(φ')² φ''` is the total derivative `d/dt ((φ')³ / 3)` (`cubic_total_derivative`);
- shifting `φ' ↦ φ' + c` changes `(φ')² φ''` by a total derivative (`shift_total_derivative`);
- an invariant potential under `φ ↦ φ + c` must be constant (`shift_forbids_potential`).

## ii. Key results

- `CubicGalileon`, `cubicGalileonDensity` : cubic Galileon model and 1D density `(φ')² φ''`.
- `cubic_total_derivative` : `(v t)² a t = d/dt (v³ / 3)` whenever `v' = a`.
- `shift_total_derivative` : shifting velocity by `c` preserves total-derivative structure.
- `shift_forbids_potential` : shift-symmetric potentials are constant.

## iii. Table of contents

- A. Cubic Galileon total derivative and shift symmetry

## iv. References

* Alberto Nicolis, Riccardo Rattazzi, and Enrico Trincherini, *The Galileon as a Local Modification
  of Gravity*, *Physical Review D* (2009), Sec. II-III (https://arxiv.org/pdf/0811.2197#page=2).
  [ref: NicolisRattazziTrincherini2009]
* Gregory Walter Horndeski, *Second-Order Scalar-Tensor Field Equations in a Four-Dimensional
  Space*, *International Journal of Theoretical Physics* 10, pp. 363-384 (1974), Sec. 2-4.
  [ref: Horndeski1974]
* Cédric Deffayet, Stanley Deser, and Gilles Esposito-Farèse, *Generalized Galileons: All Scalar
  Models Whose Curved Background Extensions Maintain Second-Order Field Equations and
  Stress-Tensors*, *Physical Review D* (2009), Sec. II (https://arxiv.org/pdf/0906.1967#page=2).
  [ref: DeffayetDeserEspositoFarese2009]
* Cédric Deffayet et al., *From k-essence to Generalised Galileons*, *Physical Review D* (2011),
  Sec. II-III (https://arxiv.org/pdf/1103.3260#page=2). [ref: DeffayetGaoSteerZahariade2011]
-/

@[expose] public section

namespace GeneralRelativity

namespace Modified

namespace Galileon

/-!

## A. Cubic Galileon total derivative and shift symmetry

-/

/-- Cubic Galileon scalar–tensor theory parameterized by its cubic interaction coupling `c₃`. -/
structure CubicGalileon where
  /-- Dimensionless cubic Galileon self-interaction coupling `c₃`. -/
  c3 : ℝ

/-- One-dimensional cubic Galileon density `(φ')² φ''` for velocity `v = φ'` and
acceleration `a = φ''`. -/
def cubicGalileonDensity (v a : ℝ → ℝ) (t : ℝ) : ℝ := v t ^ 2 * a t

/-- Scaled 1D cubic Galileon density `c₃ (φ')² φ''` for a `CubicGalileon` model. -/
def CubicGalileon.density (C : CubicGalileon) (v a : ℝ → ℝ) (t : ℝ) : ℝ :=
  C.c3 * cubicGalileonDensity v a t

/-- In one dimension, the cubic Galileon density `(φ')² φ''` is the total derivative
`d/dt ((φ')³ / 3)`. -/
lemma cubic_total_derivative (v a : ℝ → ℝ) (t : ℝ) (hv : HasDerivAt v (a t) t) :
    HasDerivAt (fun s => v s ^ 3 / 3) (v t ^ 2 * a t) t := by
  have h := (hv.pow 3).div_const 3
  convert h using 1
  ring

/-- Shifting velocity by a constant `c` preserves the total-derivative structure of the cubic
Galileon density. -/
lemma shift_total_derivative (v a : ℝ → ℝ) (t c : ℝ) (hv : HasDerivAt v (a t) t) :
    HasDerivAt (fun s => (v s + c) ^ 3 / 3) ((v t + c) ^ 2 * a t) t :=
  cubic_total_derivative (fun s => v s + c) a t (hv.add_const c)

/-- A potential invariant under constant shifts `φ ↦ φ + c` must be constant everywhere,
protecting the Galileon scalar from a mass term. -/
lemma shift_forbids_potential (V : ℝ → ℝ) (h : ∀ φ c, V (φ + c) = V φ)
    (φ₁ φ₂ : ℝ) : V φ₁ = V φ₂ := by
  have h' := h φ₁ (φ₂ - φ₁)
  have hsub : φ₁ + (φ₂ - φ₁) = φ₂ := by ring
  rw [hsub] at h'
  exact h'.symm

end Galileon

end Modified

end GeneralRelativity
