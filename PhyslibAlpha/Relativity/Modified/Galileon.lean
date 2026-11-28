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

This module packages `CubicGalileon` and formalises the one-dimensional core of those mechanisms:

- `C.density v a t = C.c3 * (φ')² φ''` is the total derivative `d/dt (C.c3 * (φ')³ / 3)`
  (`CubicGalileon.density_hasDerivAt`);
- shifting `φ' ↦ φ' + c` changes `(φ')² φ''` by a total derivative (`shift_total_derivative`);

## ii. Key results

- `CubicGalileon`, `CubicGalileon.density` : cubic Galileon model and 1D density `c₃ (φ')² φ''`.
- `cubic_total_derivative`, `CubicGalileon.density_hasDerivAt` : `(v t)² a t = d/dt (v³ / 3)`
  whenever `v' = a`.
- `shift_total_derivative` : shifting velocity by `c` preserves total-derivative structure.

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

Expressing the cubic Galileon 1D density as an exact total time derivative guarantees second-order
equations of motion, while shift symmetry eliminates any non-constant potential.

-/

/-- Cubic Galileon scalar–tensor theory parameterized by its cubic interaction coupling `c₃`. -/
structure CubicGalileon where
  /-- Dimensionless cubic Galileon self-interaction coupling `c₃`. -/
  c3 : ℝ

/-- Scaled 1D cubic Galileon density `c₃ (φ')² φ''` for a `CubicGalileon` model, with velocity
`v = φ'` and acceleration `a = φ''`. -/
def CubicGalileon.density (C : CubicGalileon) (v a : ℝ → ℝ) (t : ℝ) : ℝ :=
  C.c3 * (v t ^ 2 * a t)

/-- In one dimension, `(φ')² φ''` is the total derivative `d/dt ((φ')³ / 3)`. -/
lemma cubic_total_derivative (v a : ℝ → ℝ) (t : ℝ) (hv : HasDerivAt v (a t) t) :
    HasDerivAt (fun s => v s ^ 3 / 3) (v t ^ 2 * a t) t := by
  have h := (hv.pow 3).div_const 3
  convert h using 1
  ring

/-- The scaled cubic Galileon density `C.density v a t` is the exact total derivative
`d/dt (C.c3 * v(t)³ / 3)`. -/
lemma CubicGalileon.density_hasDerivAt (C : CubicGalileon) (v a : ℝ → ℝ) (t : ℝ)
    (hv : HasDerivAt v (a t) t) :
    HasDerivAt (fun s => C.c3 * (v s ^ 3 / 3)) (C.density v a t) t :=
  (cubic_total_derivative v a t hv).const_mul C.c3

/-- Shifting velocity by a constant `c` preserves the total-derivative structure of the cubic
Galileon density. -/
lemma shift_total_derivative (v a : ℝ → ℝ) (t c : ℝ) (hv : HasDerivAt v (a t) t) :
    HasDerivAt (fun s => (v s + c) ^ 3 / 3) ((v t + c) ^ 2 * a t) t :=
  cubic_total_derivative (fun s => v s + c) a t (hv.add_const c)

end Galileon

end Modified

end GeneralRelativity
