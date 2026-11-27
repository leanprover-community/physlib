/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-!

# Modified `f(T)` teleparallel Friedmann gravity

Modified first Friedmann equation for `f(T) = T + F(T)` teleparallel cosmology and reduction to
General Relativity (TEGR) at `F = 0`.

## i. Overview

Extending the TEGR torsion Lagrangian `T` to a nonlinear function `f(T) = T + F(T)` replaces the
Einstein–Hilbert Friedmann left-hand side `3 H²` by
`3 H² + ½ F(6 H²) - 6 H² F'(6 H²)`.

## ii. Key results

- `FTTheory`, `FTTheory.tegr`, `FTTheory.quadratic` : `f(T) = T + F(T)` teleparallel theory
  specified by `F` and `dF`, with TEGR and quadratic instances.
- `FTTheory.friedmannLHS`, `FTTheory.friedmannLHS_tegr`, `FTTheory.friedmannLHS_quadratic` :
  modified `f(T)` Friedmann left-hand side and TEGR recovery.

## iii. Table of contents

- A. `f(T)` modified Friedmann cosmology

## iv. References

* Rafael Ferraro and Franco Fiorini, *Modified Teleparallel Gravity: Inflation without Inflaton*,
  *Physical Review D* 75, 084031 (2007), Sec. II
  (https://arxiv.org/abs/gr-qc/0610067). [ref: FerraroFiorini2007]
* Gabriel R. Bengochea and Rafael Ferraro, *Dark Torsion as the Cosmic Speed-Up*, *Physical Review
  D* (2009), Sec. II (https://arxiv.org/pdf/0812.1205#page=2). [ref: BengocheaFerraro2009]
* Eric V. Linder, *Einstein's Other Gravity and the Acceleration of the Universe*, *Physical Review
  D* (2010), Sec. I-II (https://arxiv.org/pdf/1005.3039#page=1). [ref: Linder2010]
* Martin Krššák and Emmanuel N. Saridakis, *The Covariant Formulation of $f(T)$ Gravity*, *Classical
  and Quantum Gravity* (2016), Sec. 2-3 (https://arxiv.org/pdf/1510.08432#page=3).
  [ref: KrssakSaridakis2016]
-/

@[expose] public section

namespace GeneralRelativity

namespace Modified

namespace Teleparallel

/-!

## A. `f(T)` modified Friedmann cosmology

On a flat FLRW background with torsion scalar `T = 6 H²`, modifying the teleparallel action by a
function `F(T)` adds `½ F(T) - T F'(T)` to the Friedmann expansion equation.

-/

/-- Extended teleparallel gravity model `f(T) = T + F(T)` parameterized by deviation `F` and its
first derivative `dF = F'`. -/
structure FTTheory where
  /-- Nonlinear torsion deviation function `F(T)`. -/
  F : ℝ → ℝ
  /-- First derivative `F'(T)`. -/
  dF : ℝ → ℝ
  /-- The stored derivative agrees with the derivative of `F` at every torsion scalar. -/
  deriv_eq : ∀ T, HasDerivAt F (dF T) T

/-- The Teleparallel Equivalent of General Relativity (`F = 0`, `dF = 0`). -/
def FTTheory.tegr : FTTheory where
  F _ := 0
  dF _ := 0
  deriv_eq T := by
    simpa using (hasDerivAt_const (x := T) (c := 0))

/-- Quadratic modified teleparallel model `F(T) = α T²`, `dF(T) = 2 α T`. -/
def FTTheory.quadratic (α : ℝ) : FTTheory where
  F T := α * T ^ 2
  dF T := 2 * α * T
  deriv_eq T := by
    have h := (hasDerivAt_pow 2 T).const_mul α
    convert h using 1
    ring

/-- Modified first Friedmann equation left-hand side for an `FTTheory` evaluated at `T = 6 H²`:
`3 H² + ½ T.F(6 H²) - 6 H² T.dF(6 H²)`. -/
noncomputable def FTTheory.friedmannLHS (T : FTTheory) (H : ℝ) : ℝ :=
  3 * H ^ 2 + (1 / 2) * T.F (6 * H ^ 2) - 6 * H ^ 2 * T.dF (6 * H ^ 2)

/-- In `FTTheory.tegr`, the `f(T)` Friedmann equation reduces identically to the standard General
Relativity Friedmann left-hand side `3 H²`. -/
lemma FTTheory.friedmannLHS_tegr (H : ℝ) :
    FTTheory.tegr.friedmannLHS H = 3 * H ^ 2 := by
  simp only [FTTheory.friedmannLHS, FTTheory.tegr]
  ring

/-- For `FTTheory.quadratic α`, the modified Friedmann left-hand side evaluates to
`3 H² - 54 α H⁴`. -/
lemma FTTheory.friedmannLHS_quadratic (H α : ℝ) :
    (FTTheory.quadratic α).friedmannLHS H = 3 * H ^ 2 - 54 * α * H ^ 4 := by
  simp only [FTTheory.friedmannLHS, FTTheory.quadratic]
  ring

end Teleparallel

end Modified

end GeneralRelativity
