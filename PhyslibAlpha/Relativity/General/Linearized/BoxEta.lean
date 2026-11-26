/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.Metrics.CoordinateMetric

/-!

# Minkowski d'Alembertian wave operator

The flat-space d'Alembertian `□_η f = η^{μν} ∂_μ ∂_ν f` on four-dimensional Minkowski spacetime.

## i. Overview

In `(-, +, +, +)` signature, the flat-space wave operator is defined by
`boxEta f x = ∑ μ, η_{μμ} ∂_μ ∂_μ f(x) = -∂_0² f + ∂_1² f + ∂_2² f + ∂_3² f`.
It governs both gravitational radiation in Lorenz gauge and scalar wave equations on Minkowski
spacetime (such as Nordström gravity).

## ii. Key results

- `boxEta` : Minkowski d'Alembertian wave operator `□_η`.
- `boxEta_zero` : `boxEta` vanishes identically on the zero field.

## iii. Table of contents

- A. The Minkowski d'Alembertian `□_η`

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 4 (Sec. 4.4). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 18 & Ch. 35.
  [ref: mtw_1973_gravitation]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 6
  (https://arxiv.org/pdf/gr-qc/9712019#page=150). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

namespace Linearized

open Pipeline

/-!

## A. The Minkowski d'Alembertian `□_η`

The flat-space hyperbolic wave operator `-∂_t² + ∇²` obtained by contracting second coordinate
derivatives with the Minkowski metric `η^{μν}`.

-/

/-- Minkowski d'Alembertian (wave operator) `□f = η^{μν} ∂_μ ∂_ν f = -∂_t² f + ∇² f`. -/
noncomputable def boxEta (f : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) : ℝ :=
  ∑ μ : Fin 4, minkowskiMetric4 μ μ * coordDeriv μ (coordDeriv μ f) x

/-- Applying `boxEta` to the identically zero scalar function yields `0`. -/
lemma boxEta_zero (x : Fin 4 → ℝ) : boxEta (fun _ : Fin 4 → ℝ => (0 : ℝ)) x = 0 := by
  have hpd : ∀ μ : Fin 4, coordDeriv μ (fun _ : Fin 4 → ℝ => (0 : ℝ)) = fun _ => 0 :=
    fun μ => funext fun y => coordDeriv_const μ 0 y
  simp only [boxEta, hpd, coordDeriv_const, mul_zero, Finset.sum_const_zero]

end Linearized

end GeneralRelativity
