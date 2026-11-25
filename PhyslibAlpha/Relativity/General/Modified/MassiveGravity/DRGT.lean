/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.Matrix.Notation
public import PhyslibAlpha.Relativity.Tensors.Tensor2
import Mathlib.Tactic.Ring

/-!

# Ghost-free dRGT massive gravity potentials

Elementary symmetric polynomials `e₀(K), …, e₃(K)` of the de Rham–Gabadadze–Tolley (dRGT)
building-block matrix `K` and the ghost-free nonlinear potential.

## i. Overview

Nonlinear completion of massive gravity without reviving the Boulware–Deser ghost uses elementary
symmetric polynomials `e_k(K)` of `K^a_b = δ^a_b - (√(g⁻¹ f))^a_b`. This module defines the power
traces, elementary symmetric polynomials up to cubic order, isotropic evaluation, and the cubic
dRGT potential `e₂(K) + α₃ e₃(K)`.

## ii. Key results

- `DRGTTheory` : cubic dRGT massive gravity model parameterized by coupling `α₃`.
- `trK1`, `trK2`, `trK3`, `elemSymm0`, `elemSymm1`, `elemSymm2`, `elemSymm3` : matrix power traces
  and elementary symmetric polynomials.
- `elemSymm_isotropic3`, `dRGTPotential`, `dRGTPotential_vacuum_zero` : isotropic evaluation and
  vanishing Minkowski vacuum potential.

## iii. Table of contents

- A. dRGT elementary symmetric potential polynomials

## iv. References

* Claudia de Rham and Gregory Gabadadze, *Generalization of the Fierz-Pauli Action*, *Physical
  Review D* (2010), Sec. II-III (https://arxiv.org/pdf/1007.0443#page=3). [ref: deRhamGabadadze2010]
* Claudia de Rham, Gregory Gabadadze, and Andrew J. Tolley, *Resummation of Massive Gravity*,
  *Physical Review Letters* (2011), pp. 1-4 (https://arxiv.org/pdf/1011.1232#page=1).
  [ref: deRhamGabadadzeTolley2011]
* S. F. Hassan and Rachel A. Rosen, *Resolving the Ghost Problem in Nonlinear Massive Gravity*,
  *Physical Review Letters* 108, 041101 (2012) (https://arxiv.org/pdf/1106.3344#page=1).
  [ref: HassanRosen2012]
* Kurt Hinterbichler, *Theoretical Aspects of Massive Gravity*, *Reviews of Modern Physics* 84, pp.
  671-710 (2012), Sec. V (https://arxiv.org/pdf/1105.3735#page=18). [ref: Hinterbichler2012]
-/

@[expose] public section

namespace GeneralRelativity

namespace Modified

namespace MassiveGravity

/-!

## A. dRGT elementary symmetric potential polynomials

-/

/-- Cubic de Rham–Gabadadze–Tolley (dRGT) massive gravity theory parameterized by `α₃`. -/
structure DRGTTheory where
  /-- Dimensionless coupling `α₃` of the cubic elementary symmetric polynomial `e₃(K)`. -/
  α3 : ℝ

/-- Matrix power traces `tr(K)`, `tr(K²)`, `tr(K³)` of the dRGT building-block tensor
`K^a_b = δ^a_b - (√(g⁻¹ f))^a_b`. -/
def trK1 (K : Tensor2 4) : ℝ := ∑ a : Fin 4, K a a

/-- Quadratic power trace `tr(K²) = ∑_{a,b} K^a_b K^b_a`. -/
def trK2 (K : Tensor2 4) : ℝ := ∑ a : Fin 4, ∑ b : Fin 4, K a b * K b a

/-- Cubic power trace `tr(K³) = ∑_{a,b,c} K^a_b K^b_c K^c_a`. -/
def trK3 (K : Tensor2 4) : ℝ := ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, K a b * K b c * K c a

/-- Zeroth dRGT elementary symmetric polynomial `e₀(K) = 1`. -/
def elemSymm0 (_K : Tensor2 4) : ℝ := 1

/-- First dRGT elementary symmetric polynomial `e₁(K) = [K] = tr(K)`. -/
def elemSymm1 (K : Tensor2 4) : ℝ := trK1 K

/-- Second dRGT elementary symmetric polynomial `e₂(K) = ½ ([K]² - [K²])`. -/
noncomputable def elemSymm2 (K : Tensor2 4) : ℝ := (1 / 2) * (trK1 K ^ 2 - trK2 K)

/-- Third dRGT elementary symmetric polynomial `e₃(K) = ⅙ ([K]³ - 3 [K] [K²] + 2 [K³])`. -/
noncomputable def elemSymm3 (K : Tensor2 4) : ℝ :=
  (1 / 6) * (trK1 K ^ 3 - 3 * trK1 K * trK2 K + 2 * trK3 K)

/-- On an isotropic spatial deformation `K = diag(0, λ, λ, λ)`, the elementary symmetric
polynomials evaluate to the binomial values `e₁ = 3 λ`, `e₂ = 3 λ²`, `e₃ = λ³`. -/
lemma elemSymm_isotropic3 (lam : ℝ) :
    let K : Tensor2 4 := Matrix.diagonal ![0, lam, lam, lam]
    elemSymm1 K = 3 * lam ∧ elemSymm2 K = 3 * lam ^ 2 ∧ elemSymm3 K = lam ^ 3 := by
  intro K
  have h0 : K 0 0 = 0 := rfl
  have h1 : K 1 1 = lam := rfl
  have h2 : K 2 2 = lam := rfl
  have h3 : K 3 3 = lam := rfl
  have hoff : ∀ i j : Fin 4, i ≠ j → K i j = 0 := fun i j hij => Matrix.diagonal_apply_ne _ hij
  simp only [elemSymm1, elemSymm2, elemSymm3, trK1, trK2, trK3,
    Fin.sum_univ_four, h0, h1, h2, h3, hoff, ne_eq, Fin.reduceEq, not_false_eq_true]
  refine ⟨by ring, by ring, by ring⟩

/-- Cubic dRGT ghost-free potential `U(K) = e₂(K) + α₃ e₃(K)` with free parameter `α₃`
(normalized so the quadratic term reproduces the Fierz–Pauli mass term). -/
noncomputable def dRGTPotential (α3 : ℝ) (K : Tensor2 4) : ℝ :=
  elemSymm2 K + α3 * elemSymm3 K

/-- At the Minkowski vacuum `K = 0` (`g = f`), the dRGT potential vanishes identically
(zero cosmological constant / tadpole-free vacuum). -/
lemma dRGTPotential_vacuum_zero (α3 : ℝ) :
    dRGTPotential α3 0 = 0 := by
  simp [dRGTPotential, elemSymm2, elemSymm3, trK1, trK2, trK3]

end MassiveGravity

end Modified

end GeneralRelativity
