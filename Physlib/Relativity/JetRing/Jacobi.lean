/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.Relativity.JetRing.Matrix
public import Mathlib.LinearAlgebra.Matrix.Adjugate
/-!
# Jacobi's formula for matrices of jets

## i. Overview

Jacobi's formula `∂ det M = tr (∂M · adj M)` for a square matrix of jets, in the generality
needed by the jets of any special unitary group: it is what makes the Maurer–Cartan form
`i (∂U) U⁻¹` of an `SU(n)` jet traceless, since `det U = 1` and `U⁻¹ = adj U`.

## ii. Key results

- `JetRing.pderiv_finset_prod` : the Leibniz rule for a finite product.
- `JetRing.jacobi` : Jacobi's formula.

## iii. Table of contents

- A. The Leibniz rule for a finite product
- B. Jacobi's formula

-/

@[expose] public section

namespace JetRing

open MvPowerSeries

/-!

## A. The Leibniz rule for a finite product

-/

/-- The Leibniz rule for a finite product. -/
lemma pderiv_finset_prod {ι : Type*} [DecidableEq ι] (μ : Fin 1 ⊕ Fin 3) (s : Finset ι)
    (f : ι → JetRing) :
    pderiv μ (∏ i ∈ s, f i) = ∑ i ∈ s, (∏ j ∈ s.erase i, f j) * pderiv μ (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Derivation.leibniz, smul_eq_mul, smul_eq_mul, ih,
      Finset.sum_insert ha, Finset.erase_insert ha, Finset.mul_sum, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hia : a ≠ i := fun h => ha (h ▸ hi)
    rw [Finset.erase_insert_of_ne hia,
      Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h)), mul_assoc]

/-!

## B. Jacobi's formula

-/

/-- **Jacobi's formula**: the derivative of a determinant is the trace of the derivative
  against the adjugate. -/
lemma jacobi {κ : Type} [Fintype κ] [DecidableEq κ] (M : Matrix κ κ JetRing)
    (μ : Fin 1 ⊕ Fin 3) :
    pderiv μ M.det = (M.map (pderiv μ) * M.adjugate).trace := by
  have hcol : ∀ (σ : Equiv.Perm κ) (j : κ),
      (∏ i ∈ Finset.univ.erase j, M (σ i) i) * pderiv μ (M (σ j) j)
        = ∏ i, (M.updateCol j fun k => pderiv μ (M k j)) (σ i) i := by
    intro σ j
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j), Matrix.updateCol_self,
      mul_comm]
    congr 1
    exact Finset.prod_congr rfl fun i hi => by
      rw [Matrix.updateCol_ne (Finset.ne_of_mem_erase hi)]
  calc pderiv μ M.det
      = ∑ j, ∑ σ : Equiv.Perm κ, Equiv.Perm.sign σ •
          ∏ i, (M.updateCol j fun k => pderiv μ (M k j)) (σ i) i := by
        rw [Matrix.det_apply, map_sum]
        simp only [Units.smul_def, map_zsmul, pderiv_finset_prod, Finset.smul_sum, hcol]
        exact Finset.sum_comm
    _ = ∑ j, Matrix.mulVec M.adjugate (fun k => pderiv μ (M k j)) j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Matrix.det_apply, ← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
    _ = (M.map (pderiv μ) * M.adjugate).trace := by
        simp only [Matrix.mulVec, dotProduct, Matrix.trace, Matrix.diag, Matrix.mul_apply,
          Matrix.map_apply]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => mul_comm _ _

end JetRing
