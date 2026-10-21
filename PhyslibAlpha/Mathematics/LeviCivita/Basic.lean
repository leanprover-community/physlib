/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Physlib.Mathematics.LeviCivita.Basic
/-!
# Contracting the Levi-Civita symbol against a matrix

The symbol is a tensor density of weight one.

## i. Overview

Contracting the Levi-Civita symbol against the rows of a matrix `M` picked out by an index
family `a` gives `det M` times the symbol of `a`. This is the statement that `ε` transforms as
a tensor density of weight one, and it is what makes an `ε` contraction invariant under a
determinant-one group.

Both sides are the determinant of the matrix of those rows: on the left by expanding it along
the Leibniz formula, on the right by the product rule, the row selection being the matrix of
Kronecker deltas of `a`. The bridge to an arbitrary commutative ring is `cast_leviCivitaSymbol`,
which carries the integer determinant of the delta matrix along the ring map from `ℤ`.

## ii. Key results

- `cast_leviCivitaSymbol` : the symbol as a determinant over any commutative ring.
- `sum_leviCivitaSymbol_mul_prod` : contracted against the rows of `M` selected by `a`, the
  symbol gives `det M` times the symbol of `a`.

## iii. Table of contents

- A. Contraction against a matrix

## iv. References

* https://en.wikipedia.org/wiki/Levi-Civita_symbol. [ref: wiki_levi_civita_symbol]

-/

@[expose] public section

open KroneckerDelta

variable {ι : Type} [DecidableEq ι] [Fintype ι]

/-!

## A. Contraction against a matrix

Contracting the symbol against the rows of a matrix `M` picked out by `a` gives `det M` times
the symbol of `a`. Both sides are the determinant of the matrix of those rows: on the left by
expanding it along the Leibniz formula, on the right by the product rule, the row selection
being the matrix of Kronecker deltas of `a`.

-/

variable {R : Type*} [CommRing R]

/-- The symbol as a determinant over any commutative ring, the integer determinant carried
along the ring map from `ℤ`. -/
lemma cast_leviCivitaSymbol (g : ι → ι) :
    ((leviCivitaSymbol g : ℤ) : R)
      = (Matrix.of fun i j : ι => if g i = j then (1 : R) else 0).det := by
  have h := RingHom.map_det (Int.castRingHom R)
    (Matrix.of fun i j : ι => if g i = j then (1 : ℤ) else 0)
  simp only [Int.coe_castRingHom, RingHom.mapMatrix_apply] at h
  rw [leviCivitaSymbol_eq_det, show (fun (i j : ι) => ((kroneckerDelta (g i) j : ℕ) : ℤ))
      = (Matrix.of fun i j : ι => if g i = j then (1 : ℤ) else 0) from by
        ext i j
        by_cases hij : g i = j <;> simp [kroneckerDelta, hij], h]
  congr 1
  ext i j
  by_cases hij : g i = j <;> simp [Matrix.map_apply, hij]

/-- The Leibniz formula with the permutation moving the column index. -/
private lemma det_eq_sum_perm_prod (X : Matrix ι ι R) :
    X.det = ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : R) * ∏ i, X i (σ i) := by
  rw [← Matrix.det_transpose X, Matrix.det_apply']
  rfl

/-- Contracted against the rows of `M` selected by `a`, the symbol gives `det M` times the
symbol of `a`. -/
lemma sum_leviCivitaSymbol_mul_prod (M : Matrix ι ι R) (a : ι → ι) :
    ∑ g : ι → ι, ((leviCivitaSymbol g : ℤ) : R) * ∏ i, M (a i) (g i)
      = M.det * ((leviCivitaSymbol a : ℤ) : R) := by
  classical
  have hrows : (Matrix.of fun i j => M (a i) j).det
      = ((leviCivitaSymbol a : ℤ) : R) * M.det := by
    rw [cast_leviCivitaSymbol, ← Matrix.det_mul]
    congr 1
    ext i j
    simp [Matrix.mul_apply]
  have hfun : ∀ (σ : Equiv.Perm ι) (g : ι → ι), (∀ i, g i = σ i) ↔ g = ⇑σ :=
    fun σ g => ⟨fun h => funext h, fun h i => by rw [h]⟩
  rw [mul_comm, ← hrows, det_eq_sum_perm_prod]
  simp only [cast_leviCivitaSymbol, det_eq_sum_perm_prod, Matrix.of_apply, Finset.sum_mul,
    Fintype.prod_boole, hfun, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_ite_eq' Finset.univ, ite_eq_left (Finset.mem_univ _)]
