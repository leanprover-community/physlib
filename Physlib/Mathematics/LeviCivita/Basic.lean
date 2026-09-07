/-
Copyright (c) 2026 Robert Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
module

public import Physlib.Mathematics.KroneckerDelta.Basic
public import Mathlib.LinearAlgebra.Matrix.Permutation
/-!

# The Levi-Civita symbol in general dimension

## i. Overview

This module defines the Levi-Civita symbol `leviCivitaSymbol` on a general finite index
type `ι`: for `g : ι → ι` it is the sign of `g` when `g` is a permutation and `0`
otherwise. Taking `ι = Fin d` gives the Levi-Civita symbol `ε_{i₁ ⋯ i_d}` in dimension
`d`, normalized by `ε_{0 1 ⋯ (d-1)} = 1`.

The definition is the `generalizedKroneckerDelta` of `g` against the identity, i.e. the
determinant of the matrix of Kronecker deltas `δ[g i, j]`, so the basic properties are
inherited from the determinant: the value `1` on the identity, antisymmetry under
transposition of two indices, vanishing on repeated indices, and the sign of a
permutation via `Matrix.det_permutation`.

## ii. Key results

- `leviCivitaSymbol` : the Levi-Civita symbol on a finite index type, valued in `ℤ`.
- `leviCivitaSymbol_id` : the normalization `ε_{0 1 ⋯ (d-1)} = 1`.
- `leviCivitaSymbol_perm` : on a permutation `σ` the symbol is the sign of `σ`.
- `leviCivitaSymbol_comp_swap` : antisymmetry under transposition of two indices.
- `leviCivitaSymbol_swap_comp` : antisymmetry under transposition of two index values.
- `leviCivitaSymbol_eq_zero_iff` : the symbol vanishes exactly on repeated indices.
- `sum_leviCivitaSymbol_mul_prod` : contracted against the rows of a matrix `M` selected by
  `a`, the symbol gives `det M` times the symbol of `a`. This is the statement that `ε`
  transforms as a tensor density of weight one.

## iii. Table of contents

- A. Definition
- B. Value on permutations
- C. Antisymmetry
- D. Vanishing on repeated indices
- E. Contraction against a matrix

## iv. References

- https://en.wikipedia.org/wiki/Levi-Civita_symbol

-/

@[expose] public section

open KroneckerDelta

/-!

## A. Definition

-/

variable {ι : Type} [DecidableEq ι] [Fintype ι]

/-- The Levi-Civita symbol on a finite index type `ι`: `leviCivitaSymbol g` is the sign
of `g` when `g : ι → ι` is a permutation, and `0` otherwise. It is the generalized
Kronecker delta of `g` against the identity, i.e. the determinant of the matrix of
Kronecker deltas `δ[g i, j]`.

For `ι = Fin d` this is the Levi-Civita symbol `ε_{i₁ ⋯ i_d}` in dimension `d`,
normalized by `ε_{0 1 ⋯ (d-1)} = 1`. -/
def leviCivitaSymbol (g : ι → ι) : ℤ :=
  generalizedKroneckerDelta g (id : ι → ι)

/-- The Levi-Civita symbol as the determinant of the matrix of Kronecker deltas
`δ[g i, j]`. -/
lemma leviCivitaSymbol_eq_det (g : ι → ι) :
    leviCivitaSymbol g = Matrix.det (fun i j => ((kroneckerDelta (g i) j : ℕ) : ℤ)) :=
  rfl

/-- The Levi-Civita symbol of the identity, i.e. `ε_{0 1 ⋯ (d-1)}`, is `1`. -/
@[simp]
lemma leviCivitaSymbol_id : leviCivitaSymbol (id : ι → ι) = 1 := by
  rw [leviCivitaSymbol_eq_det, show (fun i j => ((kroneckerDelta (id i : ι) j : ℕ) : ℤ))
    = (1 : Matrix ι ι ℤ) from funext fun i => funext fun j => by
      simp [kroneckerDelta, Matrix.one_apply]]
  exact Matrix.det_one

/-!

## B. Value on permutations

-/

/-- The Levi-Civita symbol of a permutation `σ` is the sign of `σ`. -/
@[simp]
lemma leviCivitaSymbol_perm (σ : Equiv.Perm ι) :
    leviCivitaSymbol ⇑σ = (Equiv.Perm.sign σ : ℤ) := by
  rw [leviCivitaSymbol_eq_det, show (fun i j => ((kroneckerDelta (σ i) j : ℕ) : ℤ))
    = σ.permMatrix ℤ from funext fun i => funext fun j => by
      simp [kroneckerDelta, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, eq_comm]]
  exact Matrix.det_permutation σ

/-!

## C. Antisymmetry

-/

/-- The Levi-Civita symbol is antisymmetric under transposition of two of its indices:
precomposing with the swap of two distinct index positions negates it. -/
lemma leviCivitaSymbol_comp_swap (g : ι → ι) {i j : ι} (hij : i ≠ j) :
    leviCivitaSymbol (g ∘ Equiv.swap i j) = - leviCivitaSymbol g :=
  generalizedKroneckerDelta_swap g id hij

set_option backward.isDefEq.respectTransparency false in
/-- The Levi-Civita symbol is antisymmetric under transposition of two index values:
postcomposing with the swap of two distinct values exchanges those two values wherever
they occur and negates it. -/
lemma leviCivitaSymbol_swap_comp (g : ι → ι) {i j : ι} (hij : i ≠ j) :
    leviCivitaSymbol (Equiv.swap i j ∘ g) = - leviCivitaSymbol g := by
  have h : (fun a b => ((kroneckerDelta ((Equiv.swap i j ∘ g) a) b : ℕ) : ℤ))
      = Matrix.submatrix (fun a b => ((kroneckerDelta (g a) b : ℕ) : ℤ)) id (Equiv.swap i j) :=
    funext fun a => funext fun b => by simp [kroneckerDelta, Equiv.swap_apply_eq_iff]
  rw [leviCivitaSymbol_eq_det, h, Matrix.det_permute', Equiv.Perm.sign_swap hij,
    ← leviCivitaSymbol_eq_det]
  simp

/-!

## D. Vanishing on repeated indices

-/

/-- The Levi-Civita symbol vanishes on a repeated index: if two distinct index positions
`i ≠ j` carry the same value, the symbol is zero. -/
lemma leviCivitaSymbol_eq_zero_of_eq {g : ι → ι} {i j : ι} (hij : i ≠ j) (h : g i = g j) :
    leviCivitaSymbol g = 0 := by
  rw [leviCivitaSymbol_eq_det]
  exact Matrix.det_zero_of_row_eq hij (funext fun c => by rw [h])

/-- The Levi-Civita symbol vanishes on maps which are not injective. -/
lemma leviCivitaSymbol_eq_zero_of_not_injective {g : ι → ι} (h : ¬ Function.Injective g) :
    leviCivitaSymbol g = 0 := by
  simp only [Function.Injective, not_forall] at h
  obtain ⟨i, j, hgij, hij⟩ := h
  exact leviCivitaSymbol_eq_zero_of_eq hij hgij

/-- The Levi-Civita symbol vanishes exactly on maps with a repeated index, i.e. on maps
which are not injective. -/
lemma leviCivitaSymbol_eq_zero_iff {g : ι → ι} :
    leviCivitaSymbol g = 0 ↔ ¬ Function.Injective g := by
  refine ⟨fun h hinj => ?_, leviCivitaSymbol_eq_zero_of_not_injective⟩
  obtain ⟨σ, rfl⟩ : ∃ σ : Equiv.Perm ι, ⇑σ = g :=
    ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.mp hinj), rfl⟩
  rw [leviCivitaSymbol_perm] at h
  exact Units.ne_zero (Equiv.Perm.sign σ) h

/-!

## E. Contraction against a matrix

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
  rw [Finset.sum_ite_eq' Finset.univ, if_pos (Finset.mem_univ _)]
