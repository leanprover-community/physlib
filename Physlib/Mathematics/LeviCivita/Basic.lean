/-
Copyright (c) 2026 Robert Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
module

public import Physlib.Mathematics.KroneckerDelta.Basic
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.GroupTheory.Perm.Fin
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
- `leviCivitaSymbol_eq_prod_prod_Ioi` : on `Fin n` the symbol is the product over pairs
  `i < j` of the sign of `g j - g i`.

## iii. Table of contents

- A. Definition
- B. Value on permutations
- C. Antisymmetry
- D. Vanishing on repeated indices
- E. Closed form on `Fin n`

## iv. References

* https://en.wikipedia.org/wiki/Levi-Civita_symbol. [ref: wiki_levi_civita_symbol]
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

## E. Closed form on `Fin n`

-/

/-- On `Fin n` the Levi-Civita symbol is the product over pairs `i < j` of the sign of
`g j - g i`. Unlike the determinant defining `leviCivitaSymbol`, this product is cheap to
evaluate, e.g. by `decide`. -/
lemma leviCivitaSymbol_eq_prod_prod_Ioi {n : ℕ} (g : Fin n → Fin n) :
    leviCivitaSymbol g =
      ∏ i, ∏ j ∈ Finset.Ioi i, (if g i < g j then 1 else if g i = g j then 0 else -1) := by
  by_cases hg : Function.Injective g
  · obtain ⟨σ, rfl⟩ : ∃ σ : Equiv.Perm (Fin n), ⇑σ = g :=
      ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.mp hg), rfl⟩
    rw [leviCivitaSymbol_perm, Equiv.Perm.sign_eq_prod_prod_Ioi]
    simp only [Units.coe_prod]
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j hj => ?_
    have hij : σ i ≠ σ j := σ.injective.ne (Finset.mem_Ioi.mp hj).ne
    split_ifs <;> simp
  · rw [leviCivitaSymbol_eq_zero_of_not_injective hg]
    simp only [Function.Injective, not_forall] at hg
    obtain ⟨i, j, hgij, hij⟩ := hg
    symm
    rcases lt_or_gt_of_ne hij with h | h
    · exact Finset.prod_eq_zero (Finset.mem_univ i)
        (Finset.prod_eq_zero (Finset.mem_Ioi.mpr h) (by simp [hgij]))
    · exact Finset.prod_eq_zero (Finset.mem_univ j)
        (Finset.prod_eq_zero (Finset.mem_Ioi.mpr h) (by simp [hgij]))
