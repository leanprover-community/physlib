/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.SL2C.Basic
public import PhyslibAlpha.Relativity.PauliMatrices.SelfAdjoint
/-!
# Conjugation and the kernel of the covering map

Entrywise conjugation on `SL(2, ℂ)`, and the covering map on `-1`, on entries and on adjoints.

## i. Overview

Three things about the covering map `SL(2, ℂ) →* LorentzGroup 3` are collected here, all
needed to carry a Lorentz index through a spinor computation.

Entrywise complex conjugation is a monoid endomorphism `conjHom` of `SL(2, ℂ)`, an involution,
and conjugating the group argument undoes the conjugation of the entries: the inverse
conjugate transpose at `conjHom g` is the inverse transpose at `g`. This is what lets a
right-handed slot be treated as a conjugated left-handed one.

The covering map sandwiches, `A ↦ M A Mᴴ`, so the two signs of `-1` cancel and
`toLorentzGroup (-1) = 1`: the map is two-to-one. It also intertwines conjugate transposition
with matrix transposition, `L(M†) = L(M)ᵀ`.

Finally `sum_pauliLower_mul_sl2c` is the defining intertwining identity read entrywise:
sandwiching `σ_μ` between `g` and `gᴴ` mixes the covariant Pauli matrices by the column `μ` of
the Lorentz matrix of `g`.

## ii. Key results

- `Lorentz.SL2C.conjHom` : entrywise conjugation as a monoid endomorphism.
- `Lorentz.SL2C.conjHom_involutive`, `Lorentz.SL2C.conjHom_inv_conjTranspose` : its
  involutivity, and its effect on the inverse conjugate transpose.
- `Lorentz.SL2C.toLorentzGroup_neg_one` : the centre covers the identity.
- `Lorentz.SL2C.sum_pauliLower_mul_sl2c` : the intertwining identity on entries.
- `Lorentz.SL2C.toLorentzGroup_conjTranspose` : `L(M†) = L(M)ᵀ`.

## iii. Table of contents

- A. Entrywise conjugation
- B. The kernel of the covering map
- C. The intertwining identity on entries
- D. The covering map and adjoints

## iv. References

The covering map and its properties are in `Physlib.Relativity.SL2C.Basic`.

-/

@[expose] public section

namespace Lorentz

open Module Matrix
open MatrixGroups
open Complex

namespace SL2C

/-!

## A. Entrywise conjugation

-/

/-- Entrywise complex conjugation as a monoid endomorphism of `SL(2,ℂ)`: Mathlib's
  `SpecialLinearGroup.map` along `starRingEnd ℂ`. -/
abbrev conjHom : SL(2,ℂ) →* SL(2,ℂ) := SpecialLinearGroup.map (starRingEnd ℂ)

lemma conjHom_coe (g : SL(2,ℂ)) : (conjHom g).1 = g.1.map star := rfl

/-- Conjugation is an involution, hence surjective. -/
lemma conjHom_involutive : Function.Involutive conjHom := by
  intro g
  apply Subtype.ext
  ext i j
  simp

/-- Conjugating the group argument undoes the conjugation of the entries: the inverse
  conjugate transpose at `conjHom g` is the inverse transpose at `g`. -/
lemma conjHom_inv_conjTranspose (g : SL(2,ℂ)) : (((conjHom g).1)⁻¹)ᴴ = (g.1⁻¹)ᵀ := by
  have h1 : ((conjHom g).1)⁻¹ = (g.1⁻¹).map star := by
    rw [inverse_coe, ← map_inv, inverse_coe]
    rfl
  rw [h1]
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.map_apply]

/-!

## B. The kernel of the covering map

-/

/-- **The centre of `SL(2, ℂ)` covers the identity Lorentz transformation.** The covering
  map sandwiches, `A ↦ M A Mᴴ`, so the two signs of `-1` cancel. Together with
  `_root_.map_one` this says that the covering map is two-to-one. -/
lemma toLorentzGroup_neg_one : toLorentzGroup (-1) = 1 := by
  ext1
  have h : toSelfAdjointMap (-1) = LinearMap.id := by
    ext1 A
    simp [toSelfAdjointMap]
  show toMatrix (-1) = _
  simp only [toMatrix, MonoidHom.coe_mk, OneHom.coe_mk, h, LinearMap.toMatrix_id]
  rfl

/-!

## C. The intertwining identity on entries

-/

/-- The intertwining identity `toSelfAdjointMap_basis` read entrywise: sandwiching the
  covariant Pauli matrix `σ_μ` between `g` and `gᴴ` mixes the covariant Pauli matrices by the
  column `μ` of the Lorentz matrix of `g`, the summed Lorentz index first. -/
lemma sum_pauliLower_mul_sl2c (g : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) (β β' : Fin 2) :
    ∑ p : Fin 2 × Fin 2, PauliMatrix.pauliLower μ p.1 p.2 * (g.1 β p.1 * star (g.1 β' p.2))
      = ∑ ν : Fin 1 ⊕ Fin 3, (((toLorentzGroup g).1 ν μ : ℝ) : ℂ)
        * PauliMatrix.pauliLower ν β β' := by
  have h := congrArg (fun A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) => A.1 β β')
    (toSelfAdjointMap_basis (M := g) μ)
  simp only [toSelfAdjointMap_apply_coe, AddSubmonoidClass.coe_finsetSum,
    Matrix.sum_apply, selfAdjoint.val_smul, Matrix.smul_apply, Complex.real_smul,
    PauliMatrix.pauliBasis'_coe] at h
  rw [← h, Matrix.mul_apply, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun p₂ _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun p₁ _ => by
    rw [Matrix.conjTranspose_apply]
    ring

/-!

## D. The covering map and adjoints

-/

/-- The covering map intertwines conjugate transposition with matrix
  transposition: `L(M†) = L(M)ᵀ`. -/
lemma toLorentzGroup_conjTranspose {M N : SL(2,ℂ)} (hN : N.1 = M.1ᴴ) :
    (toLorentzGroup N).1 = (toLorentzGroup M).1ᵀ := by
  ext l i
  refine Complex.ofReal_injective ?_
  have h1 := toLorentzGroup_eq_trace N l i
  have h2 := toLorentzGroup_eq_trace M i l
  rw [hN] at h1
  rw [Matrix.transpose_apply, h1, h2]
  congr 1
  rw [Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.trace_mul_cycle, ← Matrix.mul_assoc, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc]

end SL2C

end Lorentz
