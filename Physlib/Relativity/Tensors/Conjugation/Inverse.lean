/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Relativity.Tensors.Conjugation.Basic

/-!

# The inverse of a rank-two tensor

The inverse `g^{J̄I}` of a tensor `g_{IJ̄}` with one index and one conjugate index, such as a Kähler
metric.

## i. Overview

The inverse of a Kähler metric `g_{IJ̄}` is the tensor `g^{J̄I}` with two upper indices whose
contraction with `g` is the unit tensor, `g_{IJ̄} g^{J̄K} = δ_I^K`.

Convention: the colours of the inverse are `![τ (c 1), τ (c 0)]`, so its barred index comes first,
`g^{J̄I}`; the usual `g^{IJ̄}` is the same tensor with its two indices swapped. Barred first is the
order in which `g_{IJ̄} g^{J̄K}` contracts adjacent indices, so the contraction laws need no
reordering of the inverse. The matrix `(g^{J̄I})`, row `J` and column `I`, is the inverse of the
matrix `(g_{IJ̄})`; `inverseT` is defined by this matrix inversion and is zero when `(g_{IJ̄})` is
not invertible. The inverse of a Hermitian `g` is Hermitian (A) and of a positive-definite `g`
positive-definite (B).

## ii. Key results

- `ConjTensorSpecies.inverseT` is the inverse `g^{J̄I}` of a tensor `g_{IJ̄}`.
- `ConjTensorSpecies.toSquareMatrix_inverseT`: the matrix `(g^{J̄I})`, row `J` and column `I`, is
  `(g_{IJ̄})⁻¹`.
- `ConjTensorSpecies.isSymm_toSesqForm_inverseT` and
  `ConjTensorSpecies.isPosDef_toSesqForm_inverseT`: the inverse of a Hermitian or positive-definite
  `g` is Hermitian or positive-definite.

## iii. Table of contents

- A. The inverse
- B. Positive-definiteness

## iv. References

- `Matrix.inv` and `Matrix.inv_def`, in `Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean`;
- `Matrix.PosDef.inv`, in `Mathlib/LinearAlgebra/Matrix/PosDef.lean`.

-/

@[expose] public section
noncomputable section

open Module TensorSpecies TensorSpecies.Tensor

/-!

## A. The inverse

-/

namespace ConjTensorSpecies

open Tensor HasContrDualBases
open scoped Matrix

variable {k : Type} [CommRing k] [StarRing k] {C : Type} {G : Type} [Group G]
    {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Basis (basisIdx c) k (V c)}
    (S : ConjTensorSpecies k C G V basisIdx rep b) [HasContrDualBases S.toTensorSpecies]

/-- The inverse `g^{J̄I}` of a tensor `g_{IJ̄}`: the tensor with two upper indices whose matrix
`(g^{J̄I})`, row `J` and column `I`, is the inverse of the matrix `(g_{IJ̄})`. It is zero when
`(g_{IJ̄})` is not invertible. -/
def inverseT {c : Fin 2 → C} (M : S.Tensor c) (hbar : S.bar (c 0) = c 1 := by rfl) :
    S.Tensor ![S.τ (c 1), S.τ (c 0)] :=
  fromMatrixT (S := S.toTensorSpecies) (S.τ (c 1)) (S.τ (c 0))
    ((S.toSquareMatrix M hbar)⁻¹.submatrix
      (Equiv.cast (hbar ▸ S.barIdx_eq (c 0)) ∘ (dualIdxEquiv (rfl : S.τ (c 1) = S.τ (c 1))).symm)
      (dualIdxEquiv (S.τ_τ_apply (c 0))))

/-- The components of the inverse: `g^{J̄I}` is the entry `(J, I)` of `(g_{IJ̄})⁻¹`, the upper
indices `J̄` and `I` labelled by the lower indices `J` and `I` they contract with. -/
lemma toMatrix_inverseT {c : Fin 2 → C} (hbar : S.bar (c 0) = c 1) (M : S.Tensor c) :
    toMatrix (S.inverseT M hbar) =
      (S.toSquareMatrix M hbar)⁻¹.submatrix
        (Equiv.cast (hbar ▸ S.barIdx_eq (c 0)) ∘
          (dualIdxEquiv (rfl : S.τ (c 1) = S.τ (c 1))).symm)
        (dualIdxEquiv (S.τ_τ_apply (c 0))) :=
  toMatrix_fromMatrixT _ _ _

/-- The matrix `(g^{J̄I})`, row `J` from the first, barred index and column `I` from the second, is
`(g_{IJ̄})⁻¹`. -/
lemma toSquareMatrix_inverseT {c : Fin 2 → C} (hbar : S.bar (c 0) = c 1) (M : S.Tensor c) :
    S.toSquareMatrix (S.inverseT M hbar) (S.bar_tau_of_bar hbar) =
      (S.toSquareMatrix M hbar)⁻¹.submatrix
        (Equiv.cast (hbar ▸ S.barIdx_eq (c 0)) ∘
          (dualIdxEquiv (rfl : S.τ (c 1) = S.τ (c 1))).symm)
        (Equiv.cast (hbar ▸ S.barIdx_eq (c 0)) ∘
          (dualIdxEquiv (rfl : S.τ (c 1) = S.τ (c 1))).symm) := by
  rcases subsingleton_or_nontrivial k with hk | hk
  · exact Subsingleton.elim _ _
  conv_lhs => unfold toSquareMatrix
  rw [toMatrix_inverseT]
  dsimp +instances only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Matrix.reindex_apply, Matrix.submatrix_submatrix, Equiv.refl_symm, Equiv.coe_refl,
    Function.comp_id]
  exact congrArg _ (funext (S.dualIdxEquiv_bar_tau hbar))

/-- The inverse of a Hermitian tensor is Hermitian: if `(g_{IJ̄})* = g_{JĪ}`, then
`(g^{J̄I})* = g^{ĪJ}`. -/
lemma isSymm_toSesqForm_inverseT {x y : C} {c : Fin 2 → C} (hbar : S.bar (c 0) = c 1)
    (hx : S.τ x = c 0) (hy : S.τ y = S.τ (c 1)) {M : S.Tensor c}
    (hM : (S.toSesqForm x M hbar hx).IsSymm) :
    (S.toSesqForm y (S.inverseT M hbar) (S.bar_tau_of_bar hbar) hy).IsSymm := by
  rw [S.isSymm_toSesqForm_iff_toSquareMatrix_isHermitian (S.bar_tau_of_bar hbar) hy,
    toSquareMatrix_inverseT]
  exact ((S.isSymm_toSesqForm_iff_toSquareMatrix_isHermitian hbar hx M).1 hM).inv.submatrix _

end ConjTensorSpecies

/-!

## B. Positive-definiteness

Over a field, the matrix `(g_{IJ̄})` of a positive-definite `g`, such as a Kähler metric, is
invertible (`isUnit_det_toSquareMatrix_of_isPosDef`), so `g` has a true inverse. That inverse is
again positive-definite (`isPosDef_toSesqForm_inverseT`): `g^{J̄I} t_J̄ t̄_I > 0` for every
covector `t ≠ 0`.

-/

namespace ConjTensorSpecies

open Tensor HasContrDualBases

variable {k : Type} [Field k] [StarRing k] {C : Type} {G : Type} [Group G]
    {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Basis (basisIdx c) k (V c)}
    (S : ConjTensorSpecies k C G V basisIdx rep b) [HasContrDualBases S.toTensorSpecies]

section PosDef

variable [PartialOrder k]

/-- The inverse of a positive-definite tensor is positive-definite: `g^{J̄I} t_J̄ t̄_I > 0` for
every covector `t ≠ 0`. For a Kähler metric and `t_J̄ = (D_J W)*`, this makes the F-term
`g^{J̄I} (D_J W)* D_I W` of the N = 1 potential non-negative. -/
lemma isPosDef_toSesqForm_inverseT {x y : C} {c : Fin 2 → C} (hbar : S.bar (c 0) = c 1)
    (hx : S.τ x = c 0) (hy : S.τ y = S.τ (c 1)) {M : S.Tensor c}
    (hM : (S.toSesqForm x M hbar hx).IsPosDef) :
    (S.toSesqForm y (S.inverseT M hbar) (S.bar_tau_of_bar hbar) hy).IsPosDef := by
  rw [S.isPosDef_toSesqForm_iff_toSquareMatrix_posDef (S.bar_tau_of_bar hbar) hy,
    toSquareMatrix_inverseT]
  exact ((S.isPosDef_toSesqForm_iff_toSquareMatrix_posDef hbar hx M).1 hM).inv.submatrix
    ((Equiv.injective _).comp (Equiv.injective _))

end PosDef

end ConjTensorSpecies

end
end
