/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Relativity.Tensors.Conjugation.Basic
public import Physlib.Relativity.Tensors.Contraction.UnitTensorContraction

/-!

# The inverse of a rank-two tensor

The inverse `g^{J̄I}` of a tensor `g_{IJ̄}` with one index and one conjugate index, such as a
Hermitian metric, and the linear equivalence that contracts an index with `g`.

## i. Overview

The inverse of a tensor `g_{IJ̄}` is the tensor `g^{J̄I}`, with two upper indices, for which
`g_{IJ̄} g^{J̄K} = δ_I^K` and `g^{J̄I} g_{IK̄} = δ^J̄_K̄`.

The colours of the inverse are `![τ (c 1), τ (c 0)]`, so its barred index comes first, `g^{J̄I}`.
The usual `g^{IJ̄}` is the same tensor with its two indices swapped. With the barred index first,
`g_{IJ̄} g^{J̄K}` contracts adjacent indices, so the contraction laws need no reordering of the
inverse. The matrix `(g^{J̄I})`, with row `J` and column `I`, is the inverse of the matrix
`(g_{IJ̄})`. `inverseT` is defined by this matrix inversion and is zero when `(g_{IJ̄})` is not
invertible. The inverse of a Hermitian `g` is Hermitian (A), and the inverse of a
positive-definite `g` is positive-definite (B). When `(g_{IJ̄})` is invertible, the two contraction
laws hold and the inverse is unique (C). Then contracting an index with `g` is a linear
equivalence whose inverse contracts with `g^{J̄I}` (D).

## ii. Key results

- `ConjTensorSpecies.inverseT` is the inverse `g^{J̄I}` of a tensor `g_{IJ̄}`.
- `ConjTensorSpecies.toSquareMatrix_inverseT` says that the matrix `(g^{J̄I})` is `(g_{IJ̄})⁻¹`.
- `ConjTensorSpecies.isSymm_toSesqForm_inverseT` and
  `ConjTensorSpecies.isPosDef_toSesqForm_inverseT` say that the inverse of a Hermitian or
  positive-definite `g` is again Hermitian or positive-definite.
- `ConjTensorSpecies.contractInnerT_inverseT` and `ConjTensorSpecies.inverseT_contractInnerT` are
  the contraction laws `g_{IJ̄} g^{J̄K} = δ_I^K` and `g^{J̄I} g_{IK̄} = δ^J̄_K̄`.
- `ConjTensorSpecies.eq_inverseT_of_contractInnerT_eq_unitTensor` says that the inverse is unique.
- `ConjTensorSpecies.toConjDualAtIndex` contracts an index with `g`, as a linear equivalence
  whose inverse contracts with `g^{J̄I}`.

## iii. Table of contents

- A. The inverse
- B. Positive-definiteness
- C. The contraction laws
- D. Changing an index to its conjugate dual

## iv. References

- `Matrix.inv` and `Matrix.inv_def`, in `Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean`;
- `Matrix.PosDef.inv`, in `Mathlib/LinearAlgebra/Matrix/PosDef.lean`.

-/

@[expose] public section
noncomputable section

open Module TensorSpecies TensorSpecies.Tensor

namespace ConjTensorSpecies

open Tensor HasContrDualBases
open scoped Matrix

variable {k : Type} [CommRing k] [StarRing k] {C : Type} {G : Type} [Group G]
    {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Basis (basisIdx c) k (V c)}
    (S : ConjTensorSpecies k C G V basisIdx rep b) [HasContrDualBases S.toTensorSpecies]

/-!

## A. The inverse

-/

/-- The inverse `g^{J̄I}` of a tensor `g_{IJ̄}`. Its matrix, with row `J` and column `I`, is
`(g_{IJ̄})⁻¹`, and it is zero when `(g_{IJ̄})` is not invertible. -/
def inverseT {c : Fin 2 → C} (M : S.Tensor c) (hbar : S.bar (c 0) = c 1 := by rfl) :
    S.Tensor ![S.τ (c 1), S.τ (c 0)] :=
  fromMatrixT (S := S.toTensorSpecies) (S.τ (c 1)) (S.τ (c 0))
    ((S.toSquareMatrix M hbar)⁻¹.submatrix
      (Equiv.cast (hbar ▸ S.barIdx_eq (c 0)) ∘ (dualIdxEquiv (rfl : S.τ (c 1) = S.τ (c 1))).symm)
      (dualIdxEquiv (S.τ_τ_apply (c 0))))

/-- The component `g^{J̄I}` is the entry `(J, I)` of `(g_{IJ̄})⁻¹`. The upper indices `J̄` and `I`
are labelled by the lower indices `J` and `I` they contract with. -/
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

/-- The inverse of a Hermitian tensor is Hermitian. If `(g_{IJ̄})* = g_{JĪ}`, then
`(g^{J̄I})* = g^{ĪJ}`. -/
lemma isSymm_toSesqForm_inverseT {x y : C} {c : Fin 2 → C} (hbar : S.bar (c 0) = c 1)
    (hx : S.τ x = c 0) (hy : S.τ y = S.τ (c 1)) {M : S.Tensor c}
    (hM : (S.toSesqForm x M hbar hx).IsSymm) :
    (S.toSesqForm y (S.inverseT M hbar) (S.bar_tau_of_bar hbar) hy).IsSymm := by
  rw [S.isSymm_toSesqForm_iff_toSquareMatrix_isHermitian (S.bar_tau_of_bar hbar) hy,
    toSquareMatrix_inverseT]
  exact ((S.isSymm_toSesqForm_iff_toSquareMatrix_isHermitian hbar hx M).1 hM).inv.submatrix _

/-!

## B. Positive-definiteness

Over a field, the matrix `(g_{IJ̄})` of a positive-definite `g` is invertible
(`isUnit_det_toSquareMatrix_of_isPosDef`), so `g` has a true inverse and the contraction laws of C
hold for it. That inverse is again positive-definite (`isPosDef_toSesqForm_inverseT`).

-/

section PosDef

variable {k : Type} [Field k] [StarRing k] [PartialOrder k] {C : Type} {G : Type} [Group G]
    {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Basis (basisIdx c) k (V c)}
    (S : ConjTensorSpecies k C G V basisIdx rep b) [HasContrDualBases S.toTensorSpecies]

/-- The inverse of a positive-definite tensor is positive-definite, so `g^{J̄I} t_J̄ t̄_I > 0` for
every covector `t ≠ 0`. -/
lemma isPosDef_toSesqForm_inverseT {x y : C} {c : Fin 2 → C} (hbar : S.bar (c 0) = c 1)
    (hx : S.τ x = c 0) (hy : S.τ y = S.τ (c 1)) {M : S.Tensor c}
    (hM : (S.toSesqForm x M hbar hx).IsPosDef) :
    (S.toSesqForm y (S.inverseT M hbar) (S.bar_tau_of_bar hbar) hy).IsPosDef := by
  rw [S.isPosDef_toSesqForm_iff_toSquareMatrix_posDef (S.bar_tau_of_bar hbar) hy,
    toSquareMatrix_inverseT]
  exact ((S.isPosDef_toSesqForm_iff_toSquareMatrix_posDef hbar hx M).1 hM).inv.submatrix
    ((Equiv.injective _).comp (Equiv.injective _))

end PosDef

/-!

## C. The contraction laws

When the matrix `(g_{IJ̄})` is invertible, `g^{J̄I}` satisfies both contraction laws, and it is the
only tensor that satisfies the first. The unit tensor `δ` is defined over `RCLike` scalars, so
sections C and D use them.

-/

section RCLike

variable {k : Type} [RCLike k] {C : Type} {G : Type} [Group G]
    {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Basis (basisIdx c) k (V c)}
    (S : ConjTensorSpecies k C G V basisIdx rep b) [HasContrDualBases S.toTensorSpecies]

/-- If the matrix `(g_{IJ̄})` is invertible, `g_{IJ̄} g^{J̄K} = δ_I^K`. The first colour of the unit
tensor is renamed from `τ (τ (cs 0))` to `cs 0`. -/
lemma contractInnerT_inverseT {cs : Fin 2 → C} (hbar : S.bar (cs 0) = cs 1) (M : S.Tensor cs)
    (hM : IsUnit (S.toSquareMatrix M hbar).det) :
    contractInnerT rfl M (S.inverseT M hbar) =
      permT id (IsReindexing.unitTensor_of_tau_eq (S.τ_τ_apply (cs 0)))
        (unitTensor (S := S.toTensorSpecies) (S.τ (cs 0))) := by
  refine toMatrix_injective ((S.toMatrix_contractInnerT_eq_toSquareMatrix_mul hbar rfl M _).trans
    (Eq.trans ?_
      (toMatrix_permT_unitTensor (S := S.toTensorSpecies) (σ := id) _ (fun _ => rfl) _).symm))
  rw [toMatrix_inverseT]
  dsimp +instances only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ext x y
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, Function.comp_apply, id_eq,
    Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  rw [← Matrix.mul_apply, Matrix.mul_nonsing_inv _ hM, Matrix.one_apply, Matrix.one_apply]
  refine if_congr ?_ rfl rfl
  simp only [dualIdxEquiv_apply, basisIdxCongr, Equiv.cast_apply]
  constructor <;> rintro rfl <;> simp

/-- If the matrix `(g_{IJ̄})` is invertible, `g^{J̄I} g_{IK̄} = δ^J̄_K̄`. -/
lemma inverseT_contractInnerT {cs : Fin 2 → C} (hbar : S.bar (cs 0) = cs 1) (M : S.Tensor cs)
    (hM : IsUnit (S.toSquareMatrix M hbar).det) :
    contractInnerT (S.τ_τ_apply (cs 0)) (S.inverseT M hbar) M =
      unitTensor (S := S.toTensorSpecies) (cs 1) :=
  (contractInnerT_eq_unitTensor_comm rfl _ (Equiv.cast (hbar ▸ S.barIdx_eq (cs 0))).symm M _
    (S.contractInnerT_inverseT hbar M hM)).trans (permT_id_self _)

/-- If `(g_{IJ̄})` is invertible and `g_{IJ̄} t^{J̄K} = δ_I^K`, then `t` is the inverse
`g^{J̄K}`. -/
lemma eq_inverseT_of_contractInnerT_eq_unitTensor {cs : Fin 2 → C} (hbar : S.bar (cs 0) = cs 1)
    (M : S.Tensor cs) (hM : IsUnit (S.toSquareMatrix M hbar).det)
    {t : S.Tensor ![S.τ (cs 1), S.τ (cs 0)]}
    (ht : contractInnerT rfl M t =
      permT id (IsReindexing.unitTensor_of_tau_eq (S.τ_τ_apply (cs 0)))
        (unitTensor (S := S.toTensorSpecies) (S.τ (cs 0)))) :
    t = S.inverseT M hbar :=
  contractInnerT_right_injective rfl (Equiv.cast (hbar ▸ S.barIdx_eq (cs 0))).symm M hM
    (ht.trans (S.contractInnerT_inverseT hbar M hM).symm)

/-!

## D. Changing an index to its conjugate dual

When the matrix `(g_{IJ̄})` is invertible, contracting an index `I` of a tensor with `g` changes it
to its conjugate dual `J̄`, and contracting with `g^{J̄I}` changes it back. The two contraction laws
of C make these mutually inverse. For a metric `g_{IJ̄}` with lower indices this lowers an index.
If `g` has upper indices, the same map raises one.

-/

/-- The linear equivalence that contracts slot `i` of a tensor with the first index of `M`, when
the matrix `(M_{IJ̄})` is invertible. Slot `i` changes from `τ (cs 0)` to its conjugate dual
`cs 1`, and the inverse contracts with `inverseT M`. For a metric `g_{IJ̄}` this lowers an
unbarred index to a barred one, `t_{J̄} = g_{IJ̄} t^I`. -/
def toConjDualAtIndex {cs : Fin 2 → C} (M : S.Tensor cs) (hbar : S.bar (cs 0) = cs 1)
    (hM : IsUnit (S.toSquareMatrix M hbar).det) :
    {n : ℕ} → {c : Fin n → C} → (i : Fin n) → (he : c i = S.τ (cs 0)) →
      S.Tensor c ≃ₗ[k] S.Tensor (Function.update c i (cs 1))
  | 0, _, i, _ => i.elim0
  | _ + 1, _, i, he =>
    crossToSlotEquiv i he ((congrArg S.τ he).trans (S.τ_τ_apply (cs 0))) rfl M (S.inverseT M hbar)
      (S.contractInnerT_inverseT hbar M hM)
      ((S.inverseT_contractInnerT hbar M hM).trans (permT_id_self _).symm)

/-- `toConjDualAtIndex` is the contraction `crossToSlot` of slot `i` with the first index of `M`. -/
@[simp]
lemma toConjDualAtIndex_apply {nA : ℕ} {c : Fin (nA + 1) → C} {cs : Fin 2 → C} (M : S.Tensor cs)
    (hbar : S.bar (cs 0) = cs 1) (hM : IsUnit (S.toSquareMatrix M hbar).det)
    (i : Fin (nA + 1)) (he : c i = S.τ (cs 0)) (t : S.Tensor c) :
    S.toConjDualAtIndex M hbar hM i he t =
      crossToSlot i 0 ((congrArg S.τ he).trans (S.τ_τ_apply (cs 0))) M t :=
  rfl

/-- The inverse of `toConjDualAtIndex` is the contraction `crossToSlotInv` of slot `i` with the
first index of `inverseT M`. -/
@[simp]
lemma toConjDualAtIndex_symm_apply {nA : ℕ} {c : Fin (nA + 1) → C} {cs : Fin 2 → C}
    (M : S.Tensor cs) (hbar : S.bar (cs 0) = cs 1) (hM : IsUnit (S.toSquareMatrix M hbar).det)
    (i : Fin (nA + 1)) (he : c i = S.τ (cs 0)) (t : S.Tensor (Function.update c i (cs 1))) :
    (S.toConjDualAtIndex M hbar hM i he).symm t =
      crossToSlotInv (S := S.toTensorSpecies) (d := cs 1) i he rfl (S.inverseT M hbar) t :=
  rfl

end RCLike

end ConjTensorSpecies
end
end
