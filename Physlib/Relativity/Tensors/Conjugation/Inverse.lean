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

The inverse `g^{J̄I}` of a tensor `g_{IJ̄}` with one index and one conjugate index, such as a Kähler
metric, its contraction laws, and the lowering and raising of indices with `g` and `g^{J̄I}`.

## i. Overview

The inverse of a Kähler metric `g_{IJ̄}` is the tensor `g^{J̄I}` with two upper indices,

`g_{IJ̄} g^{J̄K} = δ_I^K`, `g^{J̄I} g_{IK̄} = δ^J̄_K̄`.

Convention: the colours of the inverse are `![τ (c 1), τ (c 0)]`, so its barred index comes first,
`g^{J̄I}`; the usual `g^{IJ̄}` is the same tensor with its two indices swapped. Barred first is the
order in which `g_{IJ̄} g^{J̄K}` contracts adjacent indices, so the contraction laws need no
reordering of the inverse. The matrix `(g^{J̄I})`, row `J` and column `I`, is the inverse of the
matrix `(g_{IJ̄})`; `inverseT` is defined by this matrix inversion and is zero when `(g_{IJ̄})` is
not invertible. The inverse of a Hermitian `g` is Hermitian (A) and of a positive-definite `g`
positive-definite (B). When `(g_{IJ̄})` is invertible, the two contraction laws above hold and the
inverse is unique (C), and `g` and `g^{J̄I}` lower and raise indices (D).

## ii. Key results

- `ConjTensorSpecies.inverseT` is the inverse `g^{J̄I}` of a tensor `g_{IJ̄}`.
- `ConjTensorSpecies.toSquareMatrix_inverseT`: the matrix `(g^{J̄I})`, row `J` and column `I`, is
  `(g_{IJ̄})⁻¹`.
- `ConjTensorSpecies.isSymm_toSesqForm_inverseT` and
  `ConjTensorSpecies.isPosDef_toSesqForm_inverseT`: the inverse of a Hermitian or positive-definite
  `g` is Hermitian or positive-definite.
- `ConjTensorSpecies.matMulT_inverseT` and `ConjTensorSpecies.inverseT_matMulT`:
  `g_{IJ̄} g^{J̄K} = δ_I^K` and `g^{J̄I} g_{IK̄} = δ^J̄_K̄`, products in the sense of `matMulT`.
- `ConjTensorSpecies.eq_inverseT_of_matMulT_eq_unitTensor`: the inverse is unique.
- `ConjTensorSpecies.isUnit_det_toSquareMatrix_of_isPosDef`: over a field, the matrix of a
  positive-definite `g` is invertible.
- `ConjTensorSpecies.lowerEquivT`: lowering an index with `g` and raising it with `g^{J̄I}`.

## iii. Table of contents

- A. The inverse
  - A.1. The inverse and its matrix
  - A.2. Multiplication by `g`
- B. Positive-definiteness
- C. The contraction laws
- D. Lowering and raising indices

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

/-!

### A.1. The inverse and its matrix

-/

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
`(g_{IJ̄})⁻¹`. When `(g_{IJ̄})` is invertible, `∑_I g^{J̄I} g_{IK̄} = δ_{JK}`. -/
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

/-!

### A.2. Multiplication by `g`

-/

/-- The matrix of `g_{IJ̄} t^{J̄K}` is the matrix product `(g_{IJ̄}) (t^{J̄K})`, `∑_J g_{IJ̄}
t^{J̄K}`, the summed index `J̄` of `t` labelled by `J`. -/
lemma toMatrix_matMulT_eq_toSquareMatrix_mul {cs ds : Fin 2 → C} (hbar : S.bar (cs 0) = cs 1)
    (h : S.τ (cs 1) = ds 0) (M : S.Tensor cs) (t : S.Tensor ds) :
    toMatrix (matMulT h M t) =
      S.toSquareMatrix M hbar * (toMatrix t).submatrix
        (dualIdxEquiv h ∘ (Equiv.cast (hbar ▸ S.barIdx_eq (cs 0))).symm)
        (id : basisIdx (ds 1) → _) := by
  refine (toMatrix_matMulT h M t).trans ?_
  rw [S.toMatrix_eq_submatrix_toSquareMatrix hbar M]
  exact Matrix.submatrix_id_mul_right _ (t.toMatrix.submatrix (dualIdxEquiv h) id) id
    (Equiv.cast (hbar ▸ S.barIdx_eq (cs 0)))

/-- If the matrix `(g_{IJ̄})` is invertible, `t ↦ g_{IJ̄} t^{J̄K}` is injective. -/
lemma matMulT_right_injective {cs ds : Fin 2 → C} (hbar : S.bar (cs 0) = cs 1)
    (h : S.τ (cs 1) = ds 0) (M : S.Tensor cs) (hM : IsUnit (S.toSquareMatrix M hbar).det) :
    Function.Injective (matMulT h M) := by
  intro t t' htt
  have h := congrArg toMatrix htt
  rw [S.toMatrix_matMulT_eq_toSquareMatrix_mul hbar,
    S.toMatrix_matMulT_eq_toSquareMatrix_mul hbar] at h
  let := (S.toSquareMatrix M hbar).invertibleOfIsUnitDet hM
  have h := Matrix.mul_right_injective_of_invertible (S.toSquareMatrix M hbar) h
  exact toMatrix_injective
    (Matrix.submatrix_injective ((Equiv.surjective _).comp (Equiv.surjective _))
      Function.surjective_id h)

end ConjTensorSpecies

/-!

## B. Positive-definiteness

Over a field, the matrix `(g_{IJ̄})` of a positive-definite `g`, such as a Kähler metric, is
invertible (`isUnit_det_toSquareMatrix_of_isPosDef`), so `g` has a true inverse and the
contraction laws of C hold for it. That inverse is again positive-definite
(`isPosDef_toSesqForm_inverseT`): `g^{J̄I} t_J̄ t̄_I > 0` for every covector `t ≠ 0`.

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

/-- Over a field, the matrix `(M_{IJ̄})` of a positive-definite tensor is invertible. -/
lemma isUnit_det_toSquareMatrix_of_isPosDef {x : C} {c : Fin 2 → C} (hbar : S.bar (c 0) = c 1)
    (hx : S.τ x = c 0) {M : S.Tensor c} (hM : (S.toSesqForm x M hbar hx).IsPosDef) :
    IsUnit (S.toSquareMatrix M hbar).det :=
  (Matrix.isUnit_iff_isUnit_det _).1
    ((S.isPosDef_toSesqForm_iff_toSquareMatrix_posDef hbar hx M).1 hM).isUnit

end PosDef

end ConjTensorSpecies

/-!

## C. The contraction laws

When the matrix `(g_{IJ̄})` is invertible, `g^{J̄I}` is the inverse of `g` under contraction,

`g_{IJ̄} g^{J̄K} = δ_I^K`, `g^{J̄I} g_{IK̄} = δ^J̄_K̄`

(`matMulT_inverseT`, `inverseT_matMulT`), and it is the only tensor with the first property
(`eq_inverseT_of_matMulT_eq_unitTensor`). The unit tensor `δ` is defined over `RCLike` scalars, so
this section and D are stated over them.

-/

namespace ConjTensorSpecies

open Tensor HasContrDualBases
open scoped Matrix

variable {k : Type} [RCLike k] {C : Type} {G : Type} [Group G]
    {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Basis (basisIdx c) k (V c)}
    (S : ConjTensorSpecies k C G V basisIdx rep b) [HasContrDualBases S.toTensorSpecies]

/-- `g_{IJ̄} g^{J̄K} = δ_I^K`, when the matrix `(g_{IJ̄})` is invertible. On the right, the unit
tensor at the colour of `K` has the colour of its first index `I` renamed from `τ (τ (cs 0))` to
`cs 0` (`IsReindexing.unitTensor_of_tau_eq`). -/
lemma matMulT_inverseT {cs : Fin 2 → C} (hbar : S.bar (cs 0) = cs 1) (M : S.Tensor cs)
    (hM : IsUnit (S.toSquareMatrix M hbar).det) :
    matMulT rfl M (S.inverseT M hbar) =
      permT id (IsReindexing.unitTensor_of_tau_eq (S.τ_τ_apply (cs 0)))
        (unitTensor (S := S.toTensorSpecies) (S.τ (cs 0))) := by
  refine toMatrix_injective ((S.toMatrix_matMulT_eq_toSquareMatrix_mul hbar rfl M _).trans
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

/-- `g^{J̄I} g_{IK̄} = δ^J̄_K̄`, when the matrix `(g_{IJ̄})` is invertible. -/
lemma inverseT_matMulT {cs : Fin 2 → C} (hbar : S.bar (cs 0) = cs 1) (M : S.Tensor cs)
    (hM : IsUnit (S.toSquareMatrix M hbar).det) :
    matMulT (S.τ_τ_apply (cs 0)) (S.inverseT M hbar) M =
      unitTensor (S := S.toTensorSpecies) (cs 1) :=
  (matMulT_eq_unitTensor_comm rfl _ (Equiv.cast (hbar ▸ S.barIdx_eq (cs 0))).symm M _
    (S.matMulT_inverseT hbar M hM)).trans (permT_id_self _)

/-- The inverse is unique: if `(g_{IJ̄})` is invertible and `g_{IJ̄} t^{J̄K} = δ_I^K`, then `t` is
the inverse `g^{J̄K}`. -/
lemma eq_inverseT_of_matMulT_eq_unitTensor {cs : Fin 2 → C} (hbar : S.bar (cs 0) = cs 1)
    (M : S.Tensor cs) (hM : IsUnit (S.toSquareMatrix M hbar).det)
    {t : S.Tensor ![S.τ (cs 1), S.τ (cs 0)]}
    (ht : matMulT rfl M t =
      permT id (IsReindexing.unitTensor_of_tau_eq (S.τ_τ_apply (cs 0)))
        (unitTensor (S := S.toTensorSpecies) (S.τ (cs 0)))) :
    t = S.inverseT M hbar :=
  S.matMulT_right_injective hbar rfl M hM (ht.trans (S.matMulT_inverseT hbar M hM).symm)

/-!

## D. Lowering and raising indices

When the matrix `(g_{IJ̄})` is invertible, contracting an upper index `I` of a tensor with `g`
lowers it to `J̄`, and contracting with `g^{J̄I}` raises it back. The two contraction laws of C make
these mutually inverse.

-/

/-- Lowering an index with `g_{IJ̄}`, `t^{…I…} ↦ g_{IJ̄} t^{…I…} = t_{…J̄…}`, as a linear
equivalence whose inverse raises it with `g^{J̄I}`, `t_{…J̄…} ↦ g^{J̄I} t_{…J̄…}`. Slot `i` of
`t` carries the upper index `I` (`he`) and `(g_{IJ̄})` is invertible (`hM`). Convention: `t`
contracts with the first index of `g`, so for a Kähler metric lowering a holomorphic index gives
an antiholomorphic one, `t_{J̄} = g_{IJ̄} t^I`. -/
def lowerEquivT {cs : Fin 2 → C} (M : S.Tensor cs) (hbar : S.bar (cs 0) = cs 1)
    (hM : IsUnit (S.toSquareMatrix M hbar).det) :
    {n : ℕ} → {c : Fin n → C} → (i : Fin n) → (he : c i = S.τ (cs 0)) →
      S.Tensor c ≃ₗ[k] S.Tensor (Function.update c i (cs 1))
  | 0, _, i, _ => i.elim0
  | _ + 1, _, i, he =>
    crossToSlotEquiv i he ((congrArg S.τ he).trans (S.τ_τ_apply (cs 0))) rfl M (S.inverseT M hbar)
      (S.matMulT_inverseT hbar M hM) ((S.inverseT_matMulT hbar M hM).trans (permT_id_self _).symm)

/-- Lowering is the contraction `crossToSlot` of slot `i` with the first index of `g`. -/
@[simp]
lemma lowerEquivT_apply {nA : ℕ} {c : Fin (nA + 1) → C} {cs : Fin 2 → C} (M : S.Tensor cs)
    (hbar : S.bar (cs 0) = cs 1) (hM : IsUnit (S.toSquareMatrix M hbar).det)
    (i : Fin (nA + 1)) (he : c i = S.τ (cs 0)) (t : S.Tensor c) :
    S.lowerEquivT M hbar hM i he t =
      crossToSlot i 0 ((congrArg S.τ he).trans (S.τ_τ_apply (cs 0))) M t :=
  rfl

/-- Raising is the contraction `crossToSlotInv` of slot `i` with the first index of `g^{J̄I}`. -/
@[simp]
lemma lowerEquivT_symm_apply {nA : ℕ} {c : Fin (nA + 1) → C} {cs : Fin 2 → C} (M : S.Tensor cs)
    (hbar : S.bar (cs 0) = cs 1) (hM : IsUnit (S.toSquareMatrix M hbar).det)
    (i : Fin (nA + 1)) (he : c i = S.τ (cs 0)) (t : S.Tensor (Function.update c i (cs 1))) :
    (S.lowerEquivT M hbar hM i he).symm t =
      crossToSlotInv (S := S.toTensorSpecies) (d := cs 1) i he rfl (S.inverseT M hbar) t :=
  rfl

end ConjTensorSpecies
end
end
