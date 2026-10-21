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
metric, and its contraction laws.

## i. Overview

The inverse of a Kähler metric `g_{IJ̄}` is the tensor `g^{J̄I}` with two upper indices,

`g_{IJ̄} g^{J̄K} = δ_I^K`, `g^{J̄I} g_{IK̄} = δ^J̄_K̄`.

Convention: the colours of the inverse are `![τ (c 1), τ (c 0)]`, so in slot order its barred index
comes first, `g^{J̄I}`. `inverseT` defines it by matrix inversion: the matrix `(g^{J̄I})` is the
inverse of `(g_{IJ̄})`. It is zero when `(g_{IJ̄})` is not invertible. The inverse of a Hermitian
`g` is Hermitian (A) and of a positive-definite `g` positive-definite (B). When `(g_{IJ̄})` is
invertible, the two contraction laws above hold and the inverse is unique (C). The laws are the
hypotheses of `crossToSlotEquiv`, so `g` and its inverse lower and raise indices.

## ii. Key results

- `ConjTensorSpecies.inverseT` is the inverse `g^{J̄I}` of a tensor `g_{IJ̄}`.
- `ConjTensorSpecies.toSquareMatrix_inverseT`: the matrix `(g^{J̄I})` is `(g_{IJ̄})⁻¹`.
- `ConjTensorSpecies.isSymm_toSesqForm_inverseT` and
  `ConjTensorSpecies.isPosDef_toSesqForm_inverseT`: the inverse of a Hermitian or positive-definite
  `g` is Hermitian or positive-definite.
- `ConjTensorSpecies.matMulT_inverseT` and `ConjTensorSpecies.inverseT_matMulT`:
  `g_{IJ̄} g^{J̄K} = δ_I^K` and `g^{J̄I} g_{IK̄} = δ^J̄_K̄`, products in the sense of `matMulT`.
- `ConjTensorSpecies.eq_inverseT`: the inverse is unique.

## iii. Table of contents

- A. The inverse
  - A.1. The inverse and its matrix
  - A.2. Multiplication by `g`
- B. Positive-definiteness
- C. The contraction laws

## iv. References

- `Matrix.nonsing_inv`, in `Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean`;
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

/-- The components of the inverse: `g^{J̄I}` is entry `(J, I)` of the inverse of the matrix
`(g_{IJ̄})`, each upper label read as the lower label it contracts with. -/
lemma toMatrix_inverseT {c : Fin 2 → C} (hbar : S.bar (c 0) = c 1) (M : S.Tensor c) :
    toMatrix (S.inverseT M hbar) =
      (S.toSquareMatrix M hbar)⁻¹.submatrix
        (Equiv.cast (hbar ▸ S.barIdx_eq (c 0)) ∘
          (dualIdxEquiv (rfl : S.τ (c 1) = S.τ (c 1))).symm)
        (dualIdxEquiv (S.τ_τ_apply (c 0))) :=
  toMatrix_fromMatrixT _ _ _

/-- The matrix `(g^{J̄I})` of the inverse is `(g_{IJ̄})⁻¹`, rows and columns relabelled alike.
When `(g_{IJ̄})` is invertible this gives `∑_I g^{J̄I} g_{IK̄} = δ_{JK}`. -/
lemma toSquareMatrix_inverseT {c : Fin 2 → C} (hbar : S.bar (c 0) = c 1) (M : S.Tensor c) :
    S.toSquareMatrix (S.inverseT M hbar) (S.bar_tau_of_bar hbar) =
      (S.toSquareMatrix M hbar)⁻¹.submatrix
        (Equiv.cast (hbar ▸ S.barIdx_eq (c 0)) ∘
          (dualIdxEquiv (rfl : S.τ (c 1) = S.τ (c 1))).symm)
        (Equiv.cast (hbar ▸ S.barIdx_eq (c 0)) ∘
          (dualIdxEquiv (rfl : S.τ (c 1) = S.τ (c 1))).symm) := by
  rcases subsingleton_or_nontrivial k with hk | hk
  · exact Subsingleton.elim _ _
  obtain ⟨a, d, rfl⟩ : ∃ a d, c = ![a, d] := ⟨c 0, c 1, by funext i; fin_cases i <;> rfl⟩
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
  have hM' := (S.isSymm_toSesqForm_iff_toSquareMatrix_isHermitian hbar hx M).1 hM
  refine (S.isSymm_toSesqForm_iff_toSquareMatrix_isHermitian (S.bar_tau_of_bar hbar) hy
    (S.inverseT M hbar)).2 ?_
  rw [toSquareMatrix_inverseT]
  exact hM'.inv.submatrix _

/-!

### A.2. Multiplication by `g`

-/

/-- The matrix of `g_{IJ̄} t^{J̄K}` is `(g_{IJ̄})` times the matrix of `t`, with the row label `J̄`
of `t` read as `J`. -/
lemma toMatrix_matMulT_eq_toSquareMatrix_mul {cs : Fin 2 → C} {e : C}
    (hbar : S.bar (cs 0) = cs 1) (M : S.Tensor cs) (t : S.Tensor ![S.τ (cs 1), e]) :
    toMatrix (matMulT rfl M t) =
      S.toSquareMatrix M hbar * (toMatrix t).submatrix
        (dualIdxEquiv (rfl : S.τ (cs 1) = S.τ (cs 1)) ∘
          (Equiv.cast (hbar ▸ S.barIdx_eq (cs 0))).symm) (id : basisIdx e → _) := by
  refine (toMatrix_matMulT rfl M t).trans ?_
  rw [S.toMatrix_eq_submatrix_toSquareMatrix hbar M]
  exact Matrix.submatrix_id_mul_right _ (t.toMatrix.submatrix (dualIdxEquiv rfl) id) id
    (Equiv.cast (hbar ▸ S.barIdx_eq (cs 0)))

/-- If the matrix `(g_{IJ̄})` is invertible, `t ↦ g_{IJ̄} t^{J̄K}` is injective. -/
lemma matMulT_right_injective {cs : Fin 2 → C} {c : C} (hbar : S.bar (cs 0) = cs 1)
    (M : S.Tensor cs) (hM : IsUnit (S.toSquareMatrix M hbar).det) :
    Function.Injective (matMulT rfl M (ds := ![S.τ (cs 1), c])) := by
  intro t t' h
  have h := congrArg toMatrix h
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
invertible (`Matrix.PosDef.isUnit`), so `g` has a true inverse and the contraction laws of C hold
for it. That inverse is again positive-definite (`isPosDef_toSesqForm_inverseT`):
`g^{J̄I} t_J̄ t̄_I > 0` for every covector `t ≠ 0`.

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
  have hM' := (S.isPosDef_toSesqForm_iff_toSquareMatrix_posDef hbar hx M).1 hM
  refine (S.isPosDef_toSesqForm_iff_toSquareMatrix_posDef (S.bar_tau_of_bar hbar) hy
    (S.inverseT M hbar)).2 ?_
  rw [toSquareMatrix_inverseT]
  exact hM'.inv.submatrix ((Equiv.injective _).comp (Equiv.injective _))

end PosDef

end ConjTensorSpecies

/-!

## C. The contraction laws

When the matrix `(g_{IJ̄})` is invertible, `g^{J̄I}` is the inverse of `g` under contraction,

`g_{IJ̄} g^{J̄K} = δ_I^K`, `g^{J̄I} g_{IK̄} = δ^J̄_K̄`

(`matMulT_inverseT`, `inverseT_matMulT`), each a product `matMulT` of two rank-two tensors.
By `toMatrix_matMulT` these are `N N⁻¹ = 1` and `N⁻¹ N = 1` for `N = (g_{IJ̄})`. Since
multiplication by `g` is injective (`matMulT_right_injective`), `g^{J̄K}` is the only tensor
satisfying the first law (`eq_inverseT`). The unit tensor `δ` is defined over `RCLike` scalars, so
this section works over `RCLike` scalars.

-/

namespace ConjTensorSpecies

open Tensor HasContrDualBases
open scoped Matrix

variable {k : Type} [RCLike k] {C : Type} {G : Type} [Group G]
    {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Basis (basisIdx c) k (V c)}
    (S : ConjTensorSpecies k C G V basisIdx rep b) [HasContrDualBases S.toTensorSpecies]

/-- `g_{IJ̄} g^{J̄K} = δ_I^K`, when the matrix `(g_{IJ̄})` is invertible. The unit tensor at
`τ (cs 0)` has colours `![τ (τ (cs 0)), τ (cs 0)]`, recoloured here to `![cs 0, τ (cs 0)]`. -/
lemma matMulT_inverseT {cs : Fin 2 → C} (hbar : S.bar (cs 0) = cs 1) (M : S.Tensor cs)
    (hM : IsUnit (S.toSquareMatrix M hbar).det) :
    matMulT rfl M (S.inverseT M hbar) =
      permT id (IsReindexing.unitTensor_pair (S.τ_τ_apply (cs 0)))
        (unitTensor (S := S.toTensorSpecies) (S.τ (cs 0))) := by
  refine toMatrix_injective ((S.toMatrix_matMulT_eq_toSquareMatrix_mul hbar M _).trans (Eq.trans ?_
    (toMatrix_permT_unitTensor (S := S.toTensorSpecies) (σ := id) _ (fun _ => rfl) _).symm))
  rw [toMatrix_inverseT]
  ext x y
  -- `submatrix_apply` keys through the `![…]` colour lists only with this option.
  set_option backward.isDefEq.respectTransparency false in
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
      unitTensor (S := S.toTensorSpecies) (cs 1) := by
  refine toMatrix_injective ((toMatrix_matMulT _ _ M).trans
    (Eq.trans ?_ (toMatrix_unitTensor (S := S.toTensorSpecies) (cs 1)).symm))
  rw [toMatrix_inverseT, S.toMatrix_eq_submatrix_toSquareMatrix hbar M,
    Matrix.submatrix_submatrix, Function.id_comp, Function.comp_id]
  dsimp +instances only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Matrix.submatrix_mul_equiv, Matrix.nonsing_inv_mul _ hM]
  ext x y
  simp only [Matrix.submatrix_apply, Function.comp_apply, Matrix.one_apply]
  refine if_congr ?_ rfl rfl
  rw [EmbeddingLike.apply_eq_iff_eq]
  simp only [dualIdxEquiv, Equiv.symm_trans_apply, Equiv.symm_symm]
  rfl

/-- The inverse is unique: if `(g_{IJ̄})` is invertible and `g_{IJ̄} t^{J̄K} = δ_I^K`, then `t` is
the inverse `g^{J̄K}`. -/
lemma eq_inverseT {cs : Fin 2 → C} (hbar : S.bar (cs 0) = cs 1) (M : S.Tensor cs)
    (hM : IsUnit (S.toSquareMatrix M hbar).det) {t : S.Tensor ![S.τ (cs 1), S.τ (cs 0)]}
    (ht : matMulT rfl M t =
      permT id (IsReindexing.unitTensor_pair (S.τ_τ_apply (cs 0)))
        (unitTensor (S := S.toTensorSpecies) (S.τ (cs 0)))) :
    t = S.inverseT M hbar :=
  S.matMulT_right_injective hbar M hM (ht.trans (S.matMulT_inverseT hbar M hM).symm)

end ConjTensorSpecies
end
end
