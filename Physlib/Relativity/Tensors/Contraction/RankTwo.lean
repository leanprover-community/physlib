/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Relativity.Tensors.Contraction.CrossToSlot
public import Physlib.Relativity.Tensors.ComponentIdx.Single
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
/-!

# The bilinear map and the product of rank-two tensors

The bilinear map of a rank-two tensor and the product of two rank-two tensors.

## i. Overview

A rank-two tensor `M` defines a bilinear map on one-slot tensors by contracting one argument into
each of its slots, `t, s ↦ M_{zw} tᶻ sʷ`. In the bases dual to the slots of `M` the matrix of this
map is the component matrix `toMatrix M`.

`contractInnerT A B` is the tensor `A_{μν} B^{νρ}`, in which the second index of `A` is contracted
with the first index of `B`. Its indices are `μ` and `ρ`, with colours `![cs 0, ds 1]`. The general
contraction `crossToEnd` gives the same tensor, but its colours are a composite of the two colour
lists. With `contractInnerT`, an identity such as `η_{μν} η^{νρ} = δ_μ^ρ` needs no renaming of the
colours of the product. For contraction-dual bases, the matrix of `A_{μν} B^{νρ}` is the matrix
product of `(A_{μν})` and `(B^{νρ})` (`toMatrix_contractInnerT`).

## ii. Key results

- `TensorSpecies.Tensor.toLinearMap₂` : the bilinear map `t, s ↦ M_{zw} tᶻ sʷ` of a rank-two
    tensor, with its component formula `toLinearMap₂_apply`.
- `TensorSpecies.Tensor.toMatrix₂_toLinearMap₂` : its matrix in the dual bases is the component
    matrix of `M`.
- `TensorSpecies.Tensor.contractInnerT` : the contraction `A_{μν} B^{νρ}` of two rank-two tensors.
- `TensorSpecies.Tensor.toMatrix_contractInnerT` : for contraction-dual bases, its matrix is the
    matrix product.

## iii. Table of contents

- A. Pairing a rank-two tensor with two vectors
- B. Contracting two rank-two tensors

## iv. References

* None.

-/

@[expose] public section

namespace TensorSpecies

variable {k : Type} [CommRing k] {C : Type} {G : Type} [Group G]
    {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Module.Basis (basisIdx c) k (V c)}
    {S : TensorSpecies k C G V basisIdx rep b}

namespace Tensor

/-!

## A. Pairing a rank-two tensor with two vectors

Contracting a vector into each slot of a rank-two tensor `M` gives a bilinear map. This holds for
any species: the only colour condition is duality, an argument contracts with a slot when its
colour is dual to the slot's. For a species without conjugation this map is the metric form
itself; a species with conjugation composes it with conjugation of one argument to get a
sesquilinear form (`ConjTensorSpecies.toSesqForm`).

-/

/-- The bilinear map `t, s ↦ M_{μν} tᵘ sᵛ` of a rank-two tensor: `t` fills the first index of `M`,
`s` the second. For the Minkowski metric this is the inner product `η_{μν} tᵘ sᵛ`. -/
noncomputable def toLinearMap₂ (x y : C) {cM : Fin 2 → C} (M : Tensor S cM)
    (hx : S.τ x = cM 0 := by rfl) (hy : S.τ y = cM 1 := by rfl) :
    Tensor S ![x] →ₗ[k] Tensor S ![y] →ₗ[k] k :=
  ((crossToEnd (0 : Fin 1) (0 : Fin 1)
    (by simp only [Function.update_self]; show S.τ (cM 1) = y; rw [← hy, S.τ_τ_apply])).comp
    (crossToSlot (0 : Fin 1) (0 : Fin 2) hx M)).compr₂ toScalar

/-- In components, the bilinear map is `∑_{μ,ν} M_{μν} tᵘ sᵛ`. -/
lemma toLinearMap₂_apply [HasContrDualBases S] {x y : C} {cM : Fin 2 → C} (hx : S.τ x = cM 0)
    (hy : S.τ y = cM 1) (M : Tensor S cM) (t : Tensor S ![x]) (s : Tensor S ![y]) :
    toLinearMap₂ x y M hx hy t s =
      ∑ w : basisIdx y, ∑ z : basisIdx x,
        (basis ![x]).repr t (ComponentIdx.single.symm z) *
          toMatrix M (HasContrDualBases.dualIdxEquiv hx z) (HasContrDualBases.dualIdxEquiv hy w) *
          (basis ![y]).repr s (ComponentIdx.single.symm w) := by
  nontriviality k
  set_option backward.isDefEq.respectTransparency false in
  rw [toLinearMap₂, LinearMap.compr₂_apply, LinearMap.comp_apply, toScalar_eq_repr,
    crossToEnd_basis_repr_eq_sum_dual]
  simp only [crossToSlot_basis_repr_eq_sum_dual, Finset.sum_mul]
  refine Fintype.sum_equiv (HasContrDualBases.dualIdxEquiv hy).symm _ _ fun w =>
    Finset.sum_congr rfl fun z _ => ?_
  rw [toMatrix_apply, Equiv.apply_symm_apply,
    HasContrDualBases.dualIdxEquiv_symm hy (by rw [← hy, S.τ_τ_apply])]
  congr 1
  · congr 2 with j <;> fin_cases j <;> rfl
  · congr 1 with j
    fin_cases j
    rfl

/-- On basis vectors, the bilinear map gives `M(e_μ, e_ν) = M_{μν}`, so its matrix is the component
matrix `(M_{μν})`. -/
lemma toMatrix₂_toLinearMap₂ [HasContrDualBases S] {x y : C} {cM : Fin 2 → C}
    (hx : S.τ x = cM 0) (hy : S.τ y = cM 1) (M : Tensor S cM) :
    LinearMap.toMatrix₂
      ((basis ![x]).reindex (ComponentIdx.single.trans (HasContrDualBases.dualIdxEquiv hx)))
      ((basis ![y]).reindex (ComponentIdx.single.trans (HasContrDualBases.dualIdxEquiv hy)))
      (toLinearMap₂ x y M hx hy) = toMatrix M := by
  ext z w
  rw [LinearMap.toMatrix₂_apply, toLinearMap₂_apply]
  simp [Finsupp.single_apply, -HasContrDualBases.dualIdxEquiv_apply]

/-!

## B. Contracting two rank-two tensors

-/

/-- The contraction `A_{μν} B^{νρ}` of the second index of `A` with the first index of `B`, whose
colours are dual by `h`. The result has the indices `μ` and `ρ`, in that order. -/
noncomputable def contractInnerT {cs ds : Fin 2 → C} (h : S.τ (cs 1) = ds 0) :
    Tensor S cs →ₗ[k] Tensor S ds →ₗ[k] Tensor S ![cs 0, ds 1] :=
  (crossToEnd (Fin.last 1) (0 : Fin 2) h).compr₂
    (permT id (IsReindexing.on_id.mpr fun j => by fin_cases j <;> rfl))

/-- `contractInnerT` is `crossToEnd` of the last index of `A` with the first index of `B`, with the
colours of the result renamed to `![cs 0, ds 1]`. -/
lemma contractInnerT_apply {cs ds : Fin 2 → C} (h : S.τ (cs 1) = ds 0) (a : Tensor S cs)
    (b : Tensor S ds) :
    contractInnerT h a b = permT id (IsReindexing.on_id.mpr fun j => by fin_cases j <;> rfl)
      (crossToEnd (Fin.last 1) (0 : Fin 2) h a b) :=
  rfl

/-- `crossToEnd` of the last index of `A` with the first index of `B` is `contractInnerT` with its
colours renamed. This is `contractInnerT_apply` read from right to left. -/
lemma crossToEnd_eq_permT_contractInnerT {cs ds : Fin 2 → C} (h : S.τ (cs 1) = ds 0)
    (a : Tensor S cs) (b : Tensor S ds) :
    crossToEnd (Fin.last 1) (0 : Fin 2) h a b =
      permT id (IsReindexing.on_id.mpr fun j => by fin_cases j <;> rfl) (contractInnerT h a b) := by
  rw [contractInnerT_apply, permT_permT]
  exact (permT_congr_eq_id _ _ _ rfl).symm

/-- The matrix of `A_{μν} B^{νρ}` is the matrix product of `(A_{μν})` and `(B^{νρ})`, with the
labels of `ν` in `B` matched to those in `A` by `dualIdxEquiv`. This is `toMatrix_crossToEnd_pair`
at general colour lists. -/
lemma toMatrix_contractInnerT [HasContrDualBases S] {cs ds : Fin 2 → C} (h : S.τ (cs 1) = ds 0)
    (a : Tensor S cs) (b : Tensor S ds) :
    toMatrix (contractInnerT h a b) =
      toMatrix a * (toMatrix b).submatrix (HasContrDualBases.dualIdxEquiv h) id := by
  obtain ⟨c0, c1, rfl⟩ : ∃ c0 c1, cs = ![c0, c1] := ⟨cs 0, cs 1, by funext i; fin_cases i <;> rfl⟩
  obtain ⟨c2, c3, rfl⟩ : ∃ c2 c3, ds = ![c2, c3] := ⟨ds 0, ds 1, by funext i; fin_cases i <;> rfl⟩
  ext y0 y3
  refine (permT_basis_repr_of_id (fun _ => rfl) _ _ _).trans ((congrArg _ ?_).trans
    (congrFun (congrFun (toMatrix_crossToEnd_pair h a b) y0) y3))
  funext i
  fin_cases i <;> rfl

/-- If the matrix `(M_{μν})`, made square by the label bijection `e`, is invertible, then
`t ↦ M_{μν} t^{νρ}` is injective. -/
lemma contractInnerT_right_injective [HasContrDualBases S] {cs ds : Fin 2 → C}
    (h : S.τ (cs 1) = ds 0) (e : basisIdx (cs 0) ≃ basisIdx (cs 1)) (M : Tensor S cs)
    (hM : IsUnit ((toMatrix M).submatrix id e).det) :
    Function.Injective (contractInnerT h M) := by
  intro t t' htt
  let := ((toMatrix M).submatrix id e).invertibleOfIsUnitDet hM
  have h' : (toMatrix M).submatrix id e *
        ((toMatrix t).submatrix (HasContrDualBases.dualIdxEquiv h) id).submatrix e id =
      (toMatrix M).submatrix id e *
        ((toMatrix t').submatrix (HasContrDualBases.dualIdxEquiv h) id).submatrix e id := by
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id,
      Matrix.submatrix_id_id, ← toMatrix_contractInnerT, ← toMatrix_contractInnerT, htt]
  exact toMatrix_injective (Matrix.submatrix_injective (Equiv.surjective _) Function.surjective_id
    (Matrix.submatrix_injective e.surjective Function.surjective_id
      (Matrix.mul_right_injective_of_invertible _ h')))

/-- `contractInnerT` commutes with the action of `G`. For a Lorentz transformation `Λ`,
`(Λ A)_{μν} (Λ B)^{νρ} = Λ (A_{μν} B^{νρ})`. -/
lemma contractInnerT_equivariant {cs ds : Fin 2 → C} (h : S.τ (cs 1) = ds 0) (g : G)
    (a : Tensor S cs) (b : Tensor S ds) :
    contractInnerT h (g • a) (g • b) = g • contractInnerT h a b := by
  rw [contractInnerT_apply, contractInnerT_apply, crossToEnd_equivariant, permT_equivariant]

end Tensor

end TensorSpecies
