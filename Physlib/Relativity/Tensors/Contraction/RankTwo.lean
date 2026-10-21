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

## i. Overview

A rank-two tensor `M` defines a bilinear map on one-slot tensors by contracting one argument into
each of its slots, `t, s ↦ M_{zw} tᶻ sʷ`. In the bases dual to the slots of `M` the matrix of this
map is the component matrix `toMatrix M`.

Two rank-two tensors multiply like matrices. `matMulT h a b` contracts the second index of `a` with
the first index of `b`, `a_{IJ} b^{JK}`, where `h : S.τ (cs 1) = ds 0` records that the two indices
are dual. The result carries the colours `![cs 0, ds 1]` of the surviving indices `I` and `K`.
`crossToEnd`, which contracts at any slots and ranks, gives the same tensor at the colour list
`Fin.append (cs ∘ (Fin.last 1).succAbove) (ds ∘ (0 : Fin 2).succAbove)`, which equals
`![cs 0, ds 1]` only propositionally. `matMulT` recolours once, so that statements about products,
such as `g_{IJ̄} g^{J̄K} = δ_I^K`, need no further cast. In components the product is the matrix
product, `toMatrix_matMulT`.

## ii. Key results

- `TensorSpecies.Tensor.toLinearMap₂` : the bilinear map `t, s ↦ M_{zw} tᶻ sʷ` of a rank-two
    tensor, with its component formula `toLinearMap₂_apply`.
- `TensorSpecies.Tensor.toMatrix₂_toLinearMap₂` : its matrix in the dual bases is the component
    matrix of `M`.
- `TensorSpecies.Tensor.matMulT` : the product `a_{IJ} b^{JK}` of two rank-two tensors, with
    `toMatrix_matMulT`, its matrix is the product of the component matrices.

## iii. Table of contents

- A. Pairing a rank-two tensor with two vectors
- B. The product of two rank-two tensors

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

## B. The product of two rank-two tensors

-/

/-- The product `a_{IJ} b^{JK}` of two rank-two tensors: the second index of `a` contracted with
the first index of `b`, where `h : S.τ (cs 1) = ds 0`. The surviving indices `I` and `K` keep
their colours, `![cs 0, ds 1]`. -/
noncomputable def matMulT {cs ds : Fin 2 → C} (h : S.τ (cs 1) = ds 0) :
    Tensor S cs →ₗ[k] Tensor S ds →ₗ[k] Tensor S ![cs 0, ds 1] :=
  (crossToEnd (Fin.last 1) (0 : Fin 2) h).compr₂
    (permT id (IsReindexing.on_id.mpr fun j => by fin_cases j <;> rfl))

/-- The product is the cross contraction of the last slot of `a` with the first slot of `b`,
recoloured to `![cs 0, ds 1]`. -/
lemma matMulT_apply {cs ds : Fin 2 → C} (h : S.τ (cs 1) = ds 0) (a : Tensor S cs)
    (b : Tensor S ds) :
    matMulT h a b = permT id (IsReindexing.on_id.mpr fun j => by fin_cases j <;> rfl)
      (crossToEnd (Fin.last 1) (0 : Fin 2) h a b) :=
  rfl

/-- Cross contraction of the last slot of `a` with the first slot of `b` is their product,
recoloured back to the colour list `crossToEnd` produces. -/
lemma crossToEnd_eq_permT_matMulT {cs ds : Fin 2 → C} (h : S.τ (cs 1) = ds 0) (a : Tensor S cs)
    (b : Tensor S ds) :
    crossToEnd (Fin.last 1) (0 : Fin 2) h a b =
      permT id (IsReindexing.on_id.mpr fun j => by fin_cases j <;> rfl) (matMulT h a b) := by
  rw [matMulT_apply, permT_permT]
  exact (permT_congr_eq_id _ _ _ rfl).symm

/-- The matrix of a product is the product of the matrices, the middle labels matched by
`HasContrDualBases.dualIdxEquiv`. -/
lemma toMatrix_matMulT [HasContrDualBases S] {cs ds : Fin 2 → C} (h : S.τ (cs 1) = ds 0)
    (a : Tensor S cs) (b : Tensor S ds) :
    toMatrix (matMulT h a b) =
      toMatrix a * (toMatrix b).submatrix (HasContrDualBases.dualIdxEquiv h) id := by
  obtain ⟨c0, c1, rfl⟩ : ∃ c0 c1, cs = ![c0, c1] := ⟨cs 0, cs 1, by funext i; fin_cases i <;> rfl⟩
  obtain ⟨c2, c3, rfl⟩ : ∃ c2 c3, ds = ![c2, c3] := ⟨ds 0, ds 1, by funext i; fin_cases i <;> rfl⟩
  ext y0 y3
  refine (permT_basis_repr_of_id (fun _ => rfl) _ _ _).trans ((congrArg _ ?_).trans
    ((crossToEnd_pair_basis_repr h a b y0 y3).trans rfl))
  funext i
  fin_cases i <;> rfl

end Tensor

end TensorSpecies
