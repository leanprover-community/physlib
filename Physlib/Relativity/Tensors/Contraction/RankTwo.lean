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

# The bilinear map of a rank-two tensor

## i. Overview

A rank-two tensor `M` defines a bilinear map on one-slot tensors by contracting one argument into
each of its slots, `t, s ↦ M_{zw} tᶻ sʷ`. In the bases dual to the slots of `M` the matrix of this
map is the component matrix `toMatrix M`.

## ii. Key results

- `TensorSpecies.Tensor.toLinearMap₂` : the bilinear map `t, s ↦ M_{zw} tᶻ sʷ` of a rank-two
    tensor, with its component formula `toLinearMap₂_apply`.
- `TensorSpecies.Tensor.toMatrix₂_toLinearMap₂` : its matrix in the dual bases is the component
    matrix of `M`.

## iii. Table of contents

- A. Pairing a rank-two tensor with two vectors

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

end Tensor

end TensorSpecies
