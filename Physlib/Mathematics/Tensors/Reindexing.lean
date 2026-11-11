/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.Tensors.Tensor
/-!

# Relabeling the indices of a tensor

A bijection of the indices of a tensor that keeps their colors, and its action on tensors, as in the
transpose `T^μ_ν ↦ T_ν^μ`.

## i. Overview

A relabeling `σ : ColorEquiv c₁ c₂` is a bijection `σ.toEquiv : ι₁ ≃ ι₂` of the indices of a tensor
that keeps their colors, with the proof `σ.color_eq`. For the transpose `T^μ_ν ↦ T_ν^μ` it swaps
the indices `0` and `1`, and the colors `![up, down]` become `![down, up]`. A permutation that would
turn an up index into a down one is not a relabeling, since that needs a metric. The labels `ι₁`
and `ι₂` may be different types, as `Fin 1 ⊕ Fin 1` and `Fin 2` for the product `u^μ v^ν`.

`S.reindex σ` moves each vector of a tensor to its new index. The name follows Mathlib's
`PiTensorProduct.reindex`. Index notation uses it to line up indices, as in `A^μ_ν + B_ν^μ`.

## ii. Key results

- `ColorEquiv` is a bijection of indices that keeps their colors, with `refl`, `symm` and `trans`.
- `Species.permIndices` moves the vectors of a tensor along a bijection of indices, with no colors
  involved. It is Mathlib's `PiTensorProduct.reindex`.
- `Species.reindex` applies a relabeling to tensors, `permIndices` followed by `congrIndices` of the
  moves along the equalities of colors, and `Species.reindex_pure` gives it on a pure tensor.
- `Species.reindex_trans`, `Species.reindex_refl` and `Species.reindex_symm` prove that relabeling
  respects composites, the identity and inverses, and `Species.reindex_reindex` is the first on a
  tensor.
- `Species.reindex` is an equivalence of representations, so relabeling commutes with the group
  action.
- `Species.tensorBasis_repr_reindex` gives the components of a relabeled tensor,
  `(Tᵀ)_ν^μ = T^μ_ν`.

## iii. Table of contents

- A. Relabelings that keep colors
- B. Relabeling tensors
- C. Composition and equivariance
- D. Components

## iv. References

None.

-/

@[expose] public section

open TensorProduct PiTensorProduct

namespace Tensor

/-!

## A. Relabelings that keep colors

-/

/-- A relabeling of indices that keeps their colors, made of a bijection of indices and the proof
that each new index has the color of the old index it comes from. The proof is stated at the new
indices `j`, so that `c₂ j` reduces at indices such as `inl x` or `0`. For finitely many concrete
indices it is found by `rfl` or by cases. Two relabelings are equal when their bijections are
(`ColorEquiv.ext`). -/
@[ext]
structure ColorEquiv {K : Type} {ι₁ ι₂ : Type} (c₁ : ι₁ → Color K) (c₂ : ι₂ → Color K) where
  /-- The bijection of indices, old index `i` to new index `toEquiv i`. -/
  toEquiv : ι₁ ≃ ι₂
  /-- The new index `j` has the color of the old index `toEquiv.symm j`. -/
  color_eq : ∀ j, c₁ (toEquiv.symm j) = c₂ j := by
    first | exact fun _ => rfl | (intro j; fin_cases j <;> rfl)

namespace ColorEquiv

variable {K : Type} {ι₁ ι₂ ι₃ : Type} {c₁ : ι₁ → Color K} {c₂ : ι₂ → Color K}
    {c₃ : ι₃ → Color K}

/-- The identity relabeling, where every index stays in place. -/
def refl (c₁ : ι₁ → Color K) : ColorEquiv c₁ c₁ := ⟨Equiv.refl ι₁, fun _ => rfl⟩

/-- The inverse relabeling, where every index returns to its old position. -/
def symm (σ : ColorEquiv c₁ c₂) : ColorEquiv c₂ c₁ :=
  ⟨σ.toEquiv.symm, fun i => by simpa using (σ.color_eq (σ.toEquiv i)).symm⟩

/-- The relabeling `σ₁` followed by `σ₂`. -/
def trans (σ₁ : ColorEquiv c₁ c₂) (σ₂ : ColorEquiv c₂ c₃) : ColorEquiv c₁ c₃ :=
  ⟨σ₁.toEquiv.trans σ₂.toEquiv, fun j => (σ₁.color_eq _).trans (σ₂.color_eq j)⟩

/-- The relabeling that swaps the two indices of a tensor on two indices, `![a, b] → ![b, a]`. -/
def swapTwo (a b : Color K) : ColorEquiv (K := K) ![a, b] ![b, a] := ⟨Equiv.swap 0 1, by
  intro j; fin_cases j <;> rfl⟩

@[simp]
lemma toEquiv_swapTwo (a b : Color K) : (swapTwo a b).toEquiv = Equiv.swap 0 1 := rfl

@[simp]
lemma toEquiv_refl (c₁ : ι₁ → Color K) : (refl c₁).toEquiv = Equiv.refl ι₁ := rfl

@[simp]
lemma toEquiv_symm (σ : ColorEquiv c₁ c₂) : σ.symm.toEquiv = σ.toEquiv.symm := rfl

@[simp]
lemma toEquiv_trans (σ₁ : ColorEquiv c₁ c₂) (σ₂ : ColorEquiv c₂ c₃) :
    (σ₁.trans σ₂).toEquiv = σ₁.toEquiv.trans σ₂.toEquiv := rfl

@[simp]
lemma symm_symm (σ : ColorEquiv c₁ c₂) : σ.symm.symm = σ := ColorEquiv.ext (Equiv.symm_symm _)

end ColorEquiv

namespace Species

variable {k : Type} [RCLike k] {K : Type} {G : Type} [Group G] {basisIdx : K → Type}
    [∀ κ, Fintype (basisIdx κ)] [∀ κ, DecidableEq (basisIdx κ)] {S : Species k G K basisIdx}

variable {ι₁ ι₂ ι₃ : Type}

/-!

## B. Relabeling tensors

-/

variable (S) in
/-- The bijection `e` of indices applied to tensors, moving the vector of the old index `i` to the
new index `e i`, with the colors `c ∘ e.symm`. It is Mathlib's `PiTensorProduct.reindex`. -/
noncomputable def permIndices (c : ι₁ → Color K) (e : ι₁ ≃ ι₂) :
    (S.tensorRep c).Equiv (S.tensorRep (c ∘ e.symm)) :=
  equivOfPure (S.toPiTensor c ≪≫ₗ PiTensorProduct.reindex k (fun i => S.V (c i)) e ≪≫ₗ
    (S.toPiTensor (c ∘ e.symm)).symm) fun g f => by
      simp only [smul_pure, LinearEquiv.trans_apply, toPiTensor_pure,
        PiTensorProduct.reindex_tprod, toPiTensor_symm_tprod]
      rfl

/-- On a pure tensor, the new index `j` holds the vector of the old index `e.symm j`. -/
@[simp]
lemma permIndices_pure (c : ι₁ → Color K) (e : ι₁ ≃ ι₂) (f : Π i, S.V (c i)) :
    S.permIndices c e (S.pure f) = S.pure fun j => f (e.symm j) := by
  simp [permIndices, PiTensorProduct.reindex_tprod]

variable (S) in
/-- The relabeling `σ` applied to tensors, as in the transpose `T^μ_ν ↦ T_ν^μ`. The new index `j`
holds the vector of the old index `σ.toEquiv.symm j`, moved along `σ.color_eq j`. It is
`permIndices` of `σ.toEquiv` followed by `congrIndices` of the moves. -/
noncomputable def reindex {c₁ : ι₁ → Color K} {c₂ : ι₂ → Color K} (σ : ColorEquiv c₁ c₂) :
    (S.tensorRep c₁).Equiv (S.tensorRep c₂) :=
  (S.permIndices c₁ σ.toEquiv).trans (S.congrIndices fun j => S.cast (σ.color_eq j))

/-- On a pure tensor, the new index `j` holds the vector of the old index `σ.toEquiv.symm j`, moved
along `σ.color_eq j`. -/
@[simp]
lemma reindex_pure {c₁ : ι₁ → Color K} {c₂ : ι₂ → Color K} (σ : ColorEquiv c₁ c₂)
    (f : Π i, S.V (c₁ i)) :
    S.reindex σ (S.pure f) = S.pure fun j => S.cast (σ.color_eq j) (f (σ.toEquiv.symm j)) := by
  rw [reindex, Representation.Equiv.trans_apply, permIndices_pure, congrIndices_pure]

/-!

## C. Composition and equivariance

-/

/-- Relabeling by the identity is the identity. -/
lemma reindex_refl (c₁ : ι₁ → Color K) : S.reindex (ColorEquiv.refl c₁) = .refl _ :=
  equiv_ext_pure fun f => by rw [reindex_pure]; rfl

/-- Relabeling by `σ₁.trans σ₂` is relabeling by `σ₁` and then by `σ₂`. -/
lemma reindex_trans {c₁ : ι₁ → Color K} {c₂ : ι₂ → Color K} {c₃ : ι₃ → Color K}
    (σ₁ : ColorEquiv c₁ c₂) (σ₂ : ColorEquiv c₂ c₃) :
    S.reindex (σ₁.trans σ₂) = (S.reindex σ₁).trans (S.reindex σ₂) :=
  equiv_ext_pure fun f => by
    simp only [Representation.Equiv.trans_apply, reindex_pure, cast_apply, cast_cast]
    rfl

/-- Relabeling by `σ₁` and then by `σ₂` is relabeling by `σ₁.trans σ₂`, on a tensor. -/
lemma reindex_reindex {c₁ : ι₁ → Color K} {c₂ : ι₂ → Color K} {c₃ : ι₃ → Color K}
    (σ₁ : ColorEquiv c₁ c₂) (σ₂ : ColorEquiv c₂ c₃) (t : S.Tensor c₁) :
    S.reindex σ₂ (S.reindex σ₁ t) = S.reindex (σ₁.trans σ₂) t := by
  rw [reindex_trans, Representation.Equiv.trans_apply]

/-- The inverse of relabeling by `σ` is relabeling by `σ.symm`. -/
lemma reindex_symm {c₁ : ι₁ → Color K} {c₂ : ι₂ → Color K} (σ : ColorEquiv c₁ c₂) :
    (S.reindex σ).symm = S.reindex σ.symm :=
  Representation.Equiv.ext <| funext fun t => EquivLike.injective (S.reindex σ) <| by
    rw [Representation.Equiv.apply_symm_apply, reindex_reindex,
      show σ.symm.trans σ = .refl c₂ from ColorEquiv.ext (Equiv.symm_trans_self _), reindex_refl]
    rfl

/-!

## D. Components

-/

/-- The components of a relabeled tensor are those of the tensor, as in `(Tᵀ)_ν^μ = T^μ_ν`. The
old index `i` takes the label `y (σ.toEquiv i)` of its new index, cast along the equality of their
colors. For concrete colors and labels the cast is between equal types, and `rfl` removes it. -/
lemma tensorBasis_repr_reindex [Fintype ι₁] [Fintype ι₂] {c₁ : ι₁ → Color K}
    {c₂ : ι₂ → Color K} (σ : ColorEquiv c₁ c₂) (t : S.Tensor c₁)
    (y : Π j, basisIdx (c₂ j).kind) :
    (S.tensorBasis c₂).repr (S.reindex σ t) y =
      (S.tensorBasis c₁).repr t fun i =>
        cast (congrArg (basisIdx ∘ Color.kind) (σ.symm.color_eq i)) (y (σ.toEquiv i)) := by
  induction t using inductionOn_pure with
  | hsmul r t ht => simp only [map_smul, Finsupp.smul_apply, ht]
  | hadd t t' ht ht' => simp only [map_add, Finsupp.add_apply, ht, ht']
  | h f =>
    rw [reindex_pure, tensorBasis_repr_pure, tensorBasis_repr_pure]
    refine Fintype.prod_equiv σ.toEquiv.symm _ _ fun j => ?_
    -- The label `y j` is read at the new index `σ.toEquiv (σ.toEquiv.symm j)`, which is `j` only
    -- up to a proof.
    rw [basis_repr_cast]
    exact congrArg _ (eq_of_heq ((cast_heq _ _).trans
      ((congr_arg_heq y (σ.toEquiv.apply_symm_apply j)).symm.trans (cast_heq _ _).symm)))

end Species

end Tensor
