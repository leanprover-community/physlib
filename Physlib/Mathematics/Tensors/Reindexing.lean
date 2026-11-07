/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.Tensors.Tensor
/-!

# Relabeling the slots of a tensor

A bijection of the slots of a tensor that keeps their colors, and its action on tensors, as in the
transpose `T^μ_ν ↦ T_ν^μ`.

## i. Overview

A tensor has one slot for each index, and each slot has a color, such as up or down. `T^μ_ν` has
two slots, the first up and the second down. The transpose `T_ν^μ` has the same components with
the indices written in the other order. Its first slot is down and its second is up.

A relabeling `σ` is a permutation of the indices. It says which position each index moves to, and
it may only move an index together with its color. For the transpose, `σ` swaps the positions `0`
and `1`, and the colors `![up, down]` become `![down, up]`. A permutation that would turn an up
index into a down one is not a relabeling. That operation is raising or lowering, and it needs a
metric.

Formally `σ : ColorEquiv c₁ c₂` is a bijection `σ.toEquiv : ι₁ ≃ ι₂` of the slots, where the
labels `ι₁` and `ι₂` may be different types, together with the proof
`σ.color_eq j : c₁ (σ.toEquiv.symm j) = c₂ j` that the new slot `j` has the color of the old slot
it comes from. For concrete colors the proof is found automatically.

`S.reindex σ : S.Tensor c₁ ≃ₗ[k] S.Tensor c₂` moves each vector to its new slot, so the transpose
sends `u ⊗ α` to `α ⊗ u` and has components `(Tᵀ)_ν^μ = T^μ_ν`. Nothing is computed. Lean writes
the color of the new slot differently from the color of the old one, so each vector is retyped
along `σ.color_eq`, and for concrete colors this retyping is the identity. The name follows
Mathlib's `PiTensorProduct.reindex`.

Relabelings appear wherever indices are lined up. Index notation relabels `B` in `A^μ_ν + B_ν^μ`
before adding, so the result is the tensor `(A + Bᵀ)^μ_ν` with the slots in the order of `A`. The
symmetry `g_μν = g_νμ` compares `g` with its relabeling. The product `u^μ v^ν` of two vectors,
whose slots are labeled "slot of `u`" and "slot of `v`" (`Fin 1 ⊕ Fin 1`), is relabeled to a
tensor with slots `0, 1` (`Fin 2`). A relabeling can change the type of the labels as well as
their order.

## ii. Key results

- `ColorEquiv` is a bijection of slots that keeps their colors, with `refl`, `symm` and `trans`.
- `Species.reindex` applies a relabeling to tensors, and `Species.reindex_pure` gives it on a pure
  tensor.
- `Species.reindex_reindex` proves that two relabelings in sequence are their composite, and
  `Species.reindex_refl` that the identity relabeling does nothing.
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

namespace Tensors

/-!

## A. Relabelings that keep colors

-/

/-- A relabeling of slots that keeps their colors, made of a bijection of slots and the proof that
each new slot has the color of the old slot it comes from. The proof is stated at the new labels
`j`, so that `c₂ j` reduces at labels such as `inl x` or `0`. For finitely many concrete slots it
is found by `rfl` or by cases. Two relabelings are equal when their bijections are
(`ColorEquiv.ext`). -/
@[ext]
structure ColorEquiv {K : Type} {ι₁ ι₂ : Type} (c₁ : ι₁ → Color K) (c₂ : ι₂ → Color K) where
  /-- The bijection of slots, old slot `i` to new slot `toEquiv i`. -/
  toEquiv : ι₁ ≃ ι₂
  /-- The new slot `j` has the color of the old slot `toEquiv.symm j`. -/
  color_eq : ∀ j, c₁ (toEquiv.symm j) = c₂ j := by
    first | exact fun _ => rfl | (intro j; fin_cases j <;> rfl)

namespace ColorEquiv

variable {K : Type} {ι₁ ι₂ ι₃ : Type} {c₁ : ι₁ → Color K} {c₂ : ι₂ → Color K}
    {c₃ : ι₃ → Color K}

/-- The identity relabeling, where every slot keeps its label. -/
def refl (c₁ : ι₁ → Color K) : ColorEquiv c₁ c₁ := ⟨Equiv.refl ι₁, fun _ => rfl⟩

/-- The inverse relabeling, where every slot gets back its old label. -/
def symm (σ : ColorEquiv c₁ c₂) : ColorEquiv c₂ c₁ :=
  ⟨σ.toEquiv.symm, fun i => by simpa using (σ.color_eq (σ.toEquiv i)).symm⟩

/-- The relabeling `σ₁` followed by `σ₂`. -/
def trans (σ₁ : ColorEquiv c₁ c₂) (σ₂ : ColorEquiv c₂ c₃) : ColorEquiv c₁ c₃ :=
  ⟨σ₁.toEquiv.trans σ₂.toEquiv, fun j => (σ₁.color_eq _).trans (σ₂.color_eq j)⟩

end ColorEquiv

namespace Species

variable {k : Type} [CommRing k] {K : Type} {G : Type} [Group G] {basisIdx : K → Type}
    [∀ κ, Fintype (basisIdx κ)] [∀ κ, DecidableEq (basisIdx κ)] {S : Species k G K basisIdx}

variable {ι₁ ι₂ ι₃ : Type}

/-!

## B. Relabeling tensors

-/

variable (S) in
/-- The relabeling `σ` applied to tensors, as in the transpose `T^μ_ν ↦ T_ν^μ`. The new slot `j`
holds the vector of the old slot `σ.toEquiv.symm j`, moved along `σ.color_eq j`. It is Mathlib's
`PiTensorProduct.reindex` followed by `PiTensorProduct.congr` of `LinearEquiv.cast`. -/
noncomputable def reindex {c₁ : ι₁ → Color K} {c₂ : ι₂ → Color K} (σ : ColorEquiv c₁ c₂) :
    (S.tensorRep c₁).Equiv (S.tensorRep c₂) :=
  equivOfPure (S.toPiTensor c₁ ≪≫ₗ PiTensorProduct.reindex k _ σ.toEquiv ≪≫ₗ
    PiTensorProduct.congr (fun j => (S.cast (σ.color_eq j)).toLinearEquiv) ≪≫ₗ
    (S.toPiTensor c₂).symm) fun g f => by
      simp only [smul_pure, LinearEquiv.trans_apply, toPiTensor_pure,
        PiTensorProduct.reindex_tprod, congr_tprod, toPiTensor_symm_tprod]
      exact congrArg S.pure (funext fun j => cast_rep _ _ _)

/-- On a pure tensor, the new slot `j` holds the vector of the old slot `σ.toEquiv.symm j`, moved
along `σ.color_eq j`. -/
@[simp]
lemma reindex_pure {c₁ : ι₁ → Color K} {c₂ : ι₂ → Color K} (σ : ColorEquiv c₁ c₂)
    (f : Π i, S.V (c₁ i)) :
    S.reindex σ (S.pure f) = S.pure fun j => S.cast (σ.color_eq j) (f (σ.toEquiv.symm j)) := by
  simp [reindex, PiTensorProduct.reindex_tprod, congr_tprod]

/-!

## C. Composition and equivariance

-/

/-- Relabeling by the identity does nothing. -/
lemma reindex_refl {c₁ : ι₁ → Color K} (t : S.Tensor c₁) : S.reindex (ColorEquiv.refl c₁) t = t :=
  LinearMap.congr_fun (f := (S.reindex (ColorEquiv.refl c₁)).toLinearMap)
    (ext_pure (g := LinearMap.id) fun f => by
      rw [Representation.Equiv.coe_toLinearMap, reindex_pure]; rfl) t

/-- Relabeling by `σ₁` and then by `σ₂` is relabeling by `σ₁.trans σ₂`. -/
lemma reindex_reindex {c₁ : ι₁ → Color K} {c₂ : ι₂ → Color K} {c₃ : ι₃ → Color K}
    (σ₁ : ColorEquiv c₁ c₂) (σ₂ : ColorEquiv c₂ c₃) (t : S.Tensor c₁) :
    S.reindex σ₂ (S.reindex σ₁ t) = S.reindex (σ₁.trans σ₂) t :=
  LinearMap.congr_fun (f := ((S.reindex σ₁).trans (S.reindex σ₂)).toLinearMap)
    (ext_pure (g := (S.reindex (σ₁.trans σ₂)).toLinearMap) fun f => by
      simp only [Representation.Equiv.coe_toLinearMap, Representation.Equiv.trans_apply,
        reindex_pure, cast_apply, cast_cast]
      rfl) t

/-!

## D. Components

-/

/-- The components of a relabeled tensor are those of the tensor, as in `(Tᵀ)_ν^μ = T^μ_ν`. The
old slot `i` takes the label `y (σ.toEquiv i)` of its new slot, cast along the equality of their
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
    refine (Fintype.prod_equiv σ.toEquiv _ _ fun i => ?_).symm
    -- The old slot `σ.toEquiv.symm (σ.toEquiv i)` is `i` only up to a proof, so it is generalized.
    have h : ∀ i' (_ : i' = i) (d : Color K) (p : c₁ i' = d) (q : d = c₁ i) (z : basisIdx d.kind),
        (S.basis (c₁ i)).repr (f i) (cast (congrArg (basisIdx ∘ Color.kind) q) z) =
          (S.basis d).repr (S.cast p (f i')) z := by
      rintro _ rfl _ rfl _ _
      rfl
    exact h _ (σ.toEquiv.symm_apply_apply i) _ _ (σ.symm.color_eq i) _

end Species

end Tensors
