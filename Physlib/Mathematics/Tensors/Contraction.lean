/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.Tensors.Product
public import Mathlib.LinearAlgebra.PiTensorProduct.Dual
/-!

# Contraction of tensors

The contraction of pairs of indices, an index with its dual in each pair, as in the trace
`T^ρμ_μ` or the full contraction `T^μν U_μν`, and its properties.

## i. Overview

A contraction pairs indices of dual colors and sums over their common label, as in the trace
`(tr T)^ρ = T^ρμ_μ` of a Lorentz tensor `T^ρμ_ν` on the index type `Fin 3`. On a pure tensor
`u ⊗ v ⊗ α` the trace is `(v^μ α_μ) u`, where `v^μ α_μ` is the species contraction `S.contr`.

The pairs to contract are chosen by a reindexing `σ : ColorEquiv c (contrColors c' a)` of the
indices. It sends each free index to an index `inl x`, of color `c' x`, and the two indices of a
pair `j` to the indices `inr (inl j)` and `inr (inr j)`, of colors `a j` and `(a j).dual`. For the
trace, `σ` sends `0 ↦ inl 0`, `1 ↦ inr (inl ())` and `2 ↦ inr (inr ())`, and the index notation
`{T | ρ μ μ}ᵀ` builds it from the repeated name. Since `σ` keeps colors, the two indices of each
pair are dual without a separate hypothesis. `Tensor.contr σ` reindexes by `σ` and then contracts
each pair by `S.contr (a j)`, with the first index of the pair as its first argument.

Two tensors are contracted by contracting their product. In the full contraction `T^μν U_μν` the
product `T ⊗ U` has four indices, which form two pairs and leave no index, `κ = Empty`. The
following properties let a contraction of several tensors be computed one step at a time.
- Only the pairs of indices matter. Two contractions of the same pairs of indices are equal, in
  whatever order the pairs are listed and whichever index of a pair comes first.
- A tensor that changes sign when its pairs are permuted contracts to zero, since its contraction
  equals its own negative. For `A` antisymmetric and `B` symmetric, renaming `μ ↔ ν` turns
  `A^μν B_μν` into `A^νμ B_νμ = -A^μν B_μν`, so `A^μν B_μν = 0`.
- Pairs can be contracted one at a time. Contracting `μ` and then `ν` in `T^μ_μ^ν_ν` is
  contracting both pairs at once.
- A factor that takes no part in a contraction can be multiplied before or after it,
  `(T^μ_μν) U^ρ = (T ⊗ U)^μ_μν^ρ`.

The components of a contraction are sums of components of the tensor, `(tr T)^ρ = ∑ μ, T^ρμ_μ`,
since the bases of a color and its dual are dual.

## ii. Key results

- `Tensor.contr` contracts the pairs of indices chosen by `σ`, as in `T^ρμ_μ`, with the
  colors `contrColors` of the free indices and the pairs.
- `Tensor.contr_pure` gives the contraction of a pure tensor.
- `Tensor.contr` is an intertwining map, so it commutes with the group action.
- `Tensor.contr_reindex` and `Tensor.reindex_contr` absorb a reindexing before
  or after a contraction.
- `ColorEquiv.SamePair` says that two choices of pairs contract the same two indices, and
  `Tensor.contr_eq_of_samePair` proves that two contractions of the same pairs of indices,
  in any order, are equal.
- `Tensor.contr_noPairs` proves that a contraction with no pairs, along
  `ColorEquiv.noPairs`, is the identity.
- `Tensor.contr_eq_zero_of_reindex_eq_neg` and
  `Tensor.contr_tmulEquiv_eq_zero_of_antisymm_symm` prove `A^μν B_μν = 0` for `A`
  antisymmetric and `B` symmetric.
- `Tensor.contr_contr` proves that two contractions in sequence are one, along
  `ColorEquiv.chain`.
- `Tensor.tmulEquiv_contr_left` and `Tensor.tmulEquiv_contr_right` prove that
  contracting a factor commutes with the product, along `ColorEquiv.tmulRight` and
  `ColorEquiv.tmulLeft`.
- `Tensor.tensorBasis_repr_contr` gives the components of a contraction, from
  `Tensor.tensorBasis_repr_contrStd` in the standard arrangement of indices.
- `Tensor.tensorBasis_repr_contr_one_pair` and
  `Tensor.tensorBasis_repr_contr_two_pairs` give the same with one and with two pairs.

## iii. Table of contents

- A. Choices of pairs of indices
- B. Contraction in the standard arrangement of indices
- C. Contraction of chosen pairs of indices
  - C.1. Reindexing
  - C.2. Contractions of the same pairs of indices
  - C.3. Symmetric against antisymmetric
  - C.4. Two contractions are one
  - C.5. Products with a tensor that is not contracted
- D. Components

## iv. References

There are no known references for the material in this module.

-/

@[expose] public section

open TensorProduct PiTensorProduct

namespace Tensor

/-!

## A. Choices of pairs of indices

-/

/-- The colors of the standard arrangement `κ ⊕ (J ⊕ J)` of indices. The free index `inl x` has
the color `c x`, and the two indices `inr (inl j)` and `inr (inr j)` of the pair `j` have the colors
`a j` and `(a j).dual`. -/
noncomputable abbrev contrColors {K κ J : Type} (c : κ → Color K) (a : J → Color K) :
    κ ⊕ (J ⊕ J) → Color K :=
  prodColors c (prodColors a fun j => (a j).dual)

namespace ColorEquiv

variable {K : Type} {ι₁ ι₂ κ κ₁ J J' J₁ J₂ : Type}

/-- The reindexing of a contraction with no pairs, where every index is free and stays in place. -/
def noPairs (c : ι₁ → Color K) :
    ColorEquiv c (contrColors c (Empty.elim : Empty → Color K)) where
  toEquiv.toFun := .inl
  toEquiv.invFun := Sum.elim id (Sum.elim Empty.elim Empty.elim)
  toEquiv.left_inv _ := rfl
  toEquiv.right_inv := by rintro (x | e | e) <;> first | rfl | exact e.elim
  color_eq := by rintro (x | e | e) <;> first | rfl | exact e.elim

variable {c : ι₁ → Color K} {c' : κ → Color K}

/-- The pair `j` of `σ` and the pair `j'` of `τ` contract the same two indices, in either order. -/
def SamePair {a : J → Color K} {a' : J' → Color K}
    (σ : ColorEquiv c (contrColors c' a)) (τ : ColorEquiv c (contrColors c' a')) (j : J)
    (j' : J') : Prop :=
  (σ.toEquiv.symm (.inr (.inl j)) = τ.toEquiv.symm (.inr (.inl j')) ∧
      σ.toEquiv.symm (.inr (.inr j)) = τ.toEquiv.symm (.inr (.inr j'))) ∨
    (σ.toEquiv.symm (.inr (.inl j)) = τ.toEquiv.symm (.inr (.inr j')) ∧
      σ.toEquiv.symm (.inr (.inr j)) = τ.toEquiv.symm (.inr (.inl j')))

instance [DecidableEq ι₁] {a : J → Color K} {a' : J' → Color K}
    (σ : ColorEquiv c (contrColors c' a)) (τ : ColorEquiv c (contrColors c' a')) (j : J)
    (j' : J') : Decidable (σ.SamePair τ j j') := by
  unfold SamePair
  infer_instance

/-- A pair of `τ` is the same pair as at most one pair of `σ`. -/
lemma SamePair.left_unique {a : J → Color K} {a' : J' → Color K}
    {σ : ColorEquiv c (contrColors c' a)} {τ : ColorEquiv c (contrColors c' a')} {j₁ j₂ : J}
    {j' : J'} (h₁ : σ.SamePair τ j₁ j') (h₂ : σ.SamePair τ j₂ j') : j₁ = j₂ := by
  have hσ := σ.toEquiv.symm.injective
  rcases h₁ with ⟨h₁, h₁'⟩ | ⟨h₁, h₁'⟩ <;> rcases h₂ with ⟨h₂, h₂'⟩ | ⟨h₂, h₂'⟩
  · simpa using hσ (h₁.trans h₂.symm)
  · simpa using hσ (h₁'.trans h₂.symm)
  · simpa using hσ (h₁.trans h₂'.symm)
  · simpa using hσ (h₁.trans h₂.symm)

/-- A pair of `σ` is the same pair as at most one pair of `τ`. -/
lemma SamePair.right_unique {a : J → Color K} {a' : J' → Color K}
    {σ : ColorEquiv c (contrColors c' a)} {τ : ColorEquiv c (contrColors c' a')} {j : J}
    {j₁ j₂ : J'} (h₁ : σ.SamePair τ j j₁) (h₂ : σ.SamePair τ j j₂) : j₁ = j₂ := by
  have hτ := τ.toEquiv.symm.injective
  rcases h₁ with ⟨h₁, -⟩ | ⟨h₁, -⟩ <;> rcases h₂ with ⟨h₂, -⟩ | ⟨h₂, -⟩ <;>
    simpa using hτ (h₁.symm.trans h₂)

/-- When `σ` and `τ` keep the same free indices and every pair of `σ` is a pair of `τ`, every pair
of `τ` is a pair of `σ`. The indices of a pair of `τ` are not free, so they lie in a pair of `σ`. -/
lemma exists_samePair_left {a : J → Color K} {a' : J' → Color K}
    {σ : ColorEquiv c (contrColors c' a)} {τ : ColorEquiv c (contrColors c' a')}
    (hfree : ∀ x, σ.toEquiv.symm (.inl x) = τ.toEquiv.symm (.inl x))
    (h₁ : ∀ j, ∃ j', σ.SamePair τ j j') (j' : J') : ∃ j, σ.SamePair τ j j' := by
  have hτ := τ.toEquiv.symm.injective
  rcases hs : σ.toEquiv (τ.toEquiv.symm (.inr (.inl j'))) with x | j | j <;>
    rw [← Equiv.eq_symm_apply] at hs
  · rw [hfree] at hs
    have := hτ hs
    simp at this
  · obtain ⟨j'', h | h⟩ := h₁ j
    · obtain rfl : j'' = j' := by simpa using hτ (h.1.symm.trans hs.symm)
      exact ⟨j, .inl h⟩
    · have := hτ (h.1.symm.trans hs.symm)
      simp at this
  · obtain ⟨j'', h | h⟩ := h₁ j
    · have := hτ (h.2.symm.trans hs.symm)
      simp at this
    · obtain rfl : j'' = j' := by simpa using hτ (h.2.symm.trans hs.symm)
      exact ⟨j, .inr h⟩

/-- The pairs of two contractions in sequence, `σ₁` and then `σ₂`, as one choice of pairs
`J₁ ⊕ J₂`, the pairs `J₁` of `σ₁` followed by the pairs `J₂` of `σ₂`. -/
noncomputable def chain {c₁ : κ₁ → Color K} {a₁ : J₁ → Color K} {a₂ : J₂ → Color K}
    (σ₁ : ColorEquiv c (contrColors c₁ a₁)) (σ₂ : ColorEquiv c₁ (contrColors c' a₂)) :
    ColorEquiv c (contrColors c' (prodColors a₁ a₂)) :=
  σ₁.trans ((σ₂.sumCongr (.refl _)).trans ⟨(Equiv.sumAssoc _ _ _).trans
    (Equiv.sumCongr (Equiv.refl _) ((Equiv.sumComm _ _).trans (Equiv.sumSumSumComm _ _ _ _))),
    by rintro (_ | (_ | _) | (_ | _)) <;> rfl⟩)

/-- The pairs `σ` of `T`, as pairs of `T ⊗ U` for a factor `U` on the right, with colors `d`. The
indices of `U` are free and come after the free indices of `T`. -/
noncomputable def tmulRight {a : J → Color K} (σ : ColorEquiv c (contrColors c' a))
    (d : ι₂ → Color K) :
    ColorEquiv (prodColors c d) (contrColors (prodColors c' d) a) :=
  (σ.sumCongr (.refl d)).trans (swapLast c' d _)

/-- The pairs `σ` of `T`, as pairs of `U ⊗ T` for a factor `U` on the left, with colors `d`. The
indices of `U` are free and come before the free indices of `T`. -/
noncomputable def tmulLeft {a : J → Color K} (σ : ColorEquiv c (contrColors c' a))
    (d : ι₂ → Color K) :
    ColorEquiv (prodColors d c) (contrColors (prodColors d c') a) :=
  ((refl d).sumCongr σ).trans (sumAssoc _ _ _).symm

end ColorEquiv

variable {k : Type} [RCLike k] {K : Type} {G : Type} [Group G] {basisIdx : K → Type}
    [∀ κ, Fintype (basisIdx κ)] [∀ κ, DecidableEq (basisIdx κ)] {S : Species k G K basisIdx}

variable {ι₁ ι₂ κ κ' κ₁ J J' J₁ J₂ : Type}

open Species

/-!

## B. Contraction in the standard arrangement of indices

-/

/-- The contraction of a tensor in the standard arrangement `κ ⊕ (J ⊕ J)`. For each pair `j` the
index `inr (inl j)` is contracted with the index `inr (inr j)` by `S.contr (a j)`, with the index
`inr (inl j)` as its first argument. The indices `inl x` are the free indices, with the colors
`c`. -/
noncomputable def contrStd [Fintype J] (c : κ → Color K) (a : J → Color K) :
    (S.tensorRep (contrColors c a)).IntertwiningMap (S.tensorRep c) :=
  -- The pairs are split into their first halves, of colors `a`, and their second halves, of the
  -- dual colors. Each vector of a second half is read as a linear form on the first half through
  -- `S.contr`, and the halves are paired by Mathlib's `PiTensorProduct.dualDistrib`.
  intertwiningMapOfPure ((TensorProduct.rid k _).toLinearMap ∘ₗ
    (lift ((PiTensorProduct.dualDistrib ∘ₗ
      PiTensorProduct.map (fun j => (curry (S.contr (a j)).toLinearMap).flip) ∘ₗ
      (S.toPiTensor _).toLinearMap).flip ∘ₗ (S.toPiTensor a).toLinearMap) ∘ₗ
      (S.tmulEquiv a _).symm.toLinearMap).lTensor _ ∘ₗ
    (S.tmulEquiv c _).symm.toLinearMap) fun g f => by
    simp only [smul_pure, LinearMap.comp_apply, LinearEquiv.coe_coe,
      Representation.Equiv.coe_toLinearMap, tmulEquiv_symm_pure, LinearMap.lTensor_tmul,
      lift.tmul, LinearMap.flip_apply, toPiTensor_pure, PiTensorProduct.map_tprod,
      PiTensorProduct.dualDistrib_apply, TensorProduct.rid_tmul, smul_comm g, smul_pure]
    exact congrArg (· • _) (Finset.prod_congr rfl fun j _ => S.contr_invariant (a j) g _ _)

/-- On a pure tensor the contraction multiplies the remaining vectors by the contraction of the
two vectors of each pair, as in `u ⊗ v ⊗ α ↦ (v^μ α_μ) u`. -/
lemma contrStd_pure [Fintype J] (c : κ → Color K) (a : J → Color K)
    (f : Π x, S.V (contrColors c a x)) :
    contrStd c a (S.pure f) =
      (∏ j, S.contr (a j) (f (.inr (.inl j)) ⊗ₜ f (.inr (.inr j)))) •
        S.pure (c := c) fun x => f (.inl x) := by
  simp [contrStd, PiTensorProduct.map_tprod, PiTensorProduct.dualDistrib_apply]

/-!

## C. Contraction of chosen pairs of indices

-/

/-- The contraction of the pairs of indices chosen by `σ`, as in `T^ρμ_ν ↦ T^ρμ_μ`. It is
`S.reindex σ` followed by `Tensor.contrStd c' a`. For each pair `j` the index
`σ.toEquiv.symm (inr (inl j))`, of color `a j`, is contracted with the index
`σ.toEquiv.symm (inr (inr j))`, of color `(a j).dual`. The indices `σ.toEquiv.symm (inl x)` are the
free indices, with the colors `c'`. -/
noncomputable def contr [Fintype J] {c : ι₁ → Color K} {c' : κ → Color K}
    {a : J → Color K} (σ : ColorEquiv c (contrColors c' a)) :
    (S.tensorRep c).IntertwiningMap (S.tensorRep c') :=
  (contrStd c' a).comp (S.reindex σ).toIntertwiningMap

variable {c : ι₁ → Color K} {c' : κ → Color K}

/-- On a pure tensor the contraction multiplies the remaining vectors by the contraction of the
two vectors of each pair. Each vector is moved along `σ.color_eq` to the color of its index in the
standard arrangement. -/
lemma contr_pure [Fintype J] {a : J → Color K} (σ : ColorEquiv c (contrColors c' a))
    (f : Π x, S.V (c x)) :
    contr σ (S.pure f) =
      (∏ j, S.contr (a j) (S.cast (σ.color_eq (.inr (.inl j))) (f (σ.toEquiv.symm (.inr (.inl j))))
          ⊗ₜ S.cast (σ.color_eq (.inr (.inr j))) (f (σ.toEquiv.symm (.inr (.inr j)))))) •
        S.pure (c := c') fun x => S.cast (σ.color_eq (.inl x)) (f (σ.toEquiv.symm (.inl x))) :=
  (congrArg (contrStd c' a) (reindex_pure σ f)).trans (contrStd_pure c' a _)

/-- A contraction with no pairs is the identity. -/
lemma contr_noPairs (t : Tensor S c) : contr (ColorEquiv.noPairs c) t = t :=
  DFunLike.congr_fun (intertwiningMap_ext_pure (ψ := .id _) fun p => by
    rw [contr_pure, Finset.univ_eq_empty, Finset.prod_empty, one_smul]
    exact congrArg S.pure (funext fun x => by simp only [cast_apply]; rfl)) t

/-!

### C.1. Reindexing

-/

/-- Reindexing and then contracting is contracting along the composite reindexing. -/
lemma contr_reindex [Fintype J] {c₂ : ι₂ → Color K} {a : J → Color K}
    (σ : ColorEquiv c₂ (contrColors c' a)) (τ : ColorEquiv c c₂) (t : Tensor S c) :
    contr σ (S.reindex τ t) = contr (τ.trans σ) t := by
  simp only [contr, Representation.IntertwiningMap.comp_apply,
    Representation.Equiv.coe_toIntertwiningMap, Species.reindex_reindex]

/-- Reindexing the free indices of a contraction is contracting along the composite reindexing. -/
lemma reindex_contr [Fintype J] {c'' : κ' → Color K} {a : J → Color K}
    (σ : ColorEquiv c (contrColors c' a)) (τ : ColorEquiv c' c'') (t : Tensor S c) :
    S.reindex τ (contr σ t) = contr (σ.trans (τ.sumCongr (.refl _))) t :=
  DFunLike.congr_fun (intertwiningMap_ext_pure
    (φ := (S.reindex τ).toIntertwiningMap.comp (contr σ)) fun p => by
      rw [Representation.IntertwiningMap.comp_apply, Representation.Equiv.coe_toIntertwiningMap,
        contr_pure, map_smul, reindex_pure, contr_pure]
      congr 1
      exact congrArg S.pure (funext fun x => by simp only [cast_apply, cast_cast]; rfl)) t

/-!

### C.2. Contractions of the same pairs of indices

-/

/-- Two contractions are equal when they keep the same free indices in the same order and contract
the same pairs of indices, in any order and with either index of a pair first. -/
lemma contr_eq_of_samePair [Fintype J] [Fintype J'] {a : J → Color K} {a' : J' → Color K}
    (σ : ColorEquiv c (contrColors c' a)) (τ : ColorEquiv c (contrColors c' a'))
    (hfree : ∀ x, σ.toEquiv.symm (.inl x) = τ.toEquiv.symm (.inl x))
    (h₁ : ∀ j, ∃ j', σ.SamePair τ j j') (t : Tensor S c) :
    contr σ t = contr τ t := by
  refine DFunLike.congr_fun (intertwiningMap_ext_pure fun p => ?_) t
  rw [contr_pure, contr_pure]
  choose g hg using h₁
  congr 1
  · -- The pair `j` of `σ` is the pair `g j` of `τ`, in the same order or swapped.
    refine Fintype.prod_bijective g ⟨fun j₁ j₂ hj => (hg j₁).left_unique (hj ▸ hg j₂),
      fun j' => (ColorEquiv.exists_samePair_left hfree (fun j => ⟨g j, hg j⟩) j').imp
        fun j hj => (hg j).right_unique hj⟩ _ _ fun j => ?_
    rcases hg j with ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [cast_apply_congr p h, cast_apply_congr p h']
    exacts [contr_cast_tmul_cast _ _ _ _ _ _, contr_cast_tmul_cast_symm _ _ _ _ _ _]
  · exact congrArg S.pure (funext fun x => cast_apply_congr p (hfree x) _)

/-!

### C.3. Symmetric against antisymmetric

-/

/-- A contraction of a tensor that changes sign under a reindexing `π` is zero, when `π` only
permutes the pairs along `e` and keeps the free indices. The hypothesis `ht` has the form of the
index notation `{T | μ ν = -T | ν μ}ᵀ`. -/
lemma contr_eq_zero_of_reindex_eq_neg [Fintype J] {a : J → Color K}
    (σ : ColorEquiv c (contrColors c' a)) (π : ColorEquiv c c) (e : J ≃ J)
    (hπ : π.toEquiv.trans σ.toEquiv = σ.toEquiv.trans ((Equiv.refl κ).sumCongr (e.sumCongr e)))
    {t : Tensor S c} (ht : t = S.reindex π (-t)) : contr σ t = 0 := by
  -- After `π`, each pair `j` of `σ` is its pair `e.symm j`, and the free indices are kept.
  have hs (y) : π.toEquiv.symm (σ.toEquiv.symm y) =
      σ.toEquiv.symm (((Equiv.refl κ).sumCongr (e.sumCongr e)).symm y) :=
    congrArg (fun f : Equiv _ _ => f.symm y) hπ
  have hσ : contr (π.trans σ) t = contr σ t :=
    contr_eq_of_samePair _ _ (fun x => by simp [hs]) (fun j => ⟨e.symm j, .inl ⟨by simp [hs],
      by simp [hs]⟩⟩) t
  have h : contr σ t + contr σ t = 0 := by
    conv_lhs => enter [1]; rw [ht]
    rw [contr_reindex, map_neg, hσ, neg_add_cancel]
  exact (smul_eq_zero.1 ((two_smul k _).trans h)).resolve_left two_ne_zero

/-- `A^μν B_μν = 0` for `A` antisymmetric and `B` symmetric. The contraction of `A ⊗ B` is zero
when `π₁` reverses the sign of `A`, `π₂` fixes `B`, and together they only permute the pairs. The
hypotheses have the form of the index notation, `{A | μ ν = -A | ν μ}ᵀ` and
`{B | μ ν = B | ν μ}ᵀ`. -/
lemma contr_tmulEquiv_eq_zero_of_antisymm_symm [Fintype J]
    {c₁ : ι₁ → Color K} {c₂ : ι₂ → Color K} {a : J → Color K}
    (σ : ColorEquiv (prodColors c₁ c₂) (contrColors c' a)) (π₁ : ColorEquiv c₁ c₁)
    (π₂ : ColorEquiv c₂ c₂) (e : J ≃ J)
    (hπ : (π₁.sumCongr π₂).toEquiv.trans σ.toEquiv =
      σ.toEquiv.trans ((Equiv.refl κ).sumCongr (e.sumCongr e)))
    {A : Tensor S c₁} {B : Tensor S c₂} (hA : A = S.reindex π₁ (-A)) (hB : B = S.reindex π₂ B) :
    contr σ (S.tmulEquiv c₁ c₂ (A ⊗ₜ B)) = 0 :=
  contr_eq_zero_of_reindex_eq_neg σ _ e hπ (by
    rw [← map_neg, ← neg_tmul, reindex_sumCongr_tmulEquiv, ← hA, ← hB])

/-!

### C.4. Two contractions are one

-/

/-- Two contractions in sequence are one contraction, along `σ₁.chain σ₂`. Contracting `μ` and
then `ν` in `T^μ_μ^ν_ν` is contracting both pairs at once. -/
lemma contr_contr [Fintype J₁] [Fintype J₂] {c₁ : κ₁ → Color K} {a₁ : J₁ → Color K}
    {a₂ : J₂ → Color K} (σ₁ : ColorEquiv c (contrColors c₁ a₁))
    (σ₂ : ColorEquiv c₁ (contrColors c' a₂)) (t : Tensor S c) :
    contr σ₂ (contr σ₁ t) = contr (σ₁.chain σ₂) t :=
  DFunLike.congr_fun (intertwiningMap_ext_pure (φ := (contr σ₂).comp (contr σ₁)) fun f => by
    simp only [Representation.IntertwiningMap.comp_apply, contr_pure, map_smul, smul_smul,
      Fintype.prod_sum_type, cast_apply, cast_cast]
    rfl) t

/-!

### C.5. Products with a tensor that is not contracted

-/

/-- Contracting indices of the left factor commutes with the product,
`(T^μ_μν) U^ρ = (T ⊗ U)^μ_μν^ρ`. -/
lemma tmulEquiv_contr_left [Fintype J] {a : J → Color K} {d : ι₂ → Color K}
    (σ : ColorEquiv c (contrColors c' a)) (t : Tensor S c) (u : Tensor S d) :
    S.tmulEquiv c' d (contr σ t ⊗ₜ u) =
      contr (σ.tmulRight d) (S.tmulEquiv c d (t ⊗ₜ u)) :=
  LinearMap.congr_fun (f := (S.tmulEquiv c' d).toLinearMap ∘ₗ (contr σ).toLinearMap.rTensor _)
    (g := (contr (σ.tmulRight d)).toLinearMap ∘ₗ (S.tmulEquiv c d).toLinearMap)
    (ext_pure₂ fun p p' => by
      simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul,
        Representation.IntertwiningMap.coe_toLinearMap, Representation.Equiv.coe_toIntertwiningMap]
      rw [contr_pure, ← smul_tmul', map_smul, tmulEquiv_pure, tmulEquiv_pure, contr_pure]
      congr 1
      exact congrArg S.pure (funext fun y => by rcases y with x | m <;> rfl)) (t ⊗ₜ u)

/-- Contracting indices of the right factor commutes with the product,
`U^ρ (T^μ_μν) = (U ⊗ T)^ρμ_μν`. -/
lemma tmulEquiv_contr_right [Fintype J] {a : J → Color K} {d : ι₂ → Color K}
    (σ : ColorEquiv c (contrColors c' a)) (u : Tensor S d) (t : Tensor S c) :
    S.tmulEquiv d c' (u ⊗ₜ contr σ t) =
      contr (σ.tmulLeft d) (S.tmulEquiv d c (u ⊗ₜ t)) :=
  LinearMap.congr_fun (f := (S.tmulEquiv d c').toLinearMap ∘ₗ (contr σ).toLinearMap.lTensor _)
    (g := (contr (σ.tmulLeft d)).toLinearMap ∘ₗ (S.tmulEquiv d c).toLinearMap)
    (ext_pure₂ fun p' p => by
      simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul,
        Representation.IntertwiningMap.coe_toLinearMap, Representation.Equiv.coe_toIntertwiningMap]
      rw [contr_pure, tmul_smul, map_smul, tmulEquiv_pure, tmulEquiv_pure, contr_pure]
      congr 1
      exact congrArg S.pure (funext fun y => by rcases y with x | m <;> rfl)) (u ⊗ₜ t)

/-!

## D. Components

-/

/-- The components of the contraction in the standard arrangement of indices,
`(tr T)^ρ = ∑ μ, T^ρμ_μ`, with one label `μ j` per pair `j`. -/
lemma tensorBasis_repr_contrStd [Fintype κ] [Fintype J] [DecidableEq J] (c' : κ → Color K)
    (a : J → Color K) (t : Tensor S (contrColors c' a)) (φ : Π x, basisIdx (c' x).kind) :
    (S.tensorBasis c').repr (contrStd c' a t) φ = ∑ μ : Π j, basisIdx (a j).kind,
      (S.tensorBasis (contrColors c' a)).repr t (Sum.rec φ (Sum.rec μ μ)) := by
  induction t using inductionOn_pure with
  | hsmul r t ht => simp only [map_smul, Finsupp.smul_apply, ht, smul_eq_mul, Finset.mul_sum]
  | hadd t t' ht ht' => simp only [map_add, Finsupp.add_apply, ht, ht', Finset.sum_add_distrib]
  | h f =>
    -- Each contraction of a pair is a sum over one label, and the product of sums over the
    -- pairs becomes a sum over the families of labels `μ`.
    rw [contrStd_pure, map_smul, Finsupp.smul_apply, tensorBasis_repr_pure, smul_eq_mul,
      Finset.prod_congr rfl fun j _ => contr_tmul_eq_sum_basis (a j) _ _, Fintype.prod_sum,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun μ _ => ?_
    simp only [tensorBasis_repr_pure, Fintype.prod_sum_type, Finset.prod_mul_distrib]
    ring

/-- The components of a contraction, as `(tr T)^ρ = ∑ μ, T^ρμ_μ` for a trace, with one label `μ j`
per pair `j`. The components of `T` are those of `S.reindex σ T`. -/
lemma tensorBasis_repr_contr [Fintype κ] [Fintype J] [DecidableEq J]
    {a : J → Color K} (σ : ColorEquiv c (contrColors c' a)) (t : Tensor S c)
    (φ : Π x, basisIdx (c' x).kind) :
    (S.tensorBasis c').repr (contr σ t) φ = ∑ μ : Π j, basisIdx (a j).kind,
      (S.tensorBasis (contrColors c' a)).repr (S.reindex σ t) (Sum.rec φ (Sum.rec μ μ)) :=
  tensorBasis_repr_contrStd c' a _ φ

/-- The components of the contraction of one pair, `(tr T)^ρ = ∑ μ, T^ρμ_μ` with a single label
`μ`. -/
lemma tensorBasis_repr_contr_one_pair [Fintype κ] {a : Unit → Color K}
    (σ : ColorEquiv c (contrColors c' a)) (t : Tensor S c) (φ : Π x, basisIdx (c' x).kind) :
    (S.tensorBasis c').repr (contr σ t) φ = ∑ μ : basisIdx (a ()).kind,
      (S.tensorBasis (contrColors c' a)).repr (S.reindex σ t)
        (Sum.rec φ (Sum.rec (fun _ => μ) (fun _ => μ))) := by
  rw [tensorBasis_repr_contr]
  exact Fintype.sum_equiv (Equiv.funUnique Unit (basisIdx (a ()).kind)) _ _ fun _ => rfl

/-- The components of the contraction of two pairs, `(tr T)^ρ = ∑ μ ν, T^ρμν_μν`, with one label
per pair. -/
lemma tensorBasis_repr_contr_two_pairs [Fintype κ] {a : Unit ⊕ Unit → Color K}
    (σ : ColorEquiv c (contrColors c' a)) (t : Tensor S c) (φ : Π x, basisIdx (c' x).kind) :
    (S.tensorBasis c').repr (contr σ t) φ =
      ∑ μ : basisIdx (a (.inl ())).kind, ∑ ν : basisIdx (a (.inr ())).kind,
        (S.tensorBasis (contrColors c' a)).repr (S.reindex σ t) (Sum.rec φ
          (Sum.rec (Sum.rec (fun _ => μ) fun _ => ν) (Sum.rec (fun _ => μ) fun _ => ν))) := by
  rw [tensorBasis_repr_contr, ← Fintype.sum_prod_type']
  exact Fintype.sum_equiv ((Equiv.sumPiEquivProdPi fun j => basisIdx (a j).kind).trans
    ((Equiv.piUnique _).prodCongr (Equiv.piUnique _))) _ _ fun _ => congrArg _ (funext fun j => by
      rcases j with _ | (⟨⟨⟩⟩ | ⟨⟨⟩⟩) | (⟨⟨⟩⟩ | ⟨⟨⟩⟩) <;> rfl)

end Tensor
