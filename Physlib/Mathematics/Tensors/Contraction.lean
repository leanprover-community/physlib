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
`T^ρμ_μ` or the full contraction `T^μν U_μν`, and its laws.

## i. Overview

A contraction pairs indices of dual colors and sums over their common label, as in the trace
`(tr T)^ρ = T^ρμ_μ` of a Lorentz tensor `T^ρμ_ν` on the slots `Fin 3`. On a pure tensor
`u ⊗ v ⊗ α` the trace is `(v^μ α_μ) u`, where `v^μ α_μ` is the species contraction `S.contr`.

Contraction is first defined with the slots in a standard arrangement, where they come in three
groups. The remaining slots are labeled by a type `κ`, and the pairs by a type `J`. Each pair
`j : J` has a first slot, of color `a j`, and a second slot, of the dual color `(a j).dual`. The
slots are then labeled by the disjoint union `κ ⊕ (J ⊕ J)`, with `inl x` the remaining slot `x`,
`inr (inl j)` the first slot of the pair `j` and `inr (inr j)` its second slot. For the trace
`T^ρμ_μ`, `κ = Fin 1` holds `ρ` and `J = Unit` holds the single pair `μ`. These colors are
`contrColors c' a`, and `Tensor.contrStd c' a` contracts each pair by `S.contr (a j)`, with the
first slot as its first argument. The colors of a pair are dual by construction, so no cast
appears.

Any other choice of pairs is reduced to the standard arrangement by a relabeling
`σ : ColorEquiv c (contrColors c' a)`, which sends each slot to its place there.
`Tensor.contr σ` is `S.reindex σ` followed by `Tensor.contrStd c' a`. Since `σ` keeps colors, the
two slots of each pair are dual without a separate hypothesis. For the trace, `σ` sends
`0 ↦ inl 0`, `1 ↦ inr (inl ())` and `2 ↦ inr (inr ())`. The index notation `{T | ρ μ μ}ᵀ` builds
`σ` from the repeated name.

Two tensors are contracted by contracting their product. In the full contraction `T^μν U_μν` the
product `T ⊗ U` has four slots, which form two pairs and leave no slot, `κ = Empty`. The following
laws let a contraction of several tensors be computed one step at a time.
- The order in which the pairs are listed does not matter. Relabeling the pairs gives the same
  contraction.
- A tensor that changes sign when its pairs are permuted contracts to zero, since its contraction
  equals its own negative. For `A` antisymmetric and `B` symmetric, renaming `μ ↔ ν` turns
  `A^μν B_μν` into `A^νμ B_νμ = -A^μν B_μν`, so `A^μν B_μν = 0`.
- Pairs can be contracted one at a time. Contracting `μ` and then `ν` in `T^μ_μ^ν_ν` is
  contracting both pairs at once.
- A factor that takes no part in a contraction can be multiplied before or after it,
  `(T^μ_μν) U^ρ = (T ⊗ U)^μ_μν^ρ`.

For tensors on two slots, the contraction `M^μ_ν N^ν_ρ` of the inner indices is the product of
matrices. The components of a contraction are sums of components of the tensor,
`(tr T)^ρ = ∑ μ, T^ρμ_μ`, since the bases of a color and its dual are dual.

## ii. Key results

- `contrColors` gives the colors of the standard arrangement, the remaining slots and then the
  pairs.
- `Species.Tensor.contrStd` contracts a tensor in the standard arrangement.
- `Species.Tensor.contr` contracts the pairs of indices chosen by `σ`, as in `T^ρμ_μ`.
- `Species.Tensor.contr_pure` gives the contraction of a pure tensor.
- `Species.Tensor.contr_smul` proves that contraction commutes with the group action.
- `Species.Tensor.contr_congr` proves that a contraction depends only on the bijection of slots.
- `Species.Tensor.contr_reindex_pairs` proves that relabeling the pairs does not change the
  contraction, and `Species.Tensor.contr_reindex` and `Species.Tensor.reindex_contr` absorb a
  relabeling of the slots before or after a contraction.
- `ColorEquiv.SamePair` says that two choices of pairs contract the same two slots, and
  `Species.Tensor.contr_eq_of_samePair` proves that two contractions of the same pairs of slots,
  in any order, are equal.
- `Species.Tensor.contr_eq_zero_of_reindex_eq_neg` and
  `Species.Tensor.contr_tmulEquiv_eq_zero_of_antisymm_symm` prove `A^μν B_μν = 0` for `A`
  antisymmetric and `B` symmetric.
- `Species.Tensor.contr_contr` proves that two contractions in sequence are one, along
  `ColorEquiv.chain`.
- `Species.Tensor.tmulEquiv_contr` proves that contraction commutes with a product by a tensor
  that is not contracted, along `ColorEquiv.withSpectators`.
- `Species.Tensor.tmulEquiv_contr_right` is the same with the tensor that is not contracted on the
  left, along `ColorEquiv.withSpectatorsLeft`.
- `Species.Tensor.contr_matMul` gives the contraction `M^μ_ν N^ν_ρ` of two tensors on two slots,
  and `Species.Tensor.contr_matMul_eq_deltaTensor_iff` proves that it is the delta exactly when
  their linear maps compose to the identity.
- `Species.Tensor.contr_matMulAt_pure` contracts any slot `i` with the first slot of a tensor on
  two slots, along `ColorEquiv.matMulAt`, and `Species.Tensor.contr_deltaTensor` proves
  `T^…μ… δ_μ^ν = T^…ν…`.
- `Species.Tensor.tensorBasis_repr_contr` gives the components of a contraction.
- `Species.Tensor.tensorBasis_repr_contr_unit` and
  `Species.Tensor.tensorBasis_repr_contr_unit_sum` give the same with one and with two pairs, one
  label per pair.

## iii. Table of contents

- A. Contraction in the standard arrangement of slots
- B. Contraction of chosen pairs of indices
  - B.1. Relabeling the slots and the pairs
  - B.2. Two contractions are one
  - B.3. Products with a tensor that is not contracted
- C. Products with a tensor on two slots
- D. Components

## iv. References

None.

-/

@[expose] public section

open TensorProduct PiTensorProduct

namespace Tensors

namespace Species

variable {k : Type} [CommRing k] {K : Type} {G : Type} [Group G] {basisIdx : K → Type}
    [∀ κ, Fintype (basisIdx κ)] [∀ κ, DecidableEq (basisIdx κ)] {S : Species k G K basisIdx}

variable {ι₁ ι₂ κ κ' κ₁ J J' J₁ J₂ : Type}

namespace Tensor

/-!

## A. Contraction in the standard arrangement of slots

-/

/-- The colors of the standard arrangement `κ ⊕ (J ⊕ J)` of slots. The remaining slot `inl x` has
the color `c x`, and the two slots `inr (inl j)` and `inr (inr j)` of the pair `j` have the colors
`a j` and `(a j).dual`. -/
noncomputable abbrev _root_.Tensors.contrColors {K κ J : Type} (c : κ → Color K) (a : J → Color K) :
    κ ⊕ (J ⊕ J) → Color K :=
  prodColors c (prodColors a fun j => (a j).dual)

/-- The contraction of a tensor in the standard arrangement `κ ⊕ (J ⊕ J)`. For each pair `j` the
slot `inr (inl j)` is contracted with the slot `inr (inr j)` by `S.contr (a j)`, with the slot
`inr (inl j)` as its first argument. The slots `inl x` remain, with the colors `c`. -/
noncomputable def contrStd [Fintype J] (c : κ → Color K) (a : J → Color K) :
    S.Tensor (contrColors c a) →ₗ[k] S.Tensor c :=
  -- The pairs are split into their first halves, of colors `a`, and their second halves, of the
  -- dual colors. Each vector of a second half is read as a linear form on the first half through
  -- `S.contr`, and the halves are paired by Mathlib's `PiTensorProduct.dualDistrib`.
  (TensorProduct.rid k _).toLinearMap ∘ₗ
    (lift ((PiTensorProduct.dualDistrib ∘ₗ
      PiTensorProduct.map (fun j => (curry (S.contr (a j)).toLinearMap).flip) ∘ₗ
      (S.toPiTensor _).toLinearMap).flip ∘ₗ (S.toPiTensor a).toLinearMap) ∘ₗ
      (S.tmulEquiv a _).symm.toLinearMap).lTensor _ ∘ₗ
    (S.tmulEquiv c _).symm.toLinearMap

/-- On a pure tensor the contraction multiplies the remaining vectors by the contraction of the
two vectors of each pair, as in `u ⊗ v ⊗ α ↦ (v^μ α_μ) u`. -/
lemma contrStd_pure [Fintype J] (c : κ → Color K) (a : J → Color K)
    (f : Π x, S.V (contrColors c a x)) :
    contrStd c a (S.pure f) =
      (∏ j, S.contr (a j) (f (.inr (.inl j)) ⊗ₜ f (.inr (.inr j)))) •
        S.pure (c := c) fun x => f (.inl x) := by
  simp [contrStd, PiTensorProduct.map_tprod, PiTensorProduct.dualDistrib_apply]

/-!

## B. Contraction of chosen pairs of indices

-/

/-- The contraction of the pairs of indices chosen by `σ`, as in `T^ρμ_ν ↦ T^ρμ_μ`. It is
`S.reindex σ` followed by `Tensor.contrStd c' a`. For each pair `j` the slot
`σ.toEquiv.symm (inr (inl j))`, of color `a j`, is contracted with the slot
`σ.toEquiv.symm (inr (inr j))`, of color `(a j).dual`. The slots `σ.toEquiv.symm (inl x)` remain,
with the colors `c'`. -/
noncomputable def contr [Fintype J] {c : ι₁ → Color K} {c' : κ → Color K}
    {a : J → Color K} (σ : ColorEquiv c (contrColors c' a)) : S.Tensor c →ₗ[k] S.Tensor c' :=
  contrStd c' a ∘ₗ (S.reindex σ).toLinearMap

variable {c : ι₁ → Color K} {c' : κ → Color K}

/-- On a pure tensor the contraction multiplies the remaining vectors by the contraction of the
two vectors of each pair. Each vector is moved along `σ.color_eq` to the color of its slot in the
standard arrangement. -/
lemma contr_pure [Fintype J] {a : J → Color K} (σ : ColorEquiv c (contrColors c' a))
    (f : Π x, S.V (c x)) :
    contr σ (S.pure f) =
      (∏ j, S.contr (a j) (S.cast (σ.color_eq (.inr (.inl j))) (f (σ.toEquiv.symm (.inr (.inl j))))
          ⊗ₜ S.cast (σ.color_eq (.inr (.inr j))) (f (σ.toEquiv.symm (.inr (.inr j)))))) •
        S.pure (c := c') fun x => S.cast (σ.color_eq (.inl x)) (f (σ.toEquiv.symm (.inl x))) :=
  (congrArg (contrStd c' a) (reindex_pure σ f)).trans (contrStd_pure c' a _)

/-- Contraction commutes with the group action, `(ΛT)^ρμ_μ = Λ^ρ_λ T^λμ_μ` for the action `Λ` of
`g : G`. -/
lemma contr_smul [Fintype J] {a : J → Color K} (σ : ColorEquiv c (contrColors c' a)) (g : G)
    (t : S.Tensor c) : contr σ (g • t) = g • contr σ t :=
  map_smul_of_pure (contr σ) g (fun f => by
    rw [smul_pure, contr_pure, contr_pure, smul_comm, smul_pure]
    simp only [cast_rep]
    congr 1
    exact Finset.prod_congr rfl fun j _ => S.contr_invariant (a j) g _ _) t

/-- A contraction depends only on the bijection of slots, not on the proof that it keeps colors. -/
lemma contr_congr [Fintype J] {a a' : J → Color K} (ha : a = a')
    (σ : ColorEquiv c (contrColors c' a)) (τ : ColorEquiv c (contrColors c' a'))
    (h : σ.toEquiv = τ.toEquiv) (t : S.Tensor c) : contr σ t = contr τ t := by
  subst ha
  obtain ⟨σ, _⟩ := σ
  obtain ⟨τ, _⟩ := τ
  subst h
  rfl

/-!

### B.1. Relabeling the slots and the pairs

-/

/-- Relabeling the pairs along `e : J ≃ J'` does not change the contraction. Each pair keeps its
order. -/
lemma contr_reindex_pairs [Fintype J] [Fintype J'] {a : J → Color K}
    (σ : ColorEquiv c (contrColors c' a)) (e : J ≃ J') (t : S.Tensor c) :
    contr (σ.trans ((ColorEquiv.refl c').sumCongr
      ((ColorEquiv.mk e).sumCongr (.mk e)))) t = contr σ t := by
  simp only [contr, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  rw [← reindex_reindex]
  generalize S.reindex σ t = u
  induction u using inductionOn_pure with
  | h p =>
    rw [reindex_pure, contrStd_pure, contrStd_pure]
    congr 1
    exact Equiv.prod_comp e.symm fun j => S.contr (a j) (p (.inr (.inl j)) ⊗ₜ p (.inr (.inr j)))
  | hsmul r u hu => rw [map_smul, map_smul, hu, map_smul]
  | hadd u u' hu hu' => rw [map_add, map_add, hu, hu', map_add]

/-- Relabeling the slots and then contracting is contracting along the composite relabeling. -/
lemma contr_reindex {ι₂ : Type} [Fintype J] {c₂ : ι₂ → Color K} {a : J → Color K}
    (σ : ColorEquiv c₂ (contrColors c' a)) (τ : ColorEquiv c c₂) (t : S.Tensor c) :
    contr σ (S.reindex τ t) = contr (τ.trans σ) t := by
  simp only [contr, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, reindex_reindex]

/-- Relabeling the remaining slots of a contraction is contracting along the composite
relabeling. -/
lemma reindex_contr {κ' : Type} [Fintype J] {c'' : κ' → Color K} {a : J → Color K}
    (σ : ColorEquiv c (contrColors c' a)) (τ : ColorEquiv c' c'') (t : S.Tensor c) :
    S.reindex τ (contr σ t) = contr (σ.trans (τ.sumCongr (.refl _))) t := by
  induction t using inductionOn_pure with
  | hsmul r t ht => rw [map_smul, map_smul, ht, map_smul]
  | hadd t t' ht ht' => rw [map_add, map_add, ht, ht', map_add]
  | h p =>
    rw [contr_pure, map_smul, reindex_pure, contr_pure]
    congr 1
    exact congrArg S.pure (funext fun x => by simp only [LinearEquiv.cast_apply, cast_cast]; rfl)

/-- The pair `j` of `σ` and the pair `j'` of `τ` contract the same two slots, in either order. -/
def _root_.Tensors.ColorEquiv.SamePair {a : J → Color K} {a' : J' → Color K}
    (σ : ColorEquiv c (contrColors c' a)) (τ : ColorEquiv c (contrColors c' a')) (j : J)
    (j' : J') : Prop :=
  (σ.toEquiv.symm (.inr (.inl j)) = τ.toEquiv.symm (.inr (.inl j')) ∧
      σ.toEquiv.symm (.inr (.inr j)) = τ.toEquiv.symm (.inr (.inr j'))) ∨
    (σ.toEquiv.symm (.inr (.inl j)) = τ.toEquiv.symm (.inr (.inr j')) ∧
      σ.toEquiv.symm (.inr (.inr j)) = τ.toEquiv.symm (.inr (.inl j')))

instance [DecidableEq ι₁] {a : J → Color K} {a' : J' → Color K}
    (σ : ColorEquiv c (contrColors c' a)) (τ : ColorEquiv c (contrColors c' a')) (j : J)
    (j' : J') : Decidable (σ.SamePair τ j j') := by
  unfold ColorEquiv.SamePair
  infer_instance

/-- A pair of `τ` is the same pair as at most one pair of `σ`. -/
lemma _root_.Tensors.ColorEquiv.SamePair.left_unique {a : J → Color K} {a' : J' → Color K}
    {σ : ColorEquiv c (contrColors c' a)} {τ : ColorEquiv c (contrColors c' a')} {j₁ j₂ : J}
    {j' : J'} (h₁ : σ.SamePair τ j₁ j') (h₂ : σ.SamePair τ j₂ j') : j₁ = j₂ := by
  have hσ := σ.toEquiv.symm.injective
  rcases h₁ with ⟨h₁, h₁'⟩ | ⟨h₁, h₁'⟩ <;> rcases h₂ with ⟨h₂, h₂'⟩ | ⟨h₂, h₂'⟩
  · simpa using hσ (h₁.trans h₂.symm)
  · simpa using hσ (h₁'.trans h₂.symm)
  · simpa using hσ (h₁.trans h₂'.symm)
  · simpa using hσ (h₁.trans h₂.symm)

/-- A pair of `σ` is the same pair as at most one pair of `τ`. -/
lemma _root_.Tensors.ColorEquiv.SamePair.right_unique {a : J → Color K} {a' : J' → Color K}
    {σ : ColorEquiv c (contrColors c' a)} {τ : ColorEquiv c (contrColors c' a')} {j : J}
    {j₁ j₂ : J'} (h₁ : σ.SamePair τ j j₁) (h₂ : σ.SamePair τ j j₂) : j₁ = j₂ := by
  have hτ := τ.toEquiv.symm.injective
  rcases h₁ with ⟨h₁, -⟩ | ⟨h₁, -⟩ <;> rcases h₂ with ⟨h₂, -⟩ | ⟨h₂, -⟩ <;>
    simpa using hτ (h₁.symm.trans h₂)

/-- Two contractions are equal when they keep the same slots in the same order and contract the
same pairs of slots, in any order and with either slot of a pair first. On literal slots the
hypotheses are checked by `decide`. -/
lemma contr_eq_of_samePair [Fintype J] [Fintype J'] {a : J → Color K} {a' : J' → Color K}
    (σ : ColorEquiv c (contrColors c' a)) (τ : ColorEquiv c (contrColors c' a'))
    (hfree : ∀ x, σ.toEquiv.symm (.inl x) = τ.toEquiv.symm (.inl x))
    (h₁ : ∀ j, ∃ j', σ.SamePair τ j j') (h₂ : ∀ j', ∃ j, σ.SamePair τ j j') (t : S.Tensor c) :
    contr σ t = contr τ t := by
  induction t using inductionOn_pure with
  | hsmul r t ht => rw [map_smul, map_smul, ht]
  | hadd t t' ht ht' => rw [map_add, map_add, ht, ht']
  | h p =>
    rw [contr_pure, contr_pure]
    choose g hg using h₁
    congr 1
    · -- The pair `j` of `σ` is the pair `g j` of `τ`, in the same order or swapped.
      refine Fintype.prod_bijective g ⟨fun j₁ j₂ hj => (hg j₁).left_unique (hj ▸ hg j₂),
        fun j' => (h₂ j').imp fun j hj => (hg j).right_unique hj⟩ _ _ fun j => ?_
      rcases hg j with ⟨h, h'⟩ | ⟨h, h'⟩
      · rw [cast_apply_congr p h, cast_apply_congr p h']
        exact contr_cast_tmul_cast _ _ _ _ _ _
      · rw [cast_apply_congr p h, cast_apply_congr p h']
        exact contr_cast_tmul_cast_symm _ _ _ _ _ _
    · exact congrArg S.pure (funext fun x => cast_apply_congr p (hfree x) _)

/-- A contraction of a tensor that changes sign under a relabeling `π` of its slots is zero, when
`π` only permutes the pairs along `e` and keeps the remaining slots. The hypothesis `ht` has the
form of the index notation `{T | μ ν = -T | ν μ}ᵀ`. -/
lemma contr_eq_zero_of_reindex_eq_neg [Fintype J] [Invertible (2 : k)] {a : J → Color K}
    (σ : ColorEquiv c (contrColors c' a)) (π : ColorEquiv c c) (e : J ≃ J)
    (hπ : π.toEquiv.trans σ.toEquiv = σ.toEquiv.trans ((Equiv.refl κ).sumCongr (e.sumCongr e)))
    {t : S.Tensor c} (ht : t = S.reindex π (-t)) : contr σ t = 0 := by
  -- The colors of the pairs are invariant under `e`, since `π` keeps colors.
  have he : ∀ j, a (e.symm j) = a j := fun j => by
    set x := σ.toEquiv.symm (.inr (.inl (e.symm j)))
    have hx : π.toEquiv x = σ.toEquiv.symm (.inr (.inl j)) := by
      rw [Equiv.eq_symm_apply, ← Equiv.trans_apply, hπ]
      simp [x]
    have := π.color_eq (π.toEquiv x)
    rw [Equiv.symm_apply_apply, hx] at this
    exact (σ.color_eq _).symm.trans (this.trans (σ.color_eq _))
  have h : contr σ t + contr σ t = 0 := by
    nth_rw 2 [← contr_reindex_pairs σ e t]
    rw [contr_congr (funext he) _ (π.trans σ) hπ.symm]
    nth_rw 1 [ht]
    simp only [contr, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      reindex_reindex, map_neg, neg_add_cancel]
  rw [← one_smul k (contr σ t), ← invOf_mul_self (2 : k), mul_smul, two_smul, h, smul_zero]

/-- `A^μν B_μν = 0` for `A` antisymmetric and `B` symmetric. The contraction of `A ⊗ B` is zero
when `π₁` reverses the sign of `A`, `π₂` fixes `B`, and together they only permute the pairs. The
hypotheses have the form of the index notation, `{A | μ ν = -A | ν μ}ᵀ` and
`{B | μ ν = B | ν μ}ᵀ`. -/
lemma contr_tmulEquiv_eq_zero_of_antisymm_symm [Fintype J] [Invertible (2 : k)]
    {c₁ : ι₁ → Color K} {c₂ : ι₂ → Color K} {a : J → Color K}
    (σ : ColorEquiv (prodColors c₁ c₂) (contrColors c' a)) (π₁ : ColorEquiv c₁ c₁)
    (π₂ : ColorEquiv c₂ c₂) (e : J ≃ J)
    (hπ : (π₁.sumCongr π₂).toEquiv.trans σ.toEquiv =
      σ.toEquiv.trans ((Equiv.refl κ).sumCongr (e.sumCongr e)))
    {A : S.Tensor c₁} {B : S.Tensor c₂} (hA : A = S.reindex π₁ (-A)) (hB : B = S.reindex π₂ B) :
    contr σ (S.tmulEquiv c₁ c₂ (A ⊗ₜ B)) = 0 :=
  contr_eq_zero_of_reindex_eq_neg σ _ e hπ (by
    rw [← map_neg, ← neg_tmul, reindex_sumCongr_tmulEquiv, ← hA, ← hB])

/-!

### B.2. Two contractions are one

-/

/-- The pairs of two contractions in sequence, `σ₁` and then `σ₂`, as one choice of pairs
`J₁ ⊕ J₂`, the pairs `J₁` of `σ₁` followed by the pairs `J₂` of `σ₂`. -/
noncomputable def _root_.Tensors.ColorEquiv.chain {c : ι₁ → Color K} {c₁ : κ₁ → Color K}
    {c' : κ → Color K} {a₁ : J₁ → Color K} {a₂ : J₂ → Color K}
    (σ₁ : ColorEquiv c (contrColors c₁ a₁)) (σ₂ : ColorEquiv c₁ (contrColors c' a₂)) :
    ColorEquiv c (contrColors c' (prodColors a₁ a₂)) :=
  σ₁.trans ((σ₂.sumCongr (.refl _)).trans ⟨(Equiv.sumAssoc _ _ _).trans
    (Equiv.sumCongr (Equiv.refl _) ((Equiv.sumComm _ _).trans (Equiv.sumSumSumComm _ _ _ _))),
    by rintro (_ | (_ | _) | (_ | _)) <;> rfl⟩)

/-- Two contractions in sequence are one contraction, along `σ₁.chain σ₂`. Contracting `μ` and
then `ν` in `T^μ_μ^ν_ν` is contracting both pairs at once. -/
lemma contr_contr [Fintype J₁] [Fintype J₂] {c₁ : κ₁ → Color K} {a₁ : J₁ → Color K}
    {a₂ : J₂ → Color K} (σ₁ : ColorEquiv c (contrColors c₁ a₁))
    (σ₂ : ColorEquiv c₁ (contrColors c' a₂)) (t : S.Tensor c) :
    contr σ₂ (contr σ₁ t) = contr (σ₁.chain σ₂) t := by
  induction t using inductionOn_pure with
  | h f =>
    simp only [contr_pure, map_smul, smul_smul, Fintype.prod_sum_type, LinearEquiv.cast_apply,
      cast_cast]
    rfl
  | hsmul r t ht => rw [map_smul, map_smul, ht, map_smul]
  | hadd x y hx hy => rw [map_add, map_add, hx, hy, map_add]

/-!

### B.3. Products with a tensor that is not contracted

-/

/-- The pairs `σ` of `T`, as pairs of `T ⊗ U`. The indices of `U`, on the slots `ι₂` with the
colors `d`, remain after those of `T` that are not contracted. -/
noncomputable def _root_.Tensors.ColorEquiv.withSpectators {c : ι₁ → Color K} {c' : κ → Color K}
    {a : J → Color K} (σ : ColorEquiv c (contrColors c' a)) (d : ι₂ → Color K) :
    ColorEquiv (prodColors c d) (contrColors (prodColors c' d) a) :=
  (σ.sumCongr (.refl d)).trans ((ColorEquiv.sumAssoc _ _ _).trans
    (((ColorEquiv.refl c').sumCongr (ColorEquiv.sumComm _ _)).trans
      (ColorEquiv.sumAssoc _ _ _).symm))

/-- Contracting indices of `T` and then multiplying by `U` is contracting the same indices of
`T ⊗ U`, `(T^μ_μν) U^ρ = (T ⊗ U)^μ_μν^ρ`. -/
lemma tmulEquiv_contr [Fintype J] {a : J → Color K} {d : ι₂ → Color K}
    (σ : ColorEquiv c (contrColors c' a)) (t : S.Tensor c) (u : S.Tensor d) :
    S.tmulEquiv c' d (contr σ t ⊗ₜ u) =
      contr (σ.withSpectators d) (S.tmulEquiv c d (t ⊗ₜ u)) := by
  induction t using inductionOn_pure with
  | hsmul r t ht => simp only [map_smul, ← smul_tmul', ht]
  | hadd x y hx hy => simp only [map_add, add_tmul, hx, hy]
  | h p =>
    induction u using inductionOn_pure with
    | hsmul r u hu => simp only [map_smul, tmul_smul, hu]
    | hadd x y hx hy => simp only [map_add, tmul_add, hx, hy]
    | h p' =>
      rw [contr_pure, ← smul_tmul', map_smul, tmulEquiv_pure, tmulEquiv_pure, contr_pure]
      congr 1
      exact congrArg (PiTensorProduct.tprod k) (funext fun y => by rcases y with x | m <;> rfl)

/-- The pairs `σ` of `T`, as pairs of `U ⊗ T`. The indices of `U`, with the colors `d`, come before
those of `T` that are not contracted. -/
noncomputable def _root_.Tensors.ColorEquiv.withSpectatorsLeft {c : ι₁ → Color K}
    {c' : κ → Color K} {a : J → Color K} (σ : ColorEquiv c (contrColors c' a)) (d : ι₂ → Color K) :
    ColorEquiv (prodColors d c) (contrColors (prodColors d c') a) :=
  ((ColorEquiv.refl d).sumCongr σ).trans (ColorEquiv.sumAssoc _ _ _).symm

/-- Contracting indices of `T` and then multiplying by `U` on the left is contracting the same
indices of `U ⊗ T`, `U^ρ (T^μ_μν) = (U ⊗ T)^ρμ_μν`. -/
lemma tmulEquiv_contr_right [Fintype J] {a : J → Color K} {d : ι₂ → Color K}
    (σ : ColorEquiv c (contrColors c' a)) (u : S.Tensor d) (t : S.Tensor c) :
    S.tmulEquiv d c' (u ⊗ₜ contr σ t) =
      contr (σ.withSpectatorsLeft d) (S.tmulEquiv d c (u ⊗ₜ t)) := by
  induction t using inductionOn_pure with
  | hsmul r t ht => simp only [map_smul, tmul_smul, ht]
  | hadd x y hx hy => simp only [map_add, tmul_add, hx, hy]
  | h p =>
    induction u using inductionOn_pure with
    | hsmul r u hu => simp only [map_smul, ← smul_tmul', hu]
    | hadd x y hx hy => simp only [map_add, add_tmul, hx, hy]
    | h p' =>
      rw [contr_pure, tmul_smul, map_smul, tmulEquiv_pure, tmulEquiv_pure, contr_pure]
      congr 1
      exact congrArg (PiTensorProduct.tprod k) (funext fun y => by rcases y with x | m <;> rfl)

/-!

## C. Products with a tensor on two slots

-/

/-- The pair of the product `M^μ_ν N^ν_ρ` of two tensors on two slots, the second slot of `M`, of
color `c`, with the first slot of `N`, of color `c.dual`. The slots of `μ` and `ρ` remain, as `0`
and `1`. -/
def _root_.Tensors.ColorEquiv.matMul (a c b : Color K) :
    ColorEquiv (prodColors ![a, c] ![c.dual, b]) (contrColors ![a, b] fun _ : Unit => c) where
  toEquiv.toFun
    | .inl 0 => .inl 0 | .inl 1 => .inr (.inl ()) | .inr 0 => .inr (.inr ()) | .inr 1 => .inl 1
  toEquiv.invFun
    | .inl 0 => .inl 0 | .inl 1 => .inr 1 | .inr (.inl ()) => .inl 1 | .inr (.inr ()) => .inr 0
  toEquiv.left_inv := by decide
  toEquiv.right_inv := by decide

/-- The contraction `M^μ_ν N^ν_ρ` of two tensors on two slots. It is `M` with its second factor
mapped by `N`, read through `S.contr c` as the linear map `v_ν ↦ v_ν N^ν_ρ`. -/
lemma contr_matMul (a c b : Color K) (M : S.V a ⊗[k] S.V c) (N : S.V c.dual ⊗[k] S.V b) :
    contr (ColorEquiv.matMul a c b)
        (S.tmulEquiv _ _ (S.twoSlotEquiv a c M ⊗ₜ S.twoSlotEquiv _ b N)) =
      S.twoSlotEquiv a b ((pairingToLinearMap (S.contr c).toLinearMap N).lTensor _ M) := by
  induction M using TensorProduct.inductionOn with
  | add M M' hM hM' => simp only [map_add, add_tmul, hM, hM']
  | tmul m₁ m₂ =>
  induction N using TensorProduct.inductionOn with
  | add N N' hN hN' =>
    simp only [map_add, tmul_add, LinearMap.lTensor_add, LinearMap.add_apply, hN, hN']
  | tmul n₁ n₂ =>
    simp only [twoSlotEquiv_tmul, tmulEquiv_pure, contr_pure, Fintype.prod_unique,
      LinearMap.lTensor_tmul, pairingToLinearMap_tmul, tmul_smul, map_smul]
    congr 2
    funext j
    fin_cases j <;> rfl

/-- Two tensors on two slots contract to the delta, `X_μν Y^νρ = δ_μ^ρ`, exactly when their linear
maps compose to the identity, `Y ∘ X = id`. -/
lemma contr_matMul_eq_deltaTensor_iff {x y : Color K} (X : S.V x ⊗[k] S.V y)
    (Y : S.V y.dual ⊗[k] S.V x.dual) :
    contr (ColorEquiv.matMul x y x.dual)
        (S.tmulEquiv _ _ (S.twoSlotEquiv x y X ⊗ₜ S.twoSlotEquiv _ _ Y)) = S.deltaTensor x.dual ↔
      S.toLin Y ∘ₗ S.toLin X = LinearMap.id := by
  rw [deltaTensor, contr_matMul, (S.twoSlotEquiv _ _).injective.eq_iff,
    ← (S.toLin (a := x)).injective.eq_iff, toLin, LinearEquiv.coe_ofLinearMap,
    pairingToLinearMap_lTensor]
  exact Iff.of_eq (congrArg (_ = ·) (S.snake x.dual))

/-- The relabeling of `T^…μ… F_μ^ν`, which contracts the slot `i` of `T` with the first slot of a
tensor `F` on two slots and puts the second slot of `F` in the place of `i`. It is
`ColorEquiv.matMul` at any slot of a tensor on any slots. -/
def _root_.Tensors.ColorEquiv.matMulAt [DecidableEq ι₁] {c c' : ι₁ → Color K} (i : ι₁)
    (a b : Color K) (ha : c i = a) (hi : c' i = b) (h : ∀ x, x ≠ i → c x = c' x) :
    ColorEquiv (prodColors c ![a.dual, b]) (contrColors c' fun _ : Unit => a) where
  toEquiv :=
    { toFun := Sum.elim (fun x => if x = i then .inr (.inl ()) else .inl x)
        (fun j => if j = 0 then .inr (.inr ()) else .inl i)
      invFun := Sum.elim (fun x => if x = i then .inr 1 else .inl x)
        (Sum.elim (fun _ => .inl i) fun _ => .inr 0)
      left_inv := by
        rintro (x | j)
        · by_cases hx : x = i <;> simp [hx]
        · fin_cases j <;> simp
      right_inv := by
        rintro (x | (⟨⟩ | ⟨⟩))
        · by_cases hx : x = i <;> simp [hx]
        · simp
        · simp }
  color_eq := by
    rintro (x | (⟨⟩ | ⟨⟩))
    · by_cases hx : x = i
      · subst hx
        simp [hi]
      · simp [hx, h x hx]
    · simp [ha]
    · simp

/-- On a pure tensor, contracting the slot `i` with the first slot of `F` applies `F`, read as a
linear map by `Species.toLin`, to the vector at `i`. The vectors `q` at the other slots are
those of `p`, moved along `h`. -/
lemma contr_matMulAt_pure [DecidableEq ι₁] {c c' : ι₁ → Color K} (i : ι₁) (a b : Color K)
    (ha : c i = a) (hi : c' i = b) (h : ∀ x, x ≠ i → c x = c' x) (F : S.V a.dual ⊗[k] S.V b)
    (p : Π x, S.V (c x)) (q : Π x, S.V (c' x))
    (hq : ∀ x (hx : x ≠ i), q x = S.cast (h x hx) (p x)) :
    contr (ColorEquiv.matMulAt i a b ha hi h)
        (S.tmulEquiv c ![a.dual, b] (S.pure p ⊗ₜ S.twoSlotEquiv a.dual b F)) =
      S.pure (Function.update q i (S.cast hi.symm (S.toLin F (S.cast ha (p i))))) := by
  induction F using TensorProduct.inductionOn with
  | add F F' hF hF' =>
    simp only [map_add, LinearMap.add_apply, tmul_add, hF, hF']
    rw [pure, pure, pure, MultilinearMap.map_update_add, map_add]
  | tmul x y =>
    rw [toLin_tmul, map_smul]
    conv_rhs => rw [pure, MultilinearMap.map_update_smul, map_smul, ← pure]
    rw [twoSlotEquiv_tmul, tmulEquiv_pure, contr_pure, Fintype.prod_unique]
    congr 2
    funext z
    by_cases hz : z = i
    · subst hz
      rw [Function.update_self, cast_apply_congr _ (show
        (ColorEquiv.matMulAt z a b ha hi h).toEquiv.symm (.inl z) = .inr 1 by
          simp [ColorEquiv.matMulAt])]
      rfl
    · rw [Function.update_of_ne hz, cast_apply_congr _ (show
        (ColorEquiv.matMulAt i a b ha hi h).toEquiv.symm (.inl z) = .inl z by
          simp [ColorEquiv.matMulAt, hz]), hq z hz]

/-- Contracting the slot `i` with the first slot of the delta is the identity,
`T^…μ… δ_μ^ν = T^…ν…`. -/
lemma contr_deltaTensor [DecidableEq ι₁] {c : ι₁ → Color K} (i : ι₁) (a : Color K) (ha : c i = a)
    (t : S.Tensor c) :
    contr (ColorEquiv.matMulAt i a a ha ha fun _ _ => rfl)
      (S.tmulEquiv c ![a.dual, a] (t ⊗ₜ S.deltaTensor a)) = t := by
  induction t using inductionOn_pure with
  | hsmul r t ht => rw [← smul_tmul', map_smul, map_smul, ht]
  | hadd t t' ht ht' => rw [add_tmul, map_add, map_add, ht, ht']
  | h p =>
    rw [deltaTensor, contr_matMulAt_pure i a a ha ha _ _ p p (fun _ _ => rfl), snake,
      LinearMap.id_apply, LinearEquiv.cast_apply, LinearEquiv.cast_apply, cast_cast]
    exact congrArg S.pure (Function.update_eq_self_iff.2 rfl)

/-!

## D. Components

-/

/-- The components of a contraction, as `(tr T)^ρ = ∑ μ, T^ρμ_μ` for a trace. The labels `μ` run
over the pairs, and the components of `T` are those of `S.reindex σ T`. -/
lemma tensorBasis_repr_contr [Fintype κ] [Fintype J] [DecidableEq J]
    {a : J → Color K} (σ : ColorEquiv c (contrColors c' a)) (t : S.Tensor c)
    (φ : Π x, basisIdx (c' x).kind) :
    (S.tensorBasis c').repr (contr σ t) φ = ∑ μ : Π j, basisIdx (a j).kind,
      (S.tensorBasis (contrColors c' a)).repr (S.reindex σ t) (Sum.rec φ (Sum.rec μ μ)) := by
  simp only [contr, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  generalize S.reindex σ t = u
  induction u using inductionOn_pure with
  | hsmul r u hu => simp only [map_smul, Finsupp.smul_apply, hu, smul_eq_mul, Finset.mul_sum]
  | hadd u u' hu hu' => simp only [map_add, Finsupp.add_apply, hu, hu', Finset.sum_add_distrib]
  | h f =>
    -- Each contraction of a pair is a sum over one label, and the product of sums over the
    -- pairs becomes a sum over the families of labels `μ`.
    rw [contrStd_pure, map_smul, Finsupp.smul_apply, tensorBasis_repr_pure, smul_eq_mul,
      Finset.prod_congr rfl fun j _ => contr_tmul_eq_sum_basis (a j) _ _, Fintype.prod_sum,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun μ _ => ?_
    simp only [tensorBasis_repr_pure, Fintype.prod_sum_type, Finset.prod_mul_distrib]
    ring

/-- The components of the contraction of one pair in dual bases, `(tr T)^ρ = ∑ μ, T^ρμ_μ` with a
single label `μ`. -/
lemma tensorBasis_repr_contr_unit [Fintype κ] {a : Unit → Color K}
    (σ : ColorEquiv c (contrColors c' a)) (t : S.Tensor c) (φ : Π x, basisIdx (c' x).kind) :
    (S.tensorBasis c').repr (contr σ t) φ = ∑ μ : basisIdx (a ()).kind,
      (S.tensorBasis (contrColors c' a)).repr (S.reindex σ t)
        (Sum.rec φ (Sum.rec (fun _ => μ) (fun _ => μ))) := by
  rw [tensorBasis_repr_contr]
  exact Fintype.sum_equiv (Equiv.funUnique Unit (basisIdx (a ()).kind)) _ _ fun _ => rfl

/-- The components of the contraction of two pairs in dual bases, `(tr T)^ρ = ∑ μ ν, T^ρμν_μν`
with one label per pair. -/
lemma tensorBasis_repr_contr_unit_sum [Fintype κ] {a : Unit ⊕ Unit → Color K}
    (σ : ColorEquiv c (contrColors c' a)) (t : S.Tensor c) (φ : Π x, basisIdx (c' x).kind) :
    (S.tensorBasis c').repr (contr σ t) φ =
      ∑ μ : basisIdx (a (.inl ())).kind, ∑ ν : basisIdx (a (.inr ())).kind,
        (S.tensorBasis (contrColors c' a)).repr (S.reindex σ t) (Sum.rec φ
          (Sum.rec (Sum.rec (fun _ => μ) fun _ => ν) (Sum.rec (fun _ => μ) fun _ => ν))) := by
  rw [tensorBasis_repr_contr, ← Fintype.sum_prod_type']
  exact Fintype.sum_equiv ((Equiv.sumPiEquivProdPi fun j => basisIdx (a j).kind).trans
    ((Equiv.piUnique _).prodCongr (Equiv.piUnique _))) _ _ fun _ => congrArg _ (funext fun j => by
      rcases j with _ | (⟨⟨⟩⟩ | ⟨⟨⟩⟩) | (⟨⟨⟩⟩ | ⟨⟨⟩⟩) <;> rfl)

end Tensor

end Species

end Tensors
