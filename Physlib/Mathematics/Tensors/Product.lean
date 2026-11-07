/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.Tensors.Reindexing
/-!

# The product of two tensors

The product `T ⊗ U` of two tensors has the indices of `T` followed by those of `U`.

## i. Overview

Let `T = T^μ_ν e_μ ⊗ e^ν` be a Lorentz tensor with colors `c₁ = ![⟨vec, up⟩, ⟨vec, down⟩]` on the
slots `Fin 2`, and `U = U^ρ e_ρ` a vector with colors `c₂ = ![⟨vec, up⟩]` on the slot `Fin 1`.
Their product is the element

  `T ⊗ U = T^μ_ν U^ρ e_μ ⊗ e^ν ⊗ e_ρ` of the space `ℝ⁴ ⊗ (ℝ⁴)* ⊗ ℝ⁴`.

Its slots are labeled by `Fin 2 ⊕ Fin 1`. The slots `inl 0` and `inl 1` carry the indices `μ` and
`ν` of `T`, and the slot `inr 0` carries the index `ρ` of `U`. No slot is renumbered, so no
equality of colors has to be proved.

- `prodColors c₁ c₂ : ι₁ ⊕ ι₂ → Color K` gives the colors of `T ⊗ U`, those of `T` on the slots
  `inl i` and those of `U` on the slots `inr j`.
- `S.tmulEquiv c₁ c₂` sends the element `T ⊗ₜ U` of the space `S.Tensor c₁ ⊗ S.Tensor c₂` to the
  tensor `T ⊗ U` in `S.Tensor (prodColors c₁ c₂)`. It is Mathlib's
  `PiTensorProduct.tmulEquivDep`. Its inverse splits a tensor on `ι₁ ⊕ ι₂` into its two groups of
  indices.

The product is associative and symmetric up to a relabeling of slots. For a third tensor `W`,
`(T ⊗ U) ⊗ W` on `(ι₁ ⊕ ι₂) ⊕ ι₃` and `T ⊗ (U ⊗ W)` on `ι₁ ⊕ (ι₂ ⊕ ι₃)` both have components
`T^μ_ν U^ρ W^σ`, and they are equal after the relabeling `ColorEquiv.sumAssoc`. A group element
`Λ`, such as a Lorentz transformation, acts on a product factor by factor, `Λ T ⊗ Λ U = Λ (T ⊗ U)`.

An element `M` of `V a ⊗ V b` is the tensor `S.twoSlotEquiv a b M` with colors `![a, b]`. For
example, the metric `η_μν e^μ ⊗ e^ν` in `(ℝ⁴)* ⊗ (ℝ⁴)*` is the tensor `η_μν`. The delta tensor
`S.deltaTensor c` has colors `![c.dual, c]`. It is `δ_μ^ν` for an upper color `c` and `δ^μ_ν` for
a lower one.

The components of a product are the products of the components, `(T ⊗ U)^μ_ν^ρ = T^μ_ν U^ρ`
(`tensorBasis_repr_tmulEquiv`). The components of `S.twoSlotEquiv a b M` are the coordinates of
`M` in Mathlib's basis `Basis.tensorProduct` of `V a ⊗ V b` (`tensorBasis_repr_twoSlotEquiv`).

## ii. Key results

- `prodColors` gives the colors of a product.
- `ColorEquiv.sumCongr`, `ColorEquiv.sumAssoc`, `ColorEquiv.sumComm`, `ColorEquiv.swapLast` and
  `ColorEquiv.ofFinTwo` relabel the slots of a product.
- `Species.tmulEquiv` is the product of two tensors, `T ⊗ₜ U ↦ T ⊗ U`.
- `Species.tmulEquiv_assoc` and `Species.tmulEquiv_comm` prove `(T ⊗ U) ⊗ W = T ⊗ (U ⊗ W)` and
  `(T ⊗ U)^μρ = (U ⊗ T)^ρμ`.
- `Species.reindex_sumCongr_tmulEquiv` proves that relabeling each factor relabels the product,
  with `Species.tmulEquiv_reindex_left` and `Species.tmulEquiv_reindex_right` for one factor.
- `Species.tmulEquiv_swapLast` proves `(T ⊗ W) ⊗ U = (T ⊗ U) ⊗ W` up to relabeling.
- `Species.tmulEquiv_smul` proves `Λ T ⊗ Λ U = Λ (T ⊗ U)`.
- `Species.oneSlotEquiv` turns a vector of `V c` into a tensor on one slot, and
  `Species.oneSlotEquiv_rep` proves that it commutes with the group action.
- `Species.twoSlotEquiv` turns an element of `V a ⊗ V b` into a tensor on two slots, and
  `Species.deltaTensor` is the delta `δ_μ^ν`.
- `Species.twoSlotEquiv_map_rep` proves that `Λ` acts on a tensor on two slots factor by factor.
- `Species.reindex_twoSlotEquiv` proves that swapping the two slots swaps the factors,
  `M^μν ↦ M^νμ`.
- `Species.deltaTensor_invariant` proves that the delta tensor is invariant.
- `Species.tensorBasis_repr_tmulEquiv` proves `(T ⊗ U)^μ_ν^ρ = T^μ_ν U^ρ`.
- `Species.tensorBasis_repr_oneSlotEquiv` and `Species.tensorBasis_repr_twoSlotEquiv` give the
  components of a tensor on one and on two slots.
- `Species.tensorBasis_repr_deltaTensor` gives the components of the delta tensor.
- `Species.tensorBasis_repr_deltaTensor_eq_one` proves that in dual bases they form the identity
  matrix.

## iii. Table of contents

- A. The colors and relabelings of a product
- B. The product
- C. Associativity, symmetry and equivariance
- D. Tensors on one and two slots
- E. Components

## iv. References

None.

-/

@[expose] public section

open TensorProduct PiTensorProduct

namespace Tensors

/-!

## A. The colors and relabelings of a product

-/

/-- The colors of a product `T ⊗ U`, the colors `c₁` of `T` on the slots `inl i` and the colors
`c₂` of `U` on the slots `inr j`. It equals Mathlib's `Sum.elim c₁ c₂` by `rfl`. It is reducible,
so that `simp` and `rw` see `prodColors c₁ c₂ (.inl i)` as `c₁ i` and can apply Mathlib's lemmas
on `PiTensorProduct.tmulEquivDep`. -/
noncomputable abbrev prodColors {K : Type} {ι₁ ι₂ : Type} (c₁ : ι₁ → Color K)
    (c₂ : ι₂ → Color K) : ι₁ ⊕ ι₂ → Color K :=
  fun s => Sum.rec (motive := fun _ => Color K) c₁ c₂ s

namespace ColorEquiv

variable {K : Type} {ι₁ ι₂ ι₃ ι₁' ι₂' : Type}

/-- The relabeling `σ` of the slots of `T` and `τ` of the slots of `U`, as a relabeling of the
slots of `T ⊗ U`. It is Mathlib's `Equiv.sumCongr`. -/
def sumCongr {c₁ : ι₁ → Color K} {c₁' : ι₁' → Color K} {c₂ : ι₂ → Color K}
    {c₂' : ι₂' → Color K} (σ : ColorEquiv c₁ c₁') (τ : ColorEquiv c₂ c₂') :
    ColorEquiv (prodColors c₁ c₂) (prodColors c₁' c₂') :=
  ⟨Equiv.sumCongr σ.toEquiv τ.toEquiv, by rintro (j | j); exacts [σ.color_eq j, τ.color_eq j]⟩

/-- The slots of `(T ⊗ U) ⊗ W` relabeled as those of `T ⊗ (U ⊗ W)`. It is Mathlib's
`Equiv.sumAssoc`. -/
def sumAssoc (c₁ : ι₁ → Color K) (c₂ : ι₂ → Color K) (c₃ : ι₃ → Color K) :
    ColorEquiv (prodColors (prodColors c₁ c₂) c₃) (prodColors c₁ (prodColors c₂ c₃)) :=
  ⟨Equiv.sumAssoc ι₁ ι₂ ι₃, by rintro (_ | _ | _) <;> rfl⟩

/-- The slots of `T ⊗ U` relabeled as those of `U ⊗ T`. It is Mathlib's `Equiv.sumComm`. -/
def sumComm (c₁ : ι₁ → Color K) (c₂ : ι₂ → Color K) :
    ColorEquiv (prodColors c₁ c₂) (prodColors c₂ c₁) :=
  ⟨Equiv.sumComm ι₁ ι₂, by rintro (_ | _) <;> rfl⟩

/-- The slots of `(T ⊗ W) ⊗ U` relabeled as those of `(T ⊗ U) ⊗ W`, swapping the last two
factors. -/
def swapLast (c₁ : ι₁ → Color K) (c₂ : ι₂ → Color K) (c₃ : ι₃ → Color K) :
    ColorEquiv (prodColors (prodColors c₁ c₃) c₂) (prodColors (prodColors c₁ c₂) c₃) :=
  ⟨(Equiv.sumAssoc _ _ _).trans ((Equiv.sumCongr (Equiv.refl _) (Equiv.sumComm _ _)).trans
    (Equiv.sumAssoc _ _ _).symm), by rintro ((_ | _) | _) <;> rfl⟩

/-- The slots `Fin 2` of a tensor `T^μν` relabeled as the slots `Fin 1 ⊕ Fin 1` of a product
`x^μ ⊗ y^ν`. It is Mathlib's `finSumFinEquiv`, reversed. `Species.twoSlotEquiv` relabels by its
inverse. -/
noncomputable def ofFinTwo (a b : Color K) : ColorEquiv ![a, b] (prodColors ![a] ![b]) :=
  (ColorEquiv.mk (c₂ := ![a, b]) finSumFinEquiv).symm

end ColorEquiv

namespace Species

variable {k : Type} [CommRing k] {K : Type} {G : Type} [Group G] {basisIdx : K → Type}
    [∀ κ, Fintype (basisIdx κ)] [∀ κ, DecidableEq (basisIdx κ)] {S : Species k G K basisIdx}

variable {ι₁ ι₂ ι₃ ι₁' ι₂' : Type}

/-!

## B. The product

-/

variable (S) in
/-- The product of tensors, `T ⊗ₜ U ↦ T ⊗ U` with `(T ⊗ U)^μ_ν^ρ = T^μ_ν U^ρ`. The indices of
`T` sit on the slots `inl i` and those of `U` on the slots `inr j`. It is Mathlib's
`PiTensorProduct.tmulEquivDep`. -/
noncomputable def tmulEquiv (c₁ : ι₁ → Color K) (c₂ : ι₂ → Color K) :
    S.Tensor c₁ ⊗[k] S.Tensor c₂ ≃ₗ[k] S.Tensor (prodColors c₁ c₂) :=
  TensorProduct.congr (S.toPiTensor c₁) (S.toPiTensor c₂) ≪≫ₗ
    tmulEquivDep k (fun s => S.V (prodColors c₁ c₂ s)) ≪≫ₗ (S.toPiTensor _).symm

/-- The product of the pure tensors `u ⊗ α` and `w` is the pure tensor `u ⊗ α ⊗ w`. The vectors
`f₁` of the first sit on the slots `inl i` and the vectors `f₂` of the second on the slots
`inr j`. -/
@[simp]
lemma tmulEquiv_pure (c₁ : ι₁ → Color K) (c₂ : ι₂ → Color K) (f₁ : Π i, S.V (c₁ i))
    (f₂ : Π j, S.V (c₂ j)) :
    S.tmulEquiv c₁ c₂ (S.pure f₁ ⊗ₜ S.pure f₂) =
      S.pure fun s => Sum.rec (motive := fun s => S.V (prodColors c₁ c₂ s)) f₁ f₂ s := by
  simp [tmulEquiv, tmulEquivDep_apply]

/-- The inverse of the product splits a pure tensor into the pure tensors of its two groups of
slots, `u ⊗ α ⊗ w ↦ (u ⊗ α) ⊗ₜ w`. -/
@[simp]
lemma tmulEquiv_symm_pure (c₁ : ι₁ → Color K) (c₂ : ι₂ → Color K)
    (f : Π s, S.V (prodColors c₁ c₂ s)) :
    (S.tmulEquiv c₁ c₂).symm (S.pure f) =
      S.pure (c := c₁) (fun i => f (.inl i)) ⊗ₜ S.pure (c := c₂) fun j => f (.inr j) := by
  simp [tmulEquiv, tmulEquivDep_symm_apply]

/-!

## C. Associativity, symmetry and equivariance

-/

/-- The product is associative, `(T ⊗ U) ⊗ W = T ⊗ (U ⊗ W)`, after the slots of the left side
are regrouped by `ColorEquiv.sumAssoc`. -/
lemma tmulEquiv_assoc (c₁ : ι₁ → Color K) (c₂ : ι₂ → Color K) (c₃ : ι₃ → Color K)
    (t₁ : S.Tensor c₁) (t₂ : S.Tensor c₂) (t₃ : S.Tensor c₃) :
    S.reindex (ColorEquiv.sumAssoc c₁ c₂ c₃)
        (S.tmulEquiv _ _ (S.tmulEquiv c₁ c₂ (t₁ ⊗ₜ t₂) ⊗ₜ t₃)) =
      S.tmulEquiv _ _ (t₁ ⊗ₜ S.tmulEquiv c₂ c₃ (t₂ ⊗ₜ t₃)) := by
  induction t₁ using inductionOn_pure with
  | hadd t t' ht ht' => simp only [add_tmul, map_add, ht, ht']
  | hsmul r t ht => simp only [← smul_tmul', map_smul, ht]
  | h f₁ =>
    induction t₂ using inductionOn_pure with
    | hadd t t' ht ht' => simp only [add_tmul, tmul_add, map_add, ht, ht']
    | hsmul r t ht => simp only [tmul_smul, ← smul_tmul', map_smul, ht]
    | h f₂ =>
      induction t₃ using inductionOn_pure with
      | hadd t t' ht ht' => simp only [tmul_add, map_add, ht, ht']
      | hsmul r t ht => simp only [tmul_smul, map_smul, ht]
      | h f₃ =>
        simp only [tmulEquiv_pure, reindex_pure]
        exact congrArg S.pure (funext fun s => by rcases s with _ | _ | _ <;> rfl)

/-- The product is symmetric, `(T ⊗ U)^μρ = (U ⊗ T)^ρμ`, after the indices of `U` are moved in
front by `ColorEquiv.sumComm`. -/
lemma tmulEquiv_comm (c₁ : ι₁ → Color K) (c₂ : ι₂ → Color K) (t₁ : S.Tensor c₁)
    (t₂ : S.Tensor c₂) :
    S.reindex (ColorEquiv.sumComm c₁ c₂) (S.tmulEquiv c₁ c₂ (t₁ ⊗ₜ t₂)) =
      S.tmulEquiv c₂ c₁ (t₂ ⊗ₜ t₁) := by
  induction t₁ using inductionOn_pure with
  | hsmul r t ht => simp only [smul_tmul, tmul_smul, map_smul, ht]
  | hadd t t' ht ht' => simp only [add_tmul, tmul_add, map_add, ht, ht']
  | h f₁ =>
    induction t₂ using inductionOn_pure with
    | hsmul r t ht => simp only [tmul_smul, ← smul_tmul', map_smul, ht]
    | hadd t t' ht ht' => simp only [tmul_add, add_tmul, map_add, ht, ht']
    | h f₂ =>
      rw [tmulEquiv_pure, tmulEquiv_pure, reindex_pure]
      exact congrArg S.pure (funext fun s => by rcases s with _ | _ <;> rfl)

/-- Relabeling the product along `σ.sumCongr τ` is relabeling its factors along `σ` and `τ`. -/
lemma reindex_sumCongr_tmulEquiv {c₁ : ι₁ → Color K} {c₁' : ι₁' → Color K}
    {c₂ : ι₂ → Color K} {c₂' : ι₂' → Color K} (σ : ColorEquiv c₁ c₁') (τ : ColorEquiv c₂ c₂')
    (t₁ : S.Tensor c₁) (t₂ : S.Tensor c₂) :
    S.reindex (σ.sumCongr τ) (S.tmulEquiv c₁ c₂ (t₁ ⊗ₜ t₂)) =
      S.tmulEquiv c₁' c₂' (S.reindex σ t₁ ⊗ₜ S.reindex τ t₂) := by
  induction t₁ using inductionOn_pure with
  | hsmul r t ht => simp only [← smul_tmul', map_smul, ht]
  | hadd t t' ht ht' => simp only [add_tmul, map_add, ht, ht']
  | h f₁ =>
    induction t₂ using inductionOn_pure with
    | hsmul r t ht => simp only [tmul_smul, map_smul, ht]
    | hadd t t' ht ht' => simp only [tmul_add, map_add, ht, ht']
    | h f₂ =>
      simp only [tmulEquiv_pure, reindex_pure]
      exact congrArg S.pure (funext fun s => by rcases s with _ | _ <;> rfl)

/-- Relabeling the first factor relabels the product. With `tmulEquiv_reindex_right` it moves
relabelings out of products, the form `tensor_regroup` works in. -/
lemma tmulEquiv_reindex_left {c₁ : ι₁ → Color K} {c₁' : ι₁' → Color K} {c₂ : ι₂ → Color K}
    (σ : ColorEquiv c₁ c₁') (t₁ : S.Tensor c₁) (t₂ : S.Tensor c₂) :
    S.tmulEquiv c₁' c₂ (S.reindex σ t₁ ⊗ₜ t₂) =
      S.reindex (σ.sumCongr (.refl c₂)) (S.tmulEquiv c₁ c₂ (t₁ ⊗ₜ t₂)) := by
  rw [reindex_sumCongr_tmulEquiv, reindex_refl]

/-- Relabeling the second factor relabels the product. With `tmulEquiv_reindex_left` it moves
relabelings out of products, the form `tensor_regroup` works in. -/
lemma tmulEquiv_reindex_right {c₁ : ι₁ → Color K} {c₂ : ι₂ → Color K} {c₂' : ι₂' → Color K}
    (σ : ColorEquiv c₂ c₂') (t₁ : S.Tensor c₁) (t₂ : S.Tensor c₂) :
    S.tmulEquiv c₁ c₂' (t₁ ⊗ₜ S.reindex σ t₂) =
      S.reindex ((ColorEquiv.refl c₁).sumCongr σ) (S.tmulEquiv c₁ c₂ (t₁ ⊗ₜ t₂)) := by
  rw [reindex_sumCongr_tmulEquiv, reindex_refl]

/-- Swapping the last two factors of a product, `(T ⊗ W) ⊗ U = (T ⊗ U) ⊗ W` after the slots of
`U` are moved before those of `W` by `ColorEquiv.swapLast`. -/
lemma tmulEquiv_swapLast {c₁ : ι₁ → Color K} {c₂ : ι₂ → Color K} {c₃ : ι₃ → Color K}
    (t₁ : S.Tensor c₁) (t₂ : S.Tensor c₂) (t₃ : S.Tensor c₃) :
    S.reindex (ColorEquiv.swapLast c₁ c₂ c₃)
        (S.tmulEquiv _ c₂ (S.tmulEquiv c₁ c₃ (t₁ ⊗ₜ t₃) ⊗ₜ t₂)) =
      S.tmulEquiv _ c₃ (S.tmulEquiv c₁ c₂ (t₁ ⊗ₜ t₂) ⊗ₜ t₃) := by
  induction t₁ using inductionOn_pure with
  | hadd t t' ht ht' => simp only [add_tmul, map_add, ht, ht']
  | hsmul r t ht => simp only [← smul_tmul', map_smul, ht]
  | h f₁ =>
    induction t₂ using inductionOn_pure with
    | hadd t t' ht ht' => simp only [add_tmul, tmul_add, map_add, ht, ht']
    | hsmul r t ht => simp only [tmul_smul, ← smul_tmul', map_smul, ht]
    | h f₂ =>
      induction t₃ using inductionOn_pure with
      | hadd t t' ht ht' => simp only [tmul_add, add_tmul, map_add, ht, ht']
      | hsmul r t ht => simp only [tmul_smul, ← smul_tmul', map_smul, ht]
      | h f₃ =>
        simp only [tmulEquiv_pure, reindex_pure]
        exact congrArg S.pure (funext fun s => by rcases s with (_ | _) | _ <;> rfl)

/-- The product commutes with the group action, `Λ T ⊗ Λ U = Λ (T ⊗ U)`, as in
`(Λ^μ_α T^α) (Λ^ρ_β U^β) = Λ^μ_α Λ^ρ_β (T ⊗ U)^αβ`. -/
lemma tmulEquiv_smul (c₁ : ι₁ → Color K) (c₂ : ι₂ → Color K) (g : G) (t₁ : S.Tensor c₁)
    (t₂ : S.Tensor c₂) :
    S.tmulEquiv c₁ c₂ ((g • t₁) ⊗ₜ (g • t₂)) = g • S.tmulEquiv c₁ c₂ (t₁ ⊗ₜ t₂) := by
  induction t₁ using inductionOn_pure with
  | hsmul r t ht => rw [smul_comm, ← smul_tmul', map_smul, ht, ← smul_tmul', map_smul, smul_comm]
  | hadd t t' ht ht' => simp only [smul_add, add_tmul, map_add, ht, ht']
  | h f₁ =>
    induction t₂ using inductionOn_pure with
    | hsmul r t ht => rw [smul_comm, tmul_smul, map_smul, ht, tmul_smul, map_smul, smul_comm]
    | hadd t t' ht ht' => simp only [smul_add, tmul_add, map_add, ht, ht']
    | h f₂ =>
      rw [smul_pure, smul_pure, tmulEquiv_pure, tmulEquiv_pure, smul_pure]
      exact congrArg S.pure (funext fun s => by rcases s with _ | _ <;> rfl)

/-!

## D. Tensors on one and two slots

A species gives its objects with two indices, such as the delta `S.delta c`, in Mathlib's binary
tensor product `V a ⊗ V b`, built from pairs `x ⊗ₜ y`. A tensor with two slots lives in
`S.Tensor ![a, b]`, the tensor product of a family of spaces, built from vectors assigned to the
slots `0` and `1`. The two spaces are isomorphic but are different types in Lean, as `ℝ × ℝ` and
`Fin 2 → ℝ` are. `twoSlotEquiv` identifies them, so that such an object can be used as a tensor,
for example in index notation, and its components can be read with Mathlib's
`Basis.tensorProduct`. It is built from the product. Each factor is a tensor on one slot by
`oneSlotEquiv`, and the slots `Fin 1 ⊕ Fin 1` of their product are relabeled `Fin 2`. The delta
tensor `S.deltaTensor c` is the delta seen this way.

-/

variable (S) in
/-- A vector `v` of `V c` as a tensor with the one slot `![c]`, by Mathlib's
`PiTensorProduct.subsingletonEquiv`. -/
noncomputable def oneSlotEquiv (c : Color K) : S.V c ≃ₗ[k] S.Tensor ![c] :=
  (subsingletonEquiv (s := fun i => S.V (![c] i)) 0).symm ≪≫ₗ (S.toPiTensor _).symm

/-- The tensor of `v` is the pure tensor with `v` on its one slot. -/
@[simp]
lemma oneSlotEquiv_apply (c : Color K) (v : S.V c) :
    S.oneSlotEquiv c v = S.pure (c := ![c]) (Fin.cons v finZeroElim) :=
  congrArg S.pure (funext fun i => by fin_cases i; rfl)

/-- `oneSlotEquiv` commutes with the group action, `Λv ↦ Λ • v`. -/
lemma oneSlotEquiv_rep (c : Color K) (g : G) (v : S.V c) :
    S.oneSlotEquiv c (S.rep c g v) = g • S.oneSlotEquiv c v := by
  rw [oneSlotEquiv_apply, oneSlotEquiv_apply, smul_pure]
  exact congrArg S.pure (funext fun i => by fin_cases i; rfl)

/-- The tensor of the basis vector `S.basis c (μ 0)` is the basis tensor with label `μ`. -/
lemma oneSlotEquiv_basis (c : Color K) (μ : Π i, basisIdx (![c] i).kind) :
    S.oneSlotEquiv c (S.basis c (μ 0)) = S.tensorBasis ![c] μ := by
  rw [oneSlotEquiv_apply, tensorBasis_apply]
  exact congrArg S.pure (funext fun j => by fin_cases j; rfl)

variable (S) in
/-- An element of `V a ⊗ V b` as a tensor with colors `![a, b]`, as the metric `η_μν e^μ ⊗ e^ν`
is the tensor `η_μν`. Each factor is a one-slot tensor by `oneSlotEquiv`, and the slots
`Fin 1 ⊕ Fin 1` of their product are relabeled `Fin 2` by `ColorEquiv.ofFinTwo`. -/
noncomputable def twoSlotEquiv (a b : Color K) : S.V a ⊗[k] S.V b ≃ₗ[k] S.Tensor ![a, b] :=
  TensorProduct.congr (S.oneSlotEquiv a) (S.oneSlotEquiv b) ≪≫ₗ S.tmulEquiv ![a] ![b] ≪≫ₗ
    S.reindex (ColorEquiv.ofFinTwo a b).symm

/-- The tensor of `x ⊗ₜ y` is the pure tensor with `x` on the slot `0` and `y` on the slot `1`. -/
@[simp]
lemma twoSlotEquiv_tmul (a b : Color K) (x : S.V a) (y : S.V b) :
    S.twoSlotEquiv a b (x ⊗ₜ y) =
      S.pure (c := ![a, b]) (Fin.cons x (Fin.cons y finZeroElim)) := by
  simp only [twoSlotEquiv, LinearEquiv.trans_apply, TensorProduct.congr_tmul, oneSlotEquiv_apply,
    tmulEquiv_pure, reindex_pure]
  exact congrArg S.pure (funext fun j => by fin_cases j <;> rfl)

/-- `twoSlotEquiv` commutes with the group action, which acts on `M ∈ V a ⊗ V b` factor by factor,
`Λ (x ⊗ y) = Λx ⊗ Λy`. -/
lemma twoSlotEquiv_map_rep (a b : Color K) (Λ : G) (M : S.V a ⊗[k] S.V b) :
    S.twoSlotEquiv a b (TensorProduct.map (S.rep a Λ) (S.rep b Λ) M) =
      Λ • S.twoSlotEquiv a b M := by
  induction M using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  | tmul x y =>
    simp only [TensorProduct.map_tmul, twoSlotEquiv_tmul, smul_pure]
    exact congrArg S.pure (funext fun j => by fin_cases j <;> rfl)

/-- Swapping the two slots of a tensor on two slots swaps the factors, `M^μν ↦ M^νμ`. -/
lemma reindex_twoSlotEquiv {a b : Color K} {σ : ColorEquiv ![a, b] ![b, a]}
    (hσ : σ.toEquiv = Equiv.swap 0 1) (M : S.V a ⊗[k] S.V b) :
    S.reindex σ (S.twoSlotEquiv a b M) = S.twoSlotEquiv b a (TensorProduct.comm k _ _ M) := by
  obtain ⟨e, he⟩ := σ
  subst hσ
  induction M using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
    simp only [twoSlotEquiv_tmul, reindex_pure, TensorProduct.comm_tmul]
    exact congrArg S.pure (funext fun j => by fin_cases j <;> rfl)

variable (S) in
/-- The delta `S.delta c` as a tensor with colors `![c.dual, c]`. It is `δ_μ^ν` for an upper
color `c` and `δ^μ_ν` for a lower one. -/
noncomputable def deltaTensor (c : Color K) : S.Tensor ![c.dual, c] :=
  S.twoSlotEquiv c.dual c (S.delta c)

/-- The delta tensor is invariant, `Λ δ = δ`. -/
lemma deltaTensor_invariant (c : Color K) (Λ : G) : Λ • S.deltaTensor c = S.deltaTensor c := by
  rw [deltaTensor, ← twoSlotEquiv_map_rep, delta_invariant]

/-!

## E. Components

A component of a tensor with colors `c` chooses one basis label `y j` for each slot `j`, and
`(S.tensorBasis c).repr t y` is the coefficient of `t` on the basis tensor with those labels, as
`T^μ_ν` for `y = (μ, ν)`. The components of a product are the products of the components of its
factors, with the labels `y (inl i)` on the slots of the first factor and `y (inr j)` on those of
the second. The components of a tensor on two slots are the coordinates of the element of
`V a ⊗ V b` in Mathlib's basis `Basis.tensorProduct`, so they can be computed with Mathlib's lemmas
on the binary tensor product. For the delta tensor they form the identity matrix.

-/

/-- The components of a product are the products of the components, `(T ⊗ U)^μ_ν^ρ = T^μ_ν U^ρ`.
The labels `y (inl i)` are those of `T` and the labels `y (inr j)` those of `U`. -/
lemma tensorBasis_repr_tmulEquiv [Fintype ι₁] [Fintype ι₂] (c₁ : ι₁ → Color K)
    (c₂ : ι₂ → Color K) (t₁ : S.Tensor c₁) (t₂ : S.Tensor c₂)
    (y : Π s, basisIdx (prodColors c₁ c₂ s).kind) :
    (S.tensorBasis (prodColors c₁ c₂)).repr (S.tmulEquiv c₁ c₂ (t₁ ⊗ₜ t₂)) y =
      (S.tensorBasis c₁).repr t₁ (fun i => y (.inl i)) *
        (S.tensorBasis c₂).repr t₂ (fun j => y (.inr j)) := by
  induction t₁ using inductionOn_pure with
  | hsmul r t ht =>
    simp only [← smul_tmul', map_smul, Finsupp.smul_apply, ht, smul_eq_mul, mul_assoc]
  | hadd t t' ht ht' => simp only [add_tmul, map_add, Finsupp.add_apply, ht, ht', add_mul]
  | h f₁ =>
    induction t₂ using inductionOn_pure with
    | hsmul r t ht =>
      simp only [tmul_smul, map_smul, Finsupp.smul_apply, ht, smul_eq_mul, mul_left_comm]
    | hadd t t' ht ht' => simp only [tmul_add, map_add, Finsupp.add_apply, ht, ht', mul_add]
    | h f₂ =>
      rw [tmulEquiv_pure, tensorBasis_repr_pure, tensorBasis_repr_pure, tensorBasis_repr_pure,
        Fintype.prod_sum_type]

/-- The components of the tensor of a vector `v` of `V c` are its components `v^μ`. -/
lemma tensorBasis_repr_oneSlotEquiv (c : Color K) (v : S.V c)
    (μ : Π i, basisIdx (![c] i).kind) :
    (S.tensorBasis ![c]).repr (S.oneSlotEquiv c v) μ = (S.basis c).repr v (μ 0) := by
  rw [oneSlotEquiv_apply, tensorBasis_repr_pure, Fin.prod_univ_one]
  rfl

/-- The components of the tensor of `M` in `V a ⊗ V b` are the coordinates of `M` in Mathlib's
product basis `Basis.tensorProduct`. -/
lemma tensorBasis_repr_twoSlotEquiv (a b : Color K) (M : S.V a ⊗[k] S.V b)
    (y : Π j, basisIdx (![a, b] j).kind) :
    (S.tensorBasis ![a, b]).repr (S.twoSlotEquiv a b M) y =
      ((S.basis a).tensorProduct (S.basis b)).repr M (y 0, y 1) := by
  induction M using TensorProduct.inductionOn with
  | add M M' hM hM' => simp only [map_add, Finsupp.add_apply, hM, hM']
  | tmul x x' =>
    rw [twoSlotEquiv_tmul, tensorBasis_repr_pure, Fin.prod_univ_two, mul_comm]
    -- `y 0` is a label at `a` only after unfolding `![a, b] 0`, so `rw` and `simp` cannot use
    -- Mathlib's lemma, and `exact` checks it up to unfolding.
    exact ((Module.Basis.tensorProduct_repr_tmul_apply _ _ _ _ _ _).trans (smul_eq_mul _ _)).symm

/-- The components of the delta tensor are the coordinates of `S.delta c` in Mathlib's product
basis, at the pair of labels `(μ 0, μ 1)`. -/
lemma tensorBasis_repr_deltaTensor (c : Color K) (μ : Π j, basisIdx (![c.dual, c] j).kind) :
    (S.tensorBasis ![c.dual, c]).repr (S.deltaTensor c) μ =
      ((S.basis c.dual).tensorProduct (S.basis c)).repr (S.delta c) (μ 0, μ 1) :=
  tensorBasis_repr_twoSlotEquiv _ _ _ μ

/-- The components of the delta tensor form the identity matrix, `δ_μ^ν = 1` for `μ = ν` and `0`
otherwise. -/
lemma tensorBasis_repr_deltaTensor_eq_one (c : Color K)
    (μ : Π j, basisIdx (![c.dual, c] j).kind) :
    (S.tensorBasis ![c.dual, c]).repr (S.deltaTensor c) μ =
      (1 : Matrix (basisIdx c.kind) (basisIdx c.kind) k) (μ 0) (μ 1) := by
  -- The labels `μ 0` and `μ 1` are labels at `c` only after unfolding, so they are generalized.
  suffices h : ∀ a b, ((S.basis c.dual).tensorProduct (S.basis c)).repr (S.delta c) (a, b) =
      (1 : Matrix (basisIdx c.kind) (basisIdx c.kind) k) a b from
    (tensorBasis_repr_deltaTensor c μ).trans (h (μ 0) (μ 1))
  intro a b
  have h := basis_repr_pairingToLinearMap_contr c (S.delta c) (S.basis c a) b
  simp only [S.snake, LinearMap.id_apply, Module.Basis.repr_self, Finsupp.single_apply, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at h
  rw [Matrix.one_apply, ← h]

end Species

end Tensors
