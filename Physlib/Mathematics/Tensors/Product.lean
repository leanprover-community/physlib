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

Let `T = T^μ_ν e_μ ⊗ e^ν` have colors `c₁` on the indices `Fin 2` and `U = U^ρ e_ρ` have colors
`c₂` on the index `Fin 1`. Their product `T ⊗ U = T^μ_ν U^ρ e_μ ⊗ e^ν ⊗ e_ρ` has the indices
`Fin 2 ⊕ Fin 1` with colors `prodColors c₁ c₂`, those of `T` on `inl i` and those of `U` on
`inr j`, so no index is renumbered. `S.tmulEquiv c₁ c₂` sends `T ⊗ₜ U` to `T ⊗ U`. It is
`Representation.Equiv.piTprodSum`, on Mathlib's `PiTensorProduct.tmulEquivDep`.

The product is associative and symmetric up to a reindexing, and the group acts on it
factor by factor. An element of `V a ⊗ V b`, such as the metric `η_μν e^μ ⊗ e^ν`, is a tensor on
two indices by `twoIndexEquiv`. The components of a product are the products of the components.

## ii. Key results

- `prodColors` gives the colors of a product.
- `Species.tmulEquiv` is the product of two tensors, `T ⊗ₜ U ↦ T ⊗ U`.
- `Species.tmulEquiv_assoc` and `Species.tmulEquiv_comm` prove `(T ⊗ U) ⊗ W = T ⊗ (U ⊗ W)` and
  `(T ⊗ U)^μρ = (U ⊗ T)^ρμ`.
- `Species.tmulEquiv_smul` proves `Λ T ⊗ Λ U = Λ (T ⊗ U)`.
- `Species.twoIndexEquiv` turns an element of `V a ⊗ V b` into a tensor on two indices.
- `Species.tensorBasis_repr_tmulEquiv` proves `(T ⊗ U)^μ_ν^ρ = T^μ_ν U^ρ`.

## iii. Table of contents

- A. The colors and reindexings of a product
- B. The product
- C. Associativity, symmetry and equivariance
- D. Tensors on one and two indices
- E. Components

## iv. References

There are no known references for the material in this module.

-/

@[expose] public section

open TensorProduct PiTensorProduct

namespace Tensor

/-!

## A. The colors and reindexings of a product

-/

/-- The colors of a product `T ⊗ U`, the colors `c₁` of `T` on the indices `inl i` and the colors
`c₂` of `U` on the indices `inr j`. It equals Mathlib's `Sum.elim c₁ c₂` by `rfl`, and it is
reducible so that `prodColors c₁ c₂ (.inl i)` reduces to `c₁ i`. -/
noncomputable abbrev prodColors {K : Type} {ι₁ ι₂ : Type} (c₁ : ι₁ → Color K)
    (c₂ : ι₂ → Color K) : ι₁ ⊕ ι₂ → Color K :=
  fun s => Sum.rec (motive := fun _ => Color K) c₁ c₂ s

namespace ColorEquiv

variable {K : Type} {ι₁ ι₂ ι₃ ι₁' ι₂' : Type}

/-- The reindexing `σ` of the indices of `T` and `τ` of the indices of `U`, as a reindexing of the
indices of `T ⊗ U`. It is Mathlib's `Equiv.sumCongr`. -/
def sumCongr {c₁ : ι₁ → Color K} {c₁' : ι₁' → Color K} {c₂ : ι₂ → Color K}
    {c₂' : ι₂' → Color K} (σ : ColorEquiv c₁ c₁') (τ : ColorEquiv c₂ c₂') :
    ColorEquiv (prodColors c₁ c₂) (prodColors c₁' c₂') :=
  ⟨Equiv.sumCongr σ.toEquiv τ.toEquiv, by rintro (j | j); exacts [σ.color_eq j, τ.color_eq j]⟩

/-- The indices of `(T ⊗ U) ⊗ W` reindexed as those of `T ⊗ (U ⊗ W)`. It is Mathlib's
`Equiv.sumAssoc`. -/
def sumAssoc (c₁ : ι₁ → Color K) (c₂ : ι₂ → Color K) (c₃ : ι₃ → Color K) :
    ColorEquiv (prodColors (prodColors c₁ c₂) c₃) (prodColors c₁ (prodColors c₂ c₃)) :=
  ⟨Equiv.sumAssoc ι₁ ι₂ ι₃, by rintro (_ | _ | _) <;> rfl⟩

/-- The indices of `T ⊗ U` reindexed as those of `U ⊗ T`. It is Mathlib's `Equiv.sumComm`. -/
def sumComm (c₁ : ι₁ → Color K) (c₂ : ι₂ → Color K) :
    ColorEquiv (prodColors c₁ c₂) (prodColors c₂ c₁) :=
  ⟨Equiv.sumComm ι₁ ι₂, by rintro (_ | _) <;> rfl⟩

/-- The indices of `(T ⊗ W) ⊗ U` reindexed as those of `(T ⊗ U) ⊗ W`, swapping the last two
factors. -/
noncomputable def swapLast (c₁ : ι₁ → Color K) (c₂ : ι₂ → Color K) (c₃ : ι₃ → Color K) :
    ColorEquiv (prodColors (prodColors c₁ c₃) c₂) (prodColors (prodColors c₁ c₂) c₃) :=
  (sumAssoc c₁ c₃ c₂).trans (((refl c₁).sumCongr (sumComm c₃ c₂)).trans
    (sumAssoc c₁ c₂ c₃).symm)

end ColorEquiv

namespace Species

variable {k : Type} [RCLike k] {K : Type} {G : Type} [Group G] {basisIdx : K → Type}
    [∀ κ, Fintype (basisIdx κ)] [∀ κ, DecidableEq (basisIdx κ)] {S : Species k G K basisIdx}

variable {ι₁ ι₂ ι₃ ι₁' ι₂' : Type}

/-!

## B. The product

-/

variable (S) in
/-- The product of tensors, `T ⊗ₜ U ↦ T ⊗ U` with `(T ⊗ U)^μ_ν^ρ = T^μ_ν U^ρ`. The indices of
`T` become the indices `inl i` and those of `U` the indices `inr j`. It is
`Representation.Equiv.piTprodSum`. -/
noncomputable def tmulEquiv (c₁ : ι₁ → Color K) (c₂ : ι₂ → Color K) :
    ((S.tensorRep c₁).tprod (S.tensorRep c₂)).Equiv (S.tensorRep (prodColors c₁ c₂)) :=
  Representation.Equiv.piTprodSum fun s => S.rep (prodColors c₁ c₂ s)

/-- The product of the pure tensors of the vectors `f₁` and `f₂` is the pure tensor with the vectors
`f₁` at the indices `inl i` and the vectors `f₂` at the indices `inr j`. -/
@[simp]
lemma tmulEquiv_pure (c₁ : ι₁ → Color K) (c₂ : ι₂ → Color K) (f₁ : Π i, S.V (c₁ i))
    (f₂ : Π j, S.V (c₂ j)) :
    S.tmulEquiv c₁ c₂ (S.pure f₁ ⊗ₜ S.pure f₂) =
      S.pure fun s => Sum.rec (motive := fun s => S.V (prodColors c₁ c₂ s)) f₁ f₂ s :=
  Representation.Equiv.piTprodSum_tmul (fun s => S.rep (prodColors c₁ c₂ s)) f₁ f₂

/-- The inverse of the product splits a pure tensor into the pure tensor of its vectors at the
indices `inl i` and the pure tensor of its vectors at the indices `inr j`. -/
@[simp]
lemma tmulEquiv_symm_pure (c₁ : ι₁ → Color K) (c₂ : ι₂ → Color K)
    (f : Π s, S.V (prodColors c₁ c₂ s)) :
    (S.tmulEquiv c₁ c₂).symm (S.pure f) =
      S.pure (c := c₁) (fun i => f (.inl i)) ⊗ₜ S.pure (c := c₂) fun j => f (.inr j) :=
  tmulEquivDep_symm_apply _ _ f

/-!

## C. Associativity, symmetry and equivariance

-/

/-- The product is associative, `(T ⊗ U) ⊗ W = T ⊗ (U ⊗ W)`, after the indices of the left side
are regrouped by `ColorEquiv.sumAssoc`. -/
lemma tmulEquiv_assoc (c₁ : ι₁ → Color K) (c₂ : ι₂ → Color K) (c₃ : ι₃ → Color K)
    (t₁ : Tensor S c₁) (t₂ : Tensor S c₂) (t₃ : Tensor S c₃) :
    S.reindex (ColorEquiv.sumAssoc c₁ c₂ c₃)
        (S.tmulEquiv _ _ (S.tmulEquiv c₁ c₂ (t₁ ⊗ₜ t₂) ⊗ₜ t₃)) =
      S.tmulEquiv _ _ (t₁ ⊗ₜ S.tmulEquiv c₂ c₃ (t₂ ⊗ₜ t₃)) :=
  LinearMap.congr_fun (f := (S.reindex (ColorEquiv.sumAssoc c₁ c₂ c₃)).toLinearMap ∘ₗ
      (S.tmulEquiv _ c₃).toLinearMap ∘ₗ (S.tmulEquiv c₁ c₂).toLinearMap.rTensor _)
    (g := (S.tmulEquiv c₁ _).toLinearMap ∘ₗ (S.tmulEquiv c₂ c₃).toLinearMap.lTensor _ ∘ₗ
      (TensorProduct.assoc k _ _ _).toLinearMap)
    (by
      ext f₁ f₂ f₃
      simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
        LinearMap.coe_restrictScalars, LinearMap.comp_apply, LinearMap.rTensor_tmul,
        LinearMap.lTensor_tmul, LinearEquiv.coe_coe, assoc_tmul,
        Representation.Equiv.coe_toLinearMap, tmulEquiv_pure, reindex_pure]
      exact congrArg S.pure (funext fun s => by rcases s with _ | _ | _ <;> rfl))
    ((t₁ ⊗ₜ t₂) ⊗ₜ t₃)

/-- The product is symmetric, `(T ⊗ U)^μρ = (U ⊗ T)^ρμ`, after the indices of `U` are moved in
front by `ColorEquiv.sumComm`. -/
lemma tmulEquiv_comm (c₁ : ι₁ → Color K) (c₂ : ι₂ → Color K) (t₁ : Tensor S c₁)
    (t₂ : Tensor S c₂) :
    S.reindex (ColorEquiv.sumComm c₁ c₂) (S.tmulEquiv c₁ c₂ (t₁ ⊗ₜ t₂)) =
      S.tmulEquiv c₂ c₁ (t₂ ⊗ₜ t₁) :=
  LinearMap.congr_fun (f := (S.reindex (ColorEquiv.sumComm c₁ c₂)).toLinearMap ∘ₗ
      (S.tmulEquiv c₁ c₂).toLinearMap)
    (g := (S.tmulEquiv c₂ c₁).toLinearMap ∘ₗ (TensorProduct.comm k _ _).toLinearMap)
    (by
      ext f₁ f₂
      simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
        LinearMap.coe_restrictScalars, LinearMap.comp_apply, LinearEquiv.coe_coe, comm_tmul,
        Representation.Equiv.coe_toLinearMap, tmulEquiv_pure, reindex_pure]
      exact congrArg S.pure (funext fun s => by rcases s with _ | _ <;> rfl)) _

/-- Reindexing the product along `σ.sumCongr τ` is reindexing its factors along `σ` and `τ`. -/
lemma reindex_sumCongr_tmulEquiv {c₁ : ι₁ → Color K} {c₁' : ι₁' → Color K}
    {c₂ : ι₂ → Color K} {c₂' : ι₂' → Color K} (σ : ColorEquiv c₁ c₁') (τ : ColorEquiv c₂ c₂')
    (t₁ : Tensor S c₁) (t₂ : Tensor S c₂) :
    S.reindex (σ.sumCongr τ) (S.tmulEquiv c₁ c₂ (t₁ ⊗ₜ t₂)) =
      S.tmulEquiv c₁' c₂' (S.reindex σ t₁ ⊗ₜ S.reindex τ t₂) :=
  LinearMap.congr_fun (f := (S.reindex (σ.sumCongr τ)).toLinearMap ∘ₗ
      (S.tmulEquiv c₁ c₂).toLinearMap)
    (g := (S.tmulEquiv c₁' c₂').toLinearMap ∘ₗ
      TensorProduct.map (S.reindex σ).toLinearMap (S.reindex τ).toLinearMap)
    (by
      ext f₁ f₂
      simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
        LinearMap.coe_restrictScalars, LinearMap.comp_apply, TensorProduct.map_tmul,
        Representation.Equiv.coe_toLinearMap, tmulEquiv_pure, reindex_pure]
      exact congrArg S.pure (funext fun s => by rcases s with _ | _ <;> rfl)) _

/-- Reindexing the first factor reindexes the product. With `tmulEquiv_reindex_right` it moves
reindexings out of products, the form used by index notation. -/
lemma tmulEquiv_reindex_left {c₁ : ι₁ → Color K} {c₁' : ι₁' → Color K} {c₂ : ι₂ → Color K}
    (σ : ColorEquiv c₁ c₁') (t₁ : Tensor S c₁) (t₂ : Tensor S c₂) :
    S.tmulEquiv c₁' c₂ (S.reindex σ t₁ ⊗ₜ t₂) =
      S.reindex (σ.sumCongr (.refl c₂)) (S.tmulEquiv c₁ c₂ (t₁ ⊗ₜ t₂)) := by
  rw [reindex_sumCongr_tmulEquiv, reindex_refl, Representation.Equiv.refl_apply]

/-- Reindexing the second factor reindexes the product. With `tmulEquiv_reindex_left` it moves
reindexings out of products, the form used by index notation. -/
lemma tmulEquiv_reindex_right {c₁ : ι₁ → Color K} {c₂ : ι₂ → Color K} {c₂' : ι₂' → Color K}
    (σ : ColorEquiv c₂ c₂') (t₁ : Tensor S c₁) (t₂ : Tensor S c₂) :
    S.tmulEquiv c₁ c₂' (t₁ ⊗ₜ S.reindex σ t₂) =
      S.reindex ((ColorEquiv.refl c₁).sumCongr σ) (S.tmulEquiv c₁ c₂ (t₁ ⊗ₜ t₂)) := by
  rw [reindex_sumCongr_tmulEquiv, reindex_refl, Representation.Equiv.refl_apply]

/-- Swapping the last two factors of a product, `(T ⊗ W) ⊗ U = (T ⊗ U) ⊗ W` after the indices of
`U` are moved before those of `W` by `ColorEquiv.swapLast`. -/
lemma tmulEquiv_swapLast {c₁ : ι₁ → Color K} {c₂ : ι₂ → Color K} {c₃ : ι₃ → Color K}
    (t₁ : Tensor S c₁) (t₂ : Tensor S c₂) (t₃ : Tensor S c₃) :
    S.reindex (ColorEquiv.swapLast c₁ c₂ c₃)
        (S.tmulEquiv _ c₂ (S.tmulEquiv c₁ c₃ (t₁ ⊗ₜ t₃) ⊗ₜ t₂)) =
      S.tmulEquiv _ c₃ (S.tmulEquiv c₁ c₂ (t₁ ⊗ₜ t₂) ⊗ₜ t₃) := by
  rw [ColorEquiv.swapLast, ← reindex_reindex, ← reindex_reindex, tmulEquiv_assoc,
    ← tmulEquiv_reindex_right, tmulEquiv_comm, ← reindex_symm, ← tmulEquiv_assoc]
  exact (S.reindex _).symm_apply_apply _

/-- The product commutes with the group action, `Λ T ⊗ Λ U = Λ (T ⊗ U)`, as in
`(Λ^μ_α T^α) (Λ^ρ_β U^β) = Λ^μ_α Λ^ρ_β (T ⊗ U)^αβ`. -/
lemma tmulEquiv_smul (c₁ : ι₁ → Color K) (c₂ : ι₂ → Color K) (g : G) (t₁ : Tensor S c₁)
    (t₂ : Tensor S c₂) :
    S.tmulEquiv c₁ c₂ ((g • t₁) ⊗ₜ (g • t₂)) = g • S.tmulEquiv c₁ c₂ (t₁ ⊗ₜ t₂) :=
  Representation.IntertwiningMap.isIntertwining _ _ (S.tmulEquiv c₁ c₂).toIntertwiningMap g
    (t₁ ⊗ₜ t₂)

/-!

## D. Tensors on one and two indices

A species gives objects with two indices, such as a metric `η_μν`, in Mathlib's binary
tensor product `V a ⊗ V b`. `twoIndexEquiv` identifies this space with the tensors
`Tensor S ![a, b]` on two indices, so that such an object can be used in index notation.

-/

variable (S) in
/-- A vector `v` of `V c` as a tensor with the one index `![c]`. It is
`Representation.Equiv.piTprodOfSubsingleton`. -/
noncomputable def oneIndexEquiv (c : Color K) : (S.rep c).Equiv (S.tensorRep ![c]) :=
  Representation.Equiv.piTprodOfSubsingleton (fun i => S.rep (![c] i)) 0

/-- The tensor of `v` is the pure tensor with `v` on its one index. -/
@[simp]
lemma oneIndexEquiv_apply (c : Color K) (v : S.V c) :
    S.oneIndexEquiv c v = S.pure (c := ![c]) (Fin.cons v finZeroElim) :=
  congrArg S.pure (funext fun i => by fin_cases i; rfl)

/-- The tensor of the basis vector `S.basis c (μ 0)` is the basis tensor with label `μ`. -/
lemma oneIndexEquiv_basis (c : Color K) (μ : Π i, basisIdx (![c] i).kind) :
    S.oneIndexEquiv c (S.basis c (μ 0)) = S.tensorBasis ![c] μ := by
  rw [oneIndexEquiv_apply, tensorBasis_apply]
  exact congrArg S.pure (funext fun j => by fin_cases j; rfl)

variable (S) in
/-- An element of `V a ⊗ V b` as a tensor with colors `![a, b]`, as the metric `η_μν e^μ ⊗ e^ν`
is the tensor `η_μν`. Each factor is a one-index tensor by `oneIndexEquiv`, and the indices
`Fin 1 ⊕ Fin 1` of their product become `Fin 2` by Mathlib's `finSumFinEquiv`. -/
noncomputable def twoIndexEquiv (a b : Color K) :
    ((S.rep a).tprod (S.rep b)).Equiv (S.tensorRep ![a, b]) :=
  ((S.oneIndexEquiv a).tensorCongr (S.oneIndexEquiv b)).trans <|
    (S.tmulEquiv ![a] ![b]).trans
      (S.reindex (ColorEquiv.mk (c₁ := prodColors ![a] ![b]) (c₂ := ![a, b]) finSumFinEquiv))

/-- The tensor of `x ⊗ₜ y` is the pure tensor with `x` on the index `0` and `y` on the index `1`. -/
@[simp]
lemma twoIndexEquiv_tmul (a b : Color K) (x : S.V a) (y : S.V b) :
    S.twoIndexEquiv a b (x ⊗ₜ y) =
      S.pure (c := ![a, b]) (Fin.cons x (Fin.cons y finZeroElim)) := by
  simp only [twoIndexEquiv, Representation.Equiv.trans_apply,
    Representation.Equiv.tensorCongr_tmul, oneIndexEquiv_apply, tmulEquiv_pure, reindex_pure]
  exact congrArg S.pure (funext fun j => by fin_cases j <;> rfl)

/-- Swapping the two indices of a tensor on two indices swaps the factors, `M^μν ↦ M^νμ`. -/
lemma reindex_twoIndexEquiv {a b : Color K} (M : S.V a ⊗[k] S.V b) :
    S.reindex (ColorEquiv.swapTwo a b) (S.twoIndexEquiv a b M) =
      S.twoIndexEquiv b a (TensorProduct.comm k _ _ M) := by
  induction M using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
    simp only [twoIndexEquiv_tmul, reindex_pure, TensorProduct.comm_tmul]
    exact congrArg S.pure (funext fun j => by fin_cases j <;> rfl)

/-!

## E. Components

The components of a product are the products of the components of its factors. The components
of a tensor on two indices are the coordinates in Mathlib's basis `Basis.tensorProduct`.

-/

/-- The components of a product are the products of the components, `(T ⊗ U)^μ_ν^ρ = T^μ_ν U^ρ`.
The labels `y (inl i)` are those of `T` and the labels `y (inr j)` those of `U`. -/
lemma tensorBasis_repr_tmulEquiv [Fintype ι₁] [Fintype ι₂] (c₁ : ι₁ → Color K)
    (c₂ : ι₂ → Color K) (t₁ : Tensor S c₁) (t₂ : Tensor S c₂)
    (y : Π s, basisIdx (prodColors c₁ c₂ s).kind) :
    (S.tensorBasis (prodColors c₁ c₂)).repr (S.tmulEquiv c₁ c₂ (t₁ ⊗ₜ t₂)) y =
      (S.tensorBasis c₁).repr t₁ (fun i => y (.inl i)) *
        (S.tensorBasis c₂).repr t₂ (fun j => y (.inr j)) :=
  LinearMap.congr_fun (f := (S.tensorBasis _).coord y ∘ₗ (S.tmulEquiv c₁ c₂).toLinearMap)
    (g := LinearMap.mul' k k ∘ₗ TensorProduct.map ((S.tensorBasis c₁).coord fun i => y (.inl i))
      ((S.tensorBasis c₂).coord fun j => y (.inr j))) (by
    ext f₁ f₂
    simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
      LinearMap.coe_restrictScalars, LinearMap.comp_apply, TensorProduct.map_tmul,
      LinearMap.mul'_apply, Module.Basis.coord_apply, Representation.Equiv.coe_toLinearMap]
    rw [tmulEquiv_pure, tensorBasis_repr_pure, tensorBasis_repr_pure, tensorBasis_repr_pure,
      Fintype.prod_sum_type]) _

/-- The components of the tensor of a vector `v` of `V c` are its components `v^μ`. -/
lemma tensorBasis_repr_oneIndexEquiv (c : Color K) (v : S.V c)
    (μ : Π i, basisIdx (![c] i).kind) :
    (S.tensorBasis ![c]).repr (S.oneIndexEquiv c v) μ = (S.basis c).repr v (μ 0) := by
  rw [oneIndexEquiv_apply, tensorBasis_repr_pure, Fin.prod_univ_one]
  rfl

/-- The components of the tensor of `M` in `V a ⊗ V b` are the coordinates of `M` in Mathlib's
product basis `Basis.tensorProduct`. -/
lemma tensorBasis_repr_twoIndexEquiv (a b : Color K) (M : S.V a ⊗[k] S.V b)
    (y : Π j, basisIdx (![a, b] j).kind) :
    (S.tensorBasis ![a, b]).repr (S.twoIndexEquiv a b M) y =
      ((S.basis a).tensorProduct (S.basis b)).repr M (y 0, y 1) := by
  induction M using TensorProduct.inductionOn with
  | add M M' hM hM' => simp only [map_add, Finsupp.add_apply, hM, hM']
  | tmul x x' =>
    rw [twoIndexEquiv_tmul, tensorBasis_repr_pure, Fin.prod_univ_two, mul_comm]
    -- `y 0` is a label at `a` only after unfolding `![a, b] 0`, so `rw` and `simp` cannot use
    -- Mathlib's lemma, and `exact` checks it up to unfolding.
    exact ((Module.Basis.tensorProduct_repr_tmul_apply _ _ _ _ _ _).trans (smul_eq_mul _ _)).symm

end Species

end Tensor
