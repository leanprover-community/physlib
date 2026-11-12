/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.Tensors.Product
/-!

# Types whose elements are tensors

A type `M` with its own action of a group is tensorial when its elements are identified with the
tensors of a species with given colors, compatibly with the action.

## i. Overview

A Lorentz vector `v` can be stored as its components `v^μ`, on which Mathlib's analysis acts, and
is also a tensor with one upper index, on which index notation acts. An instance
`Tensorial S c M` relates the two by a Mathlib `Representation.Equiv`
`toTensor : M → Tensor S c`, so that `toTensor (Λ v) = Λ • toTensor v`.

The action on `M` is the field `rep`, not an instance `SMul G M`, since Mathlib would extend such
an instance to `M ⊗ N` acting on the left factor only. The species and colors are determined by
`M`, so an instance belongs on a type that always means one physical object, such as
`Lorentz.Vector d`.

Instances come from the space of one index (`ofIndexSpace`), from an equivalent tensorial type
(`ofEquiv`), and from tensor products (`prod`), as for a field strength in `Vector ⊗ Vector`.

## ii. Key results

- `Tensorial` : a type whose elements are tensors, compatibly with the action of the group.
- `Tensorial.toTensor_rep` : `toTensor (Λ m) = Λ • toTensor m`.
- `Tensorial.ofIndexSpace` : the space of one index is tensorial, as the tensors with that index,
  and `Tensorial.tensorBasis_repr_toTensor_ofIndexSpace` gives its components.
- `Tensorial.ofEquiv` : a type equivalent to a tensorial type, compatibly with the actions, is
  tensorial with the same colors.
- `Tensorial.prod` : the tensor product of two tensorial types is tensorial, with
  `Tensorial.rep_tmul` : `Λ (x ⊗ y) = Λ x ⊗ Λ y` and `Tensorial.toTensor_tmul` : the tensor of
  `x ⊗ y` is the product of the tensors.
- `Tensorial.tensorBasis_repr_toTensor_prod` : the components of the tensor of `T` in `M ⊗ N` are
  its coordinates in the product basis, and `Tensorial.tensorBasis_repr_toTensor_prod_ofIndexSpace`
  states it for two spaces of one index.

## iii. Table of contents

- A. Tensorial types
- B. Tensor products of tensorial types

## iv. References

There are no known references for the material in this module.

-/

@[expose] public section

open TensorProduct

namespace Tensor

/-!

## A. Tensorial types

-/

/-- A type `M` whose elements are the tensors of `S` with colors `c`. `M` has its own action of
the group, `rep`, and `toTensor` identifies `M` with `Tensor S c` compatibly with it. -/
class Tensorial {k : outParam Type} [RCLike k] {G : outParam Type} [Group G] {K : outParam Type}
    {basisIdx : outParam (K → Type)} [∀ κ, Fintype (basisIdx κ)]
    [∀ κ, DecidableEq (basisIdx κ)] (S : outParam (Species k G K basisIdx)) {ι : outParam Type}
    (c : outParam (ι → Color K)) (M : Type*) [AddCommMonoid M] [Module k M] where
  /-- The action of the group on `M`, such as `Λ v = Λ *ᵥ v` on Lorentz vectors. -/
  rep : Representation k G M
  /-- The elements of `M` as tensors, compatibly with the action. -/
  toTensor : rep.Equiv (Representation.ofDistribMulAction k G (Tensor S c))

namespace Tensorial

variable {k : Type} [RCLike k] {K : Type} {G : Type} [Group G] {basisIdx : K → Type}
    [∀ κ, Fintype (basisIdx κ)] [∀ κ, DecidableEq (basisIdx κ)] {S : Species k G K basisIdx}
    {ι₁ ι₂ : Type} {c₁ : ι₁ → Color K} {c₂ : ι₂ → Color K} {M N : Type*} [AddCommMonoid M]
    [Module k M] [AddCommMonoid N] [Module k N]

/-- Transforming `m` and then reading it as a tensor is transforming the tensor,
`toTensor (Λ m) = Λ • toTensor m`. -/
@[simp]
lemma toTensor_rep [Tensorial S c₁ M] (g : G) (m : M) :
    toTensor (rep g m) = g • toTensor m :=
  LinearMap.congr_fun ((toTensor (M := M)).isIntertwining' g) m

variable (S) in
/-- The space `S.V c` of one index as the tensors with the one index `![c]`, with the action
`S.rep c`. A type that is such a space, such as a Weyl spinor, gets its instance from this. -/
noncomputable abbrev ofIndexSpace (c : Color K) : Tensorial S ![c] (S.V c) where
  rep := S.rep c
  toTensor := S.oneIndexEquiv c

/-- The components of the tensor of a vector `v` of the space of one index are its components
`v^μ`. -/
lemma tensorBasis_repr_toTensor_ofIndexSpace (c : Color K) (v : S.V c)
    (μ : Π i, basisIdx (![c] i).kind) :
    (S.tensorBasis ![c]).repr (toTensor (self := ofIndexSpace S c) v) μ =
      (S.basis c).repr v (μ 0) :=
  Species.tensorBasis_repr_oneIndexEquiv c v μ

/-- A type `M` with an action `r` and an equivalence `φ` to a tensorial type `N` commuting with
the actions is tensorial with the colors of `N`. -/
noncomputable abbrev ofEquiv [Tensorial S c₁ N] {r : Representation k G M}
    (φ : r.Equiv (rep (M := N))) : Tensorial S c₁ M where
  rep := r
  toTensor := φ.trans (toTensor (M := N))

/-- The tensor of `m` is the tensor of `φ m`. -/
lemma toTensor_ofEquiv [Tensorial S c₁ N] {r : Representation k G M}
    (φ : r.Equiv (rep (M := N))) (m : M) : toTensor (self := ofEquiv φ) m = toTensor (φ m) := rfl

/-!

## B. Tensor products of tensorial types

-/

/-- The tensor product `M ⊗ N` of two tensorial types is tensorial on the indices of both, with the
product action `Λ (x ⊗ y) = Λ x ⊗ Λ y` and `x ⊗ y` read as the product of the tensors of `x` and
`y`. -/
noncomputable instance prod [Tensorial S c₁ M] [Tensorial S c₂ N] :
    Tensorial S (prodColors c₁ c₂) (M ⊗[k] N) where
  rep := (rep (M := M)).tprod (rep (M := N))
  toTensor := ((toTensor (M := M)).tensorCongr (toTensor (M := N))).trans (S.tmulEquiv c₁ c₂)

/-- The group acts on `x ⊗ y` factor by factor, `Λ (x ⊗ y) = Λ x ⊗ Λ y`. -/
@[simp]
lemma rep_tmul [Tensorial S c₁ M] [Tensorial S c₂ N] (g : G) (x : M) (y : N) :
    rep g (x ⊗ₜ[k] y) = rep g x ⊗ₜ rep g y := rfl

/-- The tensor of `x ⊗ y` is the product of the tensors of `x` and `y`. -/
@[simp]
lemma toTensor_tmul [Tensorial S c₁ M] [Tensorial S c₂ N] (x : M) (y : N) :
    toTensor (x ⊗ₜ[k] y) = S.tmulEquiv c₁ c₂ (toTensor x ⊗ₜ toTensor y) := rfl

/-- The components of the tensor of `T` in `M ⊗ N` are the coordinates of `T` in the product
basis `b₁ ⊗ b₂`, when the components of the tensors of `M` and `N` are the coordinates in `b₁` and
`b₂` at the labels `j₁ μ` and `j₂ ν`. -/
lemma tensorBasis_repr_toTensor_prod [Fintype ι₁] [Fintype ι₂] [Tensorial S c₁ M]
    [Tensorial S c₂ N] {κ₁ κ₂ : Type} (b₁ : Module.Basis κ₁ k M) (b₂ : Module.Basis κ₂ k N)
    (j₁ : (Π i, basisIdx (c₁ i).kind) → κ₁) (j₂ : (Π i, basisIdx (c₂ i).kind) → κ₂)
    (h₁ : ∀ x μ, (S.tensorBasis c₁).repr (toTensor x) μ = b₁.repr x (j₁ μ))
    (h₂ : ∀ y ν, (S.tensorBasis c₂).repr (toTensor y) ν = b₂.repr y (j₂ ν)) (T : M ⊗[k] N)
    (μ : Π s, basisIdx (prodColors c₁ c₂ s).kind) :
    (S.tensorBasis (prodColors c₁ c₂)).repr (toTensor T) μ =
      (b₁.tensorProduct b₂).repr T (j₁ fun i => μ (.inl i), j₂ fun i => μ (.inr i)) := by
  induction T using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul x y =>
    rw [toTensor_tmul, Species.tensorBasis_repr_tmulEquiv, h₁, h₂,
      Module.Basis.tensorProduct_repr_tmul_apply, smul_eq_mul, mul_comm]

section ofIndexSpace

attribute [local instance] ofIndexSpace

/-- The components `T^μν` of the tensor of `T` in `V a ⊗ V b`, each factor the space of one
index, are the coordinates of `T` in Mathlib's product basis. -/
lemma tensorBasis_repr_toTensor_prod_ofIndexSpace (a b : Color K) (T : S.V a ⊗[k] S.V b)
    (μ : Π s, basisIdx (prodColors ![a] ![b] s).kind) :
    (S.tensorBasis (prodColors ![a] ![b])).repr (toTensor T) μ =
      ((S.basis a).tensorProduct (S.basis b)).repr T (μ (.inl 0), μ (.inr 0)) :=
  tensorBasis_repr_toTensor_prod _ _ (fun ν => ν 0) (fun ν => ν 0)
    (tensorBasis_repr_toTensor_ofIndexSpace a) (tensorBasis_repr_toTensor_ofIndexSpace b) T μ

end ofIndexSpace

end Tensorial

end Tensor
