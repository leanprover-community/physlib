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

A Lorentz vector `v` can be stored as its components `v^μ`, a function `Fin 1 ⊕ Fin 3 → ℝ`, on
which Mathlib's analysis acts. The same vector is also a tensor with one upper index, an element of
`S.Tensor c` for a one-slot color list `c`, which is what index notation and contraction act on.
An instance `Tensorial S c M` relates the two.

The type `M` keeps its own transformation law, the representation `rep`. For a Lorentz vector it is
`Λ v = Λ *ᵥ v`, matrix times column. The identification `toTensor : M → S.Tensor c` respects the
action, `toTensor (Λ v) = Λ • toTensor v`, so `v` transforms as a tensor with colors `c`. This is
the content of the instance. `toTensor` is a Mathlib `Representation.Equiv`, a linear equivalence
that commutes with the action.

An instance on the space of one index, such as a Lorentz vector or a Weyl spinor, comes from
`ofIndexSpace`. An instance on a type equivalent to a tensorial type, compatibly with the actions,
comes from `ofEquiv`.

The tensor product `M ⊗ N` of two tensorial types is tensorial (`Tensorial.prod`). Its action is
Mathlib's product representation, `Λ (x ⊗ y) = Λ x ⊗ Λ y`, and `x ⊗ y` is read as the product of
the tensors of `x` and `y` through `Species.tmulEquiv`. A field strength `F^μν` in
`Vector ⊗ Vector` is an example.

The action on `M` is the field `rep`, not an instance `SMul G M`. If `M` has an instance
`SMul G M`, Mathlib gives `M ⊗ N` an instance `SMul G (M ⊗ N)` that acts on the left factor only,
`Λ • (x ⊗ y) = Λ x ⊗ y`. A diagonal `SMul` instance on `M ⊗ N` would give `Λ • F` two meanings.

The species and colors are determined by `M`, so a type has one tensor structure. An instance
belongs on a type that always means one physical object, such as `Lorentz.Vector d`, and not on a
type such as `Matrix (Fin 4) (Fin 4) ℝ` that is used for several.

## ii. Key results

- `Tensorial` : a type whose elements are tensors, compatibly with the action of the group.
- `Tensorial.toTensor_rep` : `toTensor (Λ m) = Λ • toTensor m`.
- `Tensorial.ofIndexSpace` : the space of one index is tensorial, with one slot.
- `Tensorial.ofEquiv` : a type equivalent to a tensorial type, compatibly with the actions, is
  tensorial with the same colors.
- `Tensorial.prod` : the tensor product of two tensorial types is tensorial.
- `Tensorial.tensorBasis_repr_toTensor_prod` : the components of the tensor of `T` in `M ⊗ N` are
  its coordinates in the product basis.

## iii. Table of contents

- A. Tensorial types
- B. Tensor products of tensorial types

## iv. References

-/

@[expose] public section

open TensorProduct

namespace Tensors

/-!

## A. Tensorial types

-/

/-- A type `M` whose elements are the tensors of `S` with colors `c`. `M` has its own action of
the group, `rep`, and `toTensor` identifies `M` with `S.Tensor c` compatibly with it. -/
class Tensorial {k : outParam Type} [CommRing k] {G : outParam Type} [Group G] {K : outParam Type}
    {basisIdx : outParam (K → Type)} [∀ κ, Fintype (basisIdx κ)]
    [∀ κ, DecidableEq (basisIdx κ)] (S : outParam (Species k G K basisIdx)) {ι : outParam Type}
    (c : outParam (ι → Color K)) (M : Type) [AddCommMonoid M] [Module k M] where
  /-- The action of the group on `M`, such as `Λ v = Λ *ᵥ v` on Lorentz vectors. -/
  rep : Representation k G M
  /-- The elements of `M` as tensors, compatibly with the action. -/
  toTensor : rep.Equiv (Representation.ofDistribMulAction k G (S.Tensor c))

namespace Tensorial

variable {k : Type} [CommRing k] {K : Type} {G : Type} [Group G] {basisIdx : K → Type}
    [∀ κ, Fintype (basisIdx κ)] [∀ κ, DecidableEq (basisIdx κ)] {S : Species k G K basisIdx}
    {ι₁ ι₂ : Type} {c₁ : ι₁ → Color K} {c₂ : ι₂ → Color K} {M N : Type} [AddCommMonoid M]
    [Module k M] [AddCommMonoid N] [Module k N]

/-- Transforming `m` and then reading it as a tensor is transforming the tensor,
`toTensor (Λ m) = Λ • toTensor m`. -/
@[simp]
lemma toTensor_rep [Tensorial S c₁ M] (g : G) (m : M) :
    toTensor (rep g m) = g • toTensor m :=
  Representation.IntertwiningMap.isIntertwining _ _ (toTensor (M := M)).toIntertwiningMap g m

variable (S) in
/-- The space `S.V c` of one index as the tensors with the one slot `![c]`, with the action
`S.rep c`. A type that is such a space, such as a Weyl spinor, gets its instance from this. -/
noncomputable abbrev ofIndexSpace (c : Color K) : Tensorial S ![c] (S.V c) where
  rep := S.rep c
  toTensor := .mk (S.oneSlotEquiv c) fun g => LinearMap.ext (S.oneSlotEquiv_rep c g)

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

/-- The tensor product `M ⊗ N` of two tensorial types is tensorial on the slots of both, with the
product action `Λ (x ⊗ y) = Λ x ⊗ Λ y` and `x ⊗ y` read as the product of the tensors of `x` and
`y`. -/
noncomputable instance prod [Tensorial S c₁ M] [Tensorial S c₂ N] :
    Tensorial S (prodColors c₁ c₂) (M ⊗[k] N) where
  rep := (rep (M := M)).tprod (rep (M := N))
  toTensor := .mk (TensorProduct.congr (toTensor (M := M)).toLinearEquiv
      (toTensor (M := N)).toLinearEquiv ≪≫ₗ S.tmulEquiv c₁ c₂) fun g => by
    ext x y
    simp [Representation.tprod_apply, Species.tmulEquiv_smul]

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

end Tensorial

end Tensors
