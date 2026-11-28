/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Finite
public import Physlib.Mathematics.Tensors.Species
public import Physlib.Mathematics.ForMathlib.PiTensorProduct
/-!

# Tensors of a species

The tensors `Tensor S c` of a species `S` with colors `c : ι → Color K`, and the group action on
them index by index.

## i. Overview

`Tensor S c` is the vector space of tensors of a species `S` with one index for each `i : ι`, of
color `c i`. It is Mathlib's tensor product `⨂[k] i, S.V (c i)` of the vector spaces of the colors.
The index type `ι` is any type, such as `Fin n`. Mathlib's `⨂` is only a vector space.
`Tensor S c` also fixes how each index transforms, by the representation of its color.

For a real Lorentz tensor `T^μ_ν` the colors are `c = ![⟨vec, up⟩, ⟨vec, down⟩]`, and `T` lies in
the tensor product of the vectors and the covectors. A vector `u` and a covector `α` give the pure
tensor `u ⊗ α`, with components `u^μ α_ν`, and every tensor is a sum of pure tensors (A). A
Lorentz transformation `Λ` acts on each index by the representation of its color (B.1),
`(ΛT)^μ_ν = Λ^μ_σ (Λ⁻¹)^τ_ν T^σ_τ`. A map of tensors that commutes with this action needs the
check on pure tensors only (B.2). With a basis `e_μ` of the vectors, the products `e_μ ⊗ e^ν` are
a basis of the tensors, and the coordinates of `T` in it are the components `T^μ_ν` (C).

An upper and a lower index have different types, a vector space and its dual. So a tensor `T^μ` is
not accepted where `T_μ` is expected, also after unfolding `Tensor`.

Maps that act at one index of a tensor, such as lowering an index, are in `IndexMaps.lean`.

The definitions take the species `S` as an argument and are in the namespace `Tensor.Species`, so
they are written `S.pure f` and `S.tensorBasis c`. The instances on tensors, such as the action
`Tensor.mulAction`, are in the namespace `Tensor`.

## ii. Key results

- `Tensor` : the vector space of tensors, and `Species.pure` : a pure tensor.
- `Species.ext_pure` : linear maps out of tensors that agree on pure tensors are equal.
- `Species.tensorRep` : the group action on tensors, and `Species.smul_pure` : the action on a
  pure tensor.
- `Species.map_smul_of_pure` : a map that commutes with the group on pure tensors commutes with it
  on all tensors.
- `Species.tensorBasis` : the basis of tensors, and `Species.tensorBasis_repr_smul` : the
  components of `Λ • T`.

## iii. Table of contents

- A. Tensors
- B. The group action
  - B.1. The action on tensors
  - B.2. Maps that commute with the group
- C. The basis of tensors

## iv. References

There are no known references for the material in this module.

-/

@[expose] public section

open TensorProduct PiTensorProduct

variable {k : Type} [RCLike k] {K : Type} {G : Type} [Group G]

/-!

## A. Tensors

Every tensor is a sum of scalar multiples of pure tensors `S.pure f`, such as `u ⊗ α`. A linear
map out of tensors is fixed by its values on pure tensors (`ext_pure`). A property closed under
scalar multiplication and addition holds for all tensors if it holds for pure tensors
(`inductionOn_pure`). Tensors on finitely many indices form a finite-dimensional vector space, with
the product of the dimensions of the vector spaces of the indices (`finrank_tensor`).

-/

-- `Tensor S c` is a `def`, not an `abbrev`, so its instances are found only at `Tensor S c`. With
-- an `abbrev`, `z • x` on Mathlib's `⨂[k] i, S.V (c i)` would also be the action of the species.
-- A Mathlib lemma on `⨂` applies after `unfold Species.pure`. `map_pure` restates the common one.
/-- The tensors with colors `c : ι → Color K`, the vector space `⨂[k] i, S.V (c i)`. -/
def Tensor (S : Tensor.Species k G K) {ι : Type} (c : ι → Tensor.Color K) : Type :=
  ⨂[k] i, S.V (c i)

namespace Tensor

variable {ι : Type} {c : ι → Color K}

/-- Tensors add as elements of `⨂[k] i, S.V (c i)`. -/
instance instAddCommGroup {S : Species k G K} : AddCommGroup (Tensor S c) :=
  inferInstanceAs (AddCommGroup (⨂[k] i, S.V (c i)))

/-- Tensors are a vector space over `k`, as `⨂[k] i, S.V (c i)` is. -/
instance instModule {S : Species k G K} : Module k (Tensor S c) :=
  inferInstanceAs (Module k (⨂[k] i, S.V (c i)))

/-- Tensors on finitely many indices are finite-dimensional. -/
instance instFinite {S : Species k G K} [Finite ι] : Module.Finite k (Tensor S c) :=
  inferInstanceAs (Module.Finite k (⨂[k] i, S.V (c i)))

namespace Species

/-- The pure tensor `⨂ₜ i, f i` of vectors `f i` in `S.V (c i)`, such as `u ⊗ α`. -/
def pure (S : Species k G K) (f : Π i, S.V (c i)) : Tensor S c :=
  ⨂ₜ[k] i, f i

variable {S : Species k G K}

/-- Mathlib's `PiTensorProduct.map` of linear maps `f i` on a pure tensor, `u ⊗ v ↦ f₀ u ⊗ f₁ v`. -/
lemma map_pure {c' : ι → Color K} (f : Π i, S.V (c i) →ₗ[k] S.V (c' i))
    (p : Π i, S.V (c i)) :
    (PiTensorProduct.map f (S.pure p) : Tensor S c') = S.pure fun i => f i (p i) :=
  PiTensorProduct.map_tprod f p

/-- Induction on tensors through pure tensors, the default for `induction t`. -/
@[elab_as_elim, induction_eliminator]
lemma inductionOn_pure {motive : Tensor S c → Prop} (t : Tensor S c)
    (pure : ∀ f : Π i, S.V (c i), motive (S.pure f))
    (smul : ∀ (r : k) t, motive t → motive (r • t))
    (add : ∀ t₁ t₂, motive t₁ → motive t₂ → motive (t₁ + t₂)) : motive t :=
  PiTensorProduct.induction_on t (fun r f => smul r _ (pure f)) add

/-- Two linear maps out of tensors are equal when they agree on pure tensors. -/
@[ext]
lemma ext_pure {E : Type*} [AddCommMonoid E] [Module k E] {f g : Tensor S c →ₗ[k] E}
    (h : ∀ p : Π i, S.V (c i), f (S.pure p) = g (S.pure p)) : f = g :=
  PiTensorProduct.ext (MultilinearMap.ext h)

/-- Two equivalences of representations out of tensors are equal when they agree on pure
tensors. -/
lemma equiv_ext_pure {ρ' : Representation k G (Tensor S c)} {W : Type*} [AddCommMonoid W]
    [Module k W] {ρ : Representation k G W} {φ ψ : ρ'.Equiv ρ}
    (h : ∀ p : Π i, S.V (c i), φ (S.pure p) = ψ (S.pure p)) : φ = ψ :=
  Representation.Equiv.ext <| funext <| LinearMap.congr_fun (ext_pure h)

/-- The dimension of tensors is the product of the dimensions of their indices. A tensor `T^μ_ν` in
`1 + 3` dimensions has `4 · 4 = 16` components. -/
lemma finrank_tensor [Fintype ι] (c : ι → Color K) :
    Module.finrank k (Tensor S c) = ∏ i, Module.finrank k (S.V (c i)) :=
  Module.finrank_piTensorProduct

/-!

## B. The group action

### B.1. The action on tensors

A group element `Λ` transforms each index of a tensor by the representation of its color. For a
vector `u` and a covector `α`, `Λ • (u ⊗ α) = Λu ⊗ Λα` (`smul_pure`), with the dual action on
`α`. In components this is `u^μ α_ν ↦ Λ^μ_ρ u^ρ (Λ⁻¹)^σ_ν α_σ`.

Mathlib lets some groups of numbers act on every complex vector space by multiplication, such as
the phases `Circle` and the nonzero numbers `ℂˣ`. This multiplication also reaches a function into
tensors and a linear map into tensors. So a species over such a group takes a one-field structure
around the group, such as `structure Phase where val : Circle`, on which Mathlib defines no
multiplication. With it, `z • T` is the action of the species on tensors, on functions into
tensors and on pairs of tensors. On a linear map into tensors `z • f` is rejected. An element of
`Circle` enters `Phase` only through the constructor `⟨w⟩`.

-/

variable (S) in
/-- The action of the group on tensors, `Representation.piTprod` of the representations of the
colors. -/
noncomputable abbrev tensorRep (c : ι → Color K) : Representation k G (Tensor S c) :=
  Representation.piTprod fun i => S.rep (c i)

end Species

variable {S : Species k G K}

-- This instance and its projections have priority 1100, above Mathlib's scalar actions at 1000.
-- So `Λ • T`, `mul_smul` and `smul_add` use the action of the species, also for `Circle` and `ℂˣ`.
-- The four projections also win by being declared after Mathlib's instances. Only a direct test of
-- the `DistribMulAction` instance sees the priority of this one.
/-- The action `Λ • T` of the group on tensors, `S.tensorRep c Λ T`. -/
noncomputable instance (priority := 1100) distribMulAction :
    DistribMulAction G (Tensor S c) :=
  DistribMulAction.compHom (M := Module.End k (Tensor S c)) _ (S.tensorRep c)

/-- The action of `distribMulAction` as a `MulAction`. -/
noncomputable instance (priority := 1100) mulAction : MulAction G (Tensor S c) :=
  distribMulAction.toMulAction

/-- The action of `distribMulAction` as a `DistribSMul`. -/
noncomputable instance (priority := 1100) distribSMul : DistribSMul G (Tensor S c) :=
  distribMulAction.toDistribSMul

/-- The action of `distribMulAction` as a `SMulZeroClass`. -/
noncomputable instance (priority := 1100) smulZeroClass : SMulZeroClass G (Tensor S c) :=
  distribMulAction.toDistribSMul.toSMulZeroClass

/-- The scalar multiplication of `distribMulAction`. -/
noncomputable instance (priority := 1100) smul : SMul G (Tensor S c) :=
  distribMulAction.toSMul

-- The law is the instance `SMulCommClass G k`. `SMulCommClass k G` is not an instance, because
-- with it Mathlib's `TensorProduct.leftHasSMul` would let `Λ` act on `T ⊗ₜ U` through `T` alone,
-- as `(Λ • T) ⊗ₜ U`. A local `SMulCommClass.symm` restores that action where wanted.
/-- The action of the group commutes with the scalars, `Λ • (r • T) = r • (Λ • T)`. -/
instance smulCommClass : SMulCommClass G k (Tensor S c) where
  smul_comm g r t := map_smul (S.tensorRep c g) r t

namespace Species

/-- On a pure tensor the group acts on each vector by the representation of its color. -/
@[simp]
lemma smul_pure (g : G) (f : Π i, S.V (c i)) :
    g • S.pure f = S.pure fun i => S.rep (c i) g (f i) :=
  Representation.piTprod_tprod _ _ _

/-- A tensor with no indices is invariant, `Λ • s = s`. -/
lemma smul_eq_self_of_isEmpty [IsEmpty ι] (g : G) (t : Tensor S c) : g • t = t :=
  LinearMap.congr_fun (PiTensorProduct.map_eq_id_of_isEmpty _) t

/-!

### B.2. Maps that commute with the group

A map of tensors that commutes with the group, `φ (Λ • T) = Λ • φ T`, is Mathlib's
`Representation.IntertwiningMap` for `tensorRep`, or `Representation.Equiv` when invertible.
Lowering an index with `congrAt` in `IndexMaps.lean` is such an equivalence. The commutation
needs a check on pure tensors only (`map_smul_of_pure`), also for a semilinear map such as the
complex conjugation `ψ_α ↦ ψ̄_α̇` of spinors.

-/

/-- An intertwining map between tensors commutes with the actions, `φ (Λ • T) = Λ • φ T`. -/
lemma intertwiningMap_smul {ι' : Type} {c' : ι' → Color K}
    (φ : (S.tensorRep c).IntertwiningMap (S.tensorRep c')) (g : G) (t : Tensor S c) :
    φ (g • t) = g • φ t :=
  Representation.IntertwiningMap.isIntertwining _ _ φ g t

/-- An equivalence of representations of tensors commutes with the actions,
`φ (Λ • T) = Λ • φ T`. -/
lemma equiv_smul {ι' : Type} {c' : ι' → Color K}
    (φ : (S.tensorRep c).Equiv (S.tensorRep c')) (g : G) (t : Tensor S c) :
    φ (g • t) = g • φ t :=
  intertwiningMap_smul φ.toIntertwiningMap g t

/-- A semilinear map of tensors that commutes with `Λ` on pure tensors commutes with `Λ` on all
tensors. -/
lemma map_smul_of_pure {ι' : Type} {c' : ι' → Color K} {σ : k →+* k} {F : Type*}
    [FunLike F (Tensor S c) (Tensor S c')] [SemilinearMapClass F σ (Tensor S c) (Tensor S c')]
    (f : F) (g : G) (h : ∀ p : Π i, S.V (c i), f (g • S.pure p) = g • f (S.pure p))
    (t : Tensor S c) : f (g • t) = g • f t :=
  Representation.map_piTprod_of_tprod (τ := S.tensorRep c') (f : Tensor S c →ₛₗ[σ] Tensor S c') g
    h t

/-!

## C. The basis of tensors

`tensorBasis` is the basis `e_μ ⊗ e^ν` of `T^μ_ν`, given a basis of each kind of index. The
coordinates of a tensor in it are its components `T^μ_ν`. The components of `Λ • T` involve one
matrix of `Λ` per index (`tensorBasis_repr_smul`).

-/

variable {basisIdx : K → Type} [S.HasBasis basisIdx] [∀ κ, DecidableEq (basisIdx κ)]

section Finite

variable [∀ κ, Finite (basisIdx κ)]

variable (S) in
/-- The basis `e_μ ⊗ e^ν ⊗ …` of tensors, Mathlib's `Basis.piTensorProduct` of the bases of the
colors. -/
noncomputable def tensorBasis [Finite ι] (c : ι → Color K) :
    Module.Basis (Π i, basisIdx (c i).kind) k (Tensor S c) :=
  Basis.piTensorProduct fun i => S.basis (c i)

/-- A basis tensor is the pure tensor of basis vectors, `e_μ ⊗ e^ν ⊗ …`. -/
@[simp]
lemma tensorBasis_apply [Finite ι] (x : Π i, basisIdx (c i).kind) :
    S.tensorBasis c x = S.pure fun i => S.basis (c i) (x i) :=
  Basis.piTensorProduct_apply _ _

/-- The components of a pure tensor are products, `(u ⊗ α)^μ_ν = u^μ α_ν`. -/
lemma tensorBasis_repr_pure [Fintype ι] (f : Π i, S.V (c i))
    (x : Π i, basisIdx (c i).kind) :
    (S.tensorBasis c).repr (S.pure f) x = ∏ i, (S.basis (c i)).repr (f i) (x i) :=
  Basis.piTensorProduct_repr_tprod_apply _ _ _

end Finite

/-- The components of `Λ • T` are `(Λ • T)^φ = ∑ ψ, (∏ i, M_i (φ i) (ψ i)) T^ψ`. The labels `φ` and
`ψ` give one basis label per index, and `M_i` is the matrix of `Λ` at the index `i`. For `T^μ_ν`
with the colors `![⟨vec, up⟩, ⟨vec, down⟩]`, this is `(Λ • T)^μ_ν = Λ^μ_σ (Λ⁻¹)^τ_ν T^σ_τ`. -/
lemma tensorBasis_repr_smul [∀ κ, Fintype (basisIdx κ)] [Fintype ι] [DecidableEq ι] (Λ : G)
    (T : Tensor S c) (φ : Π i, basisIdx (c i).kind) :
    (S.tensorBasis c).repr (Λ • T) φ = ∑ ψ, (∏ i, LinearMap.toMatrix (S.basis (c i))
      (S.basis (c i)) (S.rep (c i) Λ) (φ i) (ψ i)) *
        (S.tensorBasis c).repr T ψ := by
  simp_rw [← PiTensorProduct.toMatrix_map_apply]
  exact congrFun (LinearMap.toMatrix_mulVec_repr (S.tensorBasis c) _ (S.tensorRep c Λ) T).symm φ

end Species

end Tensor
