/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Finite
public import Physlib.Mathematics.Tensors.ColoredSpace
public import Physlib.Mathematics.ForMathlib.PiTensorProduct
public import Physlib.Mathematics.ForMathlib.Representation
/-!

# Tensors of a species

The tensors `Tensor S c` of a species `S` with colors `c : ι → Color K`, and the group action on
them index by index.

## i. Overview

A tensor `T : Tensor S c` lies in Mathlib's space `⨂[k] i, S.colored.V (c i)`. Mathlib's `⨂` is
only a vector space. The type `Tensor S c` also fixes how each index `i` transforms, by the
representation of its color `c i`, such as `⟨vec, up⟩` for a Lorentz vector index. The index type
`ι` is any type, such as `Fin n`. One group `G` acts on all the spaces.

We define tensors and pure tensors (A). The factors are the spaces `S.colored.V (c i)` of
`ColoredSpace.lean`, a different type for each color. So a vector `v^μ` is not accepted where a
covector `w_μ` is expected. A tensor of one color is not accepted at another, also after unfolding
`Tensor`. We then let the group act index by index (B.1), and give the maps that commute with this
action (B.2). Finally we give the basis of tensors and the components `T^μ_ν` (C).

Maps that act at one index of a tensor, such as lowering an index, are in `IndexMaps.lean`.

The definitions take the species `S` as an argument and are in the namespace `Tensor.Species`, so
they are written `S.pure f` and `S.tensorBasis c`. The instances on tensors, such as the action
`Tensor.mulAction`, are in the namespace `Tensor`.

## ii. Key results

- `Tensor` is the space of tensors, and `Species.pure` is a pure tensor.
- `Species.ext_pure` proves that linear maps out of tensors that agree on pure tensors are equal.
- `Species.tensorRep` is the group action on tensors, and `Species.smul_pure` gives it on a pure
  tensor.
- `Species.map_smul_of_pure` and `Species.equivOfPure` need the commutation of a map with the
  group on pure tensors only.
- `Species.tensorBasis` is the basis of tensors, and `Species.tensorBasis_repr_smul` gives the
  components of `Λ • T`.

## iii. Table of contents

- A. Tensors
- B. The group action
  - B.1. The action on tensors
  - B.2. Maps that commute with the group
- C. The basis of tensors

## iv. References

* None.

-/

@[expose] public section

open TensorProduct PiTensorProduct

variable {k : Type} [RCLike k] {K : Type} {G : Type} [Group G] {basisIdx : K → Type}
    [∀ κ, Fintype (basisIdx κ)] [∀ κ, DecidableEq (basisIdx κ)]

/-!

## A. Tensors

Every tensor is a linear combination of pure tensors `S.pure f`, such as `u ⊗ α`. So a linear map
or an intertwining map out of tensors is fixed by its values on pure tensors. `ext` reduces to them
(`ext_pure`). A property closed under scalar multiplication and addition follows from the
pure case (`induction_on_pure`).

-/

-- `Tensor S c` is a `def`, not an `abbrev`, so Lean treats it as its own type. Then `g • T` is the
-- action of the group. On `⨂` the `•` is Mathlib's scalar action, so statements use `Tensor S c`.
-- A Mathlib lemma on `⨂` applies after `unfold Species.pure`. `map_pure` and `lift_pure` restate
-- the common ones.
/-- The tensors with colors `c : ι → Color K`, the space `⨂[k] i, S.colored.V (c i)`. -/
def Tensor (S : Tensor.Species k G K basisIdx) {ι : Type} (c : ι → Tensor.Color K) : Type :=
  ⨂[k] i, S.colored.V (c i)

/-- Tensors add as elements of `⨂[k] i, S.colored.V (c i)`. -/
noncomputable instance {S : Tensor.Species k G K basisIdx} {ι : Type} {c : ι → Tensor.Color K} :
    AddCommGroup (Tensor S c) :=
  (inferInstance : AddCommGroup (⨂[k] i, S.colored.V (c i)))

/-- Tensors are a vector space over `k`, as `⨂[k] i, S.colored.V (c i)` is. -/
noncomputable instance {S : Tensor.Species k G K basisIdx} {ι : Type} {c : ι → Tensor.Color K} :
    Module k (Tensor S c) :=
  (inferInstance : Module k (⨂[k] i, S.colored.V (c i)))

namespace Tensor

variable {ι : Type} {c : ι → Color K}

namespace Species

/-- The pure tensor `⨂ₜ i, f i` of vectors `f i` in `S.colored.V (c i)`, such as `u ⊗ α`. -/
noncomputable def pure (S : Species k G K basisIdx) (f : Π i, S.colored.V (c i)) : Tensor S c :=
  ⨂ₜ[k] i, f i

variable {S : Species k G K basisIdx}

/-- Mathlib's `PiTensorProduct.map` of linear maps `f i` on a pure tensor, `u ⊗ v ↦ f₀ u ⊗ f₁ v`. -/
lemma map_pure {c' : ι → Color K} (f : Π i, S.colored.V (c i) →ₗ[k] S.colored.V (c' i))
    (p : Π i, S.colored.V (c i)) :
    (PiTensorProduct.map f (S.pure p) : Tensor S c') = S.pure fun i => f i (p i) :=
  PiTensorProduct.map_tprod f p

/-- `PiTensorProduct.lift` of a multilinear map `F` on a pure tensor, `u ⊗ v ↦ F (u, v)`. -/
lemma lift_pure {E : Type*} [AddCommMonoid E] [Module k E]
    (F : MultilinearMap k (fun i => S.colored.V (c i)) E) (p : Π i, S.colored.V (c i)) :
    PiTensorProduct.lift F (S.pure p) = F p :=
  PiTensorProduct.lift.tprod p

/-- Induction on tensors through pure tensors. -/
lemma induction_on_pure {P : Tensor S c → Prop}
    (h : ∀ f : Π i, S.colored.V (c i), P (S.pure f)) (hsmul : ∀ (r : k) t, P t → P (r • t))
    (hadd : ∀ t₁ t₂, P t₁ → P t₂ → P (t₁ + t₂)) (t : Tensor S c) : P t :=
  PiTensorProduct.induction_on (motive := P) t (fun r f => hsmul r _ (h f)) hadd

/-- Two linear maps out of tensors are equal when they agree on pure tensors. -/
@[ext]
lemma ext_pure {E : Type*} [AddCommMonoid E] [Module k E] {f g : Tensor S c →ₗ[k] E}
    (h : ∀ p : Π i, S.colored.V (c i), f (S.pure p) = g (S.pure p)) : f = g :=
  PiTensorProduct.ext (MultilinearMap.ext h)

/-- Two equivalences of representations out of tensors are equal when they agree on pure
tensors. -/
lemma equiv_ext_pure {ρ' : Representation k G (Tensor S c)} {W : Type*} [AddCommMonoid W]
    [Module k W] {ρ : Representation k G W} {φ ψ : ρ'.Equiv ρ}
    (h : ∀ p : Π i, S.colored.V (c i), φ (S.pure p) = ψ (S.pure p)) : φ = ψ :=
  Representation.Equiv.ext <|
    funext <| LinearMap.congr_fun (ext_pure (f := φ.toLinearMap) (g := ψ.toLinearMap) h)

/-!

## B. The group action

### B.1. The action on tensors

A group element `Λ` transforms each index of a tensor by the representation of its color. For a
vector `u` and a covector `α`, `Λ • (u ⊗ α) = Λu ⊗ (Λ⁻¹)ᵀα` (`smul_pure`). In components this is
`u^μ α_ν ↦ Λ^μ_ρ u^ρ (Λ⁻¹)^σ_ν α_σ`. Mathlib already lets some groups act on vector spaces, such
as the phases `Circle`. For them `z • T` is the action of the species, not the scalar
multiplication by `z`. On a linear map `f` into tensors, `z • f` is Mathlib's action. The action of
the species on `f` is `S.tensorRep c z ∘ₗ f`.

-/

variable (S) in
/-- The action of the group on tensors, `Representation.piTprod` of the representations of the
colors. -/
noncomputable abbrev tensorRep (c : ι → Color K) : Representation k G (Tensor S c) :=
  Representation.piTprod fun i => S.colored.rep (c i)

end Species

variable {S : Species k G K basisIdx}

-- This instance and its projections have priority 1100. This is above Mathlib's scalar actions at
-- 1000 and below `high`. So `Λ • T`, `mul_smul` and `smul_add` use the action of the species, also
-- for `Circle` and `ℂˣ`.
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

-- Mathlib states this law as `SMulCommClass G k`. The other order, `SMulCommClass k G`, is not an
-- instance. With it, Mathlib's `TensorProduct.leftHasSMul` would let `Λ` act on `T ⊗ₜ U` through
-- `T` alone, as `(Λ • T) ⊗ₜ U`. A local `SMulCommClass.symm` restores that action where wanted.
/-- The action of the group commutes with the scalars, `Λ • (r • T) = r • (Λ • T)`. -/
instance smulCommClass : SMulCommClass G k (Tensor S c) where
  smul_comm g r t := map_smul (S.tensorRep c g) r t

namespace Species

/-- On a pure tensor the group acts on each vector by the representation of its color. -/
@[simp]
lemma smul_pure (g : G) (f : Π i, S.colored.V (c i)) :
    g • S.pure f = S.pure fun i => S.colored.rep (c i) g (f i) :=
  Representation.piTprod_tprod _ _ _

/-- A tensor with no indices is invariant, `Λ s = s`. -/
lemma smul_eq_self_of_isEmpty [IsEmpty ι] (g : G) (t : Tensor S c) : g • t = t :=
  LinearMap.congr_fun (PiTensorProduct.map_eq_id_of_isEmpty _) t

/-!

### B.2. Maps that commute with the group

A map of tensors that commutes with the group, `φ (Λ • T) = Λ • φ T`, is Mathlib's
`Representation.IntertwiningMap` for `tensorRep`, or `Representation.Equiv` when invertible.
Lowering an index with `congrAt` in `IndexMaps.lean` is such an equivalence. The commutation needs
a check on pure tensors only (`map_smul_of_pure`, `equivOfPure`).
`map_smul_of_pure` takes semilinear maps, so conjugate-linear maps, such as the complex conjugation
from undotted to dotted spinors, enter there.

-/

/-- An intertwining map between tensors commutes with the actions, `φ (Λ T) = Λ φ T`. -/
lemma intertwiningMap_smul {ι' : Type} {c' : ι' → Color K}
    (φ : (S.tensorRep c).IntertwiningMap (S.tensorRep c')) (g : G) (t : Tensor S c) :
    φ (g • t) = g • φ t :=
  Representation.IntertwiningMap.isIntertwining _ _ φ g t

/-- An equivalence of representations of tensors commutes with the actions, `φ (Λ T) = Λ φ T`. -/
lemma equiv_smul {ι' : Type} {c' : ι' → Color K}
    (φ : (S.tensorRep c).Equiv (S.tensorRep c')) (g : G) (t : Tensor S c) :
    φ (g • t) = g • φ t :=
  Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap g t

/-- A semilinear map of tensors that commutes with `Λ` on pure tensors commutes with `Λ` on all
tensors. -/
lemma map_smul_of_pure {ι' : Type} {c' : ι' → Color K} {σ : k →+* k} {F : Type*}
    [FunLike F (Tensor S c) (Tensor S c')] [SemilinearMapClass F σ (Tensor S c) (Tensor S c')]
    (f : F) (g : G) (h : ∀ p : Π i, S.colored.V (c i), f (g • S.pure p) = g • f (S.pure p))
    (t : Tensor S c) : f (g • t) = g • f t :=
  Representation.map_piTprod_of_tprod (τ := Representation.piTprod fun i => S.colored.rep (c' i))
    (f : Tensor S c →ₛₗ[σ] Tensor S c') g h t

variable {ι' : Type} {c' : ι' → Color K} in
/-- A linear equivalence of tensors that commutes with `Λ` on pure tensors, as an equivalence of
representations. -/
noncomputable def equivOfPure (e : Tensor S c ≃ₗ[k] Tensor S c')
    (h : ∀ (g : G) (p : Π i, S.colored.V (c i)), e (g • S.pure p) = g • e (S.pure p)) :
    (S.tensorRep c).Equiv (S.tensorRep c') :=
  .mk e fun g => LinearMap.ext fun t => map_smul_of_pure e g (h g) t

variable {ι' : Type} {c' : ι' → Color K} in
/-- `equivOfPure e h` acts as `e`. -/
@[simp]
lemma equivOfPure_apply (e : Tensor S c ≃ₗ[k] Tensor S c')
    (h : ∀ (g : G) (p : Π i, S.colored.V (c i)), e (g • S.pure p) = g • e (S.pure p))
    (t : Tensor S c) : equivOfPure e h t = e t := rfl

/-!

## C. The basis of tensors

`tensorBasis` is the basis `e_μ ⊗ e^ν`. The coordinates of a tensor in it are its components
`T^μ_ν`. The components of `Λ • T` take one matrix of `Λ` per index (`tensorBasis_repr_smul`).

-/

/-- The basis `e_μ ⊗ e^ν ⊗ …` of tensors, Mathlib's `Basis.piTensorProduct` of the bases of the
colors. -/
noncomputable def tensorBasis (S : Species k G K basisIdx) [Fintype ι] (c : ι → Color K) :
    Module.Basis (Π i, basisIdx (c i).kind) k (Tensor S c) :=
  Basis.piTensorProduct fun i => S.colored.basis (c i)

/-- A basis tensor is the pure tensor of basis vectors, `e_μ ⊗ e^ν ⊗ …`. -/
@[simp]
lemma tensorBasis_apply [Fintype ι] (x : Π i, basisIdx (c i).kind) :
    S.tensorBasis c x = S.pure fun i => S.colored.basis (c i) (x i) :=
  Basis.piTensorProduct_apply _ _

/-- The components of a pure tensor are products, `(u ⊗ α)^μ_ν = u^μ α_ν`. -/
lemma tensorBasis_repr_pure [Fintype ι] (f : Π i, S.colored.V (c i))
    (x : Π i, basisIdx (c i).kind) :
    (S.tensorBasis c).repr (S.pure f) x = ∏ i, (S.colored.basis (c i)).repr (f i) (x i) :=
  Basis.piTensorProduct_repr_tprod_apply _ _ _

/-- Tensors on finitely many indices are finite-dimensional. -/
instance [Finite ι] : Module.Finite k (Tensor S c) :=
  inferInstanceAs (Module.Finite k (⨂[k] i, S.colored.V (c i)))

/-- The dimension of tensors is the product of the dimensions of their indices. -/
lemma finrank_tensor [Fintype ι] (c : ι → Color K) :
    Module.finrank k (Tensor S c) = ∏ i, Fintype.card (basisIdx (c i).kind) :=
  Module.finrank_piTensorProduct.trans
    (Finset.prod_congr rfl fun i _ => Module.finrank_eq_card_basis (S.colored.basis (c i)))

/-- The components of `Λ • T` are `(Λ • T)^φ = ∑ ψ, (∏ i, M_i (φ i) (ψ i)) T^ψ`. The labels `φ` and
`ψ` give one basis label per index, and `M_i` is the matrix of `Λ` at the index `i`. For `T^μ_ν`
with the colors `![⟨vec, up⟩, ⟨vec, down⟩]`, this is `(Λ • T)^μ_ν = Λ^μ_σ (Λ⁻¹)^τ_ν T^σ_τ`. -/
lemma tensorBasis_repr_smul [Fintype ι] [DecidableEq ι] (Λ : G) (T : Tensor S c)
    (φ : Π i, basisIdx (c i).kind) :
    (S.tensorBasis c).repr (Λ • T) φ = ∑ ψ, (∏ i, LinearMap.toMatrix (S.colored.basis (c i))
      (S.colored.basis (c i)) (S.colored.rep (c i) Λ) (φ i) (ψ i)) *
        (S.tensorBasis c).repr T ψ := by
  simp_rw [← PiTensorProduct.toMatrix_map_apply]
  exact congrFun (LinearMap.toMatrix_mulVec_repr
    (Basis.piTensorProduct fun i => S.colored.basis (c i)) _
    (Representation.piTprod (fun i => S.colored.rep (c i)) Λ) T).symm φ

end Species

end Tensor
