/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Mathlib.RepresentationTheory.Intertwining
public import Physlib.Mathematics.ForMathlib.PiTensorProduct

/-!

# Tensor products of representations and invariant vectors

This file gives the representation on the tensor product of a family of representations, and makes
Mathlib's linear maps of such products into maps of representations.

## i. Overview

A representation `ρ` of a group or monoid `G` on a space `V` says how each element `g` of `G` acts
on `V`, by the linear map `ρ g`. A map of representations from `ρ` to `σ` on `W` is a linear map
`φ : V → W` that commutes with the group, `φ ∘ ρ g = σ g ∘ φ` for every `g`, so that the square

```
        ρ g
    V ──────► V
    │         │
  φ │         │ φ
    ▼         ▼
    W ──────► W
        σ g
```

commutes. Mathlib calls it an `IntertwiningMap`, and an `Equiv` when it is invertible. It sends an
invariant vector, `ρ g v = v`, to an invariant vector `φ v` (A).

For example, a Lorentz transformation `Λ` acts on vectors by `Λ` and on covectors by `(Λ⁻¹)ᵀ`, so
that `α_μ v^μ` is invariant. Lowering an index with the metric, `φ v = η v`, is a map of
representations from vectors to covectors. The two routes in the square give `η (Λ v)` and
`(Λ⁻¹)ᵀ (η v)`, which agree because `Λᵀ η Λ = η`, the defining property of a Lorentz
transformation.

Mathlib has the representation `ρ.tprod τ` on the tensor product of two representations, and the
tensor product `IntertwiningMap.tensor` of two intertwining maps. It has no representation on the
tensor product `⨂[k] i, M i` of a family, which is where a tensor with several indices lies. So
Mathlib's linear maps of `⨂`, such as `PiTensorProduct.reindex`, are not maps of representations.
This file defines that representation, `piTprod ρ`, and proves that Mathlib's linear maps of `⨂`
commute with it, so that they become maps of representations (C).

In the same way, the Lorentz tensors `T^μ_νρ` lie in `V ⊗ V* ⊗ V*`, with `Λ` on the vectors `V` and
`(Λ⁻¹)ᵀ` on the covectors `V*`. Reordering the factors to `V* ⊗ V ⊗ V*`, grouping them as
`V ⊗ (V* ⊗ V*)`, and contracting `V` with the first `V*`, `T^μ_μρ`, all commute with `Λ`. So each
one sends an invariant tensor to an invariant tensor, and a tensor built from invariant ones by
these maps is invariant with no further proof.

## ii. Key results

- `Representation.piTprod` : the representation on `⨂[k] i, M i` of a family of representations.
- `Representation.IsIntertwiningMap.piTprodMap` and `Representation.Equiv.piTprodCongr` :
  `PiTensorProduct.map` and `PiTensorProduct.congr` of maps of representations.
- `Representation.Equiv.piTprodReindex`, `Representation.Equiv.piTprodSum` and
  `Representation.Equiv.piTprodOfSubsingleton` : Mathlib's `reindex`, `tmulEquivDep` and
  `subsingletonEquiv` as equivalences of representations.
- `Representation.map_piTprod_of_tprod` : a map that commutes with `piTprod ρ` on pure tensors
  commutes with it on all tensors.
- `Representation.IntertwiningMap.map_invariant` : an intertwining map sends invariant vectors to
  invariant vectors.

## iii. Table of contents

- A. Invariant vectors
- B. Tensor products of equivalences
- C. Tensor products of families
  - C.1. The representation on a tensor product of a family
  - C.2. Mathlib's equivalences of tensor products
  - C.3. Commuting on pure tensors
  - C.4. Contraction of pairs of factors
- D. Representations given by actions

## iv. References

* None.

-/

@[expose] public section

open TensorProduct

variable {k G V W U X : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]
  [AddCommMonoid W] [Module k W] [AddCommMonoid U] [Module k U] [AddCommMonoid X] [Module k X]
  {ρ : Representation k G V} {σ : Representation k G W} {τ : Representation k G U}
  {π : Representation k G X}

/-!

## A. Invariant vectors

An intertwining map `φ` from `ρ` to `σ` satisfies `φ ∘ ρ g = σ g ∘ φ`, so it sends invariant
vectors to invariant vectors. If `ρ g v = v`, then `σ g (φ v) = φ (ρ g v) = φ v`
(`map_invariant`). An intertwining map from the trivial representation on `k` picks out the
invariant vector `φ 1` (`map_one_invariant`).

-/

/-- An intertwining map sends an invariant vector to an invariant vector,
`ρ g v = v → σ g (φ v) = φ v`. -/
lemma Representation.IntertwiningMap.map_invariant (φ : ρ.IntertwiningMap σ) {v : V} {g : G}
    (hv : ρ g v = v) : σ g (φ v) = φ v := by
  rw [← Representation.IntertwiningMap.isIntertwining, hv]

/-- An intertwining map `φ` from the trivial representation on `k` picks out an invariant vector,
`φ 1`. The hypothesis `φ 1 = v` turns a formula for `φ 1` into the invariance of `v`. -/
lemma Representation.IntertwiningMap.map_one_invariant
    (φ : (Representation.trivial k G k).IntertwiningMap ρ) {v : V} (hv : φ 1 = v) (g : G) :
    ρ g v = v :=
  hv ▸ φ.map_invariant rfl

/-!

## B. Tensor products of equivalences

Mathlib has the tensor product `IntertwiningMap.tensor` of two intertwining maps. `tensorCongr` is
the same for equivalences of representations, `v ⊗ w ↦ φ v ⊗ ψ w`, on `TensorProduct.congr`.

-/

/-- The tensor product of two equivalences of representations, `v ⊗ w ↦ φ v ⊗ ψ w`, Mathlib's
`TensorProduct.congr` with the actions `ρ ⊗ τ` and `σ ⊗ π`. -/
noncomputable def Representation.Equiv.tensorCongr (φ : ρ.Equiv σ) (ψ : τ.Equiv π) :
    (ρ.tprod τ).Equiv (σ.tprod π) :=
  .mk (TensorProduct.congr φ.toLinearEquiv ψ.toLinearEquiv)
    (φ.toIntertwiningMap.tensor ψ.toIntertwiningMap).isIntertwining'

@[simp]
lemma Representation.Equiv.tensorCongr_tmul (φ : ρ.Equiv σ) (ψ : τ.Equiv π) (v : V) (u : U) :
    φ.tensorCongr ψ (v ⊗ₜ u) = φ v ⊗ₜ ψ u := rfl

/-!

## C. Tensor products of families

### C.1. The representation on a tensor product of a family

`piTprod ρ` is the representation `g ↦ ⨂ i, ρ i g` on `⨂[k] i, M i`, through Mathlib's
`PiTensorProduct.map`. It is the n-ary `Representation.tprod`. When every `f i` intertwines `ρ i`
and `σ i`, `PiTensorProduct.map f` intertwines `piTprod ρ` and `piTprod σ` (`piTprodMap`), and
`piTprodCongr` is the same for equivalences of representations.

-/

section

variable {ι : Type*} {M N : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module k (M i)]
  [∀ i, AddCommMonoid (N i)] [∀ i, Module k (N i)]

/-- The tensor product of a family of representations, `g ↦ ⨂ i, ρ i g` on `⨂[k] i, M i`. It is
the n-ary `Representation.tprod`. -/
noncomputable def Representation.piTprod (ρ : Π i, Representation k G (M i)) :
    Representation k G (⨂[k] i, M i) :=
  PiTensorProduct.mapMonoidHom.comp (MonoidHom.pi ρ)

lemma Representation.piTprod_apply (ρ : Π i, Representation k G (M i)) (g : G) :
    Representation.piTprod ρ g = PiTensorProduct.map fun i => ρ i g := rfl

@[simp]
lemma Representation.piTprod_tprod (ρ : Π i, Representation k G (M i)) (g : G) (m : Π i, M i) :
    Representation.piTprod ρ g (⨂ₜ[k] i, m i) = ⨂ₜ[k] i, ρ i g (m i) :=
  PiTensorProduct.map_tprod _ _

/-- `PiTensorProduct.map f` intertwines `piTprod ρ` and `piTprod σ` when every `f i` intertwines
`ρ i` and `σ i`. -/
lemma Representation.IsIntertwiningMap.piTprodMap {ρ : Π i, Representation k G (M i)}
    {σ : Π i, Representation k G (N i)} {f : Π i, M i →ₗ[k] N i}
    (hf : ∀ i, (ρ i).IsIntertwiningMap (σ i) (f i)) :
    (Representation.piTprod ρ).IsIntertwiningMap (Representation.piTprod σ)
      (PiTensorProduct.map f) where
  isIntertwining g v := by
    rw [Representation.piTprod_apply, Representation.piTprod_apply, ← LinearMap.comp_apply,
      ← PiTensorProduct.map_comp, ← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
    exact congr(PiTensorProduct.map $(funext fun i => LinearMap.ext ((hf i).isIntertwining g)) v)

/-- The tensor product of a family of equivalences of representations, `⨂ i, v i ↦ ⨂ i, φ i (v i)`.
It is Mathlib's `PiTensorProduct.congr` with the actions `piTprod ρ` and `piTprod σ`. -/
noncomputable def Representation.Equiv.piTprodCongr {ρ : Π i, Representation k G (M i)}
    {σ : Π i, Representation k G (N i)} (φ : Π i, (ρ i).Equiv (σ i)) :
    (Representation.piTprod ρ).Equiv (Representation.piTprod σ) :=
  .mk (PiTensorProduct.congr fun i => (φ i).toLinearEquiv) fun g => LinearMap.ext
    ((Representation.IsIntertwiningMap.piTprodMap fun i =>
      ⟨(φ i).toIntertwiningMap.isIntertwining⟩).isIntertwining g)

@[simp]
lemma Representation.Equiv.piTprodCongr_tprod {ρ : Π i, Representation k G (M i)}
    {σ : Π i, Representation k G (N i)} (φ : Π i, (ρ i).Equiv (σ i)) (m : Π i, M i) :
    Representation.Equiv.piTprodCongr φ (⨂ₜ[k] i, m i) = ⨂ₜ[k] i, φ i (m i) :=
  PiTensorProduct.congr_tprod _ _

/-!

### C.2. Mathlib's equivalences of tensor products

Three of Mathlib's linear equivalences of `⨂` commute with `piTprod`, so they are equivalences of
representations. `piTprodReindex` reindexes the factors along `e : ι ≃ ι'`,
`⨂ i, v i ↦ ⨂ j, v (e.symm j)`. `piTprodSum` joins the tensor products of the two halves of a
family over `ι₁ ⊕ ι₂`. `piTprodOfSubsingleton` identifies `ρ i₀` with the tensor product of a
family over a subsingleton index type.

-/

/-- Reindexing the factors of a tensor product of representations along `e : ι ≃ ι'`,
`⨂ i, v i ↦ ⨂ j, v (e.symm j)`. It is Mathlib's `PiTensorProduct.reindex` with the actions
`piTprod ρ` and `piTprod (ρ ∘ e.symm)`. -/
noncomputable def Representation.Equiv.piTprodReindex {ι' : Type*}
    (ρ : Π i, Representation k G (M i)) (e : ι ≃ ι') :
    (Representation.piTprod ρ).Equiv (Representation.piTprod fun j => ρ (e.symm j)) :=
  .mk (PiTensorProduct.reindex k M e) fun g => PiTensorProduct.ext <| MultilinearMap.ext fun m => by
    simp [PiTensorProduct.reindex_tprod]

@[simp]
lemma Representation.Equiv.piTprodReindex_tprod {ι' : Type*} (ρ : Π i, Representation k G (M i))
    (e : ι ≃ ι') (m : Π i, M i) :
    Representation.Equiv.piTprodReindex ρ e (⨂ₜ[k] i, m i) = ⨂ₜ[k] j, m (e.symm j) :=
  PiTensorProduct.reindex_tprod _ _

/-- The tensor product of the two halves of a family of representations indexed by `ι₁ ⊕ ι₂`,
`(⨂ i, v i) ⊗ (⨂ j, w j) ↦ ⨂ s, Sum.rec v w s`. It is Mathlib's `PiTensorProduct.tmulEquivDep`
with the actions. -/
noncomputable def Representation.Equiv.piTprodSum {ι₁ ι₂ : Type*} {M : ι₁ ⊕ ι₂ → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module k (M i)] (ρ : Π i, Representation k G (M i)) :
    ((Representation.piTprod fun i => ρ (.inl i)).tprod
      (Representation.piTprod fun j => ρ (.inr j))).Equiv (Representation.piTprod ρ) :=
  .mk (PiTensorProduct.tmulEquivDep k M) fun g => by
    ext f₁ f₂
    simp only [Representation.tprod_apply, LinearMap.compMultilinearMap_apply,
      TensorProduct.AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_self,
      TensorProduct.curry_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      TensorProduct.map_tmul, Representation.piTprod_tprod, PiTensorProduct.tmulEquivDep_apply]
    exact congrArg (PiTensorProduct.tprod k) (funext fun s => by rcases s with _ | _ <;> rfl)

@[simp]
lemma Representation.Equiv.piTprodSum_tmul {ι₁ ι₂ : Type*} {M : ι₁ ⊕ ι₂ → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module k (M i)] (ρ : Π i, Representation k G (M i))
    (f₁ : Π i, M (.inl i)) (f₂ : Π j, M (.inr j)) :
    Representation.Equiv.piTprodSum ρ ((⨂ₜ[k] i, f₁ i) ⊗ₜ (⨂ₜ[k] j, f₂ j)) =
      ⨂ₜ[k] s, Sum.rec f₁ f₂ s :=
  PiTensorProduct.tmulEquivDep_apply k M f₁ f₂

/-- A representation `ρ i₀` as the tensor product of a family `ρ` over a subsingleton index type,
`v ↦ ⨂ i, v`. It is Mathlib's `PiTensorProduct.subsingletonEquiv` with the actions. -/
noncomputable def Representation.Equiv.piTprodOfSubsingleton [Subsingleton ι]
    (ρ : Π i, Representation k G (M i)) (i₀ : ι) :
    (ρ i₀).Equiv (Representation.piTprod ρ) :=
  .mk (PiTensorProduct.subsingletonEquiv i₀).symm fun g => LinearMap.ext fun v => by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      PiTensorProduct.subsingletonEquiv_symm_apply, Representation.piTprod_tprod]
    congr 1
    ext i
    obtain rfl := Subsingleton.elim i i₀
    simp

/-!

### C.3. Commuting on pure tensors

A semilinear map out of `⨂ i, M i` that commutes with `piTprod ρ g` on pure tensors `⨂ₜ i, m i`
commutes with it on all tensors (`map_piTprod_of_tprod`), since pure tensors span `⨂ i, M i`.

-/

/-- A semilinear map out of `⨂ i, M i` that commutes with `piTprod ρ g` on pure tensors commutes
with it on all tensors. -/
lemma Representation.map_piTprod_of_tprod {φ : k →+* k} {ρ : Π i, Representation k G (M i)}
    (f : (⨂[k] i, M i) →ₛₗ[φ] U) (g : G)
    (h : ∀ m : Π i, M i, f (Representation.piTprod ρ g (⨂ₜ[k] i, m i)) = τ g (f (⨂ₜ[k] i, m i)))
    (t : ⨂[k] i, M i) : f (Representation.piTprod ρ g t) = τ g (f t) := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r m => rw [map_smul, map_smulₛₗ, h, map_smulₛₗ, map_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-!

### C.4. Contraction of pairs of factors

`PiTensorProduct.contrPairs p` contracts the factors of a family over `κ ⊕ (J ⊕ J)` in pairs, by
the pairings `p j`, and keeps the factors over `κ`. When every pairing is invariant, the
contraction intertwines `piTprod ρ` and `piTprod` of the kept factors.

-/

/-- `PiTensorProduct.contrPairs p` intertwines `piTprod ρ` and `piTprod` of the kept factors when
every pairing `p j` is invariant. -/
lemma Representation.IsIntertwiningMap.contrPairs {κ J : Type*} [Fintype J]
    {M : κ ⊕ (J ⊕ J) → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module k (M i)]
    {ρ : Π i, Representation k G (M i)}
    {p : Π j, M (.inr (.inl j)) ⊗[k] M (.inr (.inr j)) →ₗ[k] k}
    (hp : ∀ j g x y, p j (ρ _ g x ⊗ₜ ρ _ g y) = p j (x ⊗ₜ y)) :
    (Representation.piTprod ρ).IsIntertwiningMap (Representation.piTprod fun x => ρ (.inl x))
      (PiTensorProduct.contrPairs p) where
  isIntertwining g v := by
    induction v using PiTensorProduct.induction_on with
    | smul_tprod r f =>
      simp only [map_smul, Representation.piTprod_tprod, PiTensorProduct.contrPairs_tprod, hp,
        smul_comm r]
    | add x y hx hy => simp only [map_add, hx, hy]

end

/-!

## D. Representations given by actions

A representation can be given by an action, `Representation.ofDistribMulAction k G V`, with
`ρ g v = g • v`. Maps of such representations commute with the actions, `φ (g • v) = g • φ v`.

-/

section

variable [DistribMulAction G V] [SMulCommClass G k V] [DistribMulAction G W] [SMulCommClass G k W]

/-- An intertwining map of representations given by actions commutes with the actions,
`φ (g • v) = g • φ v`. -/
lemma Representation.IntertwiningMap.map_smul_ofDistribMulAction
    (φ : (Representation.ofDistribMulAction k G V).IntertwiningMap
      (Representation.ofDistribMulAction k G W)) (g : G) (v : V) :
    φ (g • v) = g • φ v :=
  Representation.IntertwiningMap.isIntertwining _ _ φ g v

/-- An equivalence of representations given by actions commutes with the actions,
`φ (g • v) = g • φ v`. -/
lemma Representation.Equiv.map_smul_ofDistribMulAction
    (φ : (Representation.ofDistribMulAction k G V).Equiv
      (Representation.ofDistribMulAction k G W)) (g : G) (v : V) :
    φ (g • v) = g • φ v :=
  φ.toIntertwiningMap.map_smul_ofDistribMulAction g v

end
